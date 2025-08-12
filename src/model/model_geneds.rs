//! Functions for adding GenEd constraints.
use super::model_context::Course;
use super::model_context::ModelBuilderContext;
use crate::geneds::{GenEd, GenEdReq};
use cp_sat::builder::LinearExpr;

/// Add GenEd constraints to the model.
pub fn add_gened_constraints<'a>(ctx: &mut ModelBuilderContext<'a>) {
    let model = &mut ctx.model;
    let courses = &ctx.courses;
    let vars = &ctx.vars;
    let num_semesters = ctx.num_semesters;
    let geneds = match ctx.catalog {
        Some(catalog) => &catalog.geneds,
        None => return,
    };

    // Helper: for a course code, find its index in flat_courses
    let code_to_idx: std::collections::HashMap<_, _> = courses
        .iter()
        .enumerate()
        .map(|(i, course)| (course.code.clone(), i))
        .collect();

    // Helper: for a course code, return a variable that is 1 if the course is scheduled in any semester
    let course_in_schedule = |idx: usize| {
        let mut expr = LinearExpr::from(0);
        for s in 0..num_semesters {
            expr = expr + LinearExpr::from(vars[idx][s].clone());
        }
        expr
    };

    // Helper: for a set of course codes, return a vector of their indices (if all present)
    let codes_to_indices = |codes: &Vec<crate::schedule::CourseCode>| -> Option<Vec<usize>> {
        codes.iter().map(|c| code_to_idx.get(c).copied()).collect()
    };

    // --- Core GenEds: no overlap restrictions ---
    for gened in geneds.iter() {
        if let GenEd::Core { req, .. } = gened {
            match req {
                GenEdReq::Set(codes) => {
                    if let Some(indices) = codes_to_indices(codes) {
                        for idx in indices {
                            // Each course must be scheduled somewhere
                            model.add_ge(course_in_schedule(idx), LinearExpr::from(1));
                        }
                    }
                }
                GenEdReq::SetOpts(opts) => {
                    // At least one option set must be fully present
                    let mut option_exprs = Vec::new();
                    for opt in opts {
                        if let Some(indices) = codes_to_indices(opt) {
                            // All courses in this option must be present
                            let mut all_present = LinearExpr::from(0);
                            for idx in indices {
                                all_present = all_present + course_in_schedule(idx);
                            }
                            // If all are present, sum == len
                            // Use a bool var to represent this option
                            let opt_var = model.new_bool_var();
                            // model.add_le(all_present.clone(), LinearExpr::from(opt.len() as i64) + (LinearExpr::from(1) - opt_var.clone()) * (opt.len() as i64));
                            // model.add_ge(all_present, LinearExpr::from(opt.len() as i64) - (LinearExpr::from(1) - opt_var.clone()) * (opt.len() as i64));
                            // Instead, expand (LinearExpr * n) as repeated addition
                            let mut le_expr = LinearExpr::from(1) - opt_var.clone();
                            let mut le_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                le_scaled = le_scaled + le_expr.clone();
                            }
                            model.add_le(all_present.clone(), LinearExpr::from(opt.len() as i64) + le_scaled);
                            let mut ge_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                ge_scaled = ge_scaled + le_expr.clone();
                            }
                            model.add_ge(all_present, LinearExpr::from(opt.len() as i64) - ge_scaled);
                            option_exprs.push(opt_var);
                        }
                    }
                    if !option_exprs.is_empty() {
                        let mut sum = LinearExpr::from(0);
                        for v in option_exprs { sum = sum + LinearExpr::from(v); }
                        model.add_ge(sum, LinearExpr::from(1));
                    }
                }
                GenEdReq::Courses { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in indices { sum = sum + course_in_schedule(idx); }
                        model.add_ge(sum, LinearExpr::from(*num as i64));
                    }
                }
                GenEdReq::Credits { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in indices.iter() {
                            let credits = ctx.courses[*idx].credits;
                            // sum = sum + course_in_schedule(*idx) * credits;
                            if credits > 0 {
                                for _ in 0..credits {
                                    sum = sum + course_in_schedule(*idx);
                                }
                            } else if credits < 0 {
                                for _ in 0..(-credits) {
                                    sum = sum - course_in_schedule(*idx);
                                }
                            }
                        }
                        model.add_ge(sum, LinearExpr::from(*num as i64));
                    }
                }
            }
        }
    }

    // --- Foundation GenEds: enforce required number/credits, no course may satisfy more than one Foundation ---
    // For each Foundation, build a set of eligible courses and add a hard constraint for the requirement
    let mut foundation_sets = Vec::new();
    for gened in geneds.iter() {
        if let GenEd::Foundation { req, .. } = gened {
            match req {
                GenEdReq::Set(codes) => {
                    if let Some(indices) = codes_to_indices(codes) {
                        foundation_sets.push(indices);
                    }
                }
                GenEdReq::SetOpts(opts) => {
                    let mut all_indices = Vec::new();
                    for opt in opts {
                        if let Some(indices) = codes_to_indices(opt) {
                            all_indices.extend(indices);
                        }
                    }
                    foundation_sets.push(all_indices);
                }
                GenEdReq::Courses { courses, .. } | GenEdReq::Credits { courses, .. } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        foundation_sets.push(indices);
                    }
                }
            }
        }
    }
    let num_foundations = foundation_sets.len();
    let mut foundation_reqs = Vec::new();
    for (f, set) in foundation_sets.iter().enumerate() {
        let required = match &geneds.iter().filter(|g| matches!(g, GenEd::Foundation { .. })).nth(f) {
            Some(GenEd::Foundation { req, .. }) => match req {
                GenEdReq::Set(codes) => codes.len() as i64,
                GenEdReq::SetOpts(opts) => opts.iter().map(|o| o.len()).max().unwrap_or(1) as i64,
                GenEdReq::Courses { num, .. } => *num as i64,
                GenEdReq::Credits { num, .. } => *num as i64,
            },
            _ => 1,
        };
        foundation_reqs.push((set.clone(), required));
    }
    // Map: course idx -> eligible Foundations
    let mut course_foundations: std::collections::HashMap<usize, Vec<usize>> = std::collections::HashMap::new();
    for (f, (set, _)) in foundation_reqs.iter().enumerate() {
        for &idx in set {
            course_foundations.entry(idx).or_default().push(f);
        }
    }
    // For each required course eligible for Foundations, assign it to exactly one eligible Foundation
    for (&idx, foundations) in &course_foundations {
        if courses[idx].required && !foundations.is_empty() {
            let mut assign_vars = Vec::new();
            for &f in foundations {
                let assign = model.new_bool_var();
                // If assigned, course must be scheduled
                model.add_le(assign.clone(), course_in_schedule(idx));
                assign_vars.push(assign);
            }
            // Must be assigned to exactly one Foundation
            let mut sum = LinearExpr::from(0);
            for v in &assign_vars { sum = sum + LinearExpr::from(v.clone()); }
            // Each required course must be assigned to at most one Foundation (could be zero if not scheduled)
            model.add_le(sum.clone(), LinearExpr::from(1));
            // If the course is scheduled, it must be assigned to exactly one Foundation
            // (This ensures that only scheduled required courses are assigned)
            model.add_eq(sum, course_in_schedule(idx));
        }
    }
    // For each Foundation, require that at least the required number of distinct eligible courses are scheduled
    for (f, (set, required)) in foundation_reqs.iter().enumerate() {
        let mut sum = LinearExpr::from(0);
        let mut eligible_electives = Vec::new();
        for &idx in set {
            sum = sum + course_in_schedule(idx);
            if !courses[idx].required {
                eligible_electives.push(courses[idx].code.clone());
            }
        }
        if eligible_electives.len() > 0 {
            println!("[GENED DIAG] Foundation {} eligible electives: {:?}", f, eligible_electives);
        }
        model.add_ge(sum, LinearExpr::from(*required));
    }
    // For every pair of Foundations, require that the number of scheduled courses in the intersection is at most the overlap allowed (usually zero),
    // but do NOT count required courses (they are handled by the assignment constraint above)
    use std::collections::HashSet;
    for i in 0..num_foundations {
        for j in (i+1)..num_foundations {
            let set_i: HashSet<_> = foundation_reqs[i].0.iter().copied().collect();
            let set_j: HashSet<_> = foundation_reqs[j].0.iter().copied().collect();
            let intersection: Vec<_> = set_i.intersection(&set_j).copied().collect();
            if !intersection.is_empty() {
                // DIAGNOSTIC: Print intersection and which are required
                println!("[GENED DIAG] Foundation intersection {} & {}: {:?}", i, j, intersection.iter().map(|idx| courses[*idx].code.clone()).collect::<Vec<_>>());
                let mut required_inters = Vec::new();
                let mut nonrequired_inters = Vec::new();
                for &idx in &intersection {
                    if courses[idx].required {
                        required_inters.push(courses[idx].code.clone());
                    } else {
                        nonrequired_inters.push(courses[idx].code.clone());
                    }
                }
                println!("[GENED DIAG]   Required in intersection: {:?}", required_inters);
                println!("[GENED DIAG]   Non-required in intersection: {:?}", nonrequired_inters);
                println!("[GENED DIAG] Foundation intersection {} & {}: {:?}", i, j, intersection.iter().map(|idx| courses[*idx].code.clone()).collect::<Vec<_>>());
                let mut sum = LinearExpr::from(0);
                for &idx in &intersection {
                    if !courses[idx].required {
                        sum = sum + course_in_schedule(idx);
                    } else {
                        println!("[GENED DIAG]   Required course in intersection: {} (idx {})", courses[idx].code, idx);
                    }
                }
                model.add_le(sum, LinearExpr::from(0));
            }
        }
    }

    // The rest of the Foundation assignment logic (assignment matrix, etc.) can remain as before, but now feasibility is guaranteed by the above constraints.

    // --- Skills & Perspectives: no course may satisfy more than 3 S&Ps ---
    let mut sp_sets = Vec::new();
    for gened in geneds.iter() {
        if let GenEd::SkillAndPerspective { req, .. } = gened {
            match req {
                GenEdReq::Set(codes) | GenEdReq::Courses { courses: codes, .. } | GenEdReq::Credits { courses: codes, .. } => {
                    if let Some(indices) = codes_to_indices(codes) {
                        sp_sets.push(indices);
                    }
                }
                GenEdReq::SetOpts(opts) => {
                    let mut indices = Vec::new();
                    for opt in opts {
                        if let Some(opt_indices) = codes_to_indices(opt) {
                            indices.extend(opt_indices);
                        }
                    }
                    sp_sets.push(indices);
                }
            }
        }
    }
    // For each course, count how many S&Ps it could satisfy
    let mut course_sp_counts: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    for set in sp_sets.iter() {
        for &idx in set {
            *course_sp_counts.entry(idx).or_insert(0) += 1;
        }
    }
    // For each course, add constraint: sum of S&P assignments <= 3
    for (&idx, &count) in &course_sp_counts {
        if count > 3 {
            // For each S&P, create a bool var if this course is used for that S&P
            let mut used_vars = Vec::new();
            for set in &sp_sets {
                if set.contains(&idx) {
                    let used = model.new_bool_var();
                    model.add_le(used.clone(), course_in_schedule(idx));
                    used_vars.push(used);
                }
            }
            let mut sum = LinearExpr::from(0);
            for v in used_vars { sum = sum + LinearExpr::from(v); }
            model.add_le(sum, LinearExpr::from(3));
        }
    }

    // Print all required courses
    let required_courses: Vec<_> = courses.iter().enumerate().filter(|(_, c)| c.required).collect();
    eprintln!("[GENED DIAG] Required courses ({}):", required_courses.len());
    for (idx, c) in &required_courses {
        eprintln!("  {} (idx {})", c.code, idx);
    }
    // For each Foundation, print which required courses are eligible
    for (f, set) in foundation_sets.iter().enumerate() {
        let eligible_required: Vec<_> = set.iter().filter(|&&idx| courses[idx].required).map(|&idx| &courses[idx].code).collect();
        eprintln!("[GENED DIAG] Foundation {} eligible required: {:?}", f, eligible_required);
        if eligible_required.is_empty() {
            eprintln!("[GENED DIAG][WARNING] Foundation {} has NO eligible required courses!", f);
        }
    }
}
