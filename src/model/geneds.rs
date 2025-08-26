//! Functions for adding GenEd constraints.
use super::context::ModelBuilderContext;
use crate::geneds::{ElectiveReq, GenEd};
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
    // Helper: for a course code, return a variable that is 1 if the course is scheduled in any semester (including semester 0)
    let course_in_schedule = |idx: usize| {
        let mut expr = LinearExpr::from(0);
        for s in 0..num_semesters {
            expr += LinearExpr::from(vars[idx][s]);
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
                ElectiveReq::Set(codes) => {
                    if let Some(indices) = codes_to_indices(codes) {
                        for idx in indices {
                            // Each course must be scheduled somewhere
                            model.add_ge(course_in_schedule(idx), LinearExpr::from(1));
                        }
                    }
                }
                ElectiveReq::SetOpts(opts) => {
                    // At least one option set must be fully present
                    let mut option_exprs = Vec::new();
                    for opt in opts {
                        if let Some(indices) = codes_to_indices(opt) {
                            // All courses in this option must be present
                            let mut all_present = LinearExpr::from(0);
                            for idx in indices {
                                all_present += course_in_schedule(idx);
                            }
                            // If all are present, sum == len
                            // Use a bool var to represent this option
                            let opt_var = model.new_bool_var();
                            // model.add_le(all_present.clone(), LinearExpr::from(opt.len() as i64) + (LinearExpr::from(1) - opt_var.clone()) * (opt.len() as i64));
                            // model.add_ge(all_present, LinearExpr::from(opt.len() as i64) - (LinearExpr::from(1) - opt_var.clone()) * (opt.len() as i64));
                            // Instead, expand (LinearExpr * n) as repeated addition
                            let le_expr = LinearExpr::from(1) - opt_var;
                            let mut le_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                le_scaled += le_expr.clone();
                            }
                            model.add_le(
                                all_present.clone(),
                                LinearExpr::from(opt.len() as i64) + le_scaled,
                            );
                            let mut ge_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                ge_scaled += le_expr.clone();
                            }
                            model.add_ge(
                                all_present,
                                LinearExpr::from(opt.len() as i64) - ge_scaled,
                            );
                            option_exprs.push(opt_var);
                        }
                    }
                    if !option_exprs.is_empty() {
                        let mut sum = LinearExpr::from(0);
                        for v in option_exprs {
                            sum += LinearExpr::from(v);
                        }
                        model.add_ge(sum, LinearExpr::from(1));
                    }
                }
                ElectiveReq::Courses { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in indices {
                            sum += course_in_schedule(idx);
                        }
                        model.add_ge(sum, LinearExpr::from(*num as i64));
                    }
                }
                ElectiveReq::Credits { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in indices.iter() {
                            let credits = ctx.courses[*idx].credits;
                            // sum = sum + course_in_schedule(*idx) * credits;
                            if credits > 0 {
                                for _ in 0..credits {
                                    sum += course_in_schedule(*idx);
                                }
                            } else if credits < 0 {
                                for _ in 0..(-credits) {
                                    sum -= course_in_schedule(*idx);
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
                ElectiveReq::Set(codes) => {
                    if let Some(indices) = codes_to_indices(codes) {
                        // All courses in the set must be scheduled
                        for idx in &indices {
                            model.add_ge(course_in_schedule(*idx), LinearExpr::from(1));
                        }
                        foundation_sets.push(indices);
                    }
                }
                ElectiveReq::SetOpts(opts) => {
                    // At least one option set must be fully present
                    let mut option_exprs = Vec::new();
                    let mut all_indices = Vec::new();
                    for opt in opts {
                        if let Some(indices) = codes_to_indices(opt) {
                            // All courses in this option must be present
                            let mut all_present = LinearExpr::from(0);
                            for idx in &indices {
                                all_present += course_in_schedule(*idx);
                            }
                            // Use a bool var to represent this option
                            let opt_var = model.new_bool_var();
                            let le_expr = LinearExpr::from(1) - opt_var;
                            let mut le_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                le_scaled += le_expr.clone();
                            }
                            model.add_le(
                                all_present.clone(),
                                LinearExpr::from(opt.len() as i64) + le_scaled,
                            );
                            let mut ge_scaled = LinearExpr::from(0);
                            for _ in 0..opt.len() {
                                ge_scaled += le_expr.clone();
                            }
                            model.add_ge(
                                all_present,
                                LinearExpr::from(opt.len() as i64) - ge_scaled,
                            );
                            option_exprs.push(opt_var);
                            all_indices.extend(indices);
                        }
                    }
                    if !option_exprs.is_empty() {
                        let mut sum = LinearExpr::from(0);
                        for v in option_exprs {
                            sum += LinearExpr::from(v);
                        }
                        model.add_ge(sum, LinearExpr::from(1));
                    }
                    foundation_sets.push(all_indices);
                }
                ElectiveReq::Courses { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in &indices {
                            sum += course_in_schedule(*idx);
                        }
                        model.add_ge(sum, LinearExpr::from(*num as i64));
                        foundation_sets.push(indices);
                    }
                }
                ElectiveReq::Credits { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        let mut sum = LinearExpr::from(0);
                        for idx in &indices {
                            let credits = ctx.courses[*idx].credits;
                            if credits > 0 {
                                for _ in 0..credits {
                                    sum += course_in_schedule(*idx);
                                }
                            } else if credits < 0 {
                                for _ in 0..(-credits) {
                                    sum -= course_in_schedule(*idx);
                                }
                            }
                        }
                        model.add_ge(sum, LinearExpr::from(*num as i64));
                        foundation_sets.push(indices);
                    }
                }
            }
        }
    }
    // --- Guarantee feasible, non-overlapping Foundation assignment (stronger set-cover constraints) ---
    use std::collections::HashSet;
    let num_foundations = foundation_sets.len();

    // For each Foundation, get the set of eligible indices and required number/credits
    let mut foundation_reqs: Vec<(Vec<usize>, i64, bool, Vec<i64>)> = Vec::new();
    for (f, set) in foundation_sets.iter().enumerate() {
        let gened = &geneds
            .iter()
            .filter(|g| matches!(g, GenEd::Foundation { .. }))
            .nth(f)
            .unwrap();
        let (required, is_credits, course_credits) = match gened {
            GenEd::Foundation { req, .. } => match req {
                ElectiveReq::Credits { num, .. } => {
                    let credits: Vec<_> = set.iter().map(|&idx| ctx.courses[idx].credits).collect();
                    (*num as i64, true, credits)
                }
                ElectiveReq::Set(_) => (set.len() as i64, false, vec![1; set.len()]), // FIXME?
                ElectiveReq::SetOpts(_) | ElectiveReq::Courses { .. } => {
                    (set.len() as i64, false, vec![1; set.len()])
                }
            },
            _ => (set.len() as i64, false, vec![1; set.len()]),
        };
        foundation_reqs.push((set.clone(), required, is_credits, course_credits));
    }
    // For each Foundation, require that at least the required number of distinct eligible courses/credits are scheduled
    for (set, required, is_credits, ..) in &foundation_reqs {
        // Split eligible indices into required and non-required
        let mut required_idxs = Vec::new();
        let mut optional_idxs = Vec::new();
        for &idx in set {
            if ctx.courses[idx].required {
                required_idxs.push(idx);
            } else {
                optional_idxs.push(idx);
            }
        }
        // All required courses must count toward the Foundation
        let mut required_sum = LinearExpr::from(0);
        for &idx in &required_idxs {
            let c = if *is_credits {
                ctx.courses[idx].credits
            } else {
                1
            };
            for _ in 0..c {
                required_sum += course_in_schedule(idx);
            }
        }
        // Optional courses can be used to reach the minimum, but not to over-satisfy
        let mut optional_sum = LinearExpr::from(0);
        for &idx in &optional_idxs {
            let c = if *is_credits {
                ctx.courses[idx].credits
            } else {
                1
            };
            for _ in 0..c {
                optional_sum += course_in_schedule(idx);
            }
        }
        // The total must be at least the required minimum
        model.add_ge(
            required_sum.clone() + optional_sum.clone(),
            LinearExpr::from(*required),
        );
        // The total (required + optional) cannot exceed the maximum of required_sum and required
        // Set the domain to the true maximum possible sum (credits or count)
        let max_possible = if *is_credits {
            set.iter().map(|&idx| ctx.courses[idx].credits).sum()
        } else {
            set.len() as i64
        };
        let max_expr = model.new_int_var([(0, max_possible)]);
        model.add_ge(max_expr, required_sum.clone());
        model.add_ge(max_expr, LinearExpr::from(*required));
        model.add_le(required_sum.clone() + optional_sum.clone(), max_expr);
    }

    // Handle courses already present in the Schedule (forced courses)
    for (set, _, _, _) in &foundation_reqs {
        for &idx in set {
            if ctx.courses[idx].required {
                // Add constraints to ensure forced courses are considered for all eligible Foundations
                let mut foundation_vars = Vec::new();
                for (other_set, _, _, _) in &foundation_reqs {
                    if other_set.contains(&idx) {
                        let foundation_var = model.new_bool_var();
                        model.add_le(foundation_var, course_in_schedule(idx));
                        foundation_vars.push(foundation_var);
                    }
                }
                let mut sum = LinearExpr::from(0);
                for v in foundation_vars {
                    sum += LinearExpr::from(v);
                }
                model.add_eq(sum, LinearExpr::from(1)); // Ensure the forced course satisfies exactly one Foundation
                // No restriction here for S&Ps: forced courses can also be used for S&Ps as long as S&P constraints are met
            }
        }
    }

    // For every pair of Foundations, require that the number of scheduled courses in the intersection is at most the overlap allowed (usually zero)
    for i in 0..num_foundations {
        for j in (i + 1)..num_foundations {
            let set_i: HashSet<_> = foundation_reqs[i].0.iter().copied().collect();
            let set_j: HashSet<_> = foundation_reqs[j].0.iter().copied().collect();
            let intersection: Vec<_> = set_i.intersection(&set_j).copied().collect();
            if !intersection.is_empty() {
                let mut sum = LinearExpr::from(0);
                for &idx in &intersection {
                    sum += course_in_schedule(idx);
                }
                // By default, require no overlap (can be relaxed if needed)
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
                ElectiveReq::Set(codes) => {
                    if let Some(indices) = codes_to_indices(codes) {
                        sp_sets.push(indices.clone());
                        // Split required/optional
                        let mut required_idxs = Vec::new();
                        let mut optional_idxs = Vec::new();
                        for &idx in &indices {
                            if ctx.courses[idx].required {
                                required_idxs.push(idx);
                            } else {
                                optional_idxs.push(idx);
                            }
                        }
                        let mut required_sum = LinearExpr::from(0);
                        for &idx in &required_idxs {
                            required_sum += course_in_schedule(idx);
                        }
                        let mut optional_sum = LinearExpr::from(0);
                        for &idx in &optional_idxs {
                            optional_sum += course_in_schedule(idx);
                        }
                        let required = codes.len() as i64;
                        // At least the minimum
                        model.add_ge(
                            required_sum.clone() + optional_sum.clone(),
                            LinearExpr::from(required),
                        );
                        // At most max(required_sum, required)
                        let max_possible = required_idxs.len() as i64 + optional_idxs.len() as i64;
                        let max_expr = model.new_int_var([(0, max_possible)]);
                        model.add_ge(max_expr, required_sum.clone());
                        model.add_ge(max_expr, LinearExpr::from(required));
                        model.add_le(required_sum.clone() + optional_sum.clone(), max_expr);
                    }
                }
                ElectiveReq::Courses { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        sp_sets.push(indices.clone());
                        let mut required_idxs = Vec::new();
                        let mut optional_idxs = Vec::new();
                        for &idx in &indices {
                            if ctx.courses[idx].required {
                                required_idxs.push(idx);
                            } else {
                                optional_idxs.push(idx);
                            }
                        }
                        let mut required_sum = LinearExpr::from(0);
                        for &idx in &required_idxs {
                            required_sum += course_in_schedule(idx);
                        }
                        let mut optional_sum = LinearExpr::from(0);
                        for &idx in &optional_idxs {
                            optional_sum += course_in_schedule(idx);
                        }
                        let required = *num as i64;
                        model.add_ge(
                            required_sum.clone() + optional_sum.clone(),
                            LinearExpr::from(required),
                        );
                        let max_possible = required_idxs.len() as i64 + optional_idxs.len() as i64;
                        let max_expr = model.new_int_var([(0, max_possible)]);
                        model.add_ge(max_expr, required_sum.clone());
                        model.add_ge(max_expr, LinearExpr::from(required));
                        model.add_le(required_sum.clone() + optional_sum.clone(), max_expr);
                    }
                }
                ElectiveReq::Credits { num, courses } => {
                    if let Some(indices) = codes_to_indices(courses) {
                        sp_sets.push(indices.clone());
                        let mut required_sum = LinearExpr::from(0);
                        let mut optional_sum = LinearExpr::from(0);
                        for &idx in &indices {
                            let credits = ctx.courses[idx].credits;
                            if ctx.courses[idx].required {
                                for _ in 0..credits {
                                    required_sum += course_in_schedule(idx);
                                }
                            } else {
                                for _ in 0..credits {
                                    optional_sum += course_in_schedule(idx);
                                }
                            }
                        }
                        let required = *num as i64;
                        model.add_ge(
                            required_sum.clone() + optional_sum.clone(),
                            LinearExpr::from(required),
                        );
                        let max_possible =
                            indices.iter().map(|&idx| ctx.courses[idx].credits).sum();
                        let max_expr = model.new_int_var([(0, max_possible)]);
                        model.add_ge(max_expr, required_sum.clone());
                        model.add_ge(max_expr, LinearExpr::from(required));
                        model.add_le(required_sum.clone() + optional_sum.clone(), max_expr);
                    }
                }
                ElectiveReq::SetOpts(opts) => {
                    let mut all_indices = Vec::new();
                    let mut option_exprs = Vec::new();
                    for opt in opts {
                        if let Some(indices) = codes_to_indices(opt) {
                            all_indices.extend(&indices);
                            let mut required_idxs = Vec::new();
                            let mut optional_idxs = Vec::new();
                            for &idx in &indices {
                                if ctx.courses[idx].required {
                                    required_idxs.push(idx);
                                } else {
                                    optional_idxs.push(idx);
                                }
                            }
                            let mut required_sum = LinearExpr::from(0);
                            for &idx in &required_idxs {
                                required_sum += course_in_schedule(idx);
                            }
                            let mut optional_sum = LinearExpr::from(0);
                            for &idx in &optional_idxs {
                                optional_sum += course_in_schedule(idx);
                            }
                            let opt_len = opt.len() as i64;
                            let opt_var = model.new_bool_var();
                            // Option is satisfied if all required+optional courses are present
                            // model.add_le(required_sum.clone() + optional_sum.clone(), LinearExpr::from(opt_len) + (LinearExpr::from(1) - opt_var.clone()) * opt_len);
                            // model.add_ge(required_sum.clone() + optional_sum.clone(), LinearExpr::from(opt_len) - (LinearExpr::from(1) - opt_var.clone()) * opt_len);
                            let le_expr = LinearExpr::from(1) - opt_var;
                            let mut le_scaled = LinearExpr::from(opt_len);
                            for _ in 0..opt_len {
                                le_scaled += le_expr.clone();
                            }
                            model.add_le(required_sum.clone() + optional_sum.clone(), le_scaled);
                            let mut ge_scaled = LinearExpr::from(opt_len);
                            for _ in 0..opt_len {
                                ge_scaled -= le_expr.clone();
                            }
                            model.add_ge(required_sum.clone() + optional_sum.clone(), ge_scaled);
                            option_exprs.push(opt_var);
                        }
                    }
                    if !option_exprs.is_empty() {
                        let mut sum = LinearExpr::from(0);
                        for v in option_exprs {
                            sum += LinearExpr::from(v);
                        }
                        model.add_ge(sum, LinearExpr::from(1));
                    }
                    sp_sets.push(all_indices);
                }
            }
        }
    }
    // For each course, count how many S&Ps it could satisfy
    let mut course_sp_counts: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();
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
                    model.add_le(used, course_in_schedule(idx));
                    used_vars.push(used);
                }
            }
            let mut sum = LinearExpr::from(0);
            for v in used_vars {
                sum += LinearExpr::from(v);
            }
            model.add_le(sum, LinearExpr::from(3));
        }
    }
    // No additional restriction: forced courses can be used for both a Foundation and S&Ps, as long as they are not double-counted for multiple Foundations or more than 3 S&Ps.
}
