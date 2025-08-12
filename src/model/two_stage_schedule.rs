use crate::model::{ModelBuilderContext, build_model_pipeline};
use crate::schedule::{CourseCode, Schedule};
use cp_sat::builder::{CpModelBuilder, IntVar, LinearExpr};
use cp_sat::proto::{SatParameters, CpSolverStatus};
use anyhow::{anyhow, Result};

/// Returns Some(Vec<Vec<(CourseCode, i64)>>) if a feasible schedule is found, else None.
pub fn two_stage_lex_schedule(
    sched: &mut Schedule,
    max_credits_per_semester: i64,
) -> Result<()> {
    let mut params = SatParameters::default();
    // Time limits
    params.max_deterministic_time = Some(500.0);
    params.max_time_in_seconds = Some(500.0);

    // Set search strategy parameters for feasibility
    params.search_branching = Some(2); // FIXED_SEARCH (more systematic for feasibility)
    params.num_search_workers = Some(8); // Use more parallel workers if available
    params.interleave_search = Some(true); // Interleave different search heuristics
    params.randomize_search = Some(true); // Add randomization to escape local optima
    params.random_seed = Some(42); // Set a random seed for reproducibility
    params.log_search_progress = Some(false); // Ignore to minimize logging for now Some(true); // Log progress to help diagnose issues

    params.use_precedences_in_disjunctive_constraint = Some(true);
    params.use_overload_checker_in_cumulative_constraint = Some(true);
    params.use_timetable_edge_finding_in_cumulative_constraint = Some(true);
    params.use_disjunctive_constraint_in_cumulative_constraint = Some(true);

    // Stage 1: minimize total credits
    // Diagnostic: try disabling constraint groups one at a time
    // Only semester limit OFF for this run
    // Only semester limit OFF for this run, and add a hard cap on total credits (e.g., 150)
    let mut ctx = ModelBuilderContext::new_with_toggles(sched, max_credits_per_semester, true, true, false);

    // NO hard cap on total credits here. Only per-semester limit is enforced.
    let (mut model, vars, flat_courses) = build_model_pipeline(&mut ctx);
    let num_semesters = sched.courses.len();
    let total_credits = ctx.total_credits_expr(&vars, &flat_courses);
    model.minimize(total_credits.clone());
    let response = model.solve_with_parameters(&params);

    // Compute min_credits as the sum of all scheduled (assigned + prereq) course credits in the solution
    let min_credits = match response.status() {
        CpSolverStatus::Optimal | CpSolverStatus::Feasible => {
            let mut total = 0;
            for (i, (_course, credits)) in flat_courses.iter().enumerate() {
                for s in 0..num_semesters {
                    if vars[i][s].solution_value(&response) {
                        total += credits;
                    }
                }
            }
            total
        }
        _ => {
            // No feasible solution: run diagnostic toggling loop to see which constraint group(s) are responsible
            let mut diag_results = vec![];
            for (prereqs, geneds, semlim) in [
                (false, true, true),
                (true, false, true),
                (true, true, false),
                (true, true, true),
            ] {
                let mut ctx_diag = ModelBuilderContext::new_with_toggles(sched, max_credits_per_semester, prereqs, geneds, semlim);
                let (mut model_diag, vars_diag, flat_courses_diag) = build_model_pipeline(&mut ctx_diag);
                let mut semester_credit_vars_diag = Vec::new();
                for s in 0..num_semesters {
                    let weighted_terms: Vec<(i64, cp_sat::builder::BoolVar)> = flat_courses_diag
                        .iter()
                        .enumerate()
                        .map(|(i, (_course, credits))| (*credits, vars_diag[i][s].clone()))
                        .collect();
                    let expr: LinearExpr = weighted_terms.into_iter().collect();
                    let domain = vec![(0, max_credits_per_semester * flat_courses_diag.len() as i64)];
                    let var = model_diag.new_int_var(domain.clone());
                    model_diag.add_eq(var.clone(), expr);
                    semester_credit_vars_diag.push(var);
                }
                let response_diag = model_diag.solve_with_parameters(&params);
                let status = response_diag.status();
                println!("[DIAG] Constraint groups: prereqs={}, geneds={}, semlim={} => {:?}", prereqs, geneds, semlim, status);
                diag_results.push((prereqs, geneds, semlim, status));
            }
            return Err(anyhow!("No feasible solution found in single-stage scheduling"));
        }
    };

    // Stage 2: minimize spread, subject to min total credits
    let mut ctx2 = ModelBuilderContext::new_with_toggles(sched, max_credits_per_semester, true, true, true);
    ctx2.set_min_credits(min_credits);
    let (mut model2, vars2, flat_courses2) = build_model_pipeline(&mut ctx2);

    // Now, try disabling each constraint group in turn to diagnose infeasibility
    let mut diag_results = vec![];
    for (prereqs, geneds, semlim) in [
        (false, true, true),
        (true, false, true),
        (true, true, false),
        (true, true, true),
    ] {
        let mut ctx_diag = ModelBuilderContext::new_with_toggles(sched, max_credits_per_semester, prereqs, geneds, semlim);
        ctx_diag.set_min_credits(min_credits);
        let (mut model_diag, vars_diag, flat_courses_diag) = build_model_pipeline(&mut ctx_diag);
        let mut semester_credit_vars_diag = Vec::new();
        for s in 0..num_semesters {
            let weighted_terms: Vec<(i64, cp_sat::builder::BoolVar)> = flat_courses_diag
                .iter()
                .enumerate()
                .map(|(i, (_course, credits))| (*credits, vars_diag[i][s].clone()))
                .collect();
            let expr: LinearExpr = weighted_terms.into_iter().collect();
            let domain = vec![(0, max_credits_per_semester * flat_courses_diag.len() as i64)];
            let var = model_diag.new_int_var(domain.clone());
            model_diag.add_eq(var.clone(), expr);
            semester_credit_vars_diag.push(var);
        }
        let response_diag = model_diag.solve_with_parameters(&params);
        let status = response_diag.status();
        println!("[DIAG] Constraint groups: prereqs={}, geneds={}, semlim={} => {:?}", prereqs, geneds, semlim, status);
        diag_results.push((prereqs, geneds, semlim, status));
    }
    // Compute mean load (rounded down)
    let mean_load = min_credits / num_semesters as i64;

    // For each semester, create an IntVar for the semester's total credits using a robust idiomatic sum
    let mut semester_credit_vars = Vec::new();
    for s in 0..num_semesters {
        let weighted_terms: Vec<(i64, cp_sat::builder::BoolVar)> = flat_courses2
            .iter()
            .enumerate()
            .map(|(i, (_course, credits))| (*credits, vars2[i][s].clone()))
            .collect();
        let expr: LinearExpr = weighted_terms.into_iter().collect();
        // Domain: [0, max_credits_per_semester * flat_courses2.len() as i64]
        let domain = vec![(0, max_credits_per_semester * flat_courses2.len() as i64)];
        // Diagnostic: print the expr and domain for each semester
        println!("[DIAG] Semester {} credit expr domain: {:?}", s, domain);
        let var = model2.new_int_var(domain.clone());
        model2.add_eq(var.clone(), expr);
        semester_credit_vars.push(var);
    }

    // For each semester, create an IntVar for the absolute deviation from mean
    let mut abs_deviation_vars = Vec::new();
    for (_s, credit_var) in semester_credit_vars.iter().enumerate() {
        let diff_domain = vec![(
            -max_credits_per_semester * flat_courses2.len() as i64,
            max_credits_per_semester * flat_courses2.len() as i64,
        )];
        let diff = model2.new_int_var(diff_domain);
        // diff = semester_credits - mean_load
        model2.add_eq(
            diff.clone(),
            LinearExpr::from(credit_var.clone()) - mean_load,
        );
        let abs_domain = vec![(0, max_credits_per_semester * flat_courses2.len() as i64)];
        let abs_diff = model2.new_int_var(abs_domain);
        // abs_diff >= diff
        model2.add_ge(abs_diff.clone(), LinearExpr::from(diff.clone()));
        // abs_diff >= -diff (negate by repeated subtraction)
        let mut neg_diff_expr = LinearExpr::from(0);
        for _ in 0..1 {
            // -1 * diff
            neg_diff_expr = neg_diff_expr - LinearExpr::from(diff.clone());
        }
        model2.add_ge(abs_diff.clone(), neg_diff_expr);
        abs_deviation_vars.push(abs_diff);
    }
    // Minimize the sum of absolute deviations
    let mut spread_penalty = LinearExpr::from(0);
    for v in &abs_deviation_vars {
        spread_penalty = spread_penalty + LinearExpr::from(v.clone());
    }
    model2.minimize(spread_penalty);

    let response2 = model2.solve_with_parameters(&params);
    match response2.status() {
        CpSolverStatus::Optimal | CpSolverStatus::Feasible => {
            // Build the schedule output: Vec<Vec<(CourseCode, i64)>>
            let mut result = vec![vec![]; num_semesters];
            for (i, (course, credits)) in flat_courses2.iter().enumerate() {
                for s in 0..num_semesters {
                    if vars2[i][s].solution_value(&response2) {
                        result[s].push((course.code.clone(), *credits));
                    }
                }
            }
            // Overwrite sched.courses with the new schedule (just the codes)
            sched.courses = result
                .iter()
                .map(|sem| sem.iter().map(|(code, _)| code.clone()).collect())
                .collect();
            Ok(())
        }
        _ => {
            Err(anyhow!("No feasible solution found in two-stage scheduling"))
        }
    }
}
