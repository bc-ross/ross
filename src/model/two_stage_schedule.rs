use crate::model::{ModelBuilderContext, build_model_pipeline};
use crate::schedule::{CourseCode, Schedule};
use cp_sat::builder::{CpModelBuilder, IntVar, LinearExpr};
use cp_sat::proto::CpSolverStatus;
use anyhow::{anyhow, Result};

/// Returns Some(Vec<Vec<(CourseCode, i64)>>) if a feasible schedule is found, else None.
pub fn two_stage_lex_schedule(
    sched: &mut Schedule,
    max_credits_per_semester: i64,
) -> Result<()> {
    // Stage 1: minimize total credits
    let mut ctx = ModelBuilderContext::new(sched, max_credits_per_semester);
    let (mut model, vars, flat_courses) = build_model_pipeline(&mut ctx);
    let num_semesters = sched.courses.len();
    let total_credits = ctx.total_credits_expr(&vars, &flat_courses);
    model.minimize(total_credits.clone());
    let response = model.solve();

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
            // No feasible solution
            return Err(anyhow!("No feasible solution found in single-stage scheduling"));
        }
    };

    // Stage 2: minimize spread, subject to min total credits
    let mut ctx2 = ModelBuilderContext::new(sched, max_credits_per_semester);
    ctx2.set_min_credits(min_credits);
    let (mut model2, vars2, flat_courses2) = build_model_pipeline(&mut ctx2);
    // Compute mean load (rounded down)
    let mean_load = min_credits / num_semesters as i64;

    // For each semester, create an IntVar for the semester's total credits
    let mut semester_credit_vars = Vec::new();
    for s in 0..num_semesters {
        let mut expr = LinearExpr::from(0);
        for i in 0..flat_courses2.len() {
            let var = vars2[i][s].clone();
            let coeff = flat_courses2[i].1;
            if coeff > 0 {
                for _ in 0..coeff {
                    expr = expr + LinearExpr::from(var.clone());
                }
            } else if coeff < 0 {
                for _ in 0..(-coeff) {
                    expr = expr - LinearExpr::from(var.clone());
                }
            }
        }
        // Domain: [0, max_credits_per_semester * flat_courses2.len() as i64]
        let domain = vec![(0, max_credits_per_semester * flat_courses2.len() as i64)];
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

    let response2 = model2.solve();
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
