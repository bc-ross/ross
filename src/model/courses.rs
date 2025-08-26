//! Functions for adding course variables and required/optional constraints.
use super::context::ModelBuilderContext;

pub fn add_courses<'a>(ctx: &mut ModelBuilderContext<'a>) {
    let mut vars = Vec::new();
    for i in 0..ctx.courses.len() {
        let mut sem_vars = Vec::new();
        for s in 0..ctx.num_semesters {
            let v = ctx.model.new_bool_var_with_name(format!("c_{i}_{s}"));
            sem_vars.push(v);
        }
        vars.push(sem_vars);
    }
    ctx.vars = vars;
    // Required courses exactly once
    for (i, c) in ctx.courses.iter().enumerate() {
        if c.required {
            ctx.model.add_exactly_one(ctx.vars[i].iter().copied());
        }
    }
    // Optional courses at most once
    for (i, c) in ctx.courses.iter().enumerate() {
        if !c.required {
            ctx.model.add_at_most_one(ctx.vars[i].iter().copied());
        }
    }
    // // Enforce maximum total credits if specified
    if let Some(min_credits) = ctx.min_credits {
        let flat_courses: Vec<_> = ctx.courses.iter().map(|c| (c.clone(), c.credits)).collect();
        let total_credits_expr = ctx.total_credits_expr(&ctx.vars, &flat_courses);
        ctx.model.add_le(
            total_credits_expr,
            cp_sat::builder::LinearExpr::from(min_credits),
        );
    }
    // Enforce term offering constraints for each course
    for (i, c) in ctx.courses.iter().enumerate() {
        // Look up term offering from catalog
        let offering = ctx
            .catalog
            .and_then(|cat| cat.courses.get(&c.code))
            .map(|(_, _, off)| off);
        for s in 0..ctx.num_semesters {
            let allowed = match offering {
                Some(crate::schedule::CourseTermOffering::Fall) => s % 2 == 1, // odd semesters
                Some(crate::schedule::CourseTermOffering::Spring) => s % 2 == 0, // even semesters
                Some(crate::schedule::CourseTermOffering::Both) => true,
                Some(crate::schedule::CourseTermOffering::Discretion) => true, // allowed, but may change in future
                Some(crate::schedule::CourseTermOffering::Infrequently) => true, // allowed, but may change in future
                Some(crate::schedule::CourseTermOffering::Summer) => false,      // never schedule
                None => true,                                                    // default: allow
            };
            if !allowed {
                // Forbid scheduling this course in this semester
                ctx.model
                    .add_eq(ctx.vars[i][s], cp_sat::builder::LinearExpr::from(0));
            }
        }
    }
    // --- Incoming courses logic ---
    // Get incoming codes from context (they are always required and only scheduled in semester 0)
    let incoming_semester = 0;
    for (i, c) in ctx.courses.iter().enumerate() {
        let is_incoming = ctx.incoming_codes.contains(&c.code);
        for s in 0..ctx.num_semesters {
            if is_incoming {
                if s == incoming_semester {
                    ctx.model.add_eq(ctx.vars[i][s], 1); // Must be scheduled in semester 0
                } else {
                    ctx.model.add_eq(ctx.vars[i][s], 0); // Cannot be scheduled elsewhere
                }
            } else if s == incoming_semester {
                ctx.model.add_eq(ctx.vars[i][s], 0); // Only incoming courses allowed in semester 0
            }
        }
    }
}
