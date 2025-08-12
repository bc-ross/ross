//! Functions for adding course variables and required/optional constraints.
use super::model_context::{Course, ModelBuilderContext};

pub fn add_courses<'a>(ctx: &mut ModelBuilderContext<'a>) {
    let mut vars = Vec::new();
    for i in 0..ctx.courses.len() {
        let mut sem_vars = Vec::new();
        for s in 0..ctx.num_semesters {
            let v = ctx.model.new_bool_var_with_name(format!("c_{}_{}", i, s));
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
}
