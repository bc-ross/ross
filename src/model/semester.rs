/// Functions for adding generic semester constraints (e.g., max credits).
use super::context::ModelBuilderContext;

pub fn add_semester_constraints<'a>(ctx: &mut ModelBuilderContext<'a>) {
    // For each semester, sum the credits of all courses scheduled and add a constraint
    // Ignore semester 0 for max credits constraint
    for s in 1..ctx.num_semesters {
        let weighted_terms: Vec<(i64, _)> = ctx
            .courses
            .iter()
            .enumerate()
            .map(|(i, c)| (c.credits, ctx.vars[i][s]))
            .collect();
        let weighted_sum: cp_sat::builder::LinearExpr = weighted_terms.into_iter().collect();
        ctx.model.add_le(weighted_sum, ctx.max_credits_per_semester);
    }
}
