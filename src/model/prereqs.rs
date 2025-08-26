//! Functions for adding prerequisite constraints.
use super::context::ModelBuilderContext;
use crate::prereqs::CourseReq;
use crate::schedule::CourseCode;
use cp_sat::builder::LinearExpr;
use std::collections::HashMap;

pub fn add_prereq_constraints<'a>(ctx: &mut ModelBuilderContext<'a>) {
    let idx_map: HashMap<_, _> = ctx
        .courses
        .iter()
        .enumerate()
        .map(|(i, c)| (c.code.clone(), i))
        .collect();
    // Avoid borrow checker issues: collect prereqs first
    let prereqs: Vec<_> = ctx.courses.iter().map(|c| c.prereqs.clone()).collect();
    for (i, req) in prereqs.iter().enumerate() {
        add_prereq_for_course(ctx, &idx_map, i, req);
    }
}

fn add_prereq_for_course<'a>(
    ctx: &mut ModelBuilderContext<'a>,
    idx_map: &HashMap<CourseCode, usize>,
    course_idx: usize,
    req: &CourseReq,
) {
    use crate::prereqs::CourseReq::*;
    let num_semesters = ctx.num_semesters;
    // If the target course is an incoming course, skip prereq constraints entirely.
    // Incoming courses are allowed in semester 0 and should not be blocked by prereqs.
    if ctx.incoming_codes.contains(&ctx.courses[course_idx].code) {
        return;
    }
    match req {
        NotRequired => {}
        And(reqs) => {
            for r in reqs {
                add_prereq_for_course(ctx, idx_map, course_idx, r);
            }
        }
        Or(reqs) => {
            for s in 0..num_semesters {
                let cur = ctx.vars[course_idx][s];
                let mut or_exprs = Vec::new();
                for r in reqs {
                    let or_var = ctx.model.new_bool_var();
                    match r {
                        PreCourse(code) => {
                            if let Some(&pre_idx) = idx_map.get(code) {
                                // Allow prereqs to be satisfied in semester 0 (incoming)
                                let earlier_vars: Vec<_> =
                                    ctx.vars[pre_idx][..s].to_vec();
                                if !earlier_vars.is_empty() {
                                    let sum_earlier: LinearExpr =
                                        earlier_vars.into_iter().collect();
                                    ctx.model.add_linear_constraint(
                                        sum_earlier - or_var,
                                        [(0, i64::MAX)],
                                    );
                                    or_exprs.push(or_var);
                                }
                            }
                        }
                        CoCourse(code) => {
                            if let Some(&co_idx) = idx_map.get(code) {
                                let upto_vars: Vec<_> =
                                    ctx.vars[co_idx][..=s].to_vec();
                                if !upto_vars.is_empty() {
                                    let sum_upto: LinearExpr = upto_vars.into_iter().collect();
                                    ctx.model
                                        .add_linear_constraint(sum_upto - or_var, [(0, i64::MAX)]);
                                    or_exprs.push(or_var);
                                }
                            }
                        }
                        And(_) | Or(_) => {
                            add_prereq_for_course(ctx, idx_map, course_idx, r);
                        }
                        _ => eprintln!("Only PreCourse, CoCourse, And, Or supported, not {r:?}"),
                    }
                    or_exprs.push(or_var);
                }
                if !or_exprs.is_empty() {
                    let sum_or: LinearExpr = or_exprs.iter().copied().collect();
                    ctx.model
                        .add_linear_constraint(sum_or - cur, [(0, i64::MAX)]);
                }
            }
        }
        PreCourse(code) => {
            if let Some(&pre_idx) = idx_map.get(code) {
                for s in 0..num_semesters {
                    let cur = ctx.vars[course_idx][s];
                    if s == 0 {
                        ctx.model.add_eq(cur, 0);
                    } else {
                        let earlier_vars: Vec<_> = ctx.vars[pre_idx][..s].to_vec();
                        if !earlier_vars.is_empty() {
                            let sum_earlier: LinearExpr = earlier_vars.into_iter().collect();
                            ctx.model
                                .add_linear_constraint(sum_earlier - cur, [(0, i64::MAX)]);
                        } else {
                            ctx.model.add_eq(cur, 0);
                        }
                    }
                }
            } else {
                for s in 0..num_semesters {
                    ctx.model.add_eq(ctx.vars[course_idx][s], 0);
                }
            }
        }
        CoCourse(code) => {
            if let Some(&co_idx) = idx_map.get(code) {
                for s in 0..num_semesters {
                    let cur = ctx.vars[course_idx][s];
                    let upto_vars: Vec<_> = ctx.vars[co_idx][..=s].to_vec();
                    if !upto_vars.is_empty() {
                        let sum_upto: LinearExpr = upto_vars.into_iter().collect();
                        ctx.model
                            .add_linear_constraint(sum_upto - cur, [(0, i64::MAX)]);
                    } else {
                        ctx.model.add_eq(cur, 0);
                    }
                }
            } else {
                for s in 0..num_semesters {
                    ctx.model.add_eq(ctx.vars[course_idx][s], 0);
                }
            }
        }
        _ => unimplemented!("Only PreCourse, CoCourse, And, Or supported"),
    }
}
