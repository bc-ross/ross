//! Context struct for model building and shared state.
use crate::prereqs::CourseReq;
use crate::schedule::{Catalog, CourseCode, Schedule};
use cp_sat::builder::{BoolVar, CpModelBuilder, LinearExpr};

#[derive(Clone)]
pub struct Course {
    pub code: CourseCode,
    pub credits: i64,
    pub required: bool,
    pub prereqs: CourseReq,
}

pub struct ModelBuilderContext<'a> {
    pub model: CpModelBuilder,
    pub vars: Vec<Vec<BoolVar>>,
    pub courses: Vec<Course>,
    pub num_semesters: usize,
    pub max_credits_per_semester: i64,
    pub min_credits: Option<i64>,
    pub catalog: Option<&'a Catalog>,
    pub incoming_codes: Vec<CourseCode>,
}

impl<'a> ModelBuilderContext<'a> {
    /// Create a new ModelBuilderContext from a schedule and max credits per semester.
    pub fn new(sched: &'a Schedule, max_credits_per_semester: i64) -> Self {
        // Add incoming courses as semester 0
        let mut all_codes = std::collections::HashSet::new();
        let mut queue = std::collections::VecDeque::new();
        // Add incoming courses first
        for code in &sched.incoming {
            all_codes.insert(code.clone());
        }
        // Add planned courses and their prereqs
        for sem in &sched.courses {
            for code in sem {
                all_codes.insert(code.clone());
                queue.push_back(code.clone());
            }
        }
        while let Some(code) = queue.pop_front() {
            if let Some(req) = sched.catalog.prereqs.get(&code) {
                fn collect_prereq_codes(
                    req: &CourseReq,
                    all_codes: &mut std::collections::HashSet<CourseCode>,
                    queue: &mut std::collections::VecDeque<CourseCode>,
                ) {
                    use crate::prereqs::CourseReq::*;
                    match req {
                        And(reqs) | Or(reqs) => {
                            for r in reqs {
                                collect_prereq_codes(r, all_codes, queue);
                            }
                        }
                        PreCourse(code) | CoCourse(code) => {
                            if all_codes.insert(code.clone()) {
                                queue.push_back(code.clone());
                            }
                        }
                        _ => {}
                    }
                }
                collect_prereq_codes(req, &mut all_codes, &mut queue);
            }
        }
        // Add GenEd-eligible courses
        for gened in &sched.catalog.geneds {
            use crate::geneds::{ElectiveReq, GenEd};
            let reqs: Vec<&ElectiveReq> = match gened {
                GenEd::Core { req, .. } => vec![req],
                GenEd::Foundation { req, .. } => vec![req],
                GenEd::SkillAndPerspective { req, .. } => vec![req],
            };
            for req in reqs {
                match req {
                    ElectiveReq::Set(codes)
                    | ElectiveReq::Courses { courses: codes, .. }
                    | ElectiveReq::Credits { courses: codes, .. } => {
                        for code in codes {
                            all_codes.insert(code.clone());
                        }
                    }
                    ElectiveReq::SetOpts(opts) => {
                        for opt in opts {
                            for code in opt {
                                all_codes.insert(code.clone());
                            }
                        }
                    }
                }
            }
        }
        // Collect program electives for the selected programs
        let mut program_electives: Vec<&crate::schedule::Elective> = Vec::new();
        for prog_name in &sched.programs {
            if let Some(prog) = sched.catalog.programs.iter().find(|p| &p.name == prog_name) {
                for elective in &prog.electives {
                    program_electives.push(elective);
                    // Also ensure elective courses are included in all_codes so they can be modelled
                    use crate::geneds::ElectiveReq;
                    match &elective.req {
                        ElectiveReq::Set(codes)
                        | ElectiveReq::Courses { courses: codes, .. }
                        | ElectiveReq::Credits { courses: codes, .. } => {
                            for code in codes {
                                all_codes.insert(code.clone());
                            }
                        }
                        ElectiveReq::SetOpts(opts) => {
                            for opt in opts {
                                for code in opt {
                                    all_codes.insert(code.clone());
                                }
                            }
                        }
                    }
                }
            }
        }
        // Build Course structs for all codes, and print diagnostics
        let mut courses = Vec::new();
        for code in &all_codes {
            let (credits, prereqs) = match sched.catalog.courses.get(code) {
                Some((_name, credits_opt, _offering)) => {
                    let credits = credits_opt.unwrap_or(0) as i64;
                    let prereqs = sched
                        .catalog
                        .prereqs
                        .get(code)
                        .cloned()
                        .unwrap_or(CourseReq::NotRequired);
                    (credits, prereqs)
                }
                None => (0, CourseReq::NotRequired),
            };
            let required = if sched.incoming.contains(code) {
                true
            } else {
                sched.courses.iter().flatten().any(|c| c == code)
            };
            courses.push(Course {
                code: code.clone(),
                credits,
                required,
                prereqs,
            });
        }

        ModelBuilderContext {
            model: CpModelBuilder::default(),
            vars: Vec::new(),
            courses,
            num_semesters: sched.courses.len(), // already includes semester 0 after transformation
            max_credits_per_semester,
            min_credits: None,
            catalog: Some(&sched.catalog),
            incoming_codes: sched.incoming.clone(),
        }
    }

    /// Set the minimum total credits constraint
    pub fn set_min_credits(&mut self, min_credits: i64) {
        self.min_credits = Some(min_credits);
    }

    /// Compute the total credits LinearExpr for the current context
    pub fn total_credits_expr(
        &self,
        vars: &[Vec<BoolVar>],
        flat_courses: &[(Course, i64)],
    ) -> LinearExpr {
        let mut obj_terms = Vec::new();
        for (i, (_course, credits)) in flat_courses.iter().enumerate() {
            // Skip semester 0 (incoming) when computing total scheduled credits
            for s in 1..self.num_semesters {
                obj_terms.push((*credits, vars[i][s]));
            }
        }
        obj_terms.into_iter().collect()
    }
}

/// Build the model pipeline: add variables, constraints, and return (model, vars, flat_courses)
pub fn build_model_pipeline(
    ctx: &mut ModelBuilderContext,
) -> (CpModelBuilder, Vec<Vec<BoolVar>>, Vec<(Course, i64)>) {
    super::courses::add_courses(ctx);
    super::prereqs::add_prereq_constraints(ctx);
    super::geneds::add_gened_constraints(ctx);
    super::semester::add_semester_constraints(ctx);
    // Build flat_courses as (Course, credits)
    let flat_courses = ctx.courses.iter().map(|c| (c.clone(), c.credits)).collect();
    (
        std::mem::take(&mut ctx.model),
        ctx.vars.clone(),
        flat_courses,
    )
}
