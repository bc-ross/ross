//! Legacy model-building and schedule-building logic moved from main.rs
use super::Course;
use crate::model::Course;
use crate::prereqs;
use crate::prereqs;
use crate::schedule::{CourseCode, Schedule};

pub fn build_model_from_schedule(
    sched: &Schedule,
    max_credits_per_semester: i64,
    min_credits: Option<i64>,
) -> (
    cp_sat::builder::CpModelBuilder,
    Vec<Vec<cp_sat::builder::BoolVar>>,
    cp_sat::builder::LinearExpr,
) {
    let num_semesters = sched.courses.len();
    let mut all_codes = std::collections::HashSet::new();
    let mut queue = std::collections::VecDeque::new();
    for sem in &sched.courses {
        for code in sem {
            all_codes.insert(code.clone());
            queue.push_back(code.clone());
        }
    }
    while let Some(code) = queue.pop_front() {
        if let Some(req) = sched.catalog.prereqs.get(&code) {
            fn collect_prereq_codes(
                req: &prereqs::CourseReq,
                all_codes: &mut std::collections::HashSet<CourseCode>,
                catalog: &crate::schedule::Catalog,
                queue: &mut std::collections::VecDeque<CourseCode>,
            ) {
                use prereqs::CourseReq::*;
                match req {
                    And(reqs) | Or(reqs) => {
                        for r in reqs {
                            collect_prereq_codes(r, all_codes, catalog, queue);
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
            collect_prereq_codes(req, &mut all_codes, &sched.catalog, &mut queue);
        }
    }
    let mut gened_codes = std::collections::HashSet::new();
    for gened in &sched.catalog.geneds {
        use crate::geneds::ElectiveReq;
        let req = match gened {
            crate::geneds::GenEd::Core { req, .. } => req,
            crate::geneds::GenEd::Foundation { req, .. } => req,
            crate::geneds::GenEd::SkillAndPerspective { req, .. } => req,
        };
        match req {
            crate::geneds::ElectiveReq::Set(codes) => {
                gened_codes.extend(codes.iter().cloned());
            }
            crate::geneds::ElectiveReq::SetOpts(opts) => {
                for set in opts {
                    gened_codes.extend(set.iter().cloned());
                }
            }
            crate::geneds::ElectiveReq::Courses { courses, .. }
            | crate::geneds::ElectiveReq::Credits { courses, .. } => {
                gened_codes.extend(courses.iter().cloned());
            }
        }
    }
    for code in &all_codes {
        gened_codes.remove(code);
    }
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
                    .unwrap_or(prereqs::CourseReq::NotRequired);
                (credits, prereqs)
            }
            None => (0, prereqs::CourseReq::NotRequired),
        };
        courses.push(Course {
            code: code.clone(),
            credits,
            required: true,
            geneds: vec![],
            elective_group: None,
            prereqs,
        });
    }
    for code in &gened_codes {
        let (credits, prereqs) = match sched.catalog.courses.get(code) {
            Some((_name, credits_opt, _offering)) => {
                let credits = credits_opt.unwrap_or(0) as i64;
                let prereqs = sched
                    .catalog
                    .prereqs
                    .get(code)
                    .cloned()
                    .unwrap_or(prereqs::CourseReq::NotRequired);
                (credits, prereqs)
            }
            None => (0, prereqs::CourseReq::NotRequired),
        };
        courses.push(Course {
            code: code.clone(),
            credits,
            required: false,
            geneds: vec![],
            elective_group: None,
            prereqs,
        });
    }
    crate::model::build_model(
        &courses,
        num_semesters,
        max_credits_per_semester,
        min_credits,
        Some(&sched.catalog.geneds),
        Some(&sched.catalog),
    )
}
