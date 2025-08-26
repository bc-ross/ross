use crate::schedule::{Catalog, CourseCode, Schedule};
use anyhow::Result;
use savefile_derive::Savefile;
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Clone, Debug, Savefile, Serialize, Deserialize, Hash, Eq, PartialEq)]
pub enum GenEd {
    Core { name: String, req: ElectiveReq },
    Foundation { name: String, req: ElectiveReq },
    SkillAndPerspective { name: String, req: ElectiveReq },
}

#[derive(Clone, Debug, Savefile, Serialize, Deserialize, Hash, Eq, PartialEq)]
pub enum ElectiveReq {
    Set(Vec<CourseCode>),
    SetOpts(Vec<Vec<CourseCode>>),
    Courses {
        num: usize,
        courses: Vec<CourseCode>,
    },
    Credits {
        num: u32,
        courses: Vec<CourseCode>,
    },
}

// Helper: for a ElectiveReq, return a set of courses from schedule that can be used to satisfy it, or None if not possible
fn satisfy_req<'a>(
    req: &'a ElectiveReq,
    sched_courses: &HashSet<&'a CourseCode>,
    catalog: &Catalog,
) -> Option<HashSet<&'a CourseCode>> {
    match req {
        ElectiveReq::Set(codes) => {
            let set: HashSet<_> = codes
                .iter()
                .filter_map(|c| sched_courses.get(c))
                .copied()
                .collect();
            if set.len() == codes.len() {
                Some(set)
            } else {
                None
            }
        }
        ElectiveReq::SetOpts(opts) => {
            for opt in opts {
                let set: HashSet<_> = opt
                    .iter()
                    .filter_map(|c| sched_courses.get(c))
                    .copied()
                    .collect();
                if set.len() == opt.len() {
                    return Some(set);
                }
            }
            None
        }
        ElectiveReq::Courses { num, courses } => {
            let available: Vec<_> = courses
                .iter()
                .filter_map(|c| sched_courses.get(c))
                .copied()
                .collect();
            if available.len() >= *num {
                Some(available.into_iter().take(*num).collect())
            } else {
                None
            }
        }
        ElectiveReq::Credits { num, courses } => {
            let mut available: Vec<_> = courses
                .iter()
                .filter_map(|c| sched_courses.get(c))
                .copied()
                .collect();
            // Sort by credits descending
            available.sort_by_key(|c| {
                -(catalog
                    .courses
                    .get(*c)
                    .and_then(|(_, cr, _)| *cr)
                    .unwrap_or(0) as i32)
            });
            let mut selected = HashSet::new();
            let mut total = 0u32;
            for c in available {
                let cr = catalog
                    .courses
                    .get(c)
                    .and_then(|(_, cr, _)| *cr)
                    .unwrap_or(0);
                selected.insert(c);
                total += cr;
                if total >= *num {
                    break;
                }
            }
            if total >= *num { Some(selected) } else { None }
        }
    }
}

pub fn are_geneds_satisfied(sched: &Schedule) -> Result<bool> {
    let sched_courses: HashSet<&CourseCode> = std::iter::once(&sched.incoming)
        .chain(sched.courses.iter())
        .flatten()
        .collect();
    // 1. Core: each must be satisfied, overlap allowed
    let mut all_core_ok = true;
    for gened in sched.catalog.geneds.iter() {
        if let GenEd::Core { req, .. } = gened {
            if satisfy_req(req, &sched_courses, &sched.catalog).is_none() {
                all_core_ok = false;
            }
        }
    }
    if !all_core_ok {
        return Ok(false);
    }

    // 2. Foundation: each must be satisfied, but no course can be used for more than one Foundation
    let mut foundation_reqs = vec![];
    let mut foundation_names = vec![];
    for gened in sched.catalog.geneds.iter() {
        if let GenEd::Foundation { req, name } = gened {
            foundation_reqs.push(req);
            foundation_names.push(name);
        }
    }
    // Try all possible assignments of courses to foundation geneds (backtracking)
    fn assign_foundations<'a>(
        reqs: &[&'a ElectiveReq],
        names: &[&'a String],
        idx: usize,
        used: &mut HashSet<&'a CourseCode>,
        sched_courses: &HashSet<&'a CourseCode>,
        catalog: &Catalog,
        fail_foundation: &mut Option<String>,
    ) -> bool {
        if idx == reqs.len() {
            return true;
        }
        if let Some(candidates) = satisfy_req(reqs[idx], sched_courses, catalog) {
            let available: Vec<_> = candidates.difference(used).copied().collect();
            if available.len() < candidates.len() {
                *fail_foundation = Some(names[idx].clone());
                return false;
            }
            // Try all combinations of candidates from available (order doesn't matter)
            fn combinations<T: Clone>(
                data: &[T],
                k: usize,
                out: &mut Vec<T>,
                res: &mut Vec<Vec<T>>,
            ) {
                if out.len() == k {
                    res.push(out.clone());
                    return;
                }
                for i in 0..data.len() {
                    out.push(data[i].clone());
                    let rest = &data[i + 1..];
                    combinations(rest, k, out, res);
                    out.pop();
                }
            }
            let mut combs = Vec::new();
            let mut out = Vec::new();
            combinations(&available, candidates.len(), &mut out, &mut combs);
            for comb in &combs {
                let mut new_used = used.clone();
                new_used.extend(comb.iter().copied());
                if assign_foundations(
                    reqs,
                    names,
                    idx + 1,
                    &mut new_used,
                    sched_courses,
                    catalog,
                    fail_foundation,
                ) {
                    return true;
                }
            }
            *fail_foundation = Some(names[idx].clone());
            false
        } else {
            *fail_foundation = Some(names[idx].clone());
            false
        }
    }
    if !foundation_reqs.is_empty() {
        let mut used = HashSet::new();
        let mut fail_foundation = None;
        let req_refs: Vec<&ElectiveReq> = foundation_reqs.to_vec();
        let name_refs: Vec<&String> = foundation_names.to_vec();
        if !assign_foundations(
            &req_refs,
            &name_refs,
            0,
            &mut used,
            &sched_courses,
            &sched.catalog,
            &mut fail_foundation,
        ) {
            return Ok(false);
        }
    }

    // 3. Skills & Perspectives: each must be satisfied, but no course can be used for more than 3 S&Ps
    let mut sp_reqs = vec![];
    let mut sp_names = vec![];
    for gened in sched.catalog.geneds.iter() {
        if let GenEd::SkillAndPerspective { req, name } = gened {
            sp_reqs.push(req);
            sp_names.push(name);
        }
    }
    let mut all_sp_ok = true;
    let mut sp_course_counts: HashMap<&CourseCode, usize> = HashMap::new();
    for req in sp_reqs.iter() {
        if let Some(courses) = satisfy_req(req, &sched_courses, &sched.catalog) {
            for c in courses {
                *sp_course_counts.entry(c).or_insert(0) += 1;
            }
        } else {
            all_sp_ok = false;
        }
    }
    if !all_sp_ok {
        return Ok(false);
    }
    // No course can be used for more than 3 S&Ps
    let mut sp_overlap_fail = false;
    for count in sp_course_counts.values() {
        if *count > 3 {
            sp_overlap_fail = true;
        }
    }
    if sp_overlap_fail {
        return Ok(false);
    }
    Ok(true)
}

// Used for script_assistant crate
#[allow(dead_code)]
impl GenEd {
    pub fn all_course_codes(&self) -> Vec<CourseCode> {
        match self {
            GenEd::Core { req, .. } => req.all_course_codes(),
            GenEd::Foundation { req, .. } => req.all_course_codes(),
            GenEd::SkillAndPerspective { req, .. } => req.all_course_codes(),
        }
    }
}

#[allow(dead_code)]
impl ElectiveReq {
    pub fn all_course_codes(&self) -> Vec<CourseCode> {
        let mut codes = Vec::new();
        self.collect_course_codes(&mut codes);
        codes.into_iter().cloned().collect()
    }

    fn collect_course_codes<'a>(&'a self, codes: &mut Vec<&'a CourseCode>) {
        match self {
            ElectiveReq::Set(courses) => {
                codes.extend(courses.iter());
            }
            ElectiveReq::SetOpts(course_seqs) => {
                codes.extend(course_seqs.iter().flatten());
            }
            ElectiveReq::Courses { courses, .. } | ElectiveReq::Credits { courses, .. } => {
                codes.extend(courses.iter());
            }
        }
    }
}
