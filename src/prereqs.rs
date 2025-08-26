use savefile_derive::Savefile;
use serde::{Deserialize, Serialize};

use crate::schedule::{CourseCode, Schedule};

#[derive(Savefile, Serialize, Deserialize, Debug, Default, Hash, Clone, PartialEq, Eq)]
pub enum CourseReq {
    And(Vec<CourseReq>),
    Or(Vec<CourseReq>),
    PreCourse(CourseCode),
    CoCourse(CourseCode),
    PreCourseGrade(CourseCode, Grade),
    CoCourseGrade(CourseCode, Grade),
    Program(String), // Assoc'd STEM
    // Standing(u8), // May be Sen, Ju/Sen, Ju+, or So/Fr only -- how represent? TODO
    Instructor,
    #[default]
    NotRequired,
}

#[derive(Savefile, Serialize, Deserialize, Debug, Hash, Clone, Copy, PartialEq, Eq)]
pub enum GradeLetter {
    A,
    B,
    C,
    D,
    F,
}

impl PartialOrd for GradeLetter {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for GradeLetter {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (*self as u8).cmp(&(*other as u8)).reverse()
    }
}

#[derive(Savefile, Serialize, Deserialize, Debug, Default, Hash, Clone, PartialEq, Eq)]
pub enum GradeQualifier {
    Plus,
    Minus,
    #[default]
    None,
}

impl PartialOrd for GradeQualifier {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for GradeQualifier {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        use GradeQualifier::*;
        match (self, other) {
            (Plus, Plus) | (Minus, Minus) | (None, None) => std::cmp::Ordering::Equal,
            (Plus, _) => std::cmp::Ordering::Greater,
            (_, Plus) => std::cmp::Ordering::Less,
            (Minus, _) => std::cmp::Ordering::Greater,
            (_, Minus) => std::cmp::Ordering::Less,
        }
    }
}

#[derive(Savefile, Serialize, Deserialize, Debug, Hash, Clone, PartialEq, Eq)]
pub struct Grade {
    pub letter: GradeLetter,
    pub qualifier: GradeQualifier,
}

impl PartialOrd for Grade {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Grade {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.letter
            .cmp(&other.letter)
            .then(self.qualifier.cmp(&other.qualifier))
    }
}

#[macro_export]
macro_rules! GR {
    ($l:ident +) => {
        Grade {
            letter: GradeLetter::$l,
            qualifier: GradeQualifier::Plus,
        }
    };
    ($l:ident -) => {
        Grade {
            letter: GradeLetter::$l,
            qualifier: GradeQualifier::Minus,
        }
    };
    ($l:ident) => {
        Grade {
            letter: GradeLetter::$l,
            qualifier: GradeQualifier::None,
        }
    };
}

// Used for script_assistant crate
#[allow(dead_code)]
impl CourseReq {
    pub fn all_course_codes(&self) -> Vec<CourseCode> {
        let mut codes = Vec::new();
        self.collect_course_codes(&mut codes);
        codes.into_iter().cloned().collect()
    }

    fn collect_course_codes<'a>(&'a self, codes: &mut Vec<&'a CourseCode>) {
        match self {
            CourseReq::And(reqs) | CourseReq::Or(reqs) => {
                for req in reqs {
                    req.collect_course_codes(codes);
                }
            }
            CourseReq::PreCourse(code) | CourseReq::CoCourse(code) => {
                codes.push(code);
            }
            CourseReq::PreCourseGrade(code, _) | CourseReq::CoCourseGrade(code, _) => {
                codes.push(code);
            }
            _ => {}
        }
    }
}

impl CourseReq {
    pub fn is_satisfied(&self, sched: &Schedule, sem_idx: usize) -> bool {
        // TODO: grade is not implemented
        match self {
            CourseReq::And(reqs) => reqs.iter().all(|req| req.is_satisfied(sched, sem_idx)),
            CourseReq::Or(reqs) => reqs.iter().any(|req| req.is_satisfied(sched, sem_idx)),
            CourseReq::PreCourse(code) | CourseReq::PreCourseGrade(code, _) => {
                std::iter::once(&sched.incoming)
                    .chain(sched.courses.iter())
                    .take(sem_idx + 1)
                    .flatten()
                    .any(|c| c == code)
            }
            CourseReq::CoCourse(code) | CourseReq::CoCourseGrade(code, _) => {
                std::iter::once(&sched.incoming)
                    .chain(sched.courses.iter())
                    .take(sem_idx + 2)
                    .flatten()
                    .any(|c| c == code)
            }
            CourseReq::Program(x) => sched.programs.iter().any(|p| {
                sched
                    .catalog
                    .programs
                    .iter()
                    .any(|y| y.name == *p && y.assoc_stems.contains(x))
            }),
            CourseReq::Instructor => todo!(),
            CourseReq::NotRequired => true,
        }
    }
}
