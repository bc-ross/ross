use std::collections::HashSet;
use std::fs::File;
use std::io::Write;
#[path = "../../resources/course_reqs/mod.rs"]
mod course_reqs;

#[path = "../../resources/programs/mod.rs"]
mod programs;

#[path = "../../resources/general_education.rs"]
pub mod general_education;

#[path = "../../resources/courses.rs"]
pub mod courses;

#[path = "../../src/schedule.rs"]
pub mod schedule;

#[path = "../../src/prereqs.rs"]
pub mod prereqs;

#[path = "../../src/geneds.rs"]
pub mod geneds;

fn main() {
    let mut new_courses = HashSet::new();
    for program in programs::programs() {
        new_courses.extend(program.semesters.into_iter().flatten());
        new_courses.extend(
            program
                .electives
                .into_iter()
                .map(|e| e.req.all_course_codes())
                .flatten(),
        );
    }
    for (course, prereq) in course_reqs::prereqs() {
        new_courses.insert(course);
        new_courses.extend(prereq.all_course_codes());
    }
    for gened in general_education::geneds() {
        new_courses.extend(gened.all_course_codes());
    }

    let old_assoc_values = courses::courses();
    let courses_json = serde_json::to_string_pretty(
        &old_assoc_values
            .iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect::<HashSet<_>>(),
    )
    .unwrap();
    let mut file = File::create("old_courses.json").unwrap();
    file.write_all(courses_json.as_bytes()).unwrap();

    let old_courses: HashSet<_> = old_assoc_values.into_keys().collect();
    let unknown_courses: HashSet<_> = new_courses.difference(&old_courses).collect();
    let courses_json = serde_json::to_string_pretty(&unknown_courses).unwrap();
    let mut file = File::create("new_courses.json").unwrap();
    file.write_all(courses_json.as_bytes()).unwrap();

    println!("Exported {} courses", unknown_courses.len());
}
