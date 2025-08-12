use anyhow::{Result, anyhow};
use std::path::Path;

mod geneds;
mod load_catalogs;
mod prereqs;
mod model;
mod read_excel_file;
mod schedule;
mod version;
mod write_excel_file;

use load_catalogs::CATALOGS;
use schedule::generate_schedule;
pub use version::{SAVEFILE_VERSION, VERSION};
use write_excel_file::save_schedule;

pub static TEMPLATE_PNG: &[u8] = include_bytes!("../assets/template.png");
pub const MAX_CREDITS_PER_SEMESTER: i64 = 18;

fn main() -> Result<()> {
    // Test the full real schedule generation with strategic Foundation selection
    println!("=== Testing Real Schedule Generation with Strategic Foundation Selection ===");

    const FNAME: &str = "ross_test.xlsx";

    let sched = generate_schedule(
        CATALOGS
            .first()
            .ok_or(anyhow!("no catalogs found"))?
            .programs
            .iter()
            .map(|x| x.name.as_str())
            .take(1)
            .collect(),
        CATALOGS
            .first()
            .ok_or(anyhow!("no catalogs found"))?
            .clone(),
    )?;

    // Print the updated schedule from sched.courses
    println!("Final schedule (two-stage, balanced):");
    let mut sched_credits = 0;
    for (s, semester) in sched.courses.iter().enumerate() {
        println!("Semester {}", s + 1);
        let mut sem_credits = 0;
        for code in semester {
            // Look up credits from catalog
            let credits = sched.catalog.courses.get(code).and_then(|(_, cr, _)| *cr).unwrap_or(0);
            println!("  {} ({} credits)", code, credits);
            sem_credits += credits;
        }
        println!("  Credits: {}", sem_credits);
        sched_credits += sem_credits;
    }
    println!("Total credits: {}", sched_credits);
    match crate::geneds::are_geneds_satisfied(&sched) {
        Ok(true) => println!("All GenEds satisfied!"),
        Ok(false) => println!("GenEd requirements NOT satisfied!"),
        Err(e) => println!("GenEd check error: {}", e),
    }
    
    save_schedule(&Path::new(FNAME).to_path_buf(), &sched)?;

    println!(
        "Excel file created: {FNAME} with {} schedule",
        if sched.is_valid()? {
            "valid"
        } else {
            "invalid"
        }
    );

    Ok(())
}
