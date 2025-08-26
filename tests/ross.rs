use anyhow::{Result, anyhow};
use std::path::Path;

use ross_core::CC;
use ross_core::load_catalogs::CATALOGS;
use ross_core::read_excel_file::read_file;
use ross_core::schedule::CourseCode;
use ross_core::schedule::generate_schedule;
use ross_core::write_excel_file::save_schedule;

#[test]
fn test_ross() -> Result<()> {
    const FNAME: &str = "ross_test.xlsx";

    let sched = generate_schedule(
        CATALOGS
            .first()
            .ok_or(anyhow!("no catalogs found"))?
            .programs
            .iter()
            .map(|x| x.name.as_str())
            // .take(1)
            .collect(),
        CATALOGS
            .first()
            .ok_or(anyhow!("no catalogs found"))?
            .clone(),
        Some(vec![CC!("THEO", 1100)]), // None,
    )?;

    println!("Final schedule (two-stage, balanced):");
    println!("Final schedule (two-stage, balanced):");
    let mut sched_credits = 0;
    for (s, semester) in std::iter::once(&sched.incoming)
        .chain(sched.courses.iter())
        .enumerate()
    {
        if s == 0 {
            println!("Semester 0 (incoming only):");
        } else {
            println!("Semester {s}");
        }
        let mut sem_credits = 0;
        for code in semester {
            let credits = sched
                .catalog
                .courses
                .get(code)
                .and_then(|(_, cr, _)| *cr)
                .unwrap_or(0);
            println!("  {code} ({credits} credits)");
            sem_credits += credits;
        }
        println!("  Credits: {sem_credits}");
        if s > 0 {
            sched_credits += sem_credits;
        }
    }
    println!("Total credits (excluding incoming): {sched_credits}");

    save_schedule(&Path::new(FNAME).to_path_buf(), &sched)?;

    println!(
        "Excel file created: {FNAME} with {} schedule",
        if sched.is_valid()? {
            "valid"
        } else {
            "invalid"
        }
    );

    let _new_sched = read_file(&Path::new(FNAME).to_path_buf())?;

    Ok(())
}
