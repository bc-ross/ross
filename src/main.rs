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
            .collect(),
        CATALOGS
            .first()
            .ok_or(anyhow!("no catalogs found"))?
            .clone(),
    )?;
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
