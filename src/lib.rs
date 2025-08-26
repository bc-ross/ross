pub mod geneds;
pub mod load_catalogs;
pub mod model;
pub mod prereqs;
pub mod read_excel_file;
pub mod schedule;
pub mod version;
pub mod write_excel_file;

pub use version::{SAVEFILE_VERSION, VERSION};

pub static TEMPLATE_PNG: &[u8] = include_bytes!("../assets/template.png");
pub const MAX_CREDITS_PER_SEMESTER: i64 = 18;
