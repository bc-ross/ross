//! Model building and constraint logic for the course scheduling solver.

mod model_context;
mod model_courses;
mod model_geneds;
mod model_prereqs;
mod model_semester;
mod two_stage_schedule;

use model_context::{Course, ModelBuilderContext, build_model_pipeline};
use model_courses::*;
use model_geneds::*;
use model_prereqs::*;
use model_semester::*;
pub use two_stage_schedule::*;
