use crate::schedule::Schedule;
use crate::{SAVEFILE_VERSION, TEMPLATE_PNG};
use anyhow::Result;
use rust_xlsxwriter::{Format, FormatAlign, Image, Workbook, Worksheet};
use savefile::save_to_mem;
use std::path::PathBuf;

fn pretty_print_sched_to_sheet(sched: &Schedule, sheet: &mut Worksheet) -> Result<()> {
    let semesters = sched.courses.len() + 1;
    let mut last_row = 0;
    let mut sem_sums = vec![0; semesters];

    let total_format = Format::new().set_italic();
    let center_format = Format::new().set_align(FormatAlign::Center);

    sheet.merge_range(0, 0, 0, 1, "Incoming", &center_format)?;
    for col_idx in 1..semesters {
        sheet.merge_range(
            0,
            (col_idx * 2) as u16,
            0,
            ((col_idx * 2) + 1) as u16,
            &format!("Semester {col_idx}"),
            &center_format,
        )?;
    }

    for (row_idx, val) in sched.incoming.iter().enumerate() {
        sheet.write_string((row_idx + 1) as u32, 0, val.to_string())?;
        sheet.write_number_with_format(
            (row_idx + 1) as u32,
            1,
            sched
                .catalog
                .courses
                .get(val)
                .map(|(_, x, _)| x.unwrap_or(0))
                .ok_or(anyhow::anyhow!("Course lookup not found: {}", val))?,
            &center_format,
        )?;

        sem_sums[0] += sched
            .catalog
            .courses
            .get(val)
            .and_then(|(_, x, _)| *x)
            .unwrap_or(0);
        last_row = last_row.max(row_idx);
    }

    for (col_idx, field) in sched.courses.iter().enumerate() {
        for (row_idx, val) in field.iter().enumerate() {
            sheet.write_string(
                (row_idx + 1) as u32,
                ((col_idx + 1) * 2) as u16,
                val.to_string(),
            )?;
            sheet.write_number_with_format(
                (row_idx + 1) as u32,
                ((col_idx + 1) * 2 + 1) as u16,
                sched
                    .catalog
                    .courses
                    .get(val)
                    .map(|(_, x, _)| x.unwrap_or(0))
                    .ok_or(anyhow::anyhow!("Course lookup not found: {}", val))?,
                &center_format,
            )?;

            sem_sums[col_idx] += sched
                .catalog
                .courses
                .get(val)
                .and_then(|(_, x, _)| *x)
                .unwrap_or(0);
            last_row = last_row.max(row_idx);
        }
    }

    for (col_idx, sum) in sem_sums.iter().enumerate() {
        sheet.write_string_with_format(
            (last_row + 2) as u32,
            (col_idx * 2) as u16,
            "Total",
            &total_format,
        )?;
        sheet
            .write_formula_with_format(
                (last_row + 2) as u32,
                (col_idx * 2 + 1) as u16,
                format!(
                    "=SUM({}:{})",
                    rust_xlsxwriter::utility::row_col_to_cell(1, (col_idx * 2 + 1) as u16),
                    rust_xlsxwriter::utility::row_col_to_cell(
                        (last_row + 1) as u32,
                        (col_idx * 2 + 1) as u16
                    )
                )
                .as_str(),
                &center_format,
            )?
            .set_formula_result(
                (last_row + 2) as u32,
                (col_idx * 2 + 1) as u16,
                format!("{sum}"),
            );
        sheet.set_column_width((col_idx * 2 + 1) as u16, 2.5)?;
    }

    sheet.autofit();

    Ok(())
}

fn embed_schedule_in_sheet(sheet: &mut Worksheet, sched: &Schedule) -> Result<()> {
    sheet.insert_image(
        0,
        0,
        &Image::new_from_buffer(&[TEMPLATE_PNG, &save_to_mem(SAVEFILE_VERSION, sched)?].concat())?,
    )?;

    Ok(())
}

pub fn save_schedule(fname: &PathBuf, sched: &Schedule) -> Result<()> {
    let mut workbook = Workbook::new();

    let schedule_sheet = workbook.add_worksheet().set_name("Schedule")?;
    pretty_print_sched_to_sheet(sched, schedule_sheet)?;
    schedule_sheet.protect();

    let internal_sheet = workbook.add_worksheet().set_name("Internals")?;
    embed_schedule_in_sheet(internal_sheet, sched)?;
    internal_sheet.protect();
    #[cfg(not(debug_assertions))]
    internal_sheet.set_hidden(true);

    workbook.save(fname)?;
    Ok(())
}
