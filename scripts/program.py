import pathlib
import subprocess

PATH = pathlib.Path(__file__).parent.parent.joinpath("resources", "programs")

BASE_PREAMBLE = "use crate::schedule::Program;\n"

BASE_MIDAMBLE = "\npub fn programs() -> Vec<Program> { vec![\n"

BASE_POSTAMBLE = "]}"


def parse_course_code(code):
    code = code.strip()
    if "-" not in code:
        raise ValueError(f"Invalid course code format: {code}")
    stem, num = code.split("-", 1)
    try:
        num = int(num)
    except ValueError:
        num = f'"{num}"'
    return f'CC!("{stem.upper()}", {num})'


def main():
    print("=== Program Definition REPL ===")
    name = input("Program name: ").strip()
    fname = input("Program shortname (for file): ").strip()
    semesters = []
    sem_num = 1
    while True:
        line = input(f"Semester {sem_num} course codes (comma-separated, blank to finish): ").strip()
        if not line:
            break
        codes = [parse_course_code(code) for code in line.split(",") if code.strip()]
        semesters.append(f"            vec![{', '.join(codes)}],")
        sem_num += 1

    stems_line = input("Associated stems (comma-separated): ").strip()
    stems = [f'"{s.strip().upper()}".to_string()' for s in stems_line.split(",") if s.strip()]

    rust_code = (
        """
#![allow(unused_imports)]

use crate::CC;
use crate::geneds::ElectiveReq::*;
use crate::schedule::{CourseCode, Elective, Program};

pub fn prog() -> Program {
    Program {
    """
        + f"""
            name: "{name}".to_string(),
            semesters: vec![
    {chr(10).join(semesters)}
            ],
            assoc_stems: vec![{", ".join(stems)}],
    """
        + "electives: vec![],\n}}"
    )
    with open(PATH.joinpath("TEMP.rs").with_stem(f"prog_{fname.lower()}"), "w", encoding="utf-8") as f:
        f.write(rust_code)
    print(f"Program written to {PATH.joinpath('TEMP.rs').with_stem(f'prog_{fname.lower()}')}")

    with open(PATH.joinpath("mod.rs"), "w", encoding="utf-8") as base_f:
        base_f.write(BASE_PREAMBLE)
        for i in PATH.glob("prog_*.rs"):
            base_f.write(f"mod prog_{i.stem[5:].lower()};\n")
        base_f.write(BASE_MIDAMBLE)
        for i in PATH.glob("prog_*.rs"):
            base_f.write(f"prog_{i.stem[5:].lower()}::prog(),\n")
        base_f.write(BASE_POSTAMBLE)
    subprocess.run(["rustfmt", str(PATH.joinpath("TEMP.rs").with_stem(f"prog_{fname.lower()}"))], check=True)
    subprocess.run(["rustfmt", str(PATH.joinpath("mod.rs"))], check=True)


if __name__ == "__main__":
    main()
