#![allow(unused_imports)]

use crate::CC;
use crate::geneds::ElectiveReq::*;
use crate::schedule::{CourseCode, Elective, Program};

pub fn prog() -> Program {
    Program {
        name: "BA Physics".to_string(),
        semesters: vec![
            vec![
                CC!("PHYS", 2100),
                CC!("PHYS", 2101),
                CC!("CHEM", 1200),
                CC!("CHEM", 1201),
                CC!("MATH", 1300),
            ],
            vec![CC!("PHYS", 2110), CC!("PHYS", 2111), CC!("MATH", 1350)],
            vec![
                CC!("PHYS", 3200),
                CC!("PHYS", 3201),
                CC!("MATH", 2300),
                CC!("PHYS", 4200),
            ],
            vec![
                CC!("PHYS", 3210),
                CC!("PHYS", 3211),
                CC!("MATH", 3100),
                CC!("CSCI", 2300),
            ],
            vec![CC!("PHYS", 4100), CC!("PHYS", 4900)],
            vec![CC!("PHYS", 4300), CC!("PHYS", 4301), CC!("PHYS", 4901)],
            vec![CC!("PHYS", 4600), CC!("PHYS", 4902), CC!("PHYS", 4800)],
            vec![CC!("PHYS", 4910), CC!("PHYS", 4903), CC!("PHYS", "COMP")],
        ],
        assoc_stems: vec!["PHYS".to_string()],
        electives: vec![],
    }
}
