#![allow(unused_imports)]

use crate::CC;
use crate::geneds::ElectiveReq::*;
use crate::schedule::{CourseCode, Elective, Program};

pub fn prog() -> Program {
    Program {
        name: "BA Chemistry".to_string(),
        semesters: vec![
            vec![CC!("CHEM", 1200), CC!("CHEM", 1201), CC!("MATH", 1300)],
            vec![CC!("CHEM", 1210), CC!("CHEM", 1211), CC!("MATH", 1350)],
            vec![
                CC!("CHEM", 2200),
                CC!("CHEM", 2201),
                CC!("PHYS", 2100),
                CC!("PHYS", 2101),
            ],
            vec![
                CC!("CHEM", 2210),
                CC!("CHEM", 2211),
                CC!("PHYS", 2110),
                CC!("PHYS", 2111),
            ],
            vec![
                CC!("CHEM", 3300),
                CC!("CHEM", 3301),
                CC!("CHEM", 3500),
                CC!("CHEM", 3501),
                CC!("CHEM", 4900),
            ],
            vec![
                CC!("CHEM", 3311),
                CC!("CHEM", 3400),
                CC!("CHEM", 3401),
                CC!("CHEM", 3800),
                CC!("CHEM", 3801),
                CC!("CHEM", 4901),
            ],
            vec![CC!("CHEM", 4801), CC!("CHEM", 4902)],
            vec![CC!("CHEM", 4811), CC!("CHEM", 4903), CC!("CHEM", "COMP")],
        ],
        assoc_stems: vec!["CHEM".to_string()],
        electives: vec![Elective {
            name: "Advanced Courses".to_string(),
            req: Courses {
                num: 2,
                courses: vec![
                    CC!("CHEM", 3150),
                    CC!("CHEM", 3250),
                    CC!("CHEM", 3510),
                    CC!("CHEM", 3650),
                    CC!("CHEM", 3980),
                    CC!("CHEM", 4980),
                    CC!("CHEM", 4350),
                    CC!("CHEM", 4450),
                    CC!("CHEM", 4650),
                    CC!("CHEM", 4200),
                ],
            },
        }],
    }
}
