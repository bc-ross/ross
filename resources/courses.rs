use crate::{
    schedule::{
        CourseCode,
        CourseTermOffering::{self, *},
    },
    CC,
};
use std::collections::HashMap;

pub fn courses() -> HashMap<CourseCode, (String, Option<u32>, CourseTermOffering)> {
    HashMap::from([
        (
            CC!("ARCH", 2300),
            ("Architectural History I".into(), Some(3), Fall),
        ),
        (
            CC!("ARCH", 2301),
            ("Architectural History 2".into(), Some(3), Spring),
        ),
        (
            CC!("ARCH", 3400),
            ("Architecture of Cities".into(), Some(3), Fall),
        ),
        (
            CC!("ARCH", 4116),
            ("Capstone Studio 6".into(), Some(6), Spring),
        ),
        (CC!("ART", 1000), ("Drawing I".into(), Some(3), Both)),
        (
            CC!("ART", 1010),
            (
                "Foundations of 2-D Design: Comp & Color".into(),
                Some(3),
                Both,
            ),
        ),
        (
            CC!("ART", 1030),
            (
                "Foundations of 3-D Design: Form & Space".into(),
                Some(3),
                Both,
            ),
        ),
        (CC!("ART", 2410), ("Art Appreciation".into(), Some(3), Both)),
        (CC!("ART", 2600), ("Ceramics I".into(), Some(3), Both)),
        (
            CC!("ART", 2800),
            ("Basic Digital Photography".into(), Some(3), Discretion),
        ),
        (CC!("ART", 3411), ("Art History I".into(), Some(3), Fall)),
        (
            CC!("ART", 3412),
            ("Art History II (survey)".into(), Some(3), Spring),
        ),
        (
            CC!("ART", 3413),
            ("Twentieth Century Art".into(), Some(3), Fall),
        ),
        (
            CC!("ART", 4311),
            ("Design for Social Good".into(), Some(3), Fall),
        ),
        (
            CC!("ART", 4900),
            ("Professional Practices".into(), Some(2), Fall),
        ),
        (
            CC!("ASTR", 1300),
            ("Sun & Solar System".into(), Some(4), Fall),
        ),
        (
            CC!("ASTR", 1400),
            ("Stars & Stellar Systems".into(), Some(4), Spring),
        ),
        (
            CC!("ASTR", 3000),
            ("Observational Astronomy".into(), Some(3), Fall),
        ),
        (
            CC!("ASTR", 4100),
            ("Introduction to Astrophysics".into(), Some(3), Fall),
        ),
        (
            CC!("ASTR", 4200),
            ("Solar System Astrophysics".into(), Some(3), Fall),
        ),
        (
            CC!("ASTR", 4300),
            ("Galaxies & Cosmology".into(), Some(3), Spring),
        ),
        (CC!("BIOL", 1050), ("Microbial World".into(), Some(4), Fall)),
        (
            CC!("BIOL", 1105),
            ("Plants & Civilization".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 1107),
            ("Principles of Biology".into(), Some(4), Both),
        ),
        (
            CC!("BIOL", 1121),
            ("General Biology I".into(), Some(5), Fall),
        ),
        (
            CC!("BIOL", 1122),
            ("General Biology II".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 2243),
            ("Human Anatomy & Physiology II".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 2260),
            ("Principles of Microbiology".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 3305),
            ("Biological Statistics".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 3310),
            ("Biology III- Mechanisms of Evolution".into(), Some(3), Fall),
        ),
        (
            CC!("BIOL", 3312),
            ("Plant Biology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 3313),
            ("Taxonomy of Flowering Plants".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 3345),
            ("Developmental Biology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 3346),
            ("Comparative Vertebrate Anatomy".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 3347),
            (
                "Kansas Vertebrates Natural History".into(),
                Some(4),
                Discretion,
            ),
        ),
        (
            CC!("BIOL", 3353),
            ("Invertebrate Biology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 3354),
            ("Animal Behavior".into(), Some(4), Discretion),
        ),
        (CC!("BIOL", 3355), ("Ecology".into(), Some(4), Discretion)),
        (
            CC!("BIOL", 3360),
            ("Microbiology".into(), Some(4), Discretion),
        ),
        (CC!("BIOL", 3370), ("Genetics".into(), Some(4), Discretion)),
        (
            CC!("BIOL", 4410),
            ("Cancer Biology".into(), Some(4), Spring),
        ),
        (
            CC!("BIOL", 4475),
            ("Molecular & Cell Biology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 4476),
            ("Immunology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 4482),
            ("Animal Physiology".into(), Some(4), Discretion),
        ),
        (
            CC!("BIOL", 4484),
            ("Cell Physiology".into(), Some(4), Discretion),
        ),
        (CC!("BIOL", 4486), ("Research".into(), Some(1), Discretion)),
        (
            CC!("BUSI", 2230),
            ("Business Communication".into(), Some(3), Discretion),
        ),
        (
            CC!("BUSI", 2650),
            ("Business Statistics".into(), Some(3), Both),
        ),
        (
            CC!("BUSI", 3710),
            ("Legal Environment of Business".into(), Some(3), Both),
        ),
        (
            CC!("BUSI", 4550),
            ("Business Ethics".into(), Some(3), Discretion),
        ),
        (
            CC!("BUSI", 4850),
            (
                "Seminr on Executive Writing and Communic".into(),
                Some(1),
                Both,
            ),
        ),
        (CC!("CENG", 4600), ("Plant Design I".into(), Some(3), Fall)),
        (
            CC!("CENG", 4610),
            ("Plant Design II".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 1010),
            ("Chemistry of the Biosphere".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 1011),
            ("Chemistry of the Biosphere Lab".into(), Some(1), Discretion),
        ),
        (
            CC!("CHEM", 1200),
            ("General Chemistry I Lecture".into(), Some(3), Both),
        ),
        (
            CC!("CHEM", 1201),
            ("General Chemistry I Lab".into(), Some(1), Both),
        ),
        (
            CC!("CHEM", 1210),
            ("General Chemistry II Lecture".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 1211),
            ("General Chemistry II Lab".into(), Some(1), Spring),
        ),
        (
            CC!("CHEM", 2200),
            ("Organic Chemistry I Lecture".into(), Some(3), Fall),
        ),
        (
            CC!("CHEM", 2201),
            ("Organic Chemistry I Lab".into(), Some(1), Fall),
        ),
        (
            CC!("CHEM", 2210),
            ("Organic Chemistry II Lecture".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 2211),
            ("Organic Chem II Lab".into(), Some(1), Spring),
        ),
        (
            CC!("CHEM", 3150),
            ("Computational Chemistry".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 3250),
            ("Environmental Chemistry".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 3300),
            ("Quantitative Analysis".into(), Some(3), Fall),
        ),
        (
            CC!("CHEM", 3301),
            ("Quantitative Analysis Lab".into(), Some(1), Fall),
        ),
        (
            CC!("CHEM", 3311),
            ("Instrumental Analysis Lab".into(), Some(1), Spring),
        ),
        (
            CC!("CHEM", 3400),
            ("Inorganic Chemistry".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 3401),
            ("Inorganic Chemistry Lab".into(), Some(1), Spring),
        ),
        (CC!("CHEM", 3500), ("Biochemistry I".into(), Some(3), Fall)),
        (
            CC!("CHEM", 3501),
            ("Biochemistry I Lab".into(), Some(1), Fall),
        ),
        (
            CC!("CHEM", 3510),
            ("Biochemistry II".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 3511),
            ("Biochemistry II Lab".into(), Some(1), Spring),
        ),
        (
            CC!("CHEM", 3650),
            ("Polymer Chemistry".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 3800),
            ("Physical Chemistry I".into(), Some(3), Spring),
        ),
        (
            CC!("CHEM", 3801),
            ("Physical Chemistry I Lab".into(), Some(1), Spring),
        ),
        (
            CC!("CHEM", 3980),
            ("Special Topics".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 4200),
            ("Physical Chemistry II".into(), Some(3), Fall),
        ),
        (
            CC!("CHEM", 4350),
            ("Advanced Organic Chemistry I".into(), Some(3), Discretion),
        ),
        (
            CC!("CHEM", 4450),
            ("Topics in Biochemistry".into(), Some(3), Fall),
        ),
        (
            CC!("CHEM", 4650),
            ("Organometallic Chemistry".into(), Some(3), Discretion),
        ),
        (CC!("CHEM", 4801), ("Research I".into(), Some(1), Both)),
        (CC!("CHEM", 4811), ("Research II".into(), Some(1), Both)),
        (
            CC!("CHEM", 4900),
            ("Chemistry & Biochem Colloquium".into(), Some(1), Both),
        ),
        (
            CC!("CHEM", 4901),
            ("Chem & Biochem Colloquium 2".into(), Some(1), Both),
        ),
        (
            CC!("CHEM", 4902),
            ("Chem & Biochem Colloquium 3".into(), Some(1), Both),
        ),
        (
            CC!("CHEM", 4903),
            ("Chem & Biochem Colloquium 4".into(), Some(1), Both),
        ),
        (
            CC!("CHEM", 4980),
            ("Special Topics".into(), Some(4), Discretion),
        ),
        (
            CC!("CHEM", "COMP"),
            ("Senior Comprehensive Exam".into(), None, Both),
        ),
        (
            CC!("CIVL", 3010),
            (
                "Soil Mechanics & Civil Eng Materials Lab".into(),
                Some(2),
                Spring,
            ),
        ),
        (
            CC!("CIVL", 3020),
            (
                "Environmental & Hydraulic Engineeri Lab".into(),
                Some(2),
                Fall,
            ),
        ),
        (
            CC!("CIVL", 4700),
            ("Civil Engineering Seminar".into(), Some(1), Fall),
        ),
        (
            CC!("CRIM", 1000),
            ("Introduction to Crime & Justice".into(), Some(3), Both),
        ),
        (
            CC!("CRIM", 3100),
            ("Theories of Crime & Deviance".into(), Some(3), Spring),
        ),
        (
            CC!("CRIM", 3200),
            ("Crime Analysis".into(), Some(3), Discretion),
        ),
        (
            CC!("CRIM", 3300),
            ("Juvenile Delinquency".into(), Some(3), Fall),
        ),
        (
            CC!("CSCI", 2300),
            (
                "Programming for Scientists & Engineers".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("CSCI", 4930),
            ("Computer Science Senior Capstone".into(), Some(2), Spring),
        ),
        (
            CC!("DANC", 3800),
            ("History of Dance".into(), Some(3), Discretion),
        ),
        (
            CC!("ECON", 1000),
            ("Economics of Social & Public Issues".into(), Some(3), Fall),
        ),
        (
            CC!("ECON", 1010),
            ("Introduction to Economics".into(), Some(3), Infrequently),
        ),
        (
            CC!("ECON", 2090),
            ("Principles of Macroeconomics".into(), Some(3), Both),
        ),
        (
            CC!("ECON", 2100),
            ("Principles of Microeconomics".into(), Some(3), Both),
        ),
        (
            CC!("ECON", 3000),
            ("Contemporary Economic Thinking".into(), Some(3), Fall),
        ),
        (
            CC!("ECON", 3010),
            ("Environmental Economics".into(), Some(3), Fall),
        ),
        (
            CC!("ECON", 3260),
            ("Catholic Social Teaching".into(), Some(3), Spring),
        ),
        (
            CC!("ECON", 4010),
            ("Seminar in Economic Development".into(), Some(3), Spring),
        ),
        (
            CC!("EDUC", 2220),
            ("Science of Learning & Teaching".into(), Some(3), Both),
        ),
        (
            CC!("EDUC", 4451),
            ("Philosophy of Education".into(), Some(3), Both),
        ),
        (
            CC!("EDUC", 4470),
            ("Student Teaching Seminar".into(), Some(2), Both),
        ),
        (
            CC!("EDUC", 4492),
            (
                "Supervised Student Teaching Elem School".into(),
                Some(12),
                Both,
            ),
        ),
        (
            CC!("EDUC", 4496),
            (
                "Supervised Student Teach Secondar School".into(),
                Some(10),
                Both,
            ),
        ),
        (
            CC!("EDUC", 4497),
            ("Modified Teaching Experience".into(), Some(5), Both),
        ),
        (
            CC!("EENG", 4600),
            ("Electrical Engin Design I".into(), Some(3), Fall),
        ),
        (
            CC!("EENG", 4610),
            ("Electrical Engin Design II".into(), Some(3), Spring),
        ),
        (
            CC!("ENGL", 1000),
            ("English Composition With Review".into(), Some(4), Both),
        ),
        (
            CC!("ENGL", 1010),
            ("English Composition".into(), Some(3), Both),
        ),
        (
            CC!("ENGL", 1020),
            ("Introduction to Literature".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 1500),
            (
                "World Lit I: Ancient to Renaissance".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 1550),
            (
                "World Lit II: Enlightenment-Present".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 1575),
            (
                "World Lit 3: 19th Century to WW1".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 1600),
            ("British Literature to 1750".into(), Some(3), Both),
        ),
        (
            CC!("ENGL", 1650),
            ("British Literature After 1750".into(), Some(3), Both),
        ),
        (
            CC!("ENGL", 1700),
            ("American Literature Thru Civil War".into(), Some(3), Both),
        ),
        (
            CC!("ENGL", 1750),
            ("British Literature to 1750".into(), Some(3), Both),
        ),
        (
            CC!("ENGL", 3010),
            (
                "Old & Middle English Literature".into(),
                Some(3),
                Infrequently,
            ),
        ),
        (CC!("ENGL", 3020), ("Shakespeare".into(), Some(3), Spring)),
        (
            CC!("ENGL", 3030),
            ("Renaissance Literature".into(), Some(3), Infrequently),
        ),
        (
            CC!("ENGL", 3040),
            (
                "Restoration & 18th Century Literature".into(),
                Some(3),
                Infrequently,
            ),
        ),
        (
            CC!("ENGL", 3060),
            ("Classical Mythology".into(), Some(3), Discretion),
        ),
        (CC!("ENGL", 3110), ("The Novel".into(), Some(3), Discretion)),
        (
            CC!("ENGL", 3120),
            ("Short Story".into(), Some(3), Discretion),
        ),
        (CC!("ENGL", 3140), ("The Play".into(), Some(3), Discretion)),
        (CC!("ENGL", 3150), ("Film".into(), Some(3), Discretion)),
        (
            CC!("ENGL", 3250),
            ("Creative Writing".into(), Some(3), Fall),
        ),
        (
            CC!("ENGL", 3270),
            ("Writing Fiction".into(), Some(3), Spring),
        ),
        (
            CC!("ENGL", 4010),
            ("Romantic Literature".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 4020),
            ("Victorian Literature".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 4050),
            (
                "20th Century British Literature".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 4060),
            (
                "Contemporary American Literature".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 4110),
            ("Literary Criticism".into(), Some(3), Spring),
        ),
        (
            CC!("ENGL", 4130),
            ("Christianity & Literature".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 4140),
            (
                "The Vikings: History & Literature".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("ENGL", 4200),
            ("Legends of King Arthur".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 4250),
            ("Creative Writing II".into(), Some(3), Discretion),
        ),
        (
            CC!("ENGL", 4910),
            ("Language & Literature Seminar".into(), Some(3), Both),
        ),
        (
            CC!("ENGR", 1001),
            ("STEM Fund of Robitcs & Makerlabs".into(), Some(3), Fall),
        ),
        (
            CC!("ENGR", 1500),
            ("Technical Drawing".into(), Some(2), Spring),
        ),
        (
            CC!("ENGR", 3170),
            ("Engineering Economy & Society".into(), Some(3), Both),
        ),
        (
            CC!("ENGR", 3400),
            ("Materials Laboratory".into(), Some(2), Fall),
        ),
        (
            CC!("ENGR", 3410),
            ("Thermofluids Laboratory".into(), Some(2), Spring),
        ),
        (
            CC!("ESLG", 2220),
            ("Advanced Composition & Research".into(), Some(3), Fall),
        ),
        (
            CC!("ESLG", 2930),
            ("Public Speaking".into(), Some(3), Spring),
        ),
        (
            CC!("EXSC", 1100),
            ("Physical Fitness".into(), Some(1), Fall),
        ),
        (
            CC!("EXSC", 1101),
            ("Aerobics-FITNESS".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1105),
            (
                "Beginning Gymnastics & Body Mechanics".into(),
                Some(1),
                Fall,
            ),
        ),
        (
            CC!("EXSC", 1106),
            ("Beginning Swimming".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1107),
            (
                "Beg Weight & Circuit Training -FITNESS".into(),
                Some(1),
                Both,
            ),
        ),
        (
            CC!("EXSC", 1108),
            ("Intermediate Swimming- Fitness".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1109),
            ("Karate (FITNESS)".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1111),
            ("Varsity Sport Activity".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1114),
            ("Aikido (FITNESS)".into(), Some(1), Both),
        ),
        (
            CC!("EXSC", 1115),
            ("Wellness for Life".into(), Some(1), Both),
        ),
        (CC!("EXSC", 1116), ("Lifestyle FIT".into(), Some(1), Both)),
        (
            CC!("EXSC", 1117),
            ("Brazilian Jiu Jitsu I".into(), Some(1), Discretion),
        ),
        (CC!("EXSC", 1126), ("Zumba (FITNESS)".into(), Some(1), Both)),
        (
            CC!("EXSC", 1128),
            ("FITNESS Swimming".into(), Some(1), Both),
        ),
        (CC!("EXSC", 1129), ("Pickleball".into(), Some(1), Both)),
        (
            CC!("EXSC", 3380),
            ("Kinesiology & Biomechanical Analysis".into(), Some(3), Both),
        ),
        (
            CC!("EXSC", 4457),
            (
                "Meth & Tech Teach Phys Activity & Health".into(),
                Some(3),
                Fall,
            ),
        ),
        (
            CC!("FIAR", 1100),
            ("Introduction to Fine Arts".into(), Some(3), Infrequently),
        ),
        (
            CC!("FINC", 4940),
            (
                "History Financial Institutions & Markets".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("FREN", 1000),
            ("Beginning French".into(), Some(4), Fall),
        ),
        (
            CC!("FREN", 1020),
            ("Second Semester French".into(), Some(4), Spring),
        ),
        (
            CC!("FREN", 3040),
            (
                "Introduction to French Literature".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3500),
            ("French Study Abroad".into(), Some(1), Discretion),
        ),
        (
            CC!("FREN", 3510),
            (
                "Advanced French Grammar & Conversation".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3610),
            ("French Civilization".into(), Some(3), Discretion),
        ),
        (
            CC!("FREN", 3620),
            (
                "Survey French Lit From Origin to Classic".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3630),
            (
                "Survey French Lit-Classical to Symbolism".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3640),
            (
                "Survey French Lit-Symbolism-Current".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3650),
            (
                "Intro Francophone Literature & Cultures".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("FREN", 3700),
            ("History of French Cinema".into(), Some(3), Discretion),
        ),
        (
            CC!("GNST", 1110),
            ("Learning Community Lab".into(), Some(2), Fall),
        ),
        (CC!("GNST", 1800), ("Moot Court".into(), Some(2), Fall)),
        (
            CC!("GNST", 3000),
            (
                "International Study Reflection & Practic".into(),
                Some(1),
                Both,
            ),
        ),
        (
            CC!("GNST", 3200),
            ("Catholic Worldview Fellowship".into(), Some(3), Summer),
        ),
        (
            CC!("GREK", 1000),
            ("Beginning Greek I".into(), Some(4), Fall),
        ),
        (
            CC!("GREK", 1020),
            ("Beginning Greek II".into(), Some(4), Spring),
        ),
        (
            CC!("HIST", 1100),
            ("World Civilization to 1500".into(), Some(3), Both),
        ),
        (
            CC!("HIST", 1101),
            ("World Civilization Since 1500".into(), Some(3), Both),
        ),
        (
            CC!("HIST", 1300),
            ("United States History to 1865".into(), Some(3), Fall),
        ),
        (
            CC!("HIST", 1380),
            ("United States History Since 1865".into(), Some(3), Both),
        ),
        (
            CC!("HIST", 2000),
            ("History Methods & Historiography".into(), Some(3), Fall),
        ),
        (
            CC!("HIST", 3100),
            (
                "United States Diplomatic History".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("HIST", 3140),
            ("Medieval Travelers".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3141),
            ("The Crusades".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3280),
            ("Modern Asian Survey".into(), Some(3), Infrequently),
        ),
        (
            CC!("HIST", 3301),
            ("United States Military History".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3380),
            (
                "Early American Republic 1789-1828".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("HIST", 3381),
            (
                "United States Civil War 1828-1865".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("HIST", 3383),
            (
                "Prosperity & Depression 1919-1941".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("HIST", 3385),
            ("History of American Film".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3520),
            ("Ancient Greece".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3521),
            ("Ancient Rome".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3522),
            ("Greek & Roman History".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3540),
            ("Medieval History".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3541),
            ("Byzantine History".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3542),
            ("The Renaissance".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3543),
            ("Medieval England".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3544),
            ("Medieval Lay Religion".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3660),
            ("The Reformation Era".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3661),
            ("Early Modern Europe".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3680),
            ("French Revolution & Napoleon".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3681),
            ("Ninteenth-Century Europe".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3682),
            ("Europe 1945 - Today".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3684),
            ("Russian History".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3685),
            ("World War I".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3686),
            ("World War II".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3687),
            ("The Holocaust".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 3720),
            ("Ancient Egypt".into(), Some(3), Discretion),
        ),
        (
            CC!("HIST", 4000),
            ("Seminar in History".into(), Some(3), Spring),
        ),
        (
            CC!("HONR", 1030),
            ("Honors English Research Seminar".into(), Some(3), Fall),
        ),
        (
            CC!("ITAL", 1000),
            ("Beginning Italian".into(), Some(4), Both),
        ),
        (
            CC!("ITAL", 1020),
            ("Second Semester Italian".into(), Some(4), Both),
        ),
        (
            CC!("ITAL", 3000),
            ("Europe in the Middle Ages".into(), Some(3), Both),
        ),
        (CC!("JOUR", 2620), ("Media Writing I".into(), Some(4), Both)),
        (
            CC!("JOUR", 3300),
            ("Media Writing II".into(), Some(3), Both),
        ),
        (
            CC!("LATN", 1000),
            ("Beginning Latin I".into(), Some(4), Fall),
        ),
        (
            CC!("LATN", 1020),
            ("Beginning Latin II".into(), Some(4), Spring),
        ),
        (
            CC!("LATN", 3110),
            ("Survey of Latin Prose Authors".into(), Some(3), Discretion),
        ),
        (
            CC!("LATN", 3120),
            ("Latin Prose Authors II".into(), Some(3), Discretion),
        ),
        (
            CC!("LATN", 4110),
            ("Survey of Latin Poets".into(), Some(3), Discretion),
        ),
        (
            CC!("LATN", 4120),
            ("Latin Poets II".into(), Some(3), Discretion),
        ),
        (
            CC!("MATH", 1020),
            ("Mathematics As a Liberal Art".into(), Some(3), Both),
        ),
        (
            CC!("MATH", 1120),
            ("Mathematics for Elem Teachers II".into(), Some(3), Both),
        ),
        (
            CC!("MATH", 1220),
            ("Introductory Statistics".into(), Some(4), Both),
        ),
        (CC!("MATH", 1250), ("Pre-Calculus".into(), Some(4), Both)),
        (CC!("MATH", 1300), ("Calculus I".into(), Some(4), Both)),
        (CC!("MATH", 1350), ("Calculus II".into(), Some(4), Both)),
        (CC!("MATH", 2300), ("Calculus III".into(), Some(4), Both)),
        (
            CC!("MATH", 2550),
            ("Discrete Mathematical Structures I".into(), Some(3), Fall),
        ),
        (
            CC!("MATH", 3100),
            ("Differential Equations".into(), Some(3), Both),
        ),
        (
            CC!("MATH", 4457),
            (
                "Secondary School Math Curr & Materials".into(),
                Some(4),
                Fall,
            ),
        ),
        (
            CC!("MATH", 4930),
            ("Directed Research".into(), Some(2), Fall),
        ),
        (CC!("MCOM", 1000), ("Media & Society".into(), Some(3), Both)),
        (
            CC!("MCOM", 1030),
            ("Introduction to Cinema".into(), Some(3), Fall),
        ),
        (CC!("MCOM", 1610), ("Layout & Design".into(), Some(3), Both)),
        (
            CC!("MCOM", 2500),
            ("Web Design I".into(), Some(3), Discretion),
        ),
        (
            CC!("MCOM", 2600),
            ("Principles of Visual Communications".into(), Some(3), Both),
        ),
        (
            CC!("MCOM", 2610),
            ("Digital Photography I".into(), Some(4), Fall),
        ),
        (
            CC!("MCOM", 3310),
            ("Art of Presentation".into(), Some(3), Discretion),
        ),
        (
            CC!("MCOM", 3600),
            ("Signs & Symbols".into(), Some(3), Discretion),
        ),
        (
            CC!("MCOM", 3610),
            ("Digital Photography II".into(), Some(4), Discretion),
        ),
        (CC!("MENG", 4700), ("Senior Seminar".into(), Some(1), Fall)),
        (
            CC!("MGMT", 2250),
            ("Prin of Business Management".into(), Some(3), Both),
        ),
        (
            CC!("MGMT", 3250),
            ("International Management & Culture".into(), Some(3), Both),
        ),
        (
            CC!("MILS", 1160),
            ("Foundations of Officership".into(), Some(1), Fall),
        ),
        (
            CC!("MILS", 2160),
            ("Individual Leadership Studies".into(), Some(2), Fall),
        ),
        (
            CC!("MILS", 3160),
            ("Leadership & Problem Solving".into(), Some(3), Fall),
        ),
        (
            CC!("MKTG", 3100),
            ("Principles of Marketing".into(), Some(3), Both),
        ),
        (
            CC!("MUSC", 1100),
            ("Music Appreciation".into(), Some(3), Both),
        ),
        (
            CC!("MUSC", 1101),
            ("World Music Literature".into(), Some(3), Spring),
        ),
        (
            CC!("MUSC", 1102),
            ("History of Jazz".into(), Some(3), Discretion),
        ),
        (CC!("MUSC", 2214), ("Vocal Methods".into(), Some(1), Spring)),
        (
            CC!("MUSC", 3201),
            ("Introduction to Conducting".into(), Some(1), Fall),
        ),
        (
            CC!("MUSC", 4100),
            ("Music History I: Antiquity to 1750".into(), Some(3), Fall),
        ),
        (
            CC!("MUSC", 4110),
            ("Music History II: 1750-1900".into(), Some(3), Spring),
        ),
        (
            CC!("MUSC", 4120),
            ("Music History III: After 1900".into(), Some(3), Fall),
        ),
        (
            CC!("NASC", 1000),
            ("Environmental Science".into(), Some(3), Spring),
        ),
        (
            CC!("NASC", 1100),
            ("Environmental Geology".into(), Some(3), Spring),
        ),
        (CC!("NASC", 1400), ("Earth Science".into(), Some(3), Fall)),
        (
            CC!("NASC", 1600),
            (
                "Origins of Major Theories in Science".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("NASC", 2300),
            ("World Regional Geography".into(), Some(3), Both),
        ),
        (
            CC!("NASC", 3100),
            (
                "Historical Readings in Natural Science".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("NURS", 3200),
            ("Foundations of Nursing".into(), Some(3), Fall),
        ),
        (CC!("NURS", 3350), ("Pharmacology".into(), Some(4), Fall)),
        (CC!("NURS", 4200), ("Population Care".into(), Some(3), Fall)),
        (
            CC!("NURS", 4210),
            ("Population Care: Clinical".into(), Some(2), Fall),
        ),
        (
            CC!("NURS", 4700),
            ("Legal & Ethical Issues in Nursing".into(), Some(3), Spring),
        ),
        (CC!("PHIL", 2010), ("Logic".into(), Some(3), Both)),
        (
            CC!("PHIL", 2100),
            ("Principles of Nature".into(), Some(3), Both),
        ),
        (
            CC!("PHIL", 2310),
            ("Philosophy of Nature".into(), Some(3), Both),
        ),
        (
            CC!("PHIL", 2550),
            ("Philosophical Psychology".into(), Some(3), Both),
        ),
        (CC!("PHIL", 3250), ("Ethics".into(), Some(3), Both)),
        (
            CC!("PHIL", 3550),
            ("Political Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 3670),
            ("Faith & Reason I".into(), Some(4), Discretion),
        ),
        (
            CC!("PHIL", 3690),
            ("Faith & Reason III".into(), Some(2), Discretion),
        ),
        (CC!("PHIL", 3730), ("Metaphysics".into(), Some(3), Both)),
        (
            CC!("PHIL", 3740),
            ("Natural Theology".into(), Some(3), Both),
        ),
        (
            CC!("PHIL", 3800),
            ("Epistemology".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 3820),
            ("Philosophy of Religion".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4010),
            ("Ancient Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4020),
            ("Medieval Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4030),
            ("Islamic Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4040),
            ("Early Modern Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4050),
            ("Modern Continental Philosophy".into(), Some(3), Discretion),
        ),
        (
            CC!("PHIL", 4060),
            (
                "Modern Anglo-American Philosophy".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("PHIL", 4800),
            ("Aesthetics".into(), Some(3), Infrequently),
        ),
        (
            CC!("PHIL", 4860),
            ("Philosophy of Law".into(), Some(3), Infrequently),
        ),
        (
            CC!("PHIL", 4920),
            ("Senior Thesis".into(), Some(3), Discretion),
        ),
        (
            CC!("PHYS", 1100),
            ("Concepts in Physics".into(), Some(4), Both),
        ),
        (CC!("PHYS", 1200), ("Acoustics".into(), Some(4), Fall)),
        (
            CC!("PHYS", 1300),
            ("Our Strange Universe".into(), Some(3), Fall),
        ),
        (
            CC!("PHYS", 2000),
            ("College Physics I".into(), Some(3), Fall),
        ),
        (
            CC!("PHYS", 2001),
            ("College Physics I Lab".into(), Some(1), Fall),
        ),
        (
            CC!("PHYS", 2100),
            ("Classical Physics I".into(), Some(3), Fall),
        ),
        (
            CC!("PHYS", 2101),
            ("Introductory Physics Laborartory I".into(), Some(1), Fall),
        ),
        (
            CC!("PHYS", 2110),
            ("Classical Physics II".into(), Some(3), Spring),
        ),
        (
            CC!("PHYS", 2111),
            ("Introductory Physics Lab II".into(), Some(1), Spring),
        ),
        (
            CC!("PHYS", 3200),
            ("Relativity & Atomic Physics".into(), Some(3), Fall),
        ),
        (
            CC!("PHYS", 3201),
            ("Modern Physics Lab".into(), Some(1), Fall),
        ),
        (
            CC!("PHYS", 3210),
            (
                "Nuclear & Elementary Particle Physics".into(),
                Some(2),
                Spring,
            ),
        ),
        (
            CC!("PHYS", 3211),
            ("Modern Physics Lab II".into(), Some(1), Spring),
        ),
        (CC!("PHYS", 4100), ("Mechanics I".into(), Some(3), Fall)),
        (
            CC!("PHYS", 4200),
            ("Mathematical Methods for Physics".into(), Some(3), Fall),
        ),
        (CC!("PHYS", 4300), ("Optics".into(), Some(3), Spring)),
        (
            CC!("PHYS", 4301),
            ("Optics Laboratory".into(), Some(1), Spring),
        ),
        (
            CC!("PHYS", 4600),
            ("Electricity & Magnetism I".into(), Some(3), Fall),
        ),
        (
            CC!("PHYS", 4800),
            ("Quantum Mechanics".into(), Some(3), Fall),
        ),
        (CC!("PHYS", 4900), ("Physics Colloquium".into(), None, Both)),
        (CC!("PHYS", 4901), ("Physics Colloquium".into(), None, Both)),
        (CC!("PHYS", 4902), ("Physics Colloquium".into(), None, Both)),
        (CC!("PHYS", 4903), ("Physics Colloquium".into(), None, Both)),
        (
            CC!("PHYS", 4910),
            ("Physics & Astronomy Research".into(), Some(1), Both),
        ),
        (
            CC!("PHYS", "COMP"),
            ("Senior Comprehensive Exam".into(), None, Both),
        ),
        (
            CC!("POLS", 1000),
            ("Introduction to American Government".into(), Some(3), Fall),
        ),
        (
            CC!("POLS", 1100),
            ("Fundamentals of Politics".into(), Some(3), Fall),
        ),
        (
            CC!("POLS", 1500),
            (
                "American 20th Century Political History".into(),
                Some(3),
                Both,
            ),
        ),
        (
            CC!("POLS", 1800),
            ("Principles of American Government".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 2010),
            (
                "Comparative World Government & Politics".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("POLS", 2500),
            ("Introduction to Research Methods".into(), Some(4), Spring),
        ),
        (
            CC!("POLS", 2750),
            ("Public Policy Analysis".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 3000),
            ("Comparative Politics".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 3010),
            ("European Politics".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 3250),
            ("The American Presidency".into(), Some(3), Fall),
        ),
        (
            CC!("POLS", 3600),
            ("US Foreign Policy".into(), Some(3), Fall),
        ),
        (CC!("POLS", 3700), ("Film & Politics".into(), Some(4), Fall)),
        (
            CC!("POLS", 3750),
            (
                "American Constitutional Development".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("POLS", 3850),
            ("American Political Thought".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 4010),
            ("International Relations".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 4600),
            ("Public Administration".into(), Some(3), Spring),
        ),
        (
            CC!("POLS", 4950),
            ("Capstone Senior Seminar".into(), Some(3), Fall),
        ),
        (
            CC!("PSYC", 1000),
            ("General Psychology".into(), Some(3), Both),
        ),
        (
            CC!("PSYC", 2000),
            ("Research & Statistics in Psych I".into(), Some(3), Both),
        ),
        (
            CC!("PSYC", 2010),
            ("Research & Statistics in Psych II".into(), Some(3), Both),
        ),
        (
            CC!("PSYC", 2731),
            ("Theories of Personality".into(), Some(3), Fall),
        ),
        (CC!("PSYC", 4050), ("Biopsychology".into(), Some(3), Fall)),
        (
            CC!("PSYC", 4850),
            ("Psychology Service Experience".into(), Some(3), Both),
        ),
        (
            CC!("SOCI", 1000),
            ("Introduction to Sociology".into(), Some(3), Both),
        ),
        (
            CC!("SOCI", 2250),
            ("Social Problems".into(), Some(3), Discretion),
        ),
        (
            CC!("SOCI", 2350),
            ("Cultural Anthropology".into(), Some(3), Discretion),
        ),
        (
            CC!("SOCI", 3105),
            ("Sociological Theory".into(), Some(3), Spring),
        ),
        (
            CC!("SOCI", 3155),
            (
                "Research Design for Sociology & Crimin".into(),
                Some(3),
                Fall,
            ),
        ),
        (
            CC!("SOCI", 3205),
            ("Marriage & the Family".into(), Some(3), Spring),
        ),
        (
            CC!("SOCI", 3305),
            ("Population & Society".into(), Some(3), Discretion),
        ),
        (
            CC!("SOCI", 3330),
            ("Popular Culture".into(), Some(3), Discretion),
        ),
        (
            CC!("SOCI", 3450),
            ("Social Welfare".into(), Some(3), Discretion),
        ),
        (
            CC!("SOCI", 4175),
            ("Seminar in Social Research I".into(), Some(3), Discretion),
        ),
        (
            CC!("SPAN", 1000),
            ("Beginning Spanish".into(), Some(4), Both),
        ),
        (
            CC!("SPAN", 1020),
            ("Second Semester Spanish".into(), Some(4), Both),
        ),
        (
            CC!("SPAN", 3040),
            (
                "Introduction to Hispanic Lit & Lit Analy".into(),
                Some(3),
                Fall,
            ),
        ),
        (
            CC!("SPAN", 3400),
            ("Introduction to Hispanic Linguistics".into(), Some(3), Fall),
        ),
        (
            CC!("SPAN", 3500),
            (
                "Study Abroad: Spanish Immersion".into(),
                Some(1),
                Discretion,
            ),
        ),
        (
            CC!("SPAN", 3650),
            (
                "Survey of Latin American Literature".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("SPAN", 3660),
            ("Survey of Spanish Literature".into(), Some(3), Spring),
        ),
        (
            CC!("SPAN", 3710),
            ("Spanish Civilization & Culture".into(), Some(3), Discretion),
        ),
        (
            CC!("SPAN", 3720),
            (
                "Latin American Civilization & Culture".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("SPAN", 4700),
            (
                "Topics in Latin Am & Latino Lit & Cultur".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("SPCH", 1100),
            ("Speech Communication".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 1100),
            ("Introduction to Theology".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 2000),
            ("Christian Moral Life".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 2010),
            ("Biblical Hebrew I".into(), Some(4), Discretion),
        ),
        (
            CC!("THEO", 2020),
            ("Biblical Hebrew II".into(), Some(4), Discretion),
        ),
        (
            CC!("THEO", 2100),
            ("Old Testament 1: Pentateuch".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 2144),
            ("Liturgical Art & Architecture".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 2150),
            ("New Testament I: Synoptic Gospels".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3100),
            (
                "Old Testament II: Wisdom Literature".into(),
                Some(3),
                Discretion,
            ),
        ),
        (
            CC!("THEO", 3110),
            ("Old Testament III: Prophets".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3133),
            ("Sacramental Aesthetics".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3144),
            ("Music & Catholic Liturgy".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3150),
            (
                "New Testament Lit Ii: Pauline Literature".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("THEO", 3160),
            ("Gospel of John".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3200),
            ("Sacraments & Liturgy".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3220),
            ("Christian Marriage".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3230),
            ("John Paul II & the Family".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3240),
            ("Benedictine Spirituality".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3260),
            ("Catholic Social Teaching".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3280),
            ("Spiritual Theology".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3420),
            (
                "Hist of Catholic Church I: Apost-16th C".into(),
                Some(3),
                Fall,
            ),
        ),
        (
            CC!("THEO", 3430),
            (
                "History Catholic Church Ii: Reform-Today".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("THEO", 3450),
            ("History of Monastic Life".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3620),
            ("Theology of the Church".into(), Some(3), Fall),
        ),
        (
            CC!("THEO", 3640),
            ("Christ & the Trinity".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3660),
            ("Mary, Mother of God".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3680),
            ("Faith & Reason II".into(), Some(4), Discretion),
        ),
        (
            CC!("THEO", 3690),
            ("Faith & Reason III".into(), Some(2), Discretion),
        ),
        (
            CC!("THEO", 3820),
            ("Christianity & World Religions".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3840),
            ("Protestant Tradition".into(), Some(3), Fall),
        ),
        (
            CC!("THEO", 3920),
            ("Theology of Vatican II".into(), Some(3), Spring),
        ),
        (
            CC!("THEO", 3940),
            ("Christian Bioethics".into(), Some(3), Both),
        ),
        (
            CC!("THEO", 3950),
            ("Theology of the Environment".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 3960),
            ("American Catholic History".into(), Some(3), Discretion),
        ),
        (
            CC!("THEO", 4000),
            ("Great Catholic Thinkers".into(), Some(3), Discretion),
        ),
        (
            CC!("THTR", 1010),
            ("Introduction to the Theatre".into(), Some(3), Both),
        ),
        (
            CC!("THTR", 1150),
            ("Fundamentals of Acting".into(), Some(3), Both),
        ),
        (
            CC!("THTR", 2150),
            ("Techniques of Acting".into(), Some(3), Spring),
        ),
        (
            CC!("THTR", 3520),
            ("Scene Design".into(), Some(3), Discretion),
        ),
        (
            CC!("THTR", 3560),
            ("Lighting Design".into(), Some(3), Discretion),
        ),
        (
            CC!("THTR", 3580),
            ("Costume Design".into(), Some(3), Discretion),
        ),
        (CC!("THTR", 3800), ("Scriptwriting".into(), Some(3), Spring)),
        (
            CC!("THTR", 3810),
            ("Theatre History & Literature to 1640".into(), Some(3), Fall),
        ),
        (
            CC!("THTR", 3820),
            (
                "Theatre History & Literature 1640-1918".into(),
                Some(3),
                Spring,
            ),
        ),
        (
            CC!("THTR", 3830),
            ("Modern & Contemporary Theatre".into(), Some(3), Fall),
        ),
        (CC!("THTR", 4150), ("Play Direction".into(), Some(3), Fall)),
    ])
}
