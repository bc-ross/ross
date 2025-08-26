const fn parse_part_bytes(bytes: &[u8; 16], len: usize) -> u32 {
    let mut i = 0;
    let mut n = 0u32;
    while i < len {
        let b = bytes[i];
        if b < b'0' || b > b'9' {
            break;
        }
        n = n * 10 + (b - b'0') as u32;
        i += 1;
    }
    n
}

const fn version_to_int(version: &str) -> u32 {
    let bytes = version.as_bytes();
    let mut i = 0;
    let mut part = [0u8; 16];
    let mut part_idx = 0;
    let mut parts = [0u32; 3];
    let mut part_num = 0;

    while i <= bytes.len() {
        let b = if i < bytes.len() { bytes[i] } else { b'.' };
        if b == b'.' || i == bytes.len() {
            parts[part_num] = parse_part_bytes(&part, part_idx);
            part_num += 1;
            part = [0u8; 16];
            part_idx = 0;
            if part_num == 3 {
                break;
            }
        } else if part_idx < part.len() {
            part[part_idx] = b;
            part_idx += 1;
        }
        i += 1;
    }
    parts[0] * 1_000_000 + parts[1] * 1_000 + parts[2]
}

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const SAVEFILE_VERSION: u32 = version_to_int(VERSION);
