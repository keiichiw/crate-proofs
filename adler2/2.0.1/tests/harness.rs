use adler2::{adler32_slice, Adler32};

fn reference(seed: u32, bytes: &[u8]) -> u32 {
    let mut a = u64::from(seed & 0xffff);
    let mut b = u64::from(seed >> 16);
    for &byte in bytes {
        a = (a + u64::from(byte)) % 65521;
        b = (b + a) % 65521;
    }
    // compute() normalizes even an empty update.
    ((b % 65521) as u32) << 16 | (a % 65521) as u32
}

#[test]
fn state_roundtrip() {
    for seed in [0, 1, 65520, 65521, 65535, 0xffff0000, u32::MAX] {
        assert_eq!(Adler32::from_checksum(seed).checksum(), seed);
    }
    assert_eq!(Adler32::new().checksum(), 1);
}

#[test]
fn scalar_reference_at_chunk_boundaries() {
    for len in [0, 1, 2, 3, 4, 5, 5551, 5552, 5553, 22207, 22208, 22209, 44419] {
        for fill in [0, 1, 255] {
            let data = vec![fill; len];
            assert_eq!(adler32_slice(&data), reference(1, &data));
            for seed in [0, 1, 0xfff0fff0, u32::MAX] {
                let mut state = Adler32::from_checksum(seed);
                state.write_slice(&data);
                assert_eq!(state.checksum(), reference(seed, &data));
            }
            let mut incremental = Adler32::new();
            for part in data.chunks(7) { incremental.write_slice(part); }
            assert_eq!(incremental.checksum(), adler32_slice(&data));
        }
    }
}
