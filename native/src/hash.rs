//! Scalar SHA-256, matching the byte-aligned upstream SHA model.

pub type Hash = [u8; 32];

const INITIAL_STATE: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

const ROUND_CONSTANTS: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Incremental SHA-256 without allocation or target-specific instructions.
///
/// As in the upstream model, the final length word contains the low 64 bits of
/// the bit length. FIPS 180-4's admitted message domain is fewer than 2^61 bytes.
pub struct Sha256 {
    state: [u32; 8],
    buffer: [u8; 64],
    buffered: usize,
    byte_len: u64,
}

impl Sha256 {
    pub const fn new() -> Self {
        Self { state: INITIAL_STATE, buffer: [0; 64], buffered: 0, byte_len: 0 }
    }

    pub fn update(&mut self, mut input: &[u8]) {
        self.byte_len = self.byte_len.wrapping_add(input.len() as u64);
        if self.buffered != 0 {
            let take = core::cmp::min(64 - self.buffered, input.len());
            self.buffer[self.buffered..self.buffered + take].copy_from_slice(&input[..take]);
            self.buffered += take;
            input = &input[take..];
            if self.buffered < 64 {
                return;
            }
            compress(&mut self.state, &self.buffer);
            self.buffered = 0;
        }
        // Whole blocks are read in place; only an incomplete block is copied.
        while input.len() >= 64 {
            compress(&mut self.state, &input[..64]);
            input = &input[64..];
        }
        self.buffer[..input.len()].copy_from_slice(input);
        self.buffered = input.len();
    }

    pub fn finalize(mut self) -> Hash {
        self.buffer[self.buffered] = 0x80;
        self.buffered += 1;
        if self.buffered > 56 {
            self.buffer[self.buffered..].fill(0);
            compress(&mut self.state, &self.buffer);
            self.buffered = 0;
        }
        self.buffer[self.buffered..56].fill(0);
        self.buffer[56..].copy_from_slice(&self.byte_len.wrapping_mul(8).to_be_bytes());
        compress(&mut self.state, &self.buffer);
        let mut digest = [0; 32];
        for (word, bytes) in self.state.iter().zip(digest.chunks_exact_mut(4)) {
            bytes.copy_from_slice(&word.to_be_bytes());
        }
        digest
    }
}

impl Default for Sha256 {
    fn default() -> Self { Self::new() }
}

fn compress(state: &mut [u32; 8], block: &[u8]) {
    // The recurrence reaches back at most sixteen words, so a ring replaces
    // the full sixty-four-word message schedule without recomputation.
    let mut schedule = [0u32; 16];
    for (word, bytes) in schedule.iter_mut().zip(block.chunks_exact(4)) {
        *word = u32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    for (round, constant) in ROUND_CONSTANTS.iter().enumerate() {
        let slot = round & 15;
        if round >= 16 {
            let x = schedule[(round + 1) & 15];
            let y = schedule[(round + 14) & 15];
            let sigma0 = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
            let sigma1 = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
            schedule[slot] = schedule[slot]
                .wrapping_add(sigma0)
                .wrapping_add(schedule[(round + 9) & 15])
                .wrapping_add(sigma1);
        }
        let sigma0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let sigma1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let choose = (e & f) ^ (!e & g);
        let majority = (a & b) ^ (a & c) ^ (b & c);
        let t1 = h.wrapping_add(sigma1).wrapping_add(choose)
            .wrapping_add(*constant).wrapping_add(schedule[slot]);
        let t2 = sigma0.wrapping_add(majority);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }
    for (old, working) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *old = old.wrapping_add(working);
    }
}

pub fn hash(input: &[u8]) -> Hash {
    let mut state = Sha256::new();
    state.update(input);
    state.finalize()
}

/// Hash the actual concatenation, including non-chunk-width proof nodes.
pub fn combine(left: &[u8], right: &[u8]) -> Hash {
    let mut state = Sha256::new();
    state.update(left);
    state.update(right);
    state.finalize()
}

#[cfg(test)]
mod tests {
    use super::{combine, hash, Hash, Sha256};

    fn digest(hex: &str) -> Hash {
        assert_eq!(hex.len(), 64, "SHA-256 oracle must contain exactly 32 bytes");
        let mut out = [0; 32];
        for (byte, pair) in out.iter_mut().zip(hex.as_bytes().chunks_exact(2)) {
            fn nibble(byte: u8) -> u8 {
                match byte {
                    b'0'..=b'9' => byte - b'0',
                    b'a'..=b'f' => byte - b'a' + 10,
                    _ => panic!("invalid test vector"),
                }
            }
            *byte = (nibble(pair[0]) << 4) | nibble(pair[1]);
        }
        out
    }

    #[test]
    fn published_sha256_vectors() {
        // FIPS 180-4 / NIST SHA examples: empty, one block, two blocks,
        // the long alphabet example, and one million 'a' bytes.
        for (message, expected) in [
            (&b""[..], "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
            (&b"abc"[..], "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
            (&b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"[..],
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
            (&b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"[..],
                "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
        ] {
            assert_eq!(hash(message), digest(expected));
        }
        let mut state = Sha256::new();
        for _ in 0..1000 {
            state.update(&[b'a'; 1000]);
        }
        assert_eq!(state.finalize(), digest(
            "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"));
    }

    #[test]
    fn streaming_is_independent_of_chunk_boundaries() {
        let mut message = [0u8; 257];
        for (index, byte) in message.iter_mut().enumerate() {
            *byte = index as u8;
        }
        // Independent hashlib vector includes every possible byte value.
        assert_eq!(hash(&message), digest(
            "54acfbfedc4d8da40f76f275e1a98f10af8ef1fb9fb39e5a67a00aabcbe6597c"));
        for len in [0, 1, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 257] {
            let message = &message[..len];
            let expected = hash(message);
            for split in 0..=len {
                let mut state = Sha256::new();
                state.update(&message[..split]);
                state.update(&[]);
                state.update(&message[split..]);
                assert_eq!(state.finalize(), expected, "len={len}, split={split}");
            }
            for size in [1, 3, 7, 55, 56, 63, 64, 65, 127] {
                let mut state = Sha256::new();
                for chunk in message.chunks(size) {
                    state.update(chunk);
                }
                assert_eq!(state.finalize(), expected, "len={len}, chunk size={size}");
            }
        }
    }

    #[test]
    fn combine_retains_raw_node_lengths() {
        let expected = digest("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
        assert_eq!(combine(b"a", b"bc"), expected);
        assert_eq!(combine(b"", b"abc"), expected);
        assert_eq!(combine(b"abc", b""), expected);
        let input = [0x5a; 129];
        for split in [1, 31, 32, 63, 64, 65, 128] {
            assert_eq!(combine(&input[..split], &input[split..]), hash(&input));
        }
    }
}
