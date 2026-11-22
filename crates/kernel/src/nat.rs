//! Arbitrary-precision natural numbers for `Nat` literals (Lean's kernel uses GMP here).
//! Little-endian `u64` limbs, always normalised (no high zero limbs; zero is the empty slice).

use core::cmp::Ordering;

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Nat(Box<[u64]>);

/// Exponents and shift amounts above this are left unreduced (as Lean's kernel does), so a
/// literal cannot be made to allocate gigabytes.
pub const MAX_BITS: u64 = 1 << 24;

fn norm(mut v: Vec<u64>) -> Nat {
    while v.last() == Some(&0) {
        v.pop();
    }
    Nat(v.into_boxed_slice())
}

impl Nat {
    pub fn zero() -> Nat {
        Nat(Box::new([]))
    }
    pub fn from_u128(n: u128) -> Nat {
        norm(vec![n as u64, (n >> 64) as u64])
    }
    pub fn to_u128(&self) -> Option<u128> {
        match self.0.len() {
            0 => Some(0),
            1 => Some(self.0[0] as u128),
            2 => Some(self.0[0] as u128 | (self.0[1] as u128) << 64),
            _ => None,
        }
    }
    pub fn to_u64(&self) -> Option<u64> {
        match self.0.len() {
            0 => Some(0),
            1 => Some(self.0[0]),
            _ => None,
        }
    }
    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }
    pub fn bits(&self) -> u64 {
        match self.0.last() {
            None => 0,
            Some(&h) => (self.0.len() as u64 - 1) * 64 + (64 - h.leading_zeros() as u64),
        }
    }
    fn bit(&self, i: u64) -> bool {
        let (w, b) = ((i / 64) as usize, i % 64);
        w < self.0.len() && (self.0[w] >> b) & 1 == 1
    }

    pub fn from_limbs(v: Vec<u64>) -> Nat {
        norm(v)
    }
    pub fn add(&self, o: &Nat) -> Nat {
        let (a, b) = if self.0.len() >= o.0.len() { (&self.0, &o.0) } else { (&o.0, &self.0) };
        let mut v = Vec::with_capacity(a.len() + 1);
        let mut carry = 0u128;
        for i in 0..a.len() {
            let t = a[i] as u128 + *b.get(i).unwrap_or(&0) as u128 + carry;
            v.push(t as u64);
            carry = t >> 64;
        }
        if carry != 0 {
            v.push(carry as u64);
        }
        norm(v)
    }

    /// Truncated subtraction (`Nat.sub`): 0 when `o > self`.
    pub fn sub(&self, o: &Nat) -> Nat {
        if self.cmp(o) != Ordering::Greater {
            return Nat::zero();
        }
        let mut v = Vec::with_capacity(self.0.len());
        let mut borrow = 0i128;
        for i in 0..self.0.len() {
            let mut t = self.0[i] as i128 - *o.0.get(i).unwrap_or(&0) as i128 - borrow;
            borrow = if t < 0 { 1 } else { 0 };
            if t < 0 {
                t += 1i128 << 64;
            }
            v.push(t as u64);
        }
        norm(v)
    }

    pub fn mul(&self, o: &Nat) -> Nat {
        if self.is_zero() || o.is_zero() {
            return Nat::zero();
        }
        let mut v = vec![0u64; self.0.len() + o.0.len()];
        for (i, &x) in self.0.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &y) in o.0.iter().enumerate() {
                let t = x as u128 * y as u128 + v[i + j] as u128 + carry;
                v[i + j] = t as u64;
                carry = t >> 64;
            }
            v[i + o.0.len()] = carry as u64;
        }
        norm(v)
    }

    /// Quotient and remainder; `None` for division by zero.
    pub fn divmod(&self, d: &Nat) -> Option<(Nat, Nat)> {
        if d.is_zero() {
            return None;
        }
        if self.cmp(d) == Ordering::Less {
            return Some((Nat::zero(), self.clone()));
        }
        if let (Some(a), Some(b)) = (self.to_u128(), d.to_u128()) {
            return Some((Nat::from_u128(a / b), Nat::from_u128(a % b)));
        }
        // binary long division
        let n = self.bits();
        let mut q = vec![0u64; self.0.len()];
        let mut r = Nat::zero();
        for i in (0..n).rev() {
            r = r.shl(1);
            if self.bit(i) {
                r = r.add(&Nat::from_u128(1));
            }
            if r.cmp(d) != Ordering::Less {
                r = r.sub(d);
                q[(i / 64) as usize] |= 1 << (i % 64);
            }
        }
        Some((norm(q), r))
    }

    /// `Nat.div` / `Nat.mod` semantics: `x / 0 = 0`, `x % 0 = x`.
    pub fn div(&self, d: &Nat) -> Nat {
        self.divmod(d).map(|(q, _)| q).unwrap_or_default()
    }
    pub fn rem(&self, d: &Nat) -> Nat {
        self.divmod(d).map(|(_, r)| r).unwrap_or_else(|| self.clone())
    }

    pub fn gcd(&self, o: &Nat) -> Nat {
        let (mut a, mut b) = (self.clone(), o.clone());
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        a
    }

    /// `None` when the result would exceed [`MAX_BITS`].
    pub fn pow(&self, e: &Nat) -> Option<Nat> {
        let e = e.to_u64()?;
        if e == 0 {
            return Some(Nat::from_u128(1));
        }
        if self.bits().saturating_mul(e) > MAX_BITS + 64 {
            return None;
        }
        let (mut base, mut e, mut acc) = (self.clone(), e, Nat::from_u128(1));
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        Some(acc)
    }

    fn bitwise(&self, o: &Nat, f: impl Fn(u64, u64) -> u64) -> Nat {
        let n = self.0.len().max(o.0.len());
        norm((0..n).map(|i| f(*self.0.get(i).unwrap_or(&0), *o.0.get(i).unwrap_or(&0))).collect())
    }
    pub fn land(&self, o: &Nat) -> Nat {
        self.bitwise(o, |a, b| a & b)
    }
    pub fn lor(&self, o: &Nat) -> Nat {
        self.bitwise(o, |a, b| a | b)
    }
    pub fn xor(&self, o: &Nat) -> Nat {
        self.bitwise(o, |a, b| a ^ b)
    }

    pub fn shl(&self, k: u64) -> Nat {
        if self.is_zero() {
            return Nat::zero();
        }
        let (w, b) = ((k / 64) as usize, (k % 64) as u32);
        let mut v = vec![0u64; w];
        let mut carry = 0u64;
        for &x in self.0.iter() {
            v.push(if b == 0 { x } else { x << b | carry });
            carry = if b == 0 { 0 } else { x >> (64 - b) };
        }
        if carry != 0 {
            v.push(carry);
        }
        norm(v)
    }
    pub fn shr(&self, k: u64) -> Nat {
        let (w, b) = ((k / 64) as usize, (k % 64) as u32);
        if w >= self.0.len() {
            return Nat::zero();
        }
        let src = &self.0[w..];
        let v = (0..src.len())
            .map(|i| if b == 0 { src[i] } else { src[i] >> b | src.get(i + 1).map_or(0, |h| h << (64 - b)) })
            .collect();
        norm(v)
    }
    /// `Nat.log2`: floor(log2 n), with `log2 0 = 0`.
    pub fn log2(&self) -> Nat {
        Nat::from_u128(self.bits().saturating_sub(1) as u128)
    }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, o: &Nat) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Nat {
    fn cmp(&self, o: &Nat) -> Ordering {
        self.0.len().cmp(&o.0.len()).then_with(|| self.0.iter().rev().cmp(o.0.iter().rev()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn from_dec(s: &str) -> Option<Nat> {
        if s.is_empty() || !s.bytes().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let mut v: Vec<u64> = Vec::new();
        for chunk in s.as_bytes().chunks(18) {
            let (mut part, mut mul) = (0u64, 1u64);
            for &c in chunk {
                part = part * 10 + (c - b'0') as u64;
                mul *= 10;
            }
            let mut carry = part as u128;
            for limb in v.iter_mut() {
                let t = *limb as u128 * mul as u128 + carry;
                *limb = t as u64;
                carry = t >> 64;
            }
            if carry != 0 {
                v.push(carry as u64);
            }
        }
        Some(Nat::from_limbs(v))
    }

    fn to_dec(x: &Nat) -> String {
        if x.is_zero() {
            return "0".into();
        }
        let mut digits = Vec::new();
        let mut cur: Vec<u64> = x.0.to_vec();
        const BASE: u64 = 1_000_000_000_000_000_000;
        while !cur.is_empty() {
            let mut rem = 0u128;
            for limb in cur.iter_mut().rev() {
                let t = rem << 64 | *limb as u128;
                *limb = (t / BASE as u128) as u64;
                rem = t % BASE as u128;
            }
            while cur.last() == Some(&0) {
                cur.pop();
            }
            digits.push(rem as u64);
        }
        let mut s = digits.pop().unwrap().to_string();
        for d in digits.iter().rev() {
            s.push_str(&format!("{d:018}"));
        }
        s
    }

    fn n(s: &str) -> Nat {
        from_dec(s).unwrap()
    }

    #[test]
    fn decimal_round_trip_and_u128_agreement() {
        for s in ["0", "1", "18446744073709551615", "18446744073709551616", "340282366920938463463374607431768211456", "123456789012345678901234567890123456789012345678901234567890"] {
            assert_eq!(to_dec(&n(s)), s);
        }
        assert!(from_dec("12a").is_none() && from_dec("").is_none());
        let mut x: u64 = 0x9E37_79B9_7F4A_7C15;
        for _ in 0..2000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let (a, b) = ((x as u128) << 37 | (x >> 3) as u128, (x as u128 >> 9) + 1);
            let (na, nb) = (Nat::from_u128(a), Nat::from_u128(b));
            assert_eq!(to_dec(&na.add(&nb)), (a + b).to_string());
            assert_eq!(na.sub(&nb).to_u128(), Some(a.saturating_sub(b)));
            assert_eq!(nb.sub(&na).to_u128(), Some(b.saturating_sub(a)));
            assert_eq!(na.div(&nb).to_u128(), Some(a / b));
            assert_eq!(na.rem(&nb).to_u128(), Some(a % b));
            assert_eq!(na.land(&nb).to_u128(), Some(a & b));
            assert_eq!(na.lor(&nb).to_u128(), Some(a | b));
            assert_eq!(na.xor(&nb).to_u128(), Some(a ^ b));
            assert_eq!(na.shr(x % 130).to_u128(), Some(if x % 130 >= 128 { 0 } else { a >> (x % 130) }));
            assert_eq!(na.cmp(&nb), a.cmp(&b));
            let small = (x >> 40) as u128;
            assert_eq!(Nat::from_u128(small).mul(&Nat::from_u128(small)).to_u128(), Some(small * small));
            assert_eq!(Nat::from_u128(small).shl(x % 60).to_u128(), Some(small << (x % 60)));
        }
    }

    #[test]
    fn big_values() {
        let two = Nat::from_u128(2);
        let p = two.pow(&Nat::from_u128(200)).unwrap();
        assert_eq!(to_dec(&p), "1606938044258990275541962092341162602522202993782792835301376");
        assert_eq!(p.log2().to_u128(), Some(200));
        assert_eq!(Nat::from_u128(1).shl(200), p);
        assert_eq!(p.shr(199).to_u128(), Some(2));
        let m = p.sub(&Nat::from_u128(1)); // 2^200 - 1
        assert_eq!(m.add(&Nat::from_u128(1)), p);
        let (q, r) = m.divmod(&Nat::from_u128(1_000_000_007)).unwrap();
        assert_eq!(q.mul(&Nat::from_u128(1_000_000_007)).add(&r), m);
        assert!(r < Nat::from_u128(1_000_000_007));
        assert_eq!(p.gcd(&Nat::from_u128(48)).to_u128(), Some(16));
        assert_eq!(p.land(&m), Nat::zero());
        assert_eq!(to_dec(&p.lor(&m)), to_dec(&p.add(&m)));
        assert_eq!(p.div(&Nat::zero()), Nat::zero());
        assert_eq!(p.rem(&Nat::zero()), p);
        assert!(two.pow(&Nat::from_u128(MAX_BITS as u128 * 2)).is_none());
        assert_eq!(Nat::zero().log2(), Nat::zero());
    }
}
