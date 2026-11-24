//! Arbitrary-precision natural numbers for `Nat` literals (Lean's kernel uses GMP here).
//! Little-endian `u64` limbs, always normalised (no high zero limbs; zero is the empty slice).

use core::cmp::Ordering;

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Nat(Box<[u64]>);

/// Exponents and shift amounts above this are left unreduced (as Lean's kernel does), so a
/// literal cannot be made to allocate gigabytes.
pub const MAX_BITS: u64 = 1 << 24;

fn norm(mut v: Vec<u64>) -> Nat {
    while v.last() == Some(&0) { v.pop(); }
    Nat(v.into_boxed_slice())
}

impl Nat {
    pub fn zero() -> Nat { Nat(Box::new([])) }
    pub fn from_u128(n: u128) -> Nat { norm(vec![n as u64, (n >> 64) as u64]) }
    pub fn from_limbs(v: Vec<u64>) -> Nat { norm(v) }
    pub fn to_u128(&self) -> Option<u128> {
        (self.0.len() <= 2).then(|| self.0.iter().rev().fold(0u128, |acc, &l| acc << 64 | l as u128))
    }
    pub fn to_u64(&self) -> Option<u64> { (self.0.len() <= 1).then(|| self.0.first().copied().unwrap_or(0)) }
    pub fn is_zero(&self) -> bool { self.0.is_empty() }
    pub fn bits(&self) -> u64 { self.0.last().map_or(0, |&h| (self.0.len() as u64 - 1) * 64 + (64 - h.leading_zeros() as u64)) }
    fn bit(&self, i: u64) -> bool { self.0.get((i / 64) as usize).is_some_and(|w| (w >> (i % 64)) & 1 == 1) }
    fn limb(&self, i: usize) -> u64 { self.0.get(i).copied().unwrap_or(0) }

    pub fn add(&self, o: &Nat) -> Nat {
        let n = self.0.len().max(o.0.len());
        let mut v = Vec::with_capacity(n + 1);
        let mut carry = 0u128;
        for i in 0..n {
            let t = self.limb(i) as u128 + o.limb(i) as u128 + carry;
            v.push(t as u64);
            carry = t >> 64;
        }
        v.push(carry as u64);
        norm(v)
    }

    /// Truncated subtraction (`Nat.sub`): 0 when `o > self`.
    pub fn sub(&self, o: &Nat) -> Nat {
        if self.cmp(o) != Ordering::Greater { return Nat::zero(); }
        let (mut v, mut borrow) = (Vec::with_capacity(self.0.len()), 0i128);
        for i in 0..self.0.len() {
            let t = self.0[i] as i128 - o.limb(i) as i128 - borrow;
            borrow = (t < 0) as i128;
            v.push((t + (borrow << 64)) as u64);
        }
        norm(v)
    }

    pub fn mul(&self, o: &Nat) -> Nat {
        if self.is_zero() || o.is_zero() { return Nat::zero(); }
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
        if d.is_zero() { return None; }
        if self.cmp(d) == Ordering::Less { return Some((Nat::zero(), self.clone())); }
        if let (Some(a), Some(b)) = (self.to_u128(), d.to_u128()) {
            return Some((Nat::from_u128(a / b), Nat::from_u128(a % b)));
        }
        // binary long division
        let (mut q, mut r) = (vec![0u64; self.0.len()], Nat::zero());
        for i in (0..self.bits()).rev() {
            r = r.shl(1);
            if self.bit(i) { r = r.add(&Nat::from_u128(1)); }
            if r.cmp(d) != Ordering::Less {
                r = r.sub(d);
                q[(i / 64) as usize] |= 1 << (i % 64);
            }
        }
        Some((norm(q), r))
    }

    /// `Nat.div` / `Nat.mod` semantics: `x / 0 = 0`, `x % 0 = x`.
    pub fn div(&self, d: &Nat) -> Nat { self.divmod(d).map(|(q, _)| q).unwrap_or_default() }
    pub fn rem(&self, d: &Nat) -> Nat { self.divmod(d).map(|(_, r)| r).unwrap_or_else(|| self.clone()) }

    pub fn gcd(&self, o: &Nat) -> Nat {
        let (mut a, mut b) = (self.clone(), o.clone());
        while !b.is_zero() { (a, b) = (b.clone(), a.rem(&b)); }
        a
    }

    /// `None` when the result would exceed [`MAX_BITS`].
    pub fn pow(&self, e: &Nat) -> Option<Nat> {
        let mut e = e.to_u64()?;
        if e == 0 { return Some(Nat::from_u128(1)); }
        if self.bits().saturating_mul(e) > MAX_BITS + 64 { return None; }
        let (mut base, mut acc) = (self.clone(), Nat::from_u128(1));
        while e > 0 {
            if e & 1 == 1 { acc = acc.mul(&base); }
            e >>= 1;
            if e > 0 { base = base.mul(&base); }
        }
        Some(acc)
    }

    fn bitwise(&self, o: &Nat, f: impl Fn(u64, u64) -> u64) -> Nat {
        norm((0..self.0.len().max(o.0.len())).map(|i| f(self.limb(i), o.limb(i))).collect())
    }
    pub fn land(&self, o: &Nat) -> Nat { self.bitwise(o, |a, b| a & b) }
    pub fn lor(&self, o: &Nat) -> Nat { self.bitwise(o, |a, b| a | b) }
    pub fn xor(&self, o: &Nat) -> Nat { self.bitwise(o, |a, b| a ^ b) }

    pub fn shl(&self, k: u64) -> Nat {
        if self.is_zero() { return Nat::zero(); }
        let (w, b) = ((k / 64) as usize, (k % 64) as u32);
        let mut v = vec![0u64; w];
        let mut carry = 0u64;
        for &x in self.0.iter() {
            v.push(if b == 0 { x } else { x << b | carry });
            carry = if b == 0 { 0 } else { x >> (64 - b) };
        }
        v.push(carry);
        norm(v)
    }
    pub fn shr(&self, k: u64) -> Nat {
        let (w, b) = ((k / 64) as usize, (k % 64) as u32);
        if w >= self.0.len() { return Nat::zero(); }
        let src = &self.0[w..];
        norm((0..src.len()).map(|i| if b == 0 { src[i] } else { src[i] >> b | src.get(i + 1).map_or(0, |h| h << (64 - b)) }).collect())
    }
    /// `Nat.log2`: floor(log2 n), with `log2 0 = 0`.
    pub fn log2(&self) -> Nat { Nat::from_u128(self.bits().saturating_sub(1) as u128) }
}

impl PartialOrd for Nat {
    fn partial_cmp(&self, o: &Nat) -> Option<Ordering> { Some(self.cmp(o)) }
}
impl Ord for Nat {
    fn cmp(&self, o: &Nat) -> Ordering { self.0.len().cmp(&o.0.len()).then_with(|| self.0.iter().rev().cmp(o.0.iter().rev())) }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every operation agrees with native u128 arithmetic on random operands (xorshift, fixed seed).
    #[test]
    fn matches_u128_arithmetic() {
        let mut x = 0x2545_f491_4f6c_dd1du64;
        let mut rnd = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
        for round in 0..20_000 {
            let shift = |r: u64| r % 64;
            let a = (rnd() as u128) >> shift(rnd()) | if round % 3 == 0 { (rnd() as u128) << 64 >> shift(rnd()) } else { 0 };
            let b = (rnd() as u128) >> shift(rnd());
            let (na, nb) = (Nat::from_u128(a), Nat::from_u128(b));
            let n = |v: u128| Nat::from_u128(v);
            if let Some(s) = a.checked_add(b) { assert_eq!(na.add(&nb), n(s)); }
            assert_eq!(na.sub(&nb), n(a.saturating_sub(b)));
            if let Some(m) = (a >> 64 == 0 && b >> 64 == 0).then(|| a * b) { assert_eq!(na.mul(&nb), n(m)); }
            assert_eq!(na.div(&nb), n(a.checked_div(b).unwrap_or(0)));
            assert_eq!(na.rem(&nb), n(if b == 0 { a } else { a % b }));
            assert_eq!(na.land(&nb), n(a & b));
            assert_eq!(na.lor(&nb), n(a | b));
            assert_eq!(na.xor(&nb), n(a ^ b));
            let k = rnd() % 70;
            assert_eq!(na.shr(k), n(if k >= 128 { 0 } else { a >> k }));
            if a.leading_zeros() as u64 >= k { assert_eq!(na.shl(k), n(a << k)); }
            assert_eq!(na.cmp(&nb), a.cmp(&b));
            assert_eq!(na.to_u128(), Some(a));
            let (mut g, mut h) = (a, b);
            while h != 0 { (g, h) = (h, g % h); }
            assert_eq!(na.gcd(&nb), n(g));
            assert_eq!(na.log2(), n(if a == 0 { 0 } else { 127 - a.leading_zeros() as u128 }));
        }
        assert_eq!(Nat::from_u128(3).pow(&Nat::from_u128(40)), Some(Nat::from_u128(3u128.pow(40))));
    }

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
