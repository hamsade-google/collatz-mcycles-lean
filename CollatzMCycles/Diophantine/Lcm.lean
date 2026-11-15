module

public import Mathlib

/-!
# `lcm(1..n)` bounds from Chebyshev's `primorial n < 4 ^ n`

`D n := Nat.lcmUpto n = lcm {1, …, n}`.  We prove the purely combinatorial bounds
* `D_le_sixteen_pow : D n ≤ 16 ^ n`
* `D_le_four_pow_mul : D n ≤ 4 ^ n * 256 ^ Nat.sqrt n`
* `D_two_mul_le : D (2 * k) ≤ 2 ^ 72 * 32 ^ k`

via the divisibility `D n ∣ primorial n * D m ^ e` whenever `log_p n ≤ 1 + e · log_p m` for all
primes `p ≤ n` (instantiated with `(m, e) = (n / 2, 1)` and `(Nat.sqrt n, 2)`).
Only Chebyshev's elementary `primorial n < 4 ^ n` is used (no PNT, no Rosser–Schoenfeld).
-/

@[expose] public section
namespace CollatzMCycles.Diophantine

open Nat

/-- `D n = lcm (1, …, n)`. -/
abbrev D (n : ℕ) : ℕ := Nat.lcmUpto n

theorem D_pos (n : ℕ) : 0 < D n := Nat.lcmUpto_pos n

theorem D_ne_zero (n : ℕ) : D n ≠ 0 := Nat.lcmUpto_ne_zero n

theorem dvd_D {j n : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ n) : j ∣ D n :=
  Finset.dvd_lcm (f := id) (by simp [h1, h2])

theorem prime_dvd_primorial {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ primorial n :=
  hp.dvd_primorial_iff.mpr hpn

theorem primorial_le_four_pow (n : ℕ) : primorial n ≤ 4 ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (primorial_lt_four_pow n hn.ne').le

/-- Key divisibility. -/
theorem D_dvd_primorial_mul (n m e : ℕ)
    (h : ∀ p, p.Prime → p ≤ n → Nat.log p n ≤ 1 + e * Nat.log p m) :
    D n ∣ primorial n * D m ^ e := by
  have hprim : primorial n ≠ 0 := (primorial_pos n).ne'
  have hDm : D m ^ e ≠ 0 := pow_ne_zero _ (D_ne_zero m)
  rw [← Nat.factorization_prime_le_iff_dvd (D_ne_zero n) (mul_ne_zero hprim hDm)]
  intro p hp
  rw [Nat.factorization_lcmUpto n hp, Nat.factorization_mul hprim hDm,
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, Nat.factorization_lcmUpto m hp,
    smul_eq_mul]
  by_cases hpn : p ≤ n
  · have h1 : 1 ≤ (primorial n).factorization p :=
      hp.factorization_pos_of_dvd hprim (prime_dvd_primorial hp hpn)
    have := h p hp hpn
    omega
  · rw [Nat.log_of_lt (not_le.mp hpn)]
    exact Nat.zero_le _

theorem log_le_half (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    Nat.log p n ≤ 1 + 1 * Nat.log p (n / 2) := by
  have hp1 := hp.one_lt
  have hn0 : n ≠ 0 := by omega
  have hlog : 0 < Nat.log p n := Nat.log_pos hp1 hpn
  obtain ⟨t, ht⟩ : ∃ t, Nat.log p n = t + 1 := ⟨Nat.log p n - 1, by omega⟩
  have hpow : p ^ (t + 1) ≤ n := ht ▸ Nat.pow_log_le_self p hn0
  have h2 : p ^ t ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc p ^ t * 2 ≤ p ^ t * p := by gcongr; exact hp.two_le
      _ = p ^ (t + 1) := by ring
      _ ≤ n := hpow
  have := Nat.le_log_of_pow_le hp1 h2
  omega

theorem log_le_sqrt (n p : ℕ) (hp : p.Prime) (hpn : p ≤ n) :
    Nat.log p n ≤ 1 + 2 * Nat.log p (Nat.sqrt n) := by
  have hp1 := hp.one_lt
  have hn0 : n ≠ 0 := by omega
  set s := Nat.sqrt n with hs
  have hlt : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
  by_cases hps : p ≤ s
  · have h1 : s < p ^ (Nat.log p s + 1) := Nat.lt_pow_succ_log_self hp1 s
    have h2 : n < p ^ (2 * Nat.log p s + 2) := by
      calc n < (s + 1) ^ 2 := hlt
        _ ≤ (p ^ (Nat.log p s + 1)) ^ 2 := by gcongr; omega
        _ = p ^ (2 * Nat.log p s + 2) := by ring
    have := Nat.log_lt_of_lt_pow hn0 h2
    omega
  · push Not at hps
    have h2 : n < p ^ 2 := by
      calc n < (s + 1) ^ 2 := hlt
        _ ≤ p ^ 2 := by gcongr; omega
    have := Nat.log_lt_of_lt_pow hn0 h2
    omega

theorem D_le_sixteen_pow (n : ℕ) : D n ≤ 16 ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [D, Nat.lcmUpto]
    have hdvd := D_dvd_primorial_mul n (n / 2) 1 (fun p hp hpn => log_le_half n p hp hpn)
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (primorial_pos n).ne'
      (pow_ne_zero _ (D_ne_zero _)))) hdvd
    have hih : D (n / 2) ≤ 16 ^ (n / 2) := ih (n / 2) (by omega)
    have h16 : (16 : ℕ) ^ (n / 2) ≤ 4 ^ n := by
      calc (16 : ℕ) ^ (n / 2) = 4 ^ (2 * (n / 2)) := by rw [pow_mul]; norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc D n ≤ primorial n * D (n / 2) ^ 1 := hle
      _ ≤ 4 ^ n * 16 ^ (n / 2) := by rw [pow_one]; gcongr; exact primorial_le_four_pow n
      _ ≤ 4 ^ n * 4 ^ n := by gcongr
      _ = 16 ^ n := by rw [← mul_pow]; norm_num

theorem D_le_four_pow_mul (n : ℕ) : D n ≤ 4 ^ n * 256 ^ Nat.sqrt n := by
  have hdvd := D_dvd_primorial_mul n (Nat.sqrt n) 2 (fun p hp hpn => log_le_sqrt n p hp hpn)
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (primorial_pos n).ne'
    (pow_ne_zero _ (D_ne_zero _)))) hdvd
  calc D n ≤ primorial n * D (Nat.sqrt n) ^ 2 := hle
    _ ≤ 4 ^ n * (16 ^ Nat.sqrt n) ^ 2 := by
        gcongr; exacts [primorial_le_four_pow n, D_le_sixteen_pow _]
    _ = 4 ^ n * 256 ^ Nat.sqrt n := by rw [← pow_mul, mul_comm (Nat.sqrt n) 2, pow_mul]; norm_num

theorem sqrt_two_mul_le (k : ℕ) : Nat.sqrt (2 * k) ≤ k / 16 + 9 := by
  have h : Nat.sqrt (2 * k) < k / 16 + 10 := by
    rw [Nat.sqrt_lt']
    have h := Nat.div_add_mod k 16
    have hm := Nat.mod_lt k (show 16 > 0 by norm_num)
    generalize k / 16 = q at *
    generalize k % 16 = r at *
    subst h
    have : 32 * q + 30 < (q + 10) ^ 2 := by
      have h6 : 0 ≤ ((q : ℤ) - 6) ^ 2 := sq_nonneg _
      have : (32 * q + 30 : ℤ) < ((q : ℤ) + 10) ^ 2 := by nlinarith
      exact_mod_cast this
    omega
  omega

theorem D_two_mul_le (k : ℕ) : D (2 * k) ≤ 2 ^ 72 * 32 ^ k := by
  calc D (2 * k) ≤ 4 ^ (2 * k) * 256 ^ Nat.sqrt (2 * k) := D_le_four_pow_mul _
    _ ≤ 4 ^ (2 * k) * 256 ^ (k / 16 + 9) := by gcongr; norm_num; exact sqrt_two_mul_le k
    _ = 16 ^ k * (2 ^ (8 * (k / 16)) * 2 ^ 72) := by
        rw [pow_add, pow_mul, pow_mul]; norm_num
    _ ≤ 16 ^ k * (2 ^ k * 2 ^ 72) := by
        have : 8 * (k / 16) ≤ k := by omega
        gcongr
    _ = 2 ^ 72 * 32 ^ k := by
        rw [show (32 : ℕ) ^ k = 16 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]; ring


end CollatzMCycles.Diophantine
