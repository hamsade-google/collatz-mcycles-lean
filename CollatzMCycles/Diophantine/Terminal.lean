module

public import CollatzMCycles.Diophantine.Measure

/-!
# Diophantine Termination (Milestone M4)

We discharge `CollatzMCycles.Diophantine.terminal` for all `K ≥ K_top` by applying
`measure_bound` at `m = Nat.log 2 K + 74` (`k = 2 * m + 1`, odd).
-/

@[expose] public section
namespace CollatzMCycles.Diophantine

theorem lin_le_two_pow (d : ℕ) : 48 * d + 7911 ≤ 4194304 * 2 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
    have h1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem log_K_ge_90 {K : ℕ} (hK : 2438425051595107335801557824 ≤ K) :
    90 ≤ Nat.log 2 K := by
  apply Nat.le_log_of_pow_le (by norm_num)
  omega

theorem exp_bound_of_ge_Ktop {K : ℕ} (hK : 2438425051595107335801557824 ≤ K) :
    (24 * (2 * (Nat.log 2 K + 74) + 1) + 15) * 2 ^ 68 ≤ K := by
  set b := Nat.log 2 K
  have hb : 90 ≤ b := log_K_ge_90 hK
  have h1 := lin_le_two_pow (b - 90)
  have h2 : 24 * (2 * (b + 74) + 1) + 15 = 48 * (b - 90) + 7911 := by omega
  have h3 : 4194304 * 2 ^ (b - 90) * 2 ^ 68 = 2 ^ b := by
    rw [show (4194304 : ℕ) = 2 ^ 22 by norm_num, ← pow_add, ← pow_add,
      show 22 + (b - 90) + 68 = b by omega]
  calc (24 * (2 * (b + 74) + 1) + 15) * 2 ^ 68
      = (48 * (b - 90) + 7911) * 2 ^ 68 := by rw [h2]
    _ ≤ (4194304 * 2 ^ (b - 90)) * 2 ^ 68 := Nat.mul_le_mul_right _ h1
    _ = 2 ^ b := h3
    _ ≤ K := Nat.pow_log_le_self 2 (by omega)

theorem pow_half_shift (N : ℕ) : (1 / 2 : ℝ) ^ N = 128 * (1 / 2 : ℝ) ^ (N + 7) := by
  rw [pow_add]
  ring

/-- Terminal Diophantine exclusion (Lemma 3.7 Part 1 + Part II of the paper):
for `K ≥ K_top = 2438425051595107335801557824`, the cycle bound
`0 < (K + L) log 2 - K log 3 < 100 · 2^(1 - K / 2^68)` is impossible. -/
theorem terminal (K L : ℕ) (hK : 2438425051595107335801557824 ≤ K)
    (h0 : 0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3)
    (h1 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 <
      100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68)) :
    False := by
  set b := Nat.log 2 K
  set m := b + 74
  set k := 2 * m + 1
  have hK_lt : K < 2 ^ (b + 1) := Nat.lt_pow_succ_log_self (by norm_num) K
  have hK_le : (K : ℝ) ≤ (2 : ℝ) ^ (b + 1) := by exact_mod_cast hK_lt.le
  have hsmall : (K : ℝ) * (2 ^ 72 * (1 / 2 : ℝ) ^ m) ≤ 1 / 2 := by
    calc (K : ℝ) * (2 ^ 72 * (1 / 2 : ℝ) ^ m)
        ≤ (2 : ℝ) ^ (b + 1) * (2 ^ 72 * (1 / 2 : ℝ) ^ ((b + 1) + 72 + 1)) := by
          have hm : m = (b + 1) + 72 + 1 := by omega
          rw [hm]
          exact mul_le_mul_of_nonneg_right hK_le (by positivity)
      _ = ((2 : ℝ) * (1 / 2)) ^ (b + 1) * ((2 : ℝ) * (1 / 2)) ^ 72 * (1 / 2) := by
          rw [pow_add, pow_add, mul_pow, mul_pow]
          ring
      _ = 1 / 2 := by norm_num
  have hexp_nat : ((24 * k + 14 + 1 : ℕ) : ℝ) * 2 ^ 68 ≤ K := by
    exact_mod_cast exp_bound_of_ge_Ktop hK
  have hexp_le : 1 - (K : ℝ) / 2 ^ 68 ≤ -((24 * k + 14 : ℕ) : ℝ) := by
    push_cast at hexp_nat ⊢
    linarith only [hexp_nat]
  have hrpow : (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68) ≤ (1 / 2 : ℝ) ^ (24 * k + 14) := by
    calc (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68)
        ≤ (2 : ℝ) ^ (-((24 * k + 14 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp_le
      _ = ((2 : ℝ) ^ (24 * k + 14))⁻¹ := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
      _ = (1 / 2 : ℝ) ^ (24 * k + 14) := by rw [one_div, inv_pow]
  have hupper : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 < (1 / 2 : ℝ) ^ (24 * k + 7) := by
    have hpow_pos : (0 : ℝ) < (1 / 2 : ℝ) ^ (24 * k + 14) := by positivity
    have h128 : (1 / 2 : ℝ) ^ (24 * k + 7) = 128 * (1 / 2 : ℝ) ^ (24 * k + 14) :=
      pow_half_shift (24 * k + 7)
    calc ((K : ℝ) + L) * Real.log 2 - K * Real.log 3
        < 100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68) := h1
      _ ≤ 100 * (1 / 2 : ℝ) ^ (24 * k + 14) :=
          mul_le_mul_of_nonneg_left hrpow (by norm_num)
      _ < 128 * (1 / 2 : ℝ) ^ (24 * k + 14) :=
          mul_lt_mul_of_pos_right (by norm_num) hpow_pos
      _ = (1 / 2 : ℝ) ^ (24 * k + 7) := h128.symm
  have h1_lt_K4 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 < (K : ℝ) / 4 := by
    have hpow_le_one : (1 / 2 : ℝ) ^ (24 * k + 7) ≤ 1 :=
      pow_le_one₀ (by positivity) (by norm_num)
    have hK_real : (1 : ℝ) < (K : ℝ) / 4 := by
      have h4 : (4 : ℝ) < K := by exact_mod_cast (by omega : 4 < K)
      linarith only [h4]
    exact (hupper.trans_le hpow_le_one).trans hK_real
  have hlower := measure_bound K L m h0 h1_lt_K4 hsmall
  exact not_le_of_gt hupper hlower

end CollatzMCycles.Diophantine
