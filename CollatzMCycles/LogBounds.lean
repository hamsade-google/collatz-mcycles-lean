module

public import Mathlib

/-!
# LogBounds — exact dyadic enclosures of `log 2`, `log 3` and `δ = log₂ 3`

Paper: Part I, Lemma 3.6(1) (Mercator enclosures).

We use Mathlib's
`Real.hasSum_log_one_add_inv : 0 < a →
  HasSum (fun k => 2 * (1 / (2k+1)) * (1/(2a+1))^(2k+1)) (log (1 + a⁻¹))`
at `a = 1` (giving `log 2`, `x = 1/3`) and `a = 2` (giving `log (3/2)`, `x = 1/5`),
truncated after `N = 65` terms with the geometric tail bound
`2 x^(2N+1) / ((2N+1)(1 - x²))`, exactly as `generate_exact_bounds.py::enclose_mercator`.
The dyadic numerals below are byte-identical to `exact_bounds_meta.json["enclosures"]`.
-/

@[expose] public section
namespace CollatzMCycles
namespace LogBounds

open Real Finset

/-- `δ := log₂ 3`. Definitionally `Real.log 3 / Real.log 2`. -/
noncomputable def δ : ℝ := Real.logb 2 3

theorem δ_def : δ = Real.log 3 / Real.log 2 := rfl

/-! ### The exact dyadic numerals (from `exact_bounds_meta.json["enclosures"]`). -/

def ln2_lo : ℚ :=
  583975344386936258977467544946630882142858664240265691522820761741 /
  842498333348457493583344221469363458551160763204392890034487820288
def ln2_hi : ℚ :=
  583975344386936258977467544946630882142858664240265691522820761787 /
  842498333348457493583344221469363458551160763204392890034487820288
def ln3_lo : ℚ :=
  1851158044398033779581578997151565645157910784539172013517317963411 /
  1684996666696914987166688442938726917102321526408785780068975640576
def ln3_hi : ℚ :=
  1851158044398033779581578997151565645157910784539172013517317963503 /
  1684996666696914987166688442938726917102321526408785780068975640576
def delta_lo : ℚ :=
  2670656530554754882264608135970714174812783383528749517525579880575 /
  1684996666696914987166688442938726917102321526408785780068975640576
def delta_hi : ℚ :=
  333832066319344360283076016996339271851597922941093689690697485115 /
  210624583337114373395836055367340864637790190801098222508621955072

/-! ### Generic Mercator truncation bounds -/

/-- The `k`-th Mercator term `2 x^(2k+1)/(2k+1)` (Mathlib's normal form). -/
noncomputable def mercTerm (x : ℝ) (k : ℕ) : ℝ := 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1)

/-- Lower bound: a partial sum of nonnegative terms is below the sum. -/
theorem partial_le_of_hasSum {x S : ℝ} (hx0 : 0 ≤ x)
    (hS : HasSum (mercTerm x) S) (N : ℕ) :
    ∑ k ∈ range N, mercTerm x k ≤ S :=
  sum_le_hasSum (range N) (fun k _ => by unfold mercTerm; positivity) hS

/-- Upper bound: geometric tail `2 x^(2N+1) / ((2N+1)(1-x²))`. -/
theorem hasSum_le_partial_add_tail {x S : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hS : HasSum (mercTerm x) S) (N : ℕ) :
    S ≤ ∑ k ∈ range N, mercTerm x k
        + 2 * (1 / (2 * (N : ℝ) + 1)) * x ^ (2 * N + 1) * (1 - x ^ 2)⁻¹ := by
  have htail : HasSum (fun k => mercTerm x (k + N)) (S - ∑ k ∈ range N, mercTerm x k) :=
    (hasSum_nat_add_iff' N).mpr hS
  have hx2 : x ^ 2 < 1 := by nlinarith
  set c : ℝ := 2 * (1 / (2 * (N : ℝ) + 1)) * x ^ (2 * N + 1) with hc
  have hgeom : HasSum (fun k : ℕ => c * (x ^ 2) ^ k) (c * (1 - x ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hx2).mul_left c
  have hle : ∀ k, mercTerm x (k + N) ≤ c * (x ^ 2) ^ k := by
    intro k
    have h1 : (1 : ℝ) / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ 1 / (2 * (N : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hpow : (0 : ℝ) ≤ x ^ (2 * N + 1) * (x ^ 2) ^ k := by positivity
    calc mercTerm x (k + N)
        = 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (x ^ (2 * N + 1) * (x ^ 2) ^ k) := by
          unfold mercTerm; ring
      _ ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (x ^ (2 * N + 1) * (x ^ 2) ^ k) := by
          apply mul_le_mul_of_nonneg_right _ hpow
          linarith
      _ = c * (x ^ 2) ^ k := by rw [hc]; ring
  have := hasSum_le hle htail hgeom
  linarith

/-! ### Instances: `log 2` via `x = 1/3`, `log (3/2)` via `x = 1/5`. -/

theorem hasSum_log_two : HasSum (mercTerm (1 / 3)) (Real.log 2) := by
  have h := Real.hasSum_log_one_add_inv (a := (1 : ℝ)) one_pos
  convert h using 2 <;> norm_num [mercTerm]

theorem hasSum_log_three_halves : HasSum (mercTerm (1 / 5)) (Real.log 3 - Real.log 2) := by
  have h := Real.hasSum_log_one_add_inv (a := (2 : ℝ)) two_pos
  have h32 : Real.log 3 - Real.log 2 = Real.log (1 + (2 : ℝ)⁻¹) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [h32]
  convert h using 2; norm_num [mercTerm]

/-! ### The enclosures -/

theorem ln2_lo_le_log_two : (ln2_lo : ℝ) ≤ Real.log 2 := by
  refine le_trans ?_ (partial_le_of_hasSum (by norm_num) hasSum_log_two 65)
  simp only [mercTerm, Finset.sum_range_succ, Finset.sum_range_zero, ln2_lo]
  norm_num

theorem log_two_le_ln2_hi : Real.log 2 ≤ (ln2_hi : ℝ) := by
  refine le_trans (hasSum_le_partial_add_tail (by norm_num) (by norm_num) hasSum_log_two 65) ?_
  simp only [mercTerm, Finset.sum_range_succ, Finset.sum_range_zero, ln2_hi]
  norm_num

theorem ln3_lo_le_log_three : (ln3_lo : ℝ) ≤ Real.log 3 := by
  have h2 := partial_le_of_hasSum (by norm_num) hasSum_log_two 65
  have h3 := partial_le_of_hasSum (by norm_num) hasSum_log_three_halves 65
  have : (ln3_lo : ℝ) ≤ ∑ k ∈ range 65, mercTerm (1 / 3) k + ∑ k ∈ range 65, mercTerm (1 / 5) k := by
    simp only [mercTerm, Finset.sum_range_succ, Finset.sum_range_zero, ln3_lo]
    norm_num
  linarith

theorem log_three_le_ln3_hi : Real.log 3 ≤ (ln3_hi : ℝ) := by
  have h2 := hasSum_le_partial_add_tail (by norm_num) (by norm_num) hasSum_log_two 65
  have h3 := hasSum_le_partial_add_tail (by norm_num) (by norm_num) hasSum_log_three_halves 65
  have : ∑ k ∈ range 65, mercTerm (1 / 3) k
        + 2 * (1 / (2 * ((65 : ℕ) : ℝ) + 1)) * (1 / 3 : ℝ) ^ (2 * 65 + 1) * (1 - (1 / 3 : ℝ) ^ 2)⁻¹
      + (∑ k ∈ range 65, mercTerm (1 / 5) k
        + 2 * (1 / (2 * ((65 : ℕ) : ℝ) + 1)) * (1 / 5 : ℝ) ^ (2 * 65 + 1) * (1 - (1 / 5 : ℝ) ^ 2)⁻¹)
      ≤ (ln3_hi : ℝ) := by
    simp only [mercTerm, Finset.sum_range_succ, Finset.sum_range_zero, ln3_hi]
    norm_num
  linarith

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
theorem log_three_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)

theorem delta_lo_le_δ : (delta_lo : ℝ) ≤ δ := by
  rw [δ_def, le_div_iff₀ log_two_pos]
  have hq : (delta_lo : ℝ) * (ln2_hi : ℝ) ≤ (ln3_lo : ℝ) := by
    rw [← Rat.cast_mul, Rat.cast_le]; unfold delta_lo ln2_hi ln3_lo; norm_num
  have h0 : (0 : ℝ) ≤ (delta_lo : ℝ) := by unfold delta_lo; positivity
  calc (delta_lo : ℝ) * Real.log 2 ≤ (delta_lo : ℝ) * (ln2_hi : ℝ) :=
        mul_le_mul_of_nonneg_left log_two_le_ln2_hi h0
    _ ≤ (ln3_lo : ℝ) := hq
    _ ≤ Real.log 3 := ln3_lo_le_log_three

theorem δ_le_delta_hi : δ ≤ (delta_hi : ℝ) := by
  rw [δ_def, div_le_iff₀ log_two_pos]
  have hq : (ln3_hi : ℝ) ≤ (delta_hi : ℝ) * (ln2_lo : ℝ) := by
    rw [← Rat.cast_mul, Rat.cast_le]; unfold delta_hi ln2_lo ln3_hi; norm_num
  have h0 : (0 : ℝ) ≤ (delta_hi : ℝ) := by unfold delta_hi; positivity
  calc Real.log 3 ≤ (ln3_hi : ℝ) := log_three_le_ln3_hi
    _ ≤ (delta_hi : ℝ) * (ln2_lo : ℝ) := hq
    _ ≤ (delta_hi : ℝ) * Real.log 2 := mul_le_mul_of_nonneg_left ln2_lo_le_log_two h0

/-- Convenience: `1 < δ` and `δ < 2`. -/
theorem one_lt_δ : 1 < δ := by
  have := delta_lo_le_δ
  have h : (1 : ℝ) < (delta_lo : ℝ) := by
    rw [show (1 : ℝ) = ((1 : ℚ) : ℝ) by norm_num, Rat.cast_lt]; unfold delta_lo; norm_num
  linarith

theorem δ_lt_two : δ < 2 := by
  have := δ_le_delta_hi
  have h : (delta_hi : ℝ) < (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℚ) : ℝ) by norm_num, Rat.cast_lt]; unfold delta_hi; norm_num
  linarith

end LogBounds
end CollatzMCycles
