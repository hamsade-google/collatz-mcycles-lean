module

public import Mathlib
public import CollatzMCycles.LogBounds
public import CollatzMCycles.Blocks

/-!
# CycleProduct — Lemma 3.1 (cycle product and per-minimum reciprocal inequality)

For an `m`-cycle with blocks `j : Fin m` (cyclic `j + 1`), local minima `nmin j`,
`nmin j + 1 = 2^(k j) * a j`, and peak identity `2^(l j) * nmin (j+1) = 3^(k j) * a j - 1`,

  `0 < (K + L) log 2 − K log 3 < ∑ j, 1 / nmin j`,   `K = ∑ k j`, `L = ∑ l j`.

Proof: per block, `3^k a − 1 = (3/2)^k · nmin · (1 + ε)` with `ε = (1 − (2/3)^k)/nmin ∈ (0, 1/nmin)`;
take logs, sum over the cycle (the `log nmin` terms telescope cyclically), and use
`0 < log (1+ε) < ε`.
-/

@[expose] public section
namespace CollatzMCycles
namespace CycleProduct

open Real Finset

/-- The per-block relative excess `ε = (1 − (2/3)^k) / nmin`. -/
noncomputable def eps (nm k : ℕ) : ℝ := (1 - (2 / 3 : ℝ) ^ k) / nm

theorem eps_pos {nm k : ℕ} (hpos : 0 < nm) (hk : 1 ≤ k) : 0 < eps nm k := by
  unfold eps
  have : (2 / 3 : ℝ) ^ k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have : (0 : ℝ) < nm := by exact_mod_cast hpos
  apply div_pos <;> linarith

theorem eps_lt {nm k : ℕ} (hpos : 0 < nm) : eps nm k < 1 / nm := by
  unfold eps
  have : (0 : ℝ) < (2 / 3 : ℝ) ^ k := by positivity
  have : (0 : ℝ) < nm := by exact_mod_cast hpos
  apply div_lt_div_of_pos_right _ this
  linarith

/-- Per-block multiplicative identity in `ℝ`. -/
theorem block_identity {nm k a : ℕ} (hpos : 0 < nm) (hsplit : nm + 1 = 2 ^ k * a) :
    (3 : ℝ) ^ k * a - 1 = (3 / 2 : ℝ) ^ k * nm * (1 + eps nm k) := by
  have hnm : (nm : ℝ) ≠ 0 := by positivity
  have h : (nm : ℝ) + 1 = 2 ^ k * a := by exact_mod_cast hsplit
  have h1 : (3 / 2 : ℝ) ^ k * (2 / 3 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
  have h2 : (3 / 2 : ℝ) ^ k * 2 ^ k = 3 ^ k := by rw [← mul_pow]; norm_num
  symm
  calc (3 / 2 : ℝ) ^ k * nm * (1 + eps nm k)
      = (3 / 2 : ℝ) ^ k * (nm + 1) - (3 / 2 : ℝ) ^ k * (2 / 3 : ℝ) ^ k := by
        unfold eps; field_simp; ring
    _ = (3 / 2 : ℝ) ^ k * (2 ^ k * a) - 1 := by rw [h, h1]
    _ = 3 ^ k * a - 1 := by rw [← mul_assoc, h2]

/-- Per-block log identity: `(k + l) log 2 − k log 3 = log nm − log nm' + log (1 + ε)`
where `nm' = nmin (j+1)` satisfies `2^l * nm' = 3^k a − 1`. -/
theorem block_log_identity {nm nm' k l a : ℕ} (hpos : 0 < nm) (hpos' : 0 < nm')
    (hsplit : nm + 1 = 2 ^ k * a) (hpeak : 2 ^ l * nm' + 1 = 3 ^ k * a) :
    ((k : ℝ) + l) * Real.log 2 - k * Real.log 3
      = Real.log nm - Real.log nm' + Real.log (1 + eps nm k) := by
  have hR : (2 : ℝ) ^ l * nm' = (3 / 2 : ℝ) ^ k * nm * (1 + eps nm k) := by
    rw [← block_identity hpos hsplit]
    have : ((2 ^ l * nm' + 1 : ℕ) : ℝ) = ((3 ^ k * a : ℕ) : ℝ) := by rw [hpeak]
    push_cast at this
    linarith
  have hnm : (0 : ℝ) < nm := by exact_mod_cast hpos
  have hnm' : (0 : ℝ) < nm' := by exact_mod_cast hpos'
  have heps : (0 : ℝ) < 1 + eps nm k := by
    have : 0 ≤ eps nm k := by unfold eps; apply div_nonneg _ hnm.le; have := pow_le_one₀ (n := k) (show (0:ℝ) ≤ 2/3 by norm_num) (by norm_num); linarith
    linarith
  have hlog := congrArg Real.log hR
  rw [Real.log_mul (by positivity) hnm'.ne', Real.log_mul (by positivity) heps.ne',
    Real.log_mul (by positivity) hnm.ne', Real.log_pow, Real.log_pow,
    Real.log_div (by norm_num) (by norm_num)] at hlog
  linarith

variable {m : ℕ} [NeZero m]

/-- **Lemma 3.1.** -/
theorem cycle_product (nmin k l a : Fin m → ℕ)
    (hk : ∀ j, 1 ≤ k j)
    (hpos : ∀ j, 0 < nmin j)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j)
    (hpeak : ∀ j, 2 ^ l j * nmin (j + 1) + 1 = 3 ^ k j * a j) :
    0 < (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) * Real.log 2
          - ((∑ j, k j : ℕ) : ℝ) * Real.log 3 ∧
    (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) * Real.log 2
          - ((∑ j, k j : ℕ) : ℝ) * Real.log 3 < ∑ j, 1 / (nmin j : ℝ) := by
  -- Λ = ∑ log (1 + ε_j)
  have hΛ : (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) * Real.log 2
          - ((∑ j, k j : ℕ) : ℝ) * Real.log 3
        = ∑ j, Real.log (1 + eps (nmin j) (k j)) := by
    have hcyc : ∑ j : Fin m, Real.log (nmin (j + 1)) = ∑ j : Fin m, Real.log (nmin j) :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin m)) (fun j => Real.log (nmin j))
    have hsum : ∑ j, (((k j : ℝ) + l j) * Real.log 2 - k j * Real.log 3)
        = ∑ j, (Real.log (nmin j) - Real.log (nmin (j + 1)) + Real.log (1 + eps (nmin j) (k j))) :=
      Finset.sum_congr rfl (fun j _ =>
        block_log_identity (hpos j) (hpos (j + 1)) (hsplit j) (hpeak j))
    have hsum' : ∑ j, (((k j : ℝ) + l j) * Real.log 2 - k j * Real.log 3)
        = ∑ j, Real.log (1 + eps (nmin j) (k j)) := by
      rw [hsum]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcyc, sub_self, zero_add]
    rw [← hsum']
    push_cast
    simp only [Finset.sum_sub_distrib, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hΛ]
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := Finset.univ_nonempty
  constructor
  · apply Finset.sum_pos _ hne
    intro j _
    apply Real.log_pos
    linarith [eps_pos (hpos j) (hk j)]
  · apply Finset.sum_lt_sum_of_nonempty hne
    intro j _
    have h1 := eps_pos (hpos j) (hk j)
    have h2 := eps_lt (nm := nmin j) (k := k j) (hpos j)
    have := Real.log_lt_sub_one_of_pos (x := 1 + eps (nmin j) (k j)) (by linarith) (by linarith)
    linarith

/-- Lemma 3.1 in the `δ`-form: `0 < (K+L) − K δ < (∑ 1/nmin j) / log 2`. -/
theorem cycle_product_delta (nmin k l a : Fin m → ℕ)
    (hk : ∀ j, 1 ≤ k j)
    (hpos : ∀ j, 0 < nmin j)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j)
    (hpeak : ∀ j, 2 ^ l j * nmin (j + 1) + 1 = 3 ^ k j * a j) :
    0 < (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) - ((∑ j, k j : ℕ) : ℝ) * LogBounds.δ ∧
    (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) - ((∑ j, k j : ℕ) : ℝ) * LogBounds.δ
        < (∑ j, 1 / (nmin j : ℝ)) / Real.log 2 := by
  obtain ⟨h1, h2⟩ := cycle_product nmin k l a hk hpos hsplit hpeak
  have hl2 := LogBounds.log_two_pos
  rw [LogBounds.δ_def]
  have key : (((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) - ((∑ j, k j : ℕ) : ℝ) * (Real.log 3 / Real.log 2)
      = ((((∑ j, k j : ℕ) : ℝ) + ((∑ j, l j : ℕ) : ℝ)) * Real.log 2
          - ((∑ j, k j : ℕ) : ℝ) * Real.log 3) / Real.log 2 := by
    field_simp
  rw [key]
  constructor
  · exact div_pos h1 hl2
  · exact div_lt_div_of_pos_right h2 hl2

/-! ### Wrappers on `MCycleData` -/

/-- Peak identity in additive form: `2^(l j) * nmin (j+1) + 1 = 3^(k j) * a j`. -/
theorem _root_.CollatzMCycles.MCycleData.two_pow_l_mul_nmin_succ_add_one
    (D : MCycleData m) (j : Fin m) :
    2 ^ D.l j * D.nmin (j + 1) + 1 = 3 ^ D.k j * D.a j := by
  have h1 := D.two_pow_l_mul_nmin_succ j
  have h2 := D.peak_add_one j
  omega

/-- **Lemma 3.1** for an `m`-cycle: `0 < (K+L) log 2 − K log 3 < ∑ j, 1/nmin j`. -/
theorem _root_.CollatzMCycles.MCycleData.cycle_product (D : MCycleData m) :
    0 < ((D.K : ℝ) + D.L) * Real.log 2 - D.K * Real.log 3 ∧
    ((D.K : ℝ) + D.L) * Real.log 2 - D.K * Real.log 3 < ∑ j, 1 / (D.nmin j : ℝ) :=
  CycleProduct.cycle_product D.nmin D.k D.l D.a D.k_pos D.nmin_pos D.nmin_add_one
    D.two_pow_l_mul_nmin_succ_add_one

/-- **Lemma 3.1**, `δ`-form: `0 < (K+L) − K δ < (∑ j, 1/nmin j) / log 2`. -/
theorem _root_.CollatzMCycles.MCycleData.cycle_product_delta (D : MCycleData m) :
    0 < ((D.K : ℝ) + D.L) - D.K * LogBounds.δ ∧
    ((D.K : ℝ) + D.L) - D.K * LogBounds.δ < (∑ j, 1 / (D.nmin j : ℝ)) / Real.log 2 :=
  CycleProduct.cycle_product_delta D.nmin D.k D.l D.a D.k_pos D.nmin_pos D.nmin_add_one
    D.two_pow_l_mul_nmin_succ_add_one

end CycleProduct
end CollatzMCycles
