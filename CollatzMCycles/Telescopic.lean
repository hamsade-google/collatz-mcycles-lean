module

public import Mathlib
public import CollatzMCycles.LogBounds
public import CollatzMCycles.CycleProduct

/-!
# Telescopic — Lemma 3.4, shift-free version (telescopic affine-halving growth)

With `x j := log₂ (nmin j + 1)` and `δ = log₂ 3`:
* `k j ≤ x j`                                   (since `nmin j + 1 = 2^(k j) a j ≥ 2^(k j)`)
* `x (j+1) ≤ x j + (δ − 1) k j`                 (since `nmin (j+1) + 1 ≤ 3^(k j) a j = (3/2)^(k j) (nmin j + 1)`)
* for all `t`, `r`:  `∑_{u<t} k (r+u) ≤ (∑_{u<t} δ^u) · x r`   (induction on `t`)
* closed form (`1 ≤ t`): `x r ≥ (δ − 1) (∑_{u<t} k (r+u)) / (δ^t − 1)`.

Indices are cyclic in `Fin m` (`[NeZero m]`); `Fin.ofNat m u` is the `Nat` cast (`u % m`), so
`r + Fin.ofNat m u` with `r = Fin.ofNat m (m - t)` is Raney's `Fin.ofNat m (m - t + u)`
(see `ofNat_add_ofNat`).
-/

@[expose] public section
namespace CollatzMCycles
namespace Telescopic

open Real Finset LogBounds

variable {m : ℕ} [NeZero m]

theorem ofNat_succ (u : ℕ) : Fin.ofNat m (u + 1) = Fin.ofNat m u + 1 := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

theorem ofNat_add_ofNat (u v : ℕ) : Fin.ofNat m u + Fin.ofNat m v = Fin.ofNat m (u + v) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_mod]

/-- `x j := log₂ (nmin j + 1)`. -/
noncomputable def x (nmin : Fin m → ℕ) (j : Fin m) : ℝ := Real.logb 2 ((nmin j : ℝ) + 1)

omit [NeZero m] in
theorem k_le_x (nmin k a : Fin m → ℕ)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j) (j : Fin m) :
    (k j : ℝ) ≤ x nmin j := by
  unfold x
  have ha : 1 ≤ a j := by
    rcases Nat.eq_zero_or_pos (a j) with h | h
    · have := hsplit j; rw [h] at this; omega
    · exact h
  have h2 : (2 : ℝ) ^ k j ≤ (nmin j : ℝ) + 1 := by
    have : 2 ^ k j ≤ nmin j + 1 := by rw [hsplit j]; exact Nat.le_mul_of_pos_right _ ha
    exact_mod_cast this
  calc (k j : ℝ) = Real.logb 2 ((2 : ℝ) ^ k j) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
    _ ≤ Real.logb 2 ((nmin j : ℝ) + 1) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) h2

theorem one_step (nmin k l a : Fin m → ℕ)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j)
    (hpeak : ∀ j, 2 ^ l j * nmin (j + 1) + 1 = 3 ^ k j * a j) (j : Fin m) :
    x nmin (j + 1) ≤ x nmin j + (δ - 1) * k j := by
  unfold x
  -- nmin (j+1) + 1 ≤ 3^k a  (as 2^l ≥ 2 and 3^k a = 2^l nmin' + 1 ≥ nmin' + 1)
  have hN : nmin (j + 1) + 1 ≤ 3 ^ k j * a j := by
    have h2l : 1 ≤ 2 ^ l j := Nat.one_le_two_pow
    have := hpeak j
    nlinarith [Nat.le_mul_of_pos_left (nmin (j + 1)) h2l]
  have hNR : (nmin (j + 1) : ℝ) + 1 ≤ (3 / 2 : ℝ) ^ k j * ((nmin j : ℝ) + 1) := by
    have h3 : ((nmin (j + 1) + 1 : ℕ) : ℝ) ≤ ((3 ^ k j * a j : ℕ) : ℝ) := by exact_mod_cast hN
    have hs : ((nmin j : ℝ) + 1) = 2 ^ k j * a j := by exact_mod_cast hsplit j
    push_cast at h3
    rw [hs, ← mul_assoc, ← mul_pow]
    norm_num
    exact h3
  have hpos : (0 : ℝ) < (3 / 2 : ℝ) ^ k j * ((nmin j : ℝ) + 1) := by positivity
  calc Real.logb 2 ((nmin (j + 1) : ℝ) + 1)
      ≤ Real.logb 2 ((3 / 2 : ℝ) ^ k j * ((nmin j : ℝ) + 1)) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) hNR
    _ = (k j : ℝ) * Real.logb 2 (3 / 2) + Real.logb 2 ((nmin j : ℝ) + 1) := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow]
    _ = Real.logb 2 ((nmin j : ℝ) + 1) + (δ - 1) * k j := by
        rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_self_eq_one (by norm_num)]
        unfold δ; ring

/-- **Lemma 3.4 (shift-free, summed form).** -/
theorem telescopic (nmin k l a : Fin m → ℕ)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j)
    (hpeak : ∀ j, 2 ^ l j * nmin (j + 1) + 1 = 3 ^ k j * a j)
    (t : ℕ) (r : Fin m) :
    (∑ u ∈ range t, (k (r + Fin.ofNat m u) : ℝ)) ≤ (∑ u ∈ range t, δ ^ u) * x nmin r := by
  induction t generalizing r with
  | zero => simp
  | succ t ih =>
    -- ∑_{u<t+1} k (r+u) = k r + ∑_{u<t} k ((r+1)+u)
    have hsplit_sum : (∑ u ∈ range (t + 1), (k (r + Fin.ofNat m u) : ℝ))
        = (k r : ℝ) + ∑ u ∈ range t, (k ((r + 1) + Fin.ofNat m u) : ℝ) := by
      rw [Finset.sum_range_succ', Fin.ofNat_zero, add_zero, add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [ofNat_succ]
      congr 2
      abel
    have hgeom : (∑ u ∈ range (t + 1), δ ^ u) = 1 + δ * ∑ u ∈ range t, δ ^ u := by
      rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, add_comm]
      congr 1
      refine Finset.sum_congr rfl (fun u _ => ?_)
      ring
    have hG : 0 ≤ ∑ u ∈ range t, δ ^ u :=
      Finset.sum_nonneg (fun u _ => pow_nonneg (by linarith [one_lt_δ]) u)
    have hδ := one_lt_δ
    have hkx := k_le_x nmin k a hsplit r
    have hstep := one_step nmin k l a hsplit hpeak r
    have hih := ih (r + 1)
    -- geometric identity: 1 + (δ-1) G_t ≤ δ^t  is not needed; we use G_{t+1} = 1 + δ G_t directly:
    -- k r + G_t x(r+1) ≤ k r + G_t (x r + (δ-1) k r) = k r (1 + (δ-1) G_t) + G_t x r
    -- and k r (1 + (δ-1) G_t) ≤ x r (1 + (δ-1) G_t) since 1 + (δ-1) G_t ≥ 0, so ≤ (1 + δ G_t) x r.
    rw [hsplit_sum, hgeom]
    have hc : 0 ≤ 1 + (δ - 1) * ∑ u ∈ range t, δ ^ u := by
      have : 0 ≤ (δ - 1) * ∑ u ∈ range t, δ ^ u := mul_nonneg (by linarith) hG
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hstep hG, mul_le_mul_of_nonneg_left hkx hc]

/-- Geometric sum in closed form. -/
theorem geom_sum_δ (t : ℕ) : (∑ u ∈ range t, δ ^ u) = (δ ^ t - 1) / (δ - 1) :=
  geom_sum_eq (ne_of_gt one_lt_δ) t

theorem δ_pow_sub_one_pos {t : ℕ} (ht : 1 ≤ t) : 0 < δ ^ t - 1 := by
  have := one_lt_pow₀ one_lt_δ (by omega : t ≠ 0)
  linarith

/-- **Lemma 3.4 (shift-free, closed form).** `x r ≥ (δ − 1) (∑_{u<t} k (r+u)) / (δ^t − 1)`. -/
theorem closed_form (nmin k l a : Fin m → ℕ)
    (hsplit : ∀ j, nmin j + 1 = 2 ^ k j * a j)
    (hpeak : ∀ j, 2 ^ l j * nmin (j + 1) + 1 = 3 ^ k j * a j)
    {t : ℕ} (ht : 1 ≤ t) (r : Fin m) :
    (δ - 1) * (∑ u ∈ range t, (k (r + Fin.ofNat m u) : ℝ)) / (δ ^ t - 1) ≤ x nmin r := by
  have h := telescopic nmin k l a hsplit hpeak t r
  rw [geom_sum_δ] at h
  have hδ : 0 < δ - 1 := by linarith [one_lt_δ]
  have hp := δ_pow_sub_one_pos ht
  rw [div_le_iff₀ hp]
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ] at h
  linarith

/-! ### Wrappers on `MCycleData` -/

/-- `x j = log₂ (nmin j + 1)` for an `m`-cycle. -/
noncomputable def _root_.CollatzMCycles.MCycleData.x2 (D : MCycleData m) (j : Fin m) : ℝ :=
  Real.logb 2 ((D.nmin j : ℝ) + 1)

theorem _root_.CollatzMCycles.MCycleData.x2_eq (D : MCycleData m) : D.x2 = x D.nmin := rfl

theorem _root_.CollatzMCycles.MCycleData.k_le_x2 (D : MCycleData m) (j : Fin m) :
    (D.k j : ℝ) ≤ D.x2 j :=
  Telescopic.k_le_x D.nmin D.k D.a D.nmin_add_one j

/-- Lemma 3.4, one step: `x (j+1) ≤ x j + (δ − 1) k j`. -/
theorem _root_.CollatzMCycles.MCycleData.x2_succ_le (D : MCycleData m) (j : Fin m) :
    D.x2 (j + 1) ≤ D.x2 j + (δ - 1) * D.k j :=
  Telescopic.one_step D.nmin D.k D.l D.a D.nmin_add_one D.two_pow_l_mul_nmin_succ_add_one j

/-- **Lemma 3.4 (shift-free, summed form)** for an `m`-cycle. -/
theorem _root_.CollatzMCycles.MCycleData.telescopic (D : MCycleData m) (t : ℕ) (r : Fin m) :
    (∑ u ∈ range t, (D.k (r + Fin.ofNat m u) : ℝ)) ≤ (∑ u ∈ range t, δ ^ u) * D.x2 r :=
  Telescopic.telescopic D.nmin D.k D.l D.a D.nmin_add_one D.two_pow_l_mul_nmin_succ_add_one t r

/-- **Lemma 3.4 (shift-free, closed form)** for an `m`-cycle:
`log₂ (nmin r + 1) ≥ (δ − 1) (∑_{u<t} k (r+u)) / (δ^t − 1)`. -/
theorem _root_.CollatzMCycles.MCycleData.closed_form (D : MCycleData m) {t : ℕ} (ht : 1 ≤ t)
    (r : Fin m) :
    (δ - 1) * (∑ u ∈ range t, (D.k (r + Fin.ofNat m u) : ℝ)) / (δ ^ t - 1)
      ≤ Real.logb 2 ((D.nmin r : ℝ) + 1) :=
  Telescopic.closed_form D.nmin D.k D.l D.a D.nmin_add_one D.two_pow_l_mul_nmin_succ_add_one ht r

end Telescopic
end CollatzMCycles
