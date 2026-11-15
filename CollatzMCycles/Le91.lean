module

public import CollatzMCycles.Orbit
public import CollatzMCycles.Blocks
public import CollatzMCycles.Raney
public import CollatzMCycles.CycleProduct
public import CollatzMCycles.Telescopic
public import CollatzMCycles.Witnesses
public import CollatzMCycles.WitnessData
public import CollatzMCycles.Diophantine.Terminal

/-!
# `m ≤ 91` in the Lean kernel alone (Palomar proof chain)

No non-trivial Collatz `m`-cycle with `m ≤ 91`, assuming only Bařina's `2^71` verification as the
explicit hypothesis `hB`. Uses only kernel reduction (`decide +kernel`) and the Mathlib proof of
`Diophantine.terminal`; imports nothing from `Cascade` and no unproved statement.
-/

@[expose] public section
namespace CollatzMCycles

open Finset
open LogBounds (δ)

/-- Statement of `Diophantine.terminal` (owned by `dioph`): for `K ≥ Ktop` the linear form
`Λ = (K+L) log 2 − K log 3` cannot satisfy `0 < Λ < 100 · 2^(1 − K/2^68)`. -/
def Terminal : Prop :=
  ∀ K L : ℕ, Ktop ≤ K →
    0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 →
    ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 < 100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68) → False

/-- `Fin.ofNat m ↑j = j`. -/
theorem ofNat_val {m : ℕ} [NeZero m] (j : Fin m) : Fin.ofNat m (j : ℕ) = j :=
  Fin.ofNat_val_eq_self j

/-- Rotation-invariance of the full-cycle sum: `∑_{u<m} k (j + u) = ∑ k`. -/
theorem sum_range_rotate {m : ℕ} [NeZero m] (k : Fin m → ℕ) (j : Fin m) :
    ∑ u ∈ range m, k (j + Fin.ofNat m u) = ∑ i, k i := by
  rw [← Fin.sum_univ_eq_sum_range (fun u => k (j + Fin.ofNat m u)) m]
  simp only [ofNat_val]
  exact Equiv.sum_comp (Equiv.addLeft j) k

/--
**Core contradiction.** A Raney-rotated `MCycleData m` with `m ≤ 91` is impossible, given the
terminal Diophantine statement.
-/
theorem mcycle_false_of_terminal (hT : Terminal) {m : ℕ} [NeZero m] (hm91 : m ≤ 91)
    (D : MCycleData m)
    (hraney : ∀ t : ℕ, 1 ≤ t → t ≤ m →
      t * D.K ≤ m * ∑ u ∈ range t, D.k (Fin.ofNat m (m - t + u))) : False := by
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (NeZero.ne m)
  -- Lemma 3.1 (log form and δ form)
  obtain ⟨g0, g1⟩ := D.cycle_product
  obtain ⟨h0, h1⟩ := D.cycle_product_delta
  have h0' : 0 < ((D.K + D.L : ℕ) : ℝ) - D.K * δ := by push_cast; exact h0
  have h1' : ((D.K + D.L : ℕ) : ℝ) - D.K * δ < (∑ j, 1 / (D.nmin j : ℝ)) / Real.log 2 := by
    push_cast; exact h1
  -- K ≥ 1
  have hK1 : 1 ≤ D.K := by
    have : D.k ⟨0, hm⟩ ≤ D.K :=
      single_le_sum (f := D.k) (fun j _ => Nat.zero_le _) (mem_univ _)
    have := D.k_pos ⟨0, hm⟩
    omega
  -- suffix sums `S j = ∑_{u < m - j} k (j + u)`
  let S : Fin m → ℕ := fun j => ∑ u ∈ range (m - j), D.k (j + Fin.ofNat m u)
  have hS : ∀ j : Fin m, (m - j) * D.K ≤ m * S j := by
    intro j
    have h := hraney (m - j) (by omega) (by omega)
    have hj : m - (m - j) = j := by omega
    simp only [hj, ← Telescopic.ofNat_add_ofNat, ofNat_val] at h
    exact h
  -- Lemma 3.4 at `r = j`, `t = m − j`
  have htel : ∀ j : Fin m,
      (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((D.nmin j : ℝ) + 1) := by
    intro j
    have h := D.closed_form (t := m - j) (by omega) j
    simp only [S]
    push_cast
    exact h
  -- the kernel-checked bootstrap: K ≥ Ktop
  have hKtop : Ktop ≤ D.K :=
    chain_bound hm (WitnessData.chain m) (WitnessData.chains_ok m (by omega) hm) D.K D.L hK1
      D.nmin S D.nmin_gt hS htel h0' h1'
  -- Lemma 3.4 over the full cycle: every nmin_j + 1 ≥ 2^((δ−1)K/(δ^m−1))
  have hfull : ∀ j, (δ - 1) * D.K / (δ ^ m - 1) ≤ Real.logb 2 ((D.nmin j : ℝ) + 1) := by
    intro j
    have h := D.closed_form (t := m) hm j
    have hrot : (∑ u ∈ range m, (D.k (j + Fin.ofNat m u) : ℝ)) = D.K := by
      exact_mod_cast sum_range_rotate D.k j
    rwa [hrot] at h
  have hsum := terminal_sum_bound hm (by omega) D.K hKtop D.nmin D.nmin_pos hfull
  exact hT D.K D.L hKtop g0 (lt_of_lt_of_le g1 hsum)

/-- `not_isMCycle_of_le_91`, conditional on the terminal Diophantine statement. -/
theorem not_isMCycle_of_le_91_of_terminal (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) (hT : Terminal) (m n : ℕ) (hm : m ≤ 91)
    (hn : 2 < n) : ¬ IsMCycle m n := by
  intro h
  have : NeZero m := ⟨IsMCycle.ne_zero h⟩
  obtain ⟨D⟩ := IsMCycle.nonempty_mCycleData hB h hn
  obtain ⟨D', -, -, -, hraney⟩ := D.exists_raney
  exact mcycle_false_of_terminal hT hm D' hraney

/-- `Diophantine.terminal` (owned by `dioph`) instantiates `Terminal`. -/
theorem terminal_holds : Terminal := fun K L hK h0 h1 => Diophantine.terminal K L hK h0 h1

/--
**No non-trivial `m`-cycles for `m ≤ 91`, conditional on Bařina's `2^71` check.** For every
`n > 2` there is no `m`-cycle through `n` with `m ≤ 91`, given that every `1 ≤ k ≤ 2^71` reaches `1`
under `collatzStep`. Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/
theorem not_isMCycle_of_le_91_of_barina (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) (m n : ℕ) (hm : m ≤ 91) (hn : 2 < n) :
    ¬ IsMCycle m n :=
  not_isMCycle_of_le_91_of_terminal hB terminal_holds m n hm hn

end CollatzMCycles
