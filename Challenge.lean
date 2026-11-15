module

public import Mathlib

/-!
# Challenge: Collatz `m`-cycles for `m ≤ 91` and an explicit linear-form bound

Definitions are verbatim from Moritz Firsching's `formal-conjectures` specification of Collatz
`m`-cycles.

* `collatzShortcut` is the shortcut Collatz map: `n / 2` for even `n`, `(3n + 1) / 2` for odd `n`.
* `IsMCycle m n` says that `n > 0` lies on a cycle of `collatzShortcut` of some period `p > 0`
  whose `p` elements are distinct and which has exactly `m` local minima.

Statements:

1. `CollatzMCycles.Diophantine.terminal`: for every `K ≥ 2438425051595107335801557824` and every
   `L`, the linear form `Λ = (K + L) log 2 − K log 3` cannot satisfy
   `0 < Λ < 100 · 2^(1 − K / 2^68)`. This replaces the use of Rhin's (1987) effective
   irrationality measure in the `m`-cycle argument and is proved from Mathlib alone.
2. `CollatzMCycles.not_isMCycle_of_le_91_of_barina`: assuming every `1 ≤ k ≤ 2^71` reaches `1`
   under `collatzStep` (Bařina's 2025 computer verification, passed as the hypothesis `hB`), there
   is no `m`-cycle with `m ≤ 91` through any `n > 2`. (The cycle `1 → 2 → 1` is the trivial
   `1`-cycle, which is why `n > 2` is required.)

Supporting statements, which test the definitions and record the facts the main theorem rests on:

3. `isMCycle_one_one`, `isMCycle_one_two`: the trivial cycle `1 → 2 → 1` is a `1`-cycle through
   both `1` and `2`.
4. `CollatzMCycles.IsMCycle.ne_zero`: every cycle has at least one local minimum (`m ≠ 0`).
5. `CollatzMCycles.two_pow_71_lt_iterate`: under the same hypothesis `hB`, every element of a cycle
   of `collatzShortcut` through some `n > 2` exceeds `2^71`.
-/

@[expose] public section

/-- One step of the Collatz map: `n / 2` for even `n`, `3n + 1` for odd `n`. -/
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- The shortcut Collatz map: `n / 2` for even `n`, `(3n + 1) / 2` for odd `n`. -/
def collatzShortcut (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

/-- `n` lies on a cycle of `collatzShortcut` of period `p > 0`, with `p` distinct elements and
exactly `m` local minima. -/
def IsMCycle (m n : ℕ) : Prop :=
  0 < n ∧ ∃ p > 0, collatzShortcut^[p] n = n ∧
    ((List.range p).map (collatzShortcut^[·] n)).Nodup ∧
    ((Finset.range p).filter fun i =>
      collatzShortcut^[i + 1] n < collatzShortcut^[i] n ∧
      collatzShortcut^[i + 1] n < collatzShortcut^[i + 2] n).card = m

/-- The trivial cycle `1 → 2 → 1` is a `1`-cycle through `1`. -/
theorem isMCycle_one_one : IsMCycle 1 1 := by
  sorry

/-- The trivial cycle `1 → 2 → 1` is a `1`-cycle through `2`. -/
theorem isMCycle_one_two : IsMCycle 1 2 := by
  sorry

namespace CollatzMCycles

/-- An `m`-cycle has at least one local minimum. -/
theorem IsMCycle.ne_zero {m n : ℕ} (h : IsMCycle m n) : m ≠ 0 := by
  sorry

/-- Assuming Bařina's verification, every element of a cycle of `collatzShortcut` through some
`n > 2` exceeds `2^71`. -/
theorem two_pow_71_lt_iterate
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) {n p : ℕ} (hn : 2 < n) (hp : 0 < p)
    (hper : collatzShortcut^[p] n = n) (i : ℕ) : 2 ^ 71 < collatzShortcut^[i] n := by
  sorry

namespace Diophantine

/-- For `K ≥ 2438425051595107335801557824`, the linear form `(K + L) log 2 − K log 3` cannot lie
strictly between `0` and `100 · 2^(1 − K / 2^68)`. -/
theorem terminal (K L : ℕ) (hK : 2438425051595107335801557824 ≤ K)
    (h0 : 0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3)
    (h1 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 <
      100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68)) :
    False := by
  sorry

end Diophantine

/-- No non-trivial Collatz `m`-cycle with `m ≤ 91`, assuming Bařina's verification that every
`1 ≤ k ≤ 2^71` reaches `1`. -/
theorem not_isMCycle_of_le_91_of_barina
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) (m n : ℕ) (hm : m ≤ 91)
    (hn : 2 < n) : ¬ IsMCycle m n := by
  sorry

end CollatzMCycles
