module

public import CollatzMCycles.SpecDefs

/-!
# Orbit facts for shortcut-Collatz cycles

Basic facts about the orbit `x i := collatzShortcut^[i] n` of a periodic point `n` of
`collatzShortcut` with `2 < n`: positivity, parity characterisation of Moritz's local-minimum
predicate, periodicity, and the bound `2 ^ 71 < x i` for every `i`, taking Bařina's `2^71` verification as the explicit
hypothesis `hB`.
-/

@[expose] public section
namespace CollatzMCycles

/-! ### One-step facts -/

theorem collatzShortcut_of_even {n : ℕ} (h : Even n) : collatzShortcut n = n / 2 := by
  simp [collatzShortcut, h]

theorem collatzShortcut_of_odd {n : ℕ} (h : Odd n) : collatzShortcut n = (3 * n + 1) / 2 := by
  simp [collatzShortcut, Nat.not_even_iff_odd.mpr h]

/-- For odd `n`, `C n + 1 = (3/2) (n + 1)` exactly. -/
theorem two_mul_collatzShortcut_add_one_of_odd {n : ℕ} (h : Odd n) :
    2 * (collatzShortcut n + 1) = 3 * (n + 1) := by
  rw [collatzShortcut_of_odd h]
  obtain ⟨r, rfl⟩ := h
  omega

theorem collatzShortcut_pos {n : ℕ} (hn : 0 < n) : 0 < collatzShortcut n := by
  unfold collatzShortcut
  split_ifs with h
  · obtain ⟨r, rfl⟩ := h
    omega
  · omega

theorem iterate_collatzShortcut_pos {n : ℕ} (hn : 0 < n) (i : ℕ) :
    0 < collatzShortcut^[i] n := by
  induction i with
  | zero => simpa
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact collatzShortcut_pos ih

theorem collatzShortcut_lt_of_even {n : ℕ} (hn : 0 < n) (h : Even n) :
    collatzShortcut n < n := by
  rw [collatzShortcut_of_even h]
  omega

theorem lt_collatzShortcut_of_odd {n : ℕ} (h : Odd n) : n < collatzShortcut n := by
  have := two_mul_collatzShortcut_add_one_of_odd h
  omega

/-- Moritz's local-minimum predicate (from `IsMCycle`) is equivalent to
"`x i` even and `x (i+1)` odd" (for a positive orbit). -/
theorem localMin_iff {n : ℕ} (hn : 0 < n) (i : ℕ) :
    (collatzShortcut^[i + 1] n < collatzShortcut^[i] n ∧
      collatzShortcut^[i + 1] n < collatzShortcut^[i + 2] n) ↔
    (Even (collatzShortcut^[i] n) ∧ Odd (collatzShortcut^[i + 1] n)) := by
  have h1 : collatzShortcut^[i + 1] n = collatzShortcut (collatzShortcut^[i] n) :=
    Function.iterate_succ_apply' _ _ _
  have h2 : collatzShortcut^[i + 2] n = collatzShortcut (collatzShortcut^[i + 1] n) :=
    Function.iterate_succ_apply' _ _ _
  have p0 := iterate_collatzShortcut_pos hn i
  have p1 := iterate_collatzShortcut_pos hn (i + 1)
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · by_contra he
      rw [Nat.not_even_iff_odd] at he
      have := lt_collatzShortcut_of_odd he
      rw [← h1] at this
      omega
    · by_contra ho
      rw [Nat.not_odd_iff_even] at ho
      have := collatzShortcut_lt_of_even p1 ho
      rw [← h2] at this
      omega
  · rintro ⟨he, ho⟩
    refine ⟨?_, ?_⟩
    · rw [h1]
      exact collatzShortcut_lt_of_even p0 he
    · rw [h2]
      exact lt_collatzShortcut_of_odd ho

/-! ### Periodicity -/

theorem iterate_add_period {n p : ℕ} (hper : collatzShortcut^[p] n = n) (i : ℕ) :
    collatzShortcut^[i + p] n = collatzShortcut^[i] n := by
  rw [Function.iterate_add_apply, hper]

theorem iterate_add_mul_period {n p : ℕ} (hper : collatzShortcut^[p] n = n) (i q : ℕ) :
    collatzShortcut^[i + p * q] n = collatzShortcut^[i] n := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, iterate_add_period hper, ih]

theorem iterate_mod_period {n p : ℕ} (hper : collatzShortcut^[p] n = n) (i : ℕ) :
    collatzShortcut^[i] n = collatzShortcut^[i % p] n := by
  conv_lhs => rw [← Nat.mod_add_div i p]
  exact iterate_add_mul_period hper _ _

/-! ### The trivial cycle and Bařina's bound -/

theorem iterate_collatzShortcut_one (j : ℕ) : collatzShortcut^[j] 1 ≤ 2 := by
  have h2 : collatzShortcut^[2] 1 = 1 := by decide
  rw [iterate_mod_period h2]
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> rw [h] <;> decide

/-- The shortcut orbit hits `1` whenever the `collatzStep` orbit does
(the shortcut orbit is a subsequence of the `collatzStep` orbit). -/
theorem exists_shortcut_eq_one_of_step :
    ∀ (j x : ℕ), 0 < x → collatzStep^[j] x = 1 → ∃ i, collatzShortcut^[i] x = 1 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx h
  rcases j with _ | j
  · exact ⟨0, by simpa using h⟩
  by_cases he : Even x
  · have h1 : collatzStep^[j + 1] x = collatzStep^[j] (collatzShortcut x) := by
      rw [Function.iterate_succ_apply]
      congr 1
      simp [collatzStep, collatzShortcut, he]
    rw [h1] at h
    obtain ⟨i, hi⟩ := ih j (Nat.lt_succ_self j) _ (collatzShortcut_pos hx) h
    exact ⟨i + 1, by rw [Function.iterate_add_apply]; simpa using hi⟩
  · have hstep : collatzStep x = 3 * x + 1 := by simp [collatzStep, he]
    rcases j with _ | j
    · simp [hstep] at h
      omega
    · have h2 : collatzStep^[j + 1 + 1] x = collatzStep^[j] (collatzShortcut x) := by
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep]
        congr 1
        have hev : Even (3 * x + 1) := by
          rw [Nat.not_even_iff_odd] at he
          obtain ⟨r, rfl⟩ := he
          exact ⟨3 * r + 2, by ring⟩
        simp [collatzStep, collatzShortcut, hev, he]
      rw [h2] at h
      obtain ⟨i, hi⟩ := ih j (by omega) _ (collatzShortcut_pos hx) h
      exact ⟨i + 1, by rw [Function.iterate_add_apply]; simpa using hi⟩

/-- `1` is not on a shortcut cycle through some `n > 2`. -/
theorem iterate_ne_one {n p : ℕ} (hn : 2 < n) (hp : 0 < p)
    (hper : collatzShortcut^[p] n = n) (i : ℕ) : collatzShortcut^[i] n ≠ 1 := by
  intro h1
  rw [iterate_mod_period hper] at h1
  have hlt : i % p < p := Nat.mod_lt _ hp
  have hn' : n = collatzShortcut^[p - i % p] 1 := by
    rw [← h1, ← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le, hper]
  have := iterate_collatzShortcut_one (p - i % p)
  omega

/-- Every element of a non-trivial shortcut cycle is at least `3` (no external input). -/
theorem three_le_iterate {n p : ℕ} (hn : 2 < n) (hp : 0 < p)
    (hper : collatzShortcut^[p] n = n) (i : ℕ) : 3 ≤ collatzShortcut^[i] n := by
  have h1 := iterate_ne_one hn hp hper i
  have h2 := iterate_ne_one hn hp hper (i + 1)
  have h0 := iterate_collatzShortcut_pos (by omega : 0 < n) i
  rw [Function.iterate_succ_apply'] at h2
  by_contra hlt
  have h3 : collatzShortcut^[i] n = 2 := by omega
  rw [h3] at h2
  exact h2 (by decide)

/-- Every element of a non-trivial shortcut cycle exceeds `2 ^ 71`.
The only external input is Bařina's `2^71` verification [Ba25], passed as the hypothesis `hB`. -/
theorem two_pow_71_lt_iterate
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) {n p : ℕ} (hn : 2 < n) (hp : 0 < p)
    (hper : collatzShortcut^[p] n = n) (i : ℕ) : 2 ^ 71 < collatzShortcut^[i] n := by
  by_contra hle
  push Not at hle
  have hpos := iterate_collatzShortcut_pos (by omega : 0 < n) i
  obtain ⟨j, hj⟩ := hB _ hpos hle
  obtain ⟨i', hi'⟩ := exists_shortcut_eq_one_of_step j _ hpos hj
  rw [← Function.iterate_add_apply] at hi'
  exact iterate_ne_one hn hp hper _ hi'

/-! ### Nodup -/

theorem iterate_injOn_of_nodup {n p : ℕ}
    (hnodup : ((List.range p).map (collatzShortcut^[·] n)).Nodup)
    {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : collatzShortcut^[i] n = collatzShortcut^[j] n) : i = j := by
  rw [List.nodup_map_iff_inj_on List.nodup_range] at hnodup
  exact hnodup i (List.mem_range.mpr hi) j (List.mem_range.mpr hj) h

theorem nodup_of_iterate_injOn {n p : ℕ}
    (h : ∀ i < p, ∀ j < p, collatzShortcut^[i] n = collatzShortcut^[j] n → i = j) :
    ((List.range p).map (collatzShortcut^[·] n)).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj hij
  exact h i (List.mem_range.mp hi) j (List.mem_range.mp hj) hij

/-! ### `IsMCycle` wrappers -/

theorem IsMCycle.two_pow_71_lt
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) {m n : ℕ} (h : IsMCycle m n) (hn : 2 < n) (i : ℕ) :
    2 ^ 71 < collatzShortcut^[i] n := by
  obtain ⟨-, p, hp, hper, -⟩ := h
  exact two_pow_71_lt_iterate hB hn hp hper i

theorem IsMCycle.three_le {m n : ℕ} (h : IsMCycle m n) (hn : 2 < n) (i : ℕ) :
    3 ≤ collatzShortcut^[i] n := by
  obtain ⟨-, p, hp, hper, -⟩ := h
  exact three_le_iterate hn hp hper i

end CollatzMCycles
