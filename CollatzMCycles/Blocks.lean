module

public import CollatzMCycles.Orbit

/-!
# Block decomposition of a shortcut-Collatz `m`-cycle (Lemma 2.1 / Lemma 1.1)

From `IsMCycle m n` with `2 < n` we extract `MCycleData m`: the cycle re-based at a local
minimum `n₀`, decomposed into `m` consecutive blocks, block `j` consisting of `k j ≥ 1` odd
steps followed by `l j ≥ 1` even steps, together with the exact 2-adic parameterisation
`nmin j + 1 = 2 ^ k j * a j` (`a j` odd), `peak j = 3 ^ k j * a j - 1`,
`nmin (j+1) = (3 ^ k j * a j - 1) / 2 ^ l j`, `padicValNat 2 (3 ^ k j * a j - 1) = l j`.
-/

@[expose] public section
open Finset

namespace CollatzMCycles

/-! ### Generic finite-sum / product helpers -/

/-- A `p`-periodic summand may be rotated inside `∑ i < p`. -/
theorem sum_range_shift_of_periodic {M : Type*} [AddCommMonoid M] (g : ℕ → M) {p : ℕ}
    (hg : ∀ i, g (i + p) = g i) : ∀ r, ∑ i ∈ range p, g (r + i) = ∑ i ∈ range p, g i := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos p with hp | hp
    · simp [hp]
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [sum_range_succ, sum_range_succ']
    have h1 : ∀ i, r + 1 + i = r + (i + 1) := fun i => by omega
    have h2 : g (r + (p' + 1)) = g r := hg r
    simp only [h1, h2, Nat.add_zero]

/-- `s m = ∑_{j<m} c j` for a block-start function `s`. -/
theorem start_eq_sum_blocks (c s : ℕ → ℕ) (hs0 : s 0 = 0) :
    ∀ m, (∀ j < m, s (j + 1) = s j + c j) → s m = ∑ j ∈ range m, c j := by
  intro m
  induction m with
  | zero => intro _; simp [hs0]
  | succ m ih =>
    intro h
    rw [sum_range_succ, ← ih (fun j hj => h j (by omega)), h m (by omega)]

/-- A product over `range (s m)` splits along consecutive blocks of lengths `c j`. -/
@[to_additive /-- A sum over `range (s m)` splits along consecutive blocks of lengths `c j`. -/]
theorem prod_range_blocks {M : Type*} [CommMonoid M] (g : ℕ → M) (c s : ℕ → ℕ)
    (hs0 : s 0 = 0) :
    ∀ m, (∀ j < m, s (j + 1) = s j + c j) →
      ∏ i ∈ range (s m), g i = ∏ j ∈ range m, ∏ t ∈ range (c j), g (s j + t) := by
  intro m
  induction m with
  | zero => intro _; simp [hs0]
  | succ m ih =>
    intro h
    rw [prod_range_succ, ← ih (fun j hj => h j (by omega)), h m (by omega), prod_range_add]

/-! ### Run-length decomposition of a Boolean pattern -/

/-- Run-length decomposition. If `f` is `true` at `0` and at `p`, `false` at `p - 1`, and has
exactly `m - 1` false→true transitions inside `[0, p - 1)`, then `[0, p)` splits into `m`
consecutive blocks, each a run of `k j ≥ 1` `true`s followed by `l j ≥ 1` `false`s. -/
theorem exists_runs :
    ∀ (p m : ℕ) (f : ℕ → Bool), 0 < p → f 0 = true → f (p - 1) = false → f p = true →
    ((range (p - 1)).filter fun t => f t = false ∧ f (t + 1) = true).card + 1 = m →
    ∃ k l s : ℕ → ℕ, s 0 = 0 ∧ (∀ j, s (j + 1) = s j + k j + l j) ∧ s m = p ∧
      ∀ j < m, 1 ≤ k j ∧ 1 ≤ l j ∧ (∀ t < k j, f (s j + t) = true) ∧
        (∀ t < l j, f (s j + k j + t) = false) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro m f hp h0 hlast hp1 hcard
  -- first `true` run: `[0, k)`
  have hk_ex : ∃ t, f t = false := ⟨p - 1, hlast⟩
  set k := Nat.find hk_ex with hk_def
  have hk : f k = false := Nat.find_spec hk_ex
  have hk_min : ∀ t < k, f t = true := fun t ht => by
    have := Nat.find_min hk_ex ht
    simpa using this
  have hk_le : k ≤ p - 1 := Nat.find_min' hk_ex hlast
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, h0] at hk
      exact absurd hk (by decide)
    · exact h
  have hkp : k ≤ p := by omega
  -- first `false` run: `[k, k + l)`
  have hl_ex : ∃ t, f (k + t) = true :=
    ⟨p - k, by rw [Nat.add_sub_cancel' hkp]; exact hp1⟩
  set l := Nat.find hl_ex with hl_def
  have hl : f (k + l) = true := Nat.find_spec hl_ex
  have hl_min : ∀ t < l, f (k + t) = false := fun t ht => by
    have := Nat.find_min hl_ex ht
    simpa using this
  have hl_le : l ≤ p - k :=
    Nat.find_min' hl_ex (by rw [Nat.add_sub_cancel' hkp]; exact hp1)
  have hl_pos : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · rw [h, Nat.add_zero, hk] at hl
      exact absurd hl (by decide)
    · exact h
  have hfalse : ∀ t, k ≤ t → t < k + l → f t = false := fun t h1 h2 => by
    have := hl_min (t - k) (by omega)
    rwa [Nat.add_sub_cancel' h1] at this
  set q := k + l with hq_def
  have hq_pos : 0 < q := by omega
  have hq_le : q ≤ p := by omega
  -- the transitions inside `[0, q)`: none below `q - 1`, one at `q - 1`
  have hzero : ∀ t < q - 1, ¬ (f t = false ∧ f (t + 1) = true) := by
    rintro t ht ⟨hft, hft1⟩
    have hkt : k ≤ t := by
      by_contra hlt
      push Not at hlt
      rw [hk_min t hlt] at hft
      exact absurd hft (by decide)
    have := hfalse (t + 1) (by omega) (by omega)
    rw [this] at hft1
    exact absurd hft1 (by decide)
  have hone : f (q - 1) = false ∧ f q = true := ⟨hfalse _ (by omega) (by omega), hl⟩
  have hfirst : (∑ t ∈ range q, if f t = false ∧ f (t + 1) = true then 1 else 0) = 1 := by
    obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [hq', sum_range_succ, sum_eq_zero]
    · rw [zero_add, ite_eq_left]
      have : q' = q - 1 := by omega
      rw [this, Nat.sub_add_cancel hq_pos]
      exact hone
    · intro t ht
      rw [ite_eq_right (hzero t (by rw [mem_range] at ht; omega))]
  rcases Nat.lt_or_ge q p with hqp | hqp
  · -- recursive case: strip the first block and recurse on `[q, p)`
    have hcard' : ((range (p - q - 1)).filter fun t =>
        f (q + t) = false ∧ f (q + t + 1) = true).card + 1 = m - 1 := by
      rw [card_filter] at hcard ⊢
      have hsplit : p - 1 = q + (p - q - 1) := by omega
      rw [hsplit, sum_range_add, hfirst] at hcard
      omega
    obtain ⟨k', l', s', hs0, hs, hsm, hblk⟩ := ih (p - q) (by omega) (m - 1) (fun t => f (q + t))
      (by omega) (by simpa using hl)
      (by show f (q + (p - q - 1)) = false; rw [show q + (p - q - 1) = p - 1 by omega]; exact hlast)
      (by show f (q + (p - q)) = true; rw [Nat.add_sub_cancel' hq_le]; exact hp1) hcard'
    have hm2 : 2 ≤ m := by omega
    refine ⟨fun j => match j with | 0 => k | j + 1 => k' j,
      fun j => match j with | 0 => l | j + 1 => l' j,
      fun j => match j with | 0 => 0 | j + 1 => q + s' j, rfl, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | zero => show q + s' 0 = 0 + k + l; rw [hs0]; omega
      | succ j => show q + s' (j + 1) = q + s' j + k' j + l' j; rw [hs j]; ring
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      show q + s' m' = p
      rw [show m' + 1 - 1 = m' by omega] at hsm
      omega
    · intro j hj
      cases j with
      | zero =>
        refine ⟨hk_pos, hl_pos, fun t ht => ?_, fun t ht => ?_⟩
        · simpa using hk_min t ht
        · simpa using hl_min t ht
      | succ j =>
        obtain ⟨h1, h2, h3, h4⟩ := hblk j (by omega)
        refine ⟨h1, h2, fun t ht => ?_, fun t ht => ?_⟩
        · have := h3 t ht
          simpa [Nat.add_assoc] using this
        · have := h4 t ht
          simpa [Nat.add_assoc] using this
  · -- single block: `q = p`, hence `m = 1`
    have hqp' : q = p := le_antisymm hq_le hqp
    have hm : m = 1 := by
      rw [card_filter] at hcard
      have : (∑ t ∈ range (p - 1), if f t = false ∧ f (t + 1) = true then 1 else 0) = 0 :=
        sum_eq_zero fun t ht => by
          rw [ite_eq_right (hzero t (by rw [mem_range] at ht; omega))]
      omega
    subst hm
    refine ⟨fun _ => k, fun _ => l, fun j => j * (k + l), by simp, fun j => by ring, ?_, ?_⟩
    · show 1 * (k + l) = p
      omega
    · intro j hj
      have : j = 0 := by omega
      subst this
      exact ⟨hk_pos, hl_pos, fun t ht => by simpa using hk_min t ht,
        fun t ht => by simpa using hl_min t ht⟩

/-! ### Arithmetic of an odd run and of an even run (Lemma 1.1) -/

/-- Along a run of odd iterates, `C^t x + 1 = (3/2)^t (x + 1)` exactly. -/
theorem odd_run_pow {n₀ s k : ℕ} (hodd : ∀ t < k, Odd (collatzShortcut^[s + t] n₀)) :
    ∀ t ≤ k, 2 ^ t * (collatzShortcut^[s + t] n₀ + 1) =
      3 ^ t * (collatzShortcut^[s] n₀ + 1) := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have h1 := ih (by omega)
    have h2 := two_mul_collatzShortcut_add_one_of_odd (hodd t (by omega))
    rw [← Nat.add_assoc, Function.iterate_succ_apply', pow_succ, pow_succ]
    calc 2 ^ t * 2 * (collatzShortcut (collatzShortcut^[s + t] n₀) + 1)
        = 2 ^ t * (2 * (collatzShortcut (collatzShortcut^[s + t] n₀) + 1)) := by ring
      _ = 2 ^ t * (3 * (collatzShortcut^[s + t] n₀ + 1)) := by rw [h2]
      _ = 3 * (2 ^ t * (collatzShortcut^[s + t] n₀ + 1)) := by ring
      _ = 3 * (3 ^ t * (collatzShortcut^[s] n₀ + 1)) := by rw [h1]
      _ = 3 ^ t * 3 * (collatzShortcut^[s] n₀ + 1) := by ring

/-- Along a run of even iterates, `C^t x = x / 2^t`. -/
theorem even_run_div {n₀ s l : ℕ} (heven : ∀ t < l, Even (collatzShortcut^[s + t] n₀)) :
    ∀ t ≤ l, collatzShortcut^[s + t] n₀ = collatzShortcut^[s] n₀ / 2 ^ t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    rw [← Nat.add_assoc, Function.iterate_succ_apply',
      collatzShortcut_of_even (heven t (by omega)), ih (by omega), Nat.div_div_eq_div_mul,
      pow_succ]

theorem pow_dvd_of_even_div {P : ℕ} : ∀ l, (∀ t < l, Even (P / 2 ^ t)) → 2 ^ l ∣ P := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
    intro h
    have hl := ih fun t ht => h t (by omega)
    have := h l (by omega)
    rw [pow_succ]
    exact (Nat.dvd_div_iff_mul_dvd hl).mp (even_iff_two_dvd.mp this)

/-- Lemma 1.1 for one block: `k ≥ 1` odd steps from `C^s n₀` followed by `l ≥ 1` even steps. -/
theorem block_arith {n₀ s k l : ℕ} (_hk : 1 ≤ k) (hl : 1 ≤ l)
    (hodd : ∀ t < k, Odd (collatzShortcut^[s + t] n₀))
    (heven : ∀ t < l, Even (collatzShortcut^[s + k + t] n₀)) :
    ∃ a, Odd a ∧
      (∀ t < k, Odd (collatzShortcut^[s + t] n₀) ∧
        2 ^ t * (collatzShortcut^[s + t] n₀ + 1) = 3 ^ t * (2 ^ k * a)) ∧
      (∀ t < l, Even (collatzShortcut^[s + k + t] n₀) ∧
        collatzShortcut^[s + k + t] n₀ = (3 ^ k * a - 1) / 2 ^ t) := by
  have hk' := odd_run_pow hodd k le_rfl
  have hdvd : 2 ^ k ∣ collatzShortcut^[s] n₀ + 1 := by
    have : 2 ^ k ∣ 3 ^ k * (collatzShortcut^[s] n₀ + 1) := ⟨_, hk'.symm⟩
    exact (Nat.Coprime.pow k k (by norm_num : Nat.Coprime 2 3)).dvd_of_dvd_mul_left this
  obtain ⟨a, ha⟩ := hdvd
  have hpeak : collatzShortcut^[s + k] n₀ + 1 = 3 ^ k * a := by
    have h2 : (0 : ℕ) < 2 ^ k := by positivity
    apply Nat.eq_of_mul_eq_mul_left h2
    rw [hk', ha]
    ring
  have hev0 : Even (collatzShortcut^[s + k] n₀) := by simpa using heven 0 hl
  have ha_odd : Odd a := by
    have : Odd (3 ^ k * a) := by rw [← hpeak]; exact hev0.add_one
    exact (Nat.odd_mul.mp this).2
  refine ⟨a, ha_odd, fun t ht => ⟨hodd t ht, ?_⟩, fun t ht => ⟨heven t ht, ?_⟩⟩
  · rw [odd_run_pow hodd t ht.le, ha]
  · rw [even_run_div heven t ht.le, ← hpeak, Nat.add_sub_cancel]

/-! ### The data of an `m`-cycle -/

/-- Lemma 2.1 package. The cycle is re-based at a local minimum `n₀` (odd); block `j` occupies
orbit indices `[start j, start (j+1))` and consists of `k j` odd steps followed by `l j` even
steps; `start m = p`. The orbit element at index `i` is `collatzShortcut^[i] n₀`. -/
structure MCycleData (m : ℕ) [NeZero m] where
  /-- an element of the cycle: the local minimum number `0` -/
  n₀ : ℕ
  /-- the period -/
  p : ℕ
  p_pos : 0 < p
  periodic : collatzShortcut^[p] n₀ = n₀
  nodup : ((List.range p).map (collatzShortcut^[·] n₀)).Nodup
  /-- number of odd steps in block `j` -/
  k : Fin m → ℕ
  /-- number of even steps in block `j` -/
  l : Fin m → ℕ
  /-- odd cofactor: `nmin j + 1 = 2 ^ k j * a j` -/
  a : Fin m → ℕ
  /-- orbit index at which block `j` starts (`ℕ`-indexed so that `start m = p` makes sense) -/
  start : ℕ → ℕ
  start_zero : start 0 = 0
  start_succ : ∀ j : Fin m, start (j.val + 1) = start j.val + k j + l j
  start_last : start m = p
  k_pos : ∀ j, 1 ≤ k j
  l_pos : ∀ j, 1 ≤ l j
  a_odd : ∀ j, Odd (a j)
  odd_step : ∀ j (t : ℕ), t < k j → Odd (collatzShortcut^[start j + t] n₀) ∧
      2 ^ t * (collatzShortcut^[start j + t] n₀ + 1) = 3 ^ t * (2 ^ k j * a j)
  even_step : ∀ j (t : ℕ), t < l j → Even (collatzShortcut^[start j + k j + t] n₀) ∧
      collatzShortcut^[start j + k j + t] n₀ = (3 ^ k j * a j - 1) / 2 ^ t
  /-- Bařina's bound transported to the cycle (`Orbit.two_pow_71_lt_iterate`). -/
  lower : ∀ i, 2 ^ 71 < collatzShortcut^[i] n₀

namespace MCycleData

variable {m : ℕ} [NeZero m] (D : MCycleData m)

/-- The orbit. -/
def x (i : ℕ) : ℕ := collatzShortcut^[i] D.n₀

/-- The `j`-th local minimum. -/
def nmin (j : Fin m) : ℕ := D.x (D.start j)

/-- The `j`-th local maximum (first even element of block `j`). -/
def peak (j : Fin m) : ℕ := D.x (D.start j + D.k j)

/-- Total number of odd steps. -/
def K : ℕ := ∑ j, D.k j

/-- Total number of even steps. -/
def L : ℕ := ∑ j, D.l j

theorem x_succ (i : ℕ) : D.x (i + 1) = collatzShortcut (D.x i) :=
  Function.iterate_succ_apply' _ _ _

theorem x_add_p (i : ℕ) : D.x (i + D.p) = D.x i := iterate_add_period D.periodic i

theorem x_p : D.x D.p = D.x 0 := by simpa using D.x_add_p 0

theorem x_gt (i : ℕ) : 2 ^ 71 < D.x i := D.lower i

theorem x_pos (i : ℕ) : 0 < D.x i := lt_trans (by positivity) (D.x_gt i)

theorem x_injOn {i j : ℕ} (hi : i < D.p) (hj : j < D.p) (h : D.x i = D.x j) : i = j :=
  iterate_injOn_of_nodup D.nodup hi hj h

theorem nmin_odd (j : Fin m) : Odd (D.nmin j) := by
  have h := (D.odd_step j 0 (D.k_pos j)).1
  simpa [nmin, x] using h

theorem nmin_add_one (j : Fin m) : D.nmin j + 1 = 2 ^ D.k j * D.a j := by
  have h := (D.odd_step j 0 (D.k_pos j)).2
  simpa [nmin, x] using h

theorem peak_even (j : Fin m) : Even (D.peak j) := by
  have h := (D.even_step j 0 (D.l_pos j)).1
  simpa [peak, x] using h

theorem peak_eq (j : Fin m) : D.peak j = 3 ^ D.k j * D.a j - 1 := by
  have h := (D.even_step j 0 (D.l_pos j)).2
  simpa [peak, x] using h

theorem a_pos (j : Fin m) : 0 < D.a j := by
  have h := D.nmin_add_one j
  rcases Nat.eq_zero_or_pos (D.a j) with h0 | h0
  · rw [h0, Nat.mul_zero] at h
    omega
  · exact h0

theorem one_le_three_pow_mul (j : Fin m) : 1 ≤ 3 ^ D.k j * D.a j :=
  Nat.mul_pos (by positivity) (D.a_pos j)

theorem peak_add_one (j : Fin m) : D.peak j + 1 = 3 ^ D.k j * D.a j := by
  rw [peak_eq]
  have := D.one_le_three_pow_mul j
  omega

theorem nmin_gt (j : Fin m) : 2 ^ 71 < D.nmin j := D.x_gt _

theorem nmin_pos (j : Fin m) : 0 < D.nmin j := D.x_pos _

/-- Odd step `t` of block `j`: `x + 1 = 3^t 2^(k-t) a`. -/
theorem x_odd_step_add_one (j : Fin m) (t : ℕ) (ht : t < D.k j) :
    D.x (D.start j + t) + 1 = 3 ^ t * 2 ^ (D.k j - t) * D.a j := by
  have h : 2 ^ t * (D.x (D.start j + t) + 1) = 3 ^ t * (2 ^ D.k j * D.a j) :=
    (D.odd_step j t ht).2
  have hk : D.k j = t + (D.k j - t) := by omega
  rw [hk, pow_add] at h
  have h2 : (0 : ℕ) < 2 ^ t := by positivity
  apply Nat.eq_of_mul_eq_mul_left h2
  rw [h]
  ring

theorem x_odd_step (j : Fin m) (t : ℕ) (ht : t < D.k j) : Odd (D.x (D.start j + t)) :=
  (D.odd_step j t ht).1

theorem x_even_step (j : Fin m) (t : ℕ) (ht : t < D.l j) :
    Even (D.x (D.start j + D.k j + t)) :=
  (D.even_step j t ht).1

/-- Even step `t ≤ l j` of block `j` (including the landing point `t = l j`). -/
theorem x_even_step_eq (j : Fin m) (t : ℕ) (ht : t ≤ D.l j) :
    D.x (D.start j + D.k j + t) = (3 ^ D.k j * D.a j - 1) / 2 ^ t := by
  rcases Nat.lt_or_ge t (D.l j) with h | h
  · exact (D.even_step j t h).2
  · have ht' : t = D.l j := le_antisymm ht h
    subst ht'
    obtain ⟨l', hl'⟩ : ∃ l', D.l j = l' + 1 := ⟨D.l j - 1, by have := D.l_pos j; omega⟩
    have h1 : Even (D.x (D.start j + D.k j + l')) ∧
        D.x (D.start j + D.k j + l') = (3 ^ D.k j * D.a j - 1) / 2 ^ l' :=
      D.even_step j l' (by omega)
    rw [hl', ← Nat.add_assoc, x_succ, collatzShortcut_of_even h1.1, h1.2,
      Nat.div_div_eq_div_mul, pow_succ]

theorem two_pow_l_dvd (j : Fin m) : 2 ^ D.l j ∣ 3 ^ D.k j * D.a j - 1 :=
  pow_dvd_of_even_div _ fun t ht => by
    have h := D.even_step j t ht
    rw [← h.2]
    exact h.1

/-- `nmin (j+1)` (cyclically) is the landing point of block `j`. -/
theorem nmin_succ_eq (j : Fin m) : D.nmin (j + 1) = D.x (D.start j + D.k j + D.l j) := by
  rw [← D.start_succ j]
  unfold nmin
  have hval : ((j + 1 : Fin m) : ℕ) = (j.val + 1) % m := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  rcases Nat.lt_or_ge (j.val + 1) m with h | h
  · rw [Nat.mod_eq_of_lt h]
  · have hm : j.val + 1 = m := le_antisymm j.isLt h
    rw [hm, Nat.mod_self, D.start_zero, D.start_last]
    exact D.x_p.symm

/-- Lemma 1.1: `n_{j+1} = (3^{k_j} a_j - 1) / 2^{l_j}`. -/
theorem nmin_succ (j : Fin m) : D.nmin (j + 1) = (3 ^ D.k j * D.a j - 1) / 2 ^ D.l j := by
  rw [nmin_succ_eq]
  exact D.x_even_step_eq j _ le_rfl

/-- Lemma 1.1, exact-division form: `2^{l_j} n_{j+1} = 3^{k_j} a_j - 1`. -/
theorem two_pow_l_mul_nmin_succ (j : Fin m) :
    2 ^ D.l j * D.nmin (j + 1) = 3 ^ D.k j * D.a j - 1 := by
  rw [nmin_succ]
  exact Nat.mul_div_cancel' (D.two_pow_l_dvd j)

/-- Lemma 1.1: `l_j = ν₂(3^{k_j} a_j - 1)`. -/
theorem padicValNat_two (j : Fin m) : padicValNat 2 (3 ^ D.k j * D.a j - 1) = D.l j := by
  have hmul := D.two_pow_l_mul_nmin_succ j
  have hne : 3 ^ D.k j * D.a j - 1 ≠ 0 := by
    rw [← hmul]
    exact Nat.mul_ne_zero (by positivity) (D.nmin_pos _).ne'
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have h1 : 2 ^ (D.l j + 1) ∣ 3 ^ D.k j * D.a j - 1 :=
      (pow_dvd_pow 2 hlt).trans pow_padicValNat_dvd
    rw [← hmul, pow_succ] at h1
    have h2 : 2 ∣ D.nmin (j + 1) := Nat.dvd_of_mul_dvd_mul_left (by positivity) h1
    exact (Nat.not_even_iff_odd.mpr (D.nmin_odd (j + 1))) (even_iff_two_dvd.mpr h2)
  · exact (padicValNat_dvd_iff_le hne).mp (D.two_pow_l_dvd j)

/-! #### Sums and products over the cycle -/

/-- `ℕ`-indexed block length (`k j + l j` for `j < m`, `0` otherwise). -/
def c (i : ℕ) : ℕ := if h : i < m then D.k ⟨i, h⟩ + D.l ⟨i, h⟩ else 0

theorem start_succ' (i : ℕ) (hi : i < m) : D.start (i + 1) = D.start i + D.c i := by
  simp only [c, dite_eq_left hi]
  rw [← Nat.add_assoc]
  exact D.start_succ ⟨i, hi⟩

theorem sum_c : ∑ i ∈ range m, D.c i = ∑ j : Fin m, (D.k j + D.l j) := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [c, j.isLt]

theorem sum_start : ∑ j : Fin m, (D.k j + D.l j) = D.p := by
  rw [← sum_c, ← start_eq_sum_blocks D.c D.start D.start_zero m (fun j hj => D.start_succ' j hj),
    D.start_last]

/-- `K + L = p`. -/
theorem K_add_L : D.K + D.L = D.p := by
  rw [K, L, ← sum_add_distrib]
  exact D.sum_start

/-- Block decomposition of any product over the cycle indices `range p`: block `j` contributes its
`k j` odd-step indices `start j + t` and its `l j` even-step indices `start j + k j + t`. -/
@[to_additive /-- Block decomposition of any sum over the cycle indices `range p`: block `j`
contributes its `k j` odd-step indices `start j + t` and its `l j` even-step indices
`start j + k j + t`. -/]
theorem prod_range_p {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∏ i ∈ range D.p, g i =
      ∏ j : Fin m, ((∏ t ∈ range (D.k j), g (D.start j + t)) *
        ∏ t ∈ range (D.l j), g (D.start j + D.k j + t)) := by
  rw [← D.start_last,
    prod_range_blocks g D.c D.start D.start_zero m (fun j hj => D.start_succ' j hj),
    Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [c, dite_eq_left j.isLt, Fin.eta, prod_range_add]
  simp only [Nat.add_assoc]

end MCycleData

/-! ### Existence -/

/-- A periodic positive shortcut orbit contains an even element followed by an odd one. -/
theorem exists_even_odd {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hper : collatzShortcut^[p] n = n) :
    ∃ i, Even (collatzShortcut^[i] n) ∧ Odd (collatzShortcut^[i + 1] n) := by
  have hev : ∃ i, Even (collatzShortcut^[i] n) := by
    by_contra hall
    push Not at hall
    simp only [Nat.not_even_iff_odd] at hall
    have hmono : ∀ i, n + i ≤ collatzShortcut^[i] n := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have := lt_collatzShortcut_of_odd (hall i)
        rw [Function.iterate_succ_apply']
        omega
    have := hmono p
    rw [hper] at this
    omega
  have hod : ∃ i, Odd (collatzShortcut^[i] n) := by
    by_contra hall
    push Not at hall
    simp only [Nat.not_odd_iff_even] at hall
    have hmono : ∀ i, collatzShortcut^[i] n + i ≤ n := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        have := collatzShortcut_lt_of_even (iterate_collatzShortcut_pos hn i) (hall i)
        rw [Function.iterate_succ_apply']
        omega
    have := hmono (n + 1)
    omega
  obtain ⟨i₁, h₁⟩ := hev
  obtain ⟨i₂, h₂⟩ := hod
  have hex : ∃ t, Odd (collatzShortcut^[i₁ + t] n) := by
    refine ⟨(p - i₁ % p) + i₂, ?_⟩
    have hd := Nat.mod_add_div i₁ p
    have hl := Nat.mod_lt i₁ hp
    have : i₁ + ((p - i₁ % p) + i₂) = i₂ + p * (i₁ / p + 1) := by
      rw [Nat.mul_succ]
      omega
    rw [this, iterate_add_mul_period hper]
    exact h₂
  classical
  have ht₀ : Odd (collatzShortcut^[i₁ + Nat.find hex] n) := Nat.find_spec hex
  have ht₀pos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, Nat.add_zero] at ht₀
    exact (Nat.not_even_iff_odd.mpr ht₀) h₁
  refine ⟨i₁ + (Nat.find hex - 1), ?_, ?_⟩
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rwa [Nat.not_odd_iff_even] at this
  · rw [show i₁ + (Nat.find hex - 1) + 1 = i₁ + Nat.find hex by omega]
    exact ht₀

/-- An `m`-cycle has `m ≥ 1`. -/
theorem IsMCycle.ne_zero {m n : ℕ} (h : IsMCycle m n) : m ≠ 0 := by
  obtain ⟨hn, p, hp, hper, -, hcard⟩ := h
  obtain ⟨i, hi⟩ := exists_even_odd hn hp hper
  intro hm
  rw [hm, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
  apply hcard (Finset.mem_range.mpr (Nat.mod_lt i hp))
  rw [localMin_iff hn, ← iterate_mod_period hper i]
  have : collatzShortcut^[i % p + 1] n = collatzShortcut^[i + 1] n := by
    rw [iterate_mod_period hper (i % p + 1), iterate_mod_period hper (i + 1), Nat.mod_add_mod]
  rw [this]
  exact hi

/-- Main extraction theorem: every `m`-cycle through some `n > 2` yields `MCycleData m`. -/
theorem IsMCycle.nonempty_mCycleData
    (hB : ∀ k : ℕ, 0 < k → k ≤ 2 ^ 71 → ∃ s, collatzStep^[s] k = 1) {m n : ℕ} [NeZero m] (h : IsMCycle m n) (hn : 2 < n) :
    Nonempty (MCycleData m) := by
  obtain ⟨hn0, p, hp, hper, hnodup, hcard⟩ := h
  obtain ⟨i₀, hi₀e, hi₀o⟩ := exists_even_odd hn0 hp hper
  -- the orbit re-based at the local minimum `x (i₀ + 1)`
  set r := i₀ + 1 with hr
  set y : ℕ → ℕ := fun t => collatzShortcut^[r + t] n with hy
  have hy_iter : ∀ t, collatzShortcut^[t] (y 0) = y t := fun t => by
    show collatzShortcut^[t] (collatzShortcut^[r + 0] n) = collatzShortcut^[r + t] n
    rw [Nat.add_zero, ← Function.iterate_add_apply, Nat.add_comm]
  have hy_per : collatzShortcut^[p] (y 0) = y 0 := by
    rw [hy_iter]
    show collatzShortcut^[r + p] n = collatzShortcut^[r + 0] n
    rw [iterate_add_period hper, Nat.add_zero]
  have hy_nodup : ((List.range p).map (collatzShortcut^[·] (y 0))).Nodup := by
    apply nodup_of_iterate_injOn
    intro i hi j hj hij
    rw [hy_iter, hy_iter] at hij
    have hmod : (r + i) % p = (r + j) % p :=
      iterate_injOn_of_nodup hnodup (Nat.mod_lt _ hp) (Nat.mod_lt _ hp)
        (by rw [← iterate_mod_period hper, ← iterate_mod_period hper]; exact hij)
    have h2 : i % p = j % p := Nat.ModEq.add_left_cancel' r hmod
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
  -- parity pattern
  let f : ℕ → Bool := fun t => decide (Odd (y t))
  have hf_true : ∀ t, f t = true ↔ Odd (y t) := fun t => by simp [f]
  have hf_false : ∀ t, f t = false ↔ Even (y t) := fun t => by simp [f, Nat.not_odd_iff_even]
  have hf0 : f 0 = true := (hf_true 0).mpr (by
    show Odd (collatzShortcut^[r + 0] n)
    rw [Nat.add_zero]
    exact hi₀o)
  have hf_last : f (p - 1) = false := (hf_false _).mpr (by
    show Even (collatzShortcut^[r + (p - 1)] n)
    rw [show r + (p - 1) = i₀ + p by omega, iterate_add_period hper]
    exact hi₀e)
  have hfp : f p = true := (hf_true p).mpr (by
    show Odd (collatzShortcut^[r + p] n)
    rw [iterate_add_period hper]
    exact hi₀o)
  -- transition count
  have hcount : ((range (p - 1)).filter fun t => f t = false ∧ f (t + 1) = true).card + 1 = m := by
    have h1 : ((range p).filter fun i => collatzShortcut^[i + 1] n < collatzShortcut^[i] n ∧
          collatzShortcut^[i + 1] n < collatzShortcut^[i + 2] n) =
        (range p).filter fun i => Even (collatzShortcut^[i] n) ∧ Odd (collatzShortcut^[i + 1] n) :=
      Finset.filter_congr fun i _ => localMin_iff hn0 i
    rw [h1, card_filter] at hcard
    set g : ℕ → ℕ := fun i =>
      if Even (collatzShortcut^[i] n) ∧ Odd (collatzShortcut^[i + 1] n) then 1 else 0 with hg
    have hg_per : ∀ i, g (i + p) = g i := fun i => by
      simp only [hg]
      rw [iterate_add_period hper, show i + p + 1 = i + 1 + p by omega, iterate_add_period hper]
    rw [← sum_range_shift_of_periodic g hg_per r] at hcard
    obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rw [hp', sum_range_succ] at hcard
    have hlast : g (r + p') = 1 := by
      simp only [hg]
      rw [ite_eq_left]
      constructor
      · rw [show r + p' = i₀ + p by omega, iterate_add_period hper]
        exact hi₀e
      · rw [show r + p' + 1 = r + p by omega, iterate_add_period hper]
        exact hi₀o
    rw [hlast] at hcard
    rw [card_filter, show p - 1 = p' by omega, ← hcard]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    simp only [hg]
    have e1 : (f t = false ∧ f (t + 1) = true) ↔
        (Even (collatzShortcut^[r + t] n) ∧ Odd (collatzShortcut^[r + t + 1] n)) := by
      rw [hf_false, hf_true]
      exact Iff.rfl
    by_cases hc : f t = false ∧ f (t + 1) = true
    · rw [ite_eq_left hc, ite_eq_left (e1.mp hc)]
    · rw [ite_eq_right hc, ite_eq_right (fun h => hc (e1.mpr h))]
  obtain ⟨k, l, s, hs0, hs, hsm, hblk⟩ := exists_runs p m f hp hf0 hf_last hfp hcount
  have hodd : ∀ j : Fin m, ∀ t < k j, Odd (collatzShortcut^[s j + t] (y 0)) :=
    fun j t ht => by rw [hy_iter]; exact (hf_true _).mp ((hblk j j.isLt).2.2.1 t ht)
  have heven : ∀ j : Fin m, ∀ t < l j, Even (collatzShortcut^[s j + k j + t] (y 0)) :=
    fun j t ht => by rw [hy_iter]; exact (hf_false _).mp ((hblk j j.isLt).2.2.2 t ht)
  have hblk' : ∀ j : Fin m, ∃ a, Odd a ∧
      (∀ t < k j, Odd (collatzShortcut^[s j + t] (y 0)) ∧
        2 ^ t * (collatzShortcut^[s j + t] (y 0) + 1) = 3 ^ t * (2 ^ k j * a)) ∧
      (∀ t < l j, Even (collatzShortcut^[s j + k j + t] (y 0)) ∧
        collatzShortcut^[s j + k j + t] (y 0) = (3 ^ k j * a - 1) / 2 ^ t) :=
    fun j => block_arith (hblk j j.isLt).1 (hblk j j.isLt).2.1 (hodd j) (heven j)
  choose a ha_odd hodd_step heven_step using hblk'
  refine ⟨⟨y 0, p, hp, hy_per, hy_nodup, fun j => k j, fun j => l j, a, s, hs0, fun j => hs j, hsm,
    fun j => (hblk j j.isLt).1, fun j => (hblk j j.isLt).2.1, ha_odd, hodd_step, heven_step,
    fun i => ?_⟩⟩
  rw [hy_iter]
  exact two_pow_71_lt_iterate hB hn hp hper _

end CollatzMCycles
