module

public import Mathlib
public import CollatzMCycles.Blocks

/-!
# Lemma 3.2 (Full-Cycle Raney Suffix Rotation)

Pure finite combinatorics, no Collatz.  For `m ≥ 1` and `k : Fin m → ℕ` with
`K = ∑ k`, there is a cyclic rotation `r : Fin m` such that every suffix of the
rotated sequence `j ↦ k (r + j)` of length `t ∈ {1, …, m}` has sum at least
`t * K / m`.  Stated in `ℕ` by cross-multiplication: `t * K ≤ m * suffix`.

Proof: argmax of the cyclic prefix discrepancies `D i := m * S i − i * K` (in `ℤ`).
-/

@[expose] public section
namespace CollatzMCycles
namespace Raney

open Finset

variable {m : ℕ} [NeZero m]

/-- Cyclic extension of `k : Fin m → ℕ` to `ℕ`. -/
def cyc (k : Fin m → ℕ) (j : ℕ) : ℕ := k (Fin.ofNat m j)

/-- Prefix sums of the cyclic extension. -/
def psum (k : Fin m → ℕ) (i : ℕ) : ℕ := ∑ j ∈ range i, cyc k j

lemma psum_add (k : Fin m → ℕ) (a b : ℕ) :
    psum k (a + b) = psum k a + ∑ j ∈ range b, cyc k (a + j) := by
  unfold psum; exact Finset.sum_range_add _ a b

lemma ofNat_val (j : Fin m) : Fin.ofNat m (j : ℕ) = j := by
  rw [Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

/-- A window of length `m` of the cyclic extension sums to the full sum. -/
lemma sum_window (k : Fin m → ℕ) (i : ℕ) :
    ∑ j ∈ range m, cyc k (i + j) = ∑ j, k j := by
  rw [Finset.sum_range]
  unfold cyc
  have : ∀ j : Fin m, Fin.ofNat m (i + (j : ℕ)) = Fin.ofNat m i + j := by
    intro j; rw [Fin.ofNat_add]
  simp_rw [this]
  exact Equiv.sum_comp (Equiv.addLeft (Fin.ofNat m i)) k

lemma psum_add_m (k : Fin m → ℕ) (i : ℕ) :
    psum k (i + m) = psum k i + ∑ j, k j := by
  rw [psum_add, sum_window]

/-- Cyclic prefix discrepancy `D i = m * S i − i * K` in `ℤ`. -/
def disc (k : Fin m → ℕ) (i : ℕ) : ℤ :=
  (m : ℤ) * (psum k i : ℤ) - (i : ℤ) * ((∑ j, k j : ℕ) : ℤ)

lemma disc_add_m (k : Fin m → ℕ) (i : ℕ) : disc k (i + m) = disc k i := by
  unfold disc; rw [psum_add_m]; push_cast; ring

lemma disc_add_mul_m (k : Fin m → ℕ) (i n : ℕ) : disc k (i + n * m) = disc k i := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_mul, ← add_assoc, disc_add_m, ih]

lemma disc_mod (k : Fin m → ℕ) (i : ℕ) : disc k i = disc k (i % m) := by
  conv_lhs => rw [← Nat.mod_add_div i m, mul_comm]
  exact disc_add_mul_m k _ _

/-- The sum of a rotated sequence is the original sum. -/
lemma sum_rotate (k : Fin m → ℕ) (r : Fin m) : ∑ j, k (r + j) = ∑ j, k j :=
  Equiv.sum_comp (Equiv.addLeft r) k

/-- **Lemma 3.2 (Raney suffix rotation).**  For `k : Fin m → ℕ` (`m ≥ 1`) with
`K = ∑ j, k j`, there is a rotation `r : Fin m` such that for every
`t ∈ {1, …, m}` the length-`t` suffix of the rotated sequence
`j ↦ k (r + j)`, i.e. indices `m − t, …, m − 1`, satisfies
`t * K ≤ m * ∑_{u < t} k (r + (m − t + u))`. -/
theorem exists_rotation (k : Fin m → ℕ) :
    ∃ r : Fin m, ∀ t : ℕ, 1 ≤ t → t ≤ m →
      t * (∑ j, k j) ≤ m * ∑ u ∈ range t, k (r + Fin.ofNat m (m - t + u)) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨r, hr, hmax⟩ :=
    Finset.exists_max_image (range m) (disc k) (nonempty_range_iff.mpr hm.ne')
  have hmax' : ∀ i, disc k i ≤ disc k r := fun i => by
    rw [disc_mod k i]
    exact hmax _ (mem_range.mpr (Nat.mod_lt _ hm))
  refine ⟨Fin.ofNat m r, fun t ht1 htm => ?_⟩
  -- rewrite the suffix as a window of the cyclic extension
  have hsuf : ∑ u ∈ range t, k (Fin.ofNat m r + Fin.ofNat m (m - t + u))
      = ∑ u ∈ range t, cyc k (r + (m - t) + u) := by
    apply Finset.sum_congr rfl
    intro u _
    unfold cyc
    congr 1
    rw [Fin.ofNat_add, Fin.val_ofNat]
    apply Fin.ext
    rw [Fin.val_ofNat, Fin.val_ofNat, Nat.add_mod_mod, add_assoc]
  have hS : psum k (r + m) =
      psum k (r + (m - t)) + ∑ u ∈ range t, cyc k (r + (m - t) + u) := by
    have : r + m = (r + (m - t)) + t := by omega
    rw [this, psum_add]
  rw [hsuf]
  have hD1 := hmax' (r + (m - t))
  have hD2 : disc k (r + m) = disc k r := disc_add_m k r
  unfold disc at hD1 hD2
  rw [hS] at hD2
  push_cast [Nat.cast_sub htm] at hD1 hD2
  zify
  nlinarith [hD1, hD2]

/-- Filter form of the suffix: the same inequality with the suffix written as
the sum over `j : Fin m` with `m − t ≤ j`. -/
theorem exists_rotation_filter (k : Fin m → ℕ) :
    ∃ r : Fin m, ∀ t : ℕ, 1 ≤ t → t ≤ m →
      t * (∑ j, k j) ≤
        m * ∑ j ∈ univ.filter (fun j : Fin m => m - t ≤ (j : ℕ)), k (r + j) := by
  obtain ⟨r, hr⟩ := exists_rotation k
  refine ⟨r, fun t ht1 htm => ?_⟩
  refine (hr t ht1 htm).trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_nbij' (fun u => Fin.ofNat m (m - t + u)) (fun j => (j : ℕ) - (m - t))
    ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [mem_range] at hu
    simp only [mem_filter, mem_univ, true_and, Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    simp only [mem_range]
    have := j.isLt; omega
  · intro u hu
    simp only [mem_range] at hu
    simp only [Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have := j.isLt
    apply Fin.ext
    simp only [Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · intro u _; rfl

end Raney


/-! ## Rotating an `MCycleData` (so that downstream may assume the Raney-rotated indexing) -/

namespace MCycleData

variable {m : ℕ} [NeZero m] (D : MCycleData m)

theorem start_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ m) : D.start a ≤ D.start b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    rw [D.start_succ' b (by omega)]
    exact (ih (by omega)).trans (Nat.le_add_right _ _)

theorem start_le_p {a : ℕ} (ha : a ≤ m) : D.start a ≤ D.p := by
  rw [← D.start_last]; exact D.start_mono ha le_rfl

theorem c_eq (i : ℕ) (hi : i < m) : D.c i = D.k ⟨i, hi⟩ + D.l ⟨i, hi⟩ := by
  simp [c, hi]

theorem x_shift (s i : ℕ) : collatzShortcut^[i] (D.x s) = D.x (i + s) := by
  unfold x; rw [← Function.iterate_add_apply]

/-- Orbit index (relative to `nmin r`) at which block `r + j` of `D` starts. -/
def rstart (r : Fin m) (j : ℕ) : ℕ :=
  if r.val + j ≤ m then D.start (r.val + j) - D.start r
  else D.start (r.val + j - m) + (D.p - D.start r)

theorem rstart_zero (r : Fin m) : D.rstart r 0 = 0 := by
  simp [rstart, r.isLt.le]

theorem rstart_last (r : Fin m) : D.rstart r m = D.p := by
  have hp := D.start_le_p r.isLt.le
  unfold rstart
  split_ifs with h
  · have hr : r.val = 0 := by omega
    rw [hr, Nat.zero_add, D.start_last, D.start_zero, Nat.sub_zero]
  · rw [show r.val + m - m = r.val by omega]
    omega

omit [NeZero m] in
/-- Block index `r + j` as a natural number: `r + j` or `r + j − m`. -/
theorem val_add_fin (r j : Fin m) :
    ((r + j : Fin m) : ℕ) = if r.val + j.val < m then r.val + j.val else r.val + j.val - m := by
  rw [Fin.val_add]
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rstart_succ (r j : Fin m) :
    D.rstart r (j.val + 1) = D.rstart r j.val + D.k (r + j) + D.l (r + j) := by
  have hj := j.isLt
  have hr := r.isLt
  unfold rstart
  by_cases h1 : r.val + (j.val + 1) ≤ m
  · have h2 : r.val + j.val ≤ m := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [← Nat.add_assoc, D.start_succ' _ (by omega), D.c_eq _ (by omega)]
    have hmono := D.start_mono (Nat.le_add_right r.val j.val) h2
    have hidx : (r + j : Fin m) = ⟨r.val + j.val, by omega⟩ := by
      apply Fin.ext; rw [val_add_fin]; simp only [show r.val + j.val < m by omega, ↓reduceIte]
    rw [hidx]
    omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : r.val + j.val ≤ m
    · -- `r + j = m`, block index wraps to `0`
      have heq : r.val + j.val = m := by omega
      simp only [h2, ↓reduceIte]
      rw [heq, D.start_last]
      have hidx : (r + j : Fin m) = ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩ := by
        apply Fin.ext; rw [val_add_fin]; simp [heq]
      rw [hidx, show r.val + (j.val + 1) - m = 0 + 1 by omega, D.start_succ' 0 (by omega),
        D.start_zero, D.c_eq 0 (by omega)]
      omega
    · simp only [h2, ↓reduceIte]
      rw [show r.val + (j.val + 1) - m = (r.val + j.val - m) + 1 by omega,
        D.start_succ' _ (by omega), D.c_eq _ (by omega)]
      have hidx : (r + j : Fin m) = ⟨r.val + j.val - m, by omega⟩ := by
        apply Fin.ext; rw [val_add_fin]; simp only [show ¬ r.val + j.val < m by omega, ↓reduceIte]
      rw [hidx]
      omega

/-- The orbit of `D` shifted by `start r`, read at the relative start of block `r + j`,
is the orbit of `D` at the start of block `r + j`. -/
theorem x_rstart (r j : Fin m) (t : ℕ) :
    D.x (D.rstart r j.val + t + D.start r) = D.x (D.start ((r + j : Fin m) : ℕ) + t) := by
  have hj := j.isLt
  have hr := r.isLt
  unfold rstart
  by_cases h1 : r.val + j.val ≤ m
  · simp only [h1, ↓reduceIte]
    have hmono := D.start_mono (Nat.le_add_right r.val j.val) h1
    rw [show D.start (r.val + j.val) - D.start r + t + D.start r = D.start (r.val + j.val) + t by
      omega]
    by_cases h2 : r.val + j.val < m
    · rw [val_add_fin]; simp only [h2, ↓reduceIte]
    · have heq : r.val + j.val = m := by omega
      rw [val_add_fin]; simp only [h2, ↓reduceIte]
      rw [heq, Nat.sub_self, D.start_zero, D.start_last, Nat.zero_add, Nat.add_comm, D.x_add_p]
  · simp only [h1, ↓reduceIte]
    rw [val_add_fin]; simp only [show ¬ r.val + j.val < m by omega, ↓reduceIte]
    have := D.start_le_p r.isLt.le
    rw [show D.start (r.val + j.val - m) + (D.p - D.start r) + t + D.start r =
      (D.start (r.val + j.val - m) + t) + D.p by omega, D.x_add_p]

/-- The rotation of `D` by `r`: the same cycle re-based at `nmin r`, block `j` ↦ block `r + j`. -/
def rotate (r : Fin m) : MCycleData m where
  n₀ := D.x (D.start r)
  p := D.p
  p_pos := D.p_pos
  periodic := by rw [D.x_shift, Nat.add_comm, D.x_add_p]
  nodup := by
    apply nodup_of_iterate_injOn
    intro i hi j hj hij
    rw [D.x_shift, D.x_shift] at hij
    have hmod : (i + D.start r) % D.p = (j + D.start r) % D.p := by
      apply D.x_injOn (Nat.mod_lt _ D.p_pos) (Nat.mod_lt _ D.p_pos)
      unfold x at hij ⊢
      rw [← iterate_mod_period D.periodic, ← iterate_mod_period D.periodic]
      exact hij
    have h2 : i % D.p = j % D.p := Nat.ModEq.add_right_cancel' (D.start r) hmod
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
  k := fun j => D.k (r + j)
  l := fun j => D.l (r + j)
  a := fun j => D.a (r + j)
  start := D.rstart r
  start_zero := D.rstart_zero r
  start_succ := D.rstart_succ r
  start_last := D.rstart_last r
  k_pos := fun j => D.k_pos _
  l_pos := fun j => D.l_pos _
  a_odd := fun j => D.a_odd _
  odd_step := fun j t ht => by
    rw [D.x_shift, D.x_rstart]
    exact D.odd_step (r + j) t ht
  even_step := fun j t ht => by
    rw [D.x_shift, Nat.add_assoc (D.rstart r j), D.x_rstart, ← Nat.add_assoc]
    exact D.even_step (r + j) t ht
  lower := fun i => by rw [D.x_shift]; exact D.lower _

@[simp] theorem rotate_p (r : Fin m) : (D.rotate r).p = D.p := rfl
@[simp] theorem rotate_k (r j : Fin m) : (D.rotate r).k j = D.k (r + j) := rfl
@[simp] theorem rotate_l (r j : Fin m) : (D.rotate r).l j = D.l (r + j) := rfl
@[simp] theorem rotate_a (r j : Fin m) : (D.rotate r).a j = D.a (r + j) := rfl

@[simp] theorem rotate_K (r : Fin m) : (D.rotate r).K = D.K :=
  Raney.sum_rotate D.k r

@[simp] theorem rotate_L (r : Fin m) : (D.rotate r).L = D.L :=
  Raney.sum_rotate D.l r

@[simp] theorem rotate_x (r : Fin m) (i : ℕ) : (D.rotate r).x i = D.x (i + D.start r) :=
  D.x_shift _ _

@[simp] theorem rotate_nmin (r j : Fin m) : (D.rotate r).nmin j = D.nmin (r + j) := by
  show (D.rotate r).x (D.rstart r j) = D.x (D.start ((r + j : Fin m) : ℕ))
  have := D.x_rstart r j 0
  rw [Nat.add_zero, Nat.add_zero] at this
  rw [rotate_x, this]

@[simp] theorem rotate_peak (r j : Fin m) : (D.rotate r).peak j = D.peak (r + j) := by
  show (D.rotate r).x (D.rstart r j + D.k (r + j)) =
    D.x (D.start ((r + j : Fin m) : ℕ) + D.k (r + j))
  rw [rotate_x, D.x_rstart]

/-- Rotating an `MCycleData` by `r` yields an `MCycleData` with the same `p`, `K`, `L`
whose block `j` is block `r + j` of the original. -/
theorem exists_rotate (r : Fin m) :
    ∃ D' : MCycleData m, D'.p = D.p ∧ D'.K = D.K ∧ D'.L = D.L ∧
      (∀ j, D'.k j = D.k (r + j)) ∧ (∀ j, D'.l j = D.l (r + j)) ∧ (∀ j, D'.a j = D.a (r + j)) ∧
      (∀ j, D'.nmin j = D.nmin (r + j)) ∧ (∀ j, D'.peak j = D.peak (r + j)) :=
  ⟨D.rotate r, rfl, D.rotate_K r, D.rotate_L r, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    D.rotate_nmin r, D.rotate_peak r⟩

/-- **Lemma 3.2 for an `m`-cycle.**  Some rotation of `D` (same `p`, `K`, `L`) satisfies the
Raney suffix bound `t * K ≤ m * ∑_{u<t} k (m − t + u)` for every `t ∈ {1, …, m}`. -/
theorem exists_raney :
    ∃ D' : MCycleData m, D'.p = D.p ∧ D'.K = D.K ∧ D'.L = D.L ∧
      ∀ t : ℕ, 1 ≤ t → t ≤ m →
        t * D'.K ≤ m * ∑ u ∈ Finset.range t, D'.k (Fin.ofNat m (m - t + u)) := by
  obtain ⟨r, hr⟩ := Raney.exists_rotation D.k
  exact ⟨D.rotate r, rfl, D.rotate_K r, D.rotate_L r, fun t ht1 htm => by
    rw [rotate_K]; exact hr t ht1 htm⟩

end MCycleData

end CollatzMCycles
