module

public import Mathlib

/-!
# Padé kernel algebra (Track B kernel), all in `ℤ[X]`

Kernel: `F_k(x) = N₁(x)^k / (x (70 − x))^{2k+1}`,
`N₁(x) = (x−28)(x−30)(x−35)²(x−40)(x−42)`.

We construct, purely algebraically in `ℤ[X]` (no power series, no complex analysis),
polynomials `Ut k` (= `70·U`) of degree `≤ 2k` and `Pt k` (= `70·P`) of degree `≤ 2k − 2` with the
exact partial-fraction identity

  `70 · N₁^k = (X (70 − X))^{2k+1} · Pt + Ut(X) · (70 − X)^{2k+1} + Ut(70 − X) · X^{2k+1}`,

and the integrality `(Ut k).coeff j = 420^{2k−j} · û_j` with `û_j ∈ ℤ`
(`Uhat k := B₁^k · S^{2k+1} mod X^{2k+1}`, `B₁(w) = N₁(420 w)/864360000`, `S = Σ_{j≤2k} (6X)^j`).
We also bound `|û_{2k}| ≤ 2 · 21600^k` by a weighted-ℓ¹ (majorant) argument.
-/

@[expose] public section
namespace CollatzMCycles.Diophantine

open Polynomial Finset

noncomputable section

/-- `N₁(X) = (X−28)(X−30)(X−35)²(X−40)(X−42)`. -/
def N1 : ℤ[X] := (X - C 28) * (X - C 30) * (X - C 35) ^ 2 * (X - C 40) * (X - C 42)

/-- `B₁(w)` with `N₁(420 w) = 864360000 · B₁(w)`. -/
def B1 : ℤ[X] :=
  (1 - C 15 * X) * (1 - C 14 * X) * (1 - C 12 * X) ^ 2 * (2 - C 21 * X) * (1 - C 10 * X)

theorem N1_comp_scale : N1.comp (C 420 * X) = C 864360000 * B1 := by
  apply Polynomial.funext
  intro r
  simp [N1, B1]
  ring

theorem N1_comp_refl : N1.comp (C 70 - X) = N1 := by
  apply Polynomial.funext
  intro r
  simp [N1]
  ring

theorem comp_refl_refl (f : ℤ[X]) : (f.comp (C 70 - X)).comp (C 70 - X) = f := by
  rw [comp_assoc]
  simp

/-- `S_k = Σ_{j ≤ 2k} (6X)^j`. -/
def S (k : ℕ) : ℤ[X] := ∑ j ∈ range (2 * k + 1), (C 6 * X) ^ j

theorem S_mul : S k * (1 - C 6 * X) = 1 - (C 6 * X) ^ (2 * k + 1) := geom_sum_mul_neg _ _

/-- `Û_k = B₁^k S_k^{2k+1} mod X^{2k+1}`. -/
def Uhat (k : ℕ) : ℤ[X] := (B1 ^ k * S k ^ (2 * k + 1)) %ₘ X ^ (2 * k + 1)

theorem Uhat_coeff_eq_zero {k n : ℕ} (hn : 2 * k < n) : (Uhat k).coeff n = 0 := by
  apply coeff_eq_zero_of_degree_lt
  calc (Uhat k).degree < (X ^ (2 * k + 1) : ℤ[X]).degree := degree_modByMonic_lt _ (monic_X_pow _)
    _ = (2 * k + 1 : ℕ) := degree_X_pow _
    _ ≤ n := by exact_mod_cast hn

theorem Uhat_natDegree_le (k : ℕ) : (Uhat k).natDegree ≤ 2 * k :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hn => Uhat_coeff_eq_zero hn

theorem X_pow_dvd_B1_sub (k : ℕ) :
    X ^ (2 * k + 1) ∣ B1 ^ k - Uhat k * (1 - C 6 * X) ^ (2 * k + 1) := by
  set m := 2 * k + 1
  set q := (B1 ^ k * S k ^ m) /ₘ X ^ m
  have hmod : Uhat k + X ^ m * q = B1 ^ k * S k ^ m := modByMonic_add_div _ (X ^ m)
  have hS : S k * (1 - C 6 * X) = 1 - (C 6 * X) ^ m := S_mul
  have key : B1 ^ k - Uhat k * (1 - C 6 * X) ^ m =
      B1 ^ k * (1 - (1 - (C 6 * X) ^ m) ^ m) + X ^ m * (q * (1 - C 6 * X) ^ m) := by
    rw [← hS, mul_pow]
    linear_combination (-(1 - C 6 * X) ^ m) * hmod
  rw [key]
  apply dvd_add
  · apply Dvd.dvd.mul_left
    have h1 : (1 : ℤ[X]) - (1 - (C 6 * X) ^ m) ∣ 1 ^ m - (1 - (C 6 * X) ^ m) ^ m :=
      sub_dvd_pow_sub_pow _ _ _
    rw [one_pow] at h1
    refine dvd_trans ?_ h1
    rw [sub_sub_cancel, mul_pow]
    exact Dvd.intro_left _ rfl
  · exact Dvd.intro _ rfl

/-- `Ũ_k = 70 · U_k = Σ_j 420^{2k−j} û_j X^j`. -/
def Ut (k : ℕ) : ℤ[X] := ∑ j ∈ range (2 * k + 1), C (420 ^ (2 * k - j) * (Uhat k).coeff j) * X ^ j

theorem Ut_coeff (k n : ℕ) :
    (Ut k).coeff n = if n ≤ 2 * k then 420 ^ (2 * k - n) * (Uhat k).coeff n else 0 := by
  simp only [Ut, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

theorem Ut_coeff_of_le {k n : ℕ} (hn : n ≤ 2 * k) :
    (Ut k).coeff n = 420 ^ (2 * k - n) * (Uhat k).coeff n := by
  rw [Ut_coeff, ite_eq_left_iff.mpr fun h => absurd hn h]

theorem Ut_natDegree_le (k : ℕ) : (Ut k).natDegree ≤ 2 * k :=
  natDegree_le_iff_coeff_eq_zero.mpr fun n hn => by
    rw [Ut_coeff, ite_eq_right_iff.mpr fun h => absurd h (by omega)]

theorem Ut_comp_scale (k : ℕ) : (Ut k).comp (C 420 * X) = C (420 ^ (2 * k)) * Uhat k := by
  ext n
  rw [comp_C_mul_X_coeff, coeff_C_mul, Ut_coeff]
  split_ifs with h
  · rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_of_le h]
  · rw [Uhat_coeff_eq_zero (by omega), mul_zero, zero_mul]

theorem scale_const (k : ℕ) : (420 : ℤ) ^ (2 * k) * 70 ^ (2 * k + 1) = 70 * 864360000 ^ k := by
  rw [show (864360000 : ℤ) = 420 ^ 2 * 70 ^ 2 by norm_num, mul_pow, ← pow_mul, ← pow_mul]
  ring

/-- The main congruence `X^{2k+1} ∣ 70 N₁^k − Ũ (70 − X)^{2k+1}`. -/
theorem X_pow_dvd_main (k : ℕ) :
    X ^ (2 * k + 1) ∣ C 70 * N1 ^ k - Ut k * (C 70 - X) ^ (2 * k + 1) := by
  set m := 2 * k + 1
  set f := C 70 * N1 ^ k - Ut k * (C 70 - X) ^ m with hf
  have hcomp : f.comp (C 420 * X) =
      C (70 * 864360000 ^ k) * (B1 ^ k - Uhat k * (1 - C 6 * X) ^ m) := by
    have h70 : (C 70 - X : ℤ[X]).comp (C 420 * X) = C 70 * (1 - C 6 * X) := by
      simp only [sub_comp, C_comp, X_comp]
      rw [show (C 420 : ℤ[X]) = C 70 * C 6 by rw [← C_mul]; norm_num]
      ring
    rw [hf, sub_comp, mul_comp, mul_comp, pow_comp, pow_comp, C_comp, N1_comp_scale,
      Ut_comp_scale, h70, mul_pow, mul_pow, ← C_pow, ← C_pow]
    have hsc : (C 70 : ℤ[X]) * C (864360000 ^ k) = C (70 * 864360000 ^ k) := by rw [← C_mul]
    have : (C (420 ^ (2 * k)) : ℤ[X]) * C (70 ^ m) = C (70 * 864360000 ^ k) := by
      rw [← C_mul, scale_const]
    linear_combination (B1 ^ k) * hsc - (Uhat k * (1 - C 6 * X) ^ m) * this
  have hdvd := X_pow_dvd_B1_sub k
  rw [X_pow_dvd_iff] at hdvd ⊢
  intro d hd
  have h1 := congrArg (fun p => p.coeff d) hcomp
  rw [comp_C_mul_X_coeff, coeff_C_mul, hdvd d hd, mul_zero] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ (by norm_num))

/-- Numerator `Num_k = 70 N₁^k − Ũ(X)(70−X)^{2k+1} − Ũ(70−X) X^{2k+1}`. -/
def Num (k : ℕ) : ℤ[X] :=
  C 70 * N1 ^ k - Ut k * (C 70 - X) ^ (2 * k + 1) - (Ut k).comp (C 70 - X) * X ^ (2 * k + 1)

theorem X_pow_dvd_Num (k : ℕ) : X ^ (2 * k + 1) ∣ Num k :=
  dvd_sub (X_pow_dvd_main k) (dvd_mul_left _ _)

theorem Num_comp_refl (k : ℕ) : (Num k).comp (C 70 - X) = Num k := by
  simp only [Num, sub_comp, mul_comp, pow_comp, C_comp, X_comp, N1_comp_refl, comp_refl_refl,
    sub_sub_cancel]
  ring

theorem seventy_sub_pow_dvd_Num (k : ℕ) : (C 70 - X) ^ (2 * k + 1) ∣ Num k := by
  rcases X_pow_dvd_Num k with ⟨q, hq⟩
  refine ⟨q.comp (C 70 - X), ?_⟩
  have h := congrArg (fun p => p.comp (C 70 - X)) hq
  rw [Num_comp_refl, mul_comp, pow_comp, X_comp] at h
  exact h

/-- The monic denominator `d_k = (X (X − 70))^{2k+1}`. -/
def dmon (k : ℕ) : ℤ[X] := (X * (X - C 70)) ^ (2 * k + 1)

theorem dmon_monic (k : ℕ) : (dmon k).Monic := (monic_X.mul (monic_X_sub_C 70)).pow _

theorem dmon_natDegree (k : ℕ) : (dmon k).natDegree = 2 * (2 * k + 1) := by
  rw [dmon, (monic_X.mul (monic_X_sub_C (70 : ℤ))).natDegree_pow, monic_X.natDegree_mul
    (monic_X_sub_C 70), natDegree_X, natDegree_X_sub_C]
  ring

theorem neg_dmon (k : ℕ) : -dmon k = (X * (C 70 - X)) ^ (2 * k + 1) := by
  rw [dmon, show (X * (C 70 - X) : ℤ[X]) = -(X * (X - C 70)) by ring, Odd.neg_pow ⟨k, rfl⟩]

theorem isCoprime_X_seventy : IsCoprime (X : ℚ[X]) (70 - X) :=
  ⟨C (1 / 70), C (1 / 70), by
    have h : C (1 / 70 : ℚ) * (70 : ℚ[X]) = 1 := by
      rw [show (70 : ℚ[X]) = C 70 by rfl, ← C_mul]; norm_num
    linear_combination h⟩

theorem mul_pow_dvd_of_dvd {m : ℕ} {p : ℚ[X]}
    (h1 : X ^ m ∣ p) (h2 : (70 - X) ^ m ∣ p) : (X * (70 - X)) ^ m ∣ p := by
  rw [mul_pow]
  exact (isCoprime_X_seventy.pow (m := m) (n := m)).mul_dvd h1 h2

theorem dmon_dvd_Num (k : ℕ) : dmon k ∣ Num k := by
  have hQ : (dmon k).map (Int.castRingHom ℚ) ∣ (Num k).map (Int.castRingHom ℚ) := by
    have h1 := map_dvd (Polynomial.mapRingHom (Int.castRingHom ℚ)) (X_pow_dvd_Num k)
    have h2 := map_dvd (Polynomial.mapRingHom (Int.castRingHom ℚ)) (seventy_sub_pow_dvd_Num k)
    have hC70 : Polynomial.map (Int.castRingHom ℚ) (C 70) = 70 := by simp
    simp only [coe_mapRingHom, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, hC70]
      at h1 h2
    have h3 := mul_pow_dvd_of_dvd h1 h2
    have h4 : -(dmon k).map (Int.castRingHom ℚ) = (X * (70 - X)) ^ (2 * k + 1) := by
      have := congrArg (Polynomial.map (Int.castRingHom ℚ)) (neg_dmon k)
      simpa using this
    rw [← neg_dvd, h4]
    exact h3
  have hmonic := dmon_monic k
  rw [← modByMonic_eq_zero_iff_dvd hmonic]
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [Polynomial.map_modByMonic _ hmonic, Polynomial.map_zero,
    modByMonic_eq_zero_iff_dvd (hmonic.map _)]
  exact hQ

/-- `P̃_k = 70 · P_k`, the polynomial part. -/
def Pt (k : ℕ) : ℤ[X] := -(Num k /ₘ dmon k)

theorem Num_eq (k : ℕ) : Num k = (X * (C 70 - X)) ^ (2 * k + 1) * Pt k := by
  have h := modByMonic_add_div (Num k) (dmon k)
  rw [(modByMonic_eq_zero_iff_dvd (dmon_monic k)).mpr (dmon_dvd_Num k), zero_add] at h
  rw [Pt, ← neg_dmon, neg_mul_neg, h]

theorem N1_natDegree_le : N1.natDegree ≤ 6 := by
  unfold N1
  compute_degree!

theorem Num_natDegree_le (k : ℕ) : (Num k).natDegree ≤ 6 * k + 1 := by
  unfold Num
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_)) ?_)
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_pow_le).trans ?_
    have := N1_natDegree_le
    nlinarith
  · refine (natDegree_mul_le).trans ?_
    have h1 := Ut_natDegree_le k
    have h2 : ((C 70 - X : ℤ[X]) ^ (2 * k + 1)).natDegree ≤ 2 * k + 1 := by
      refine natDegree_pow_le.trans ?_
      have : (C 70 - X : ℤ[X]).natDegree ≤ 1 := by compute_degree!
      nlinarith
    omega
  · refine (natDegree_mul_le).trans ?_
    have h1 : ((Ut k).comp (C 70 - X)).natDegree ≤ 2 * k := by
      refine natDegree_comp_le.trans ?_
      have : (C 70 - X : ℤ[X]).natDegree ≤ 1 := by compute_degree!
      have := Ut_natDegree_le k
      nlinarith
    rw [natDegree_X_pow]
    omega

theorem Pt_natDegree_le (k : ℕ) : (Pt k).natDegree ≤ 2 * k - 1 := by
  rw [Pt, natDegree_neg, natDegree_divByMonic (Num k) (dmon_monic k), dmon_natDegree]
  have := Num_natDegree_le k
  omega

theorem Pt_coeff_eq_zero {k n : ℕ} (hn : 2 * k ≤ n) : (Pt k).coeff n = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hnum : (Num 0).natDegree < (dmon 0).natDegree := by
      rw [dmon_natDegree]
      have := Num_natDegree_le 0
      omega
    have hdiv : Num 0 /ₘ dmon 0 = 0 := divByMonic_eq_zero_iff (dmon_monic 0) |>.mpr
      (degree_lt_degree hnum)
    simp [Pt, hdiv]
  · apply coeff_eq_zero_of_natDegree_lt
    have := Pt_natDegree_le k
    omega

/-! ### Truncated weighted-ℓ¹ norm and coefficient bound on `Uhat k` -/

/-- Truncated weighted-ℓ¹ norm `∑_{i < N} |p_i| (1/32)^i` in `ℚ`. -/
def tnorm (N : ℕ) (p : ℤ[X]) : ℚ :=
  ∑ i ∈ range N, |(p.coeff i : ℚ)| * (1 / 32 : ℚ) ^ i

theorem tnorm_nonneg (N : ℕ) (p : ℤ[X]) : 0 ≤ tnorm N p :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (by positivity)

theorem tnorm_mono {M N : ℕ} (h : M ≤ N) (p : ℤ[X]) : tnorm M p ≤ tnorm N p :=
  sum_le_sum_of_subset_of_nonneg (range_mono h) fun _ _ _ => mul_nonneg (abs_nonneg _) (by positivity)

theorem coeff_le_tnorm {N n : ℕ} (hn : n < N) (p : ℤ[X]) :
    |(p.coeff n : ℚ)| * (1 / 32 : ℚ) ^ n ≤ tnorm N p := by
  rw [tnorm]
  exact single_le_sum (f := fun i => |(p.coeff i : ℚ)| * (1 / 32 : ℚ) ^ i)
    (fun _ _ => mul_nonneg (abs_nonneg _) (by positivity)) (mem_range.mpr hn)

theorem tnorm_add_le (N : ℕ) (p q : ℤ[X]) : tnorm N (p + q) ≤ tnorm N p + tnorm N q := by
  rw [tnorm, tnorm, tnorm, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [coeff_add, Int.cast_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (by positivity)

theorem tnorm_sub_le (N : ℕ) (p q : ℤ[X]) : tnorm N (p - q) ≤ tnorm N p + tnorm N q := by
  rw [tnorm, tnorm, tnorm, ← sum_add_distrib]
  refine sum_le_sum fun i _ => ?_
  rw [coeff_sub, Int.cast_sub, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_sub _ _) (by positivity)

theorem tnorm_C_mul (N : ℕ) (a : ℤ) (p : ℤ[X]) :
    tnorm N (C a * p) = |(a : ℚ)| * tnorm N p := by
  simp only [tnorm, mul_sum, coeff_C_mul, Int.cast_mul, abs_mul, mul_assoc]

theorem tnorm_X_mul_le (N : ℕ) (p : ℤ[X]) :
    tnorm N (X * p) ≤ (1 / 32 : ℚ) * tnorm N p := by
  rcases N with _ | M
  · simp [tnorm]
  · rw [tnorm, sum_range_succ', coeff_X_mul_zero, Int.cast_zero, abs_zero, zero_mul, add_zero]
    have h1 : (∑ k ∈ range M, |((X * p).coeff (k + 1) : ℚ)| * (1 / 32 : ℚ) ^ (k + 1)) =
        (1 / 32 : ℚ) * tnorm M p := by
      rw [tnorm, mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [coeff_X_mul, pow_succ]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (tnorm_mono (Nat.le_succ M) p) (by positivity)

theorem tnorm_linear_mul_le (N : ℕ) {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℤ[X]) :
    tnorm N ((C a - C b * X) * p) ≤ ((a : ℚ) + (b : ℚ) / 32) * tnorm N p := by
  have heq : (C a - C b * X) * p = C a * p - C b * (X * p) := by ring
  rw [heq]
  have h1 := tnorm_sub_le N (C a * p) (C b * (X * p))
  have ha' : (0 : ℚ) ≤ a := by positivity
  have hb' : (0 : ℚ) ≤ b := by positivity
  rw [tnorm_C_mul, tnorm_C_mul, abs_of_nonneg ha', abs_of_nonneg hb'] at h1
  have h2 := mul_le_mul_of_nonneg_left (tnorm_X_mul_le N p) hb'
  linarith

theorem tnorm_linear_chain {N : ℕ} {a b : ℤ} {M : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {q p : ℤ[X]} (hq : tnorm N q ≤ M * tnorm N p) :
    tnorm N ((C a - C b * X) * q) ≤ (((a : ℚ) + (b : ℚ) / 32) * M) * tnorm N p := by
  have h1 := tnorm_linear_mul_le N ha hb q
  have h2 : 0 ≤ (a : ℚ) + (b : ℚ) / 32 := by
    have : (0 : ℚ) ≤ a := by positivity
    have : (0 : ℚ) ≤ b := by positivity
    linarith
  calc tnorm N ((C a - C b * X) * q) ≤ ((a : ℚ) + (b : ℚ) / 32) * tnorm N q := h1
    _ ≤ ((a : ℚ) + (b : ℚ) / 32) * (M * tnorm N p) := mul_le_mul_of_nonneg_left hq h2
    _ = (((a : ℚ) + (b : ℚ) / 32) * M) * tnorm N p := by ring

theorem tnorm_B1_mul_le (N : ℕ) (p : ℤ[X]) : tnorm N (B1 * p) ≤ 14 * tnorm N p := by
  have heq : B1 * p =
      (C 1 - C 15 * X) * ((C 1 - C 14 * X) * ((C 1 - C 12 * X) *
        ((C 1 - C 12 * X) * ((C 2 - C 21 * X) * ((C 1 - C 10 * X) * p))))) := by
    unfold B1
    simp only [map_one, map_ofNat]
    ring
  rw [heq]
  have h0 : tnorm N p ≤ 1 * tnorm N p := by ring_nf; rfl
  have h1 := tnorm_linear_chain (a := 1) (b := 10) (by norm_num) (by norm_num) h0
  have h2 := tnorm_linear_chain (a := 2) (b := 21) (by norm_num) (by norm_num) h1
  have h3 := tnorm_linear_chain (a := 1) (b := 12) (by norm_num) (by norm_num) h2
  have h4 := tnorm_linear_chain (a := 1) (b := 12) (by norm_num) (by norm_num) h3
  have h5 := tnorm_linear_chain (a := 1) (b := 14) (by norm_num) (by norm_num) h4
  have h6 := tnorm_linear_chain (a := 1) (b := 15) (by norm_num) (by norm_num) h5
  refine h6.trans (mul_le_mul_of_nonneg_right (by norm_num) (tnorm_nonneg N p))

theorem tnorm_B1_pow_mul_le (N k : ℕ) (p : ℤ[X]) :
    tnorm N (B1 ^ k * p) ≤ 14 ^ k * tnorm N p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    calc tnorm N (B1 * (B1 ^ k * p)) ≤ 14 * tnorm N (B1 ^ k * p) := tnorm_B1_mul_le N _
      _ ≤ 14 * (14 ^ k * tnorm N p) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 14 ^ (k + 1) * tnorm N p := by rw [pow_succ', mul_assoc]

def S_aux (m : ℕ) : ℤ[X] := ∑ j ∈ range m, (C 6 * X) ^ j

theorem S_aux_succ (m : ℕ) : S_aux (m + 1) = 1 + C 6 * X * S_aux m := by
  rw [S_aux, sum_range_succ', pow_zero, add_comm]
  congr 1
  rw [S_aux, mul_sum]
  refine sum_congr rfl fun j _ => by rw [pow_succ']

theorem tnorm_S_aux_mul_le (N m : ℕ) (p : ℤ[X]) :
    tnorm N (S_aux m * p) ≤ (16 / 13 : ℚ) * tnorm N p := by
  induction m with
  | zero =>
    simp only [S_aux, range_zero, sum_empty, zero_mul, tnorm, coeff_zero, Int.cast_zero,
      abs_zero, zero_mul, sum_const_zero]
    exact mul_nonneg (by norm_num) (tnorm_nonneg N p)
  | succ m ih =>
    have heq : S_aux (m + 1) * p = p + C 6 * (X * (S_aux m * p)) := by
      rw [S_aux_succ]; ring
    rw [heq]
    have h1 := tnorm_add_le N p (C 6 * (X * (S_aux m * p)))
    rw [tnorm_C_mul] at h1
    have h2 := tnorm_X_mul_le N (S_aux m * p)
    have h3 : |((6 : ℤ) : ℚ)| = 6 := by norm_num
    rw [h3] at h1
    linarith

theorem tnorm_S_pow_mul_le (N k m : ℕ) (p : ℤ[X]) :
    tnorm N (S k ^ m * p) ≤ (16 / 13 : ℚ) ^ m * tnorm N p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc]
    have hS : S k = S_aux (2 * k + 1) := rfl
    calc tnorm N (S k * (S k ^ m * p)) ≤ (16 / 13 : ℚ) * tnorm N (S k ^ m * p) := by
          rw [hS]; exact tnorm_S_aux_mul_le N (2 * k + 1) _
      _ ≤ (16 / 13 : ℚ) * ((16 / 13 : ℚ) ^ m * tnorm N p) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (16 / 13 : ℚ) ^ (m + 1) * tnorm N p := by rw [pow_succ', mul_assoc]

theorem tnorm_one_le (N : ℕ) : tnorm N 1 ≤ 1 := by
  rcases N with _ | M
  · simp [tnorm]
  · rw [tnorm, sum_range_succ', coeff_one_zero, Int.cast_one, abs_one, pow_zero, mul_one]
    have h0 : (∑ k ∈ range M, |((1 : ℤ[X]).coeff (k + 1) : ℚ)| * (1 / 32 : ℚ) ^ (k + 1)) = 0 := by
      refine sum_eq_zero fun i _ => ?_
      rw [ (show (1 : ℤ[X]).coeff (i + 1) = 0 by simp [coeff_one]), Int.cast_zero, abs_zero,
        zero_mul]
    linarith

theorem Uhat_coeff_two_mul_eq (k : ℕ) :
    (Uhat k).coeff (2 * k) = (B1 ^ k * S k ^ (2 * k + 1)).coeff (2 * k) := by
  set m := 2 * k + 1
  have hmod := modByMonic_add_div (B1 ^ k * S k ^ m) (X ^ m)
  have h1 := congrArg (fun p => p.coeff (2 * k)) hmod
  have hdvd : X ^ m ∣ X ^ m * ((B1 ^ k * S k ^ m) /ₘ X ^ m) := dvd_mul_right _ _
  have hzero : (X ^ m * ((B1 ^ k * S k ^ m) /ₘ X ^ m)).coeff (2 * k) = 0 :=
    (X_pow_dvd_iff.mp hdvd) (2 * k) (by omega)
  simp only [coeff_add, hzero, add_zero] at h1
  exact h1

theorem Uhat_top_coeff_abs_le (k : ℕ) :
    |(Uhat k).coeff (2 * k)| ≤ 2 * 21720 ^ k := by
  have hle : |((Uhat k).coeff (2 * k) : ℚ)| * (1 / 32 : ℚ) ^ (2 * k) ≤
      14 ^ k * (16 / 13 : ℚ) ^ (2 * k + 1) := by
    rw [Uhat_coeff_two_mul_eq]
    calc |((B1 ^ k * S k ^ (2 * k + 1)).coeff (2 * k) : ℚ)| * (1 / 32 : ℚ) ^ (2 * k)
        ≤ tnorm (2 * k + 1) (B1 ^ k * S k ^ (2 * k + 1)) :=
          coeff_le_tnorm (by omega) _
      _ = tnorm (2 * k + 1) (B1 ^ k * (S k ^ (2 * k + 1) * 1)) := by rw [mul_one]
      _ ≤ 14 ^ k * tnorm (2 * k + 1) (S k ^ (2 * k + 1) * 1) := tnorm_B1_pow_mul_le _ _ _
      _ ≤ 14 ^ k * ((16 / 13 : ℚ) ^ (2 * k + 1) * tnorm (2 * k + 1) 1) :=
          mul_le_mul_of_nonneg_left (tnorm_S_pow_mul_le _ _ _ _) (by positivity)
      _ ≤ 14 ^ k * ((16 / 13 : ℚ) ^ (2 * k + 1) * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (tnorm_one_le _) (by positivity)) (by positivity)
      _ = 14 ^ k * (16 / 13 : ℚ) ^ (2 * k + 1) := by ring
  have hmul : |((Uhat k).coeff (2 * k) : ℚ)| ≤
      (16 / 13 : ℚ) * (14 * 32 ^ 2 * (16 / 13 : ℚ) ^ 2) ^ k := by
    have h32 : (0 : ℚ) < 32 ^ (2 * k) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hle h32.le
    have hcancel : (1 / 32 : ℚ) ^ (2 * k) * 32 ^ (2 * k) = 1 := by
      rw [← mul_pow]; norm_num
    rw [mul_assoc, hcancel, mul_one] at h2
    refine h2.trans (le_of_eq ?_)
    rw [pow_succ, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    ring
  have hbound : |((Uhat k).coeff (2 * k) : ℚ)| ≤ 2 * (21720 : ℚ) ^ k := by
    refine hmul.trans ?_
    have hbase : (14 * 32 ^ 2 * (16 / 13 : ℚ) ^ 2) ≤ 21720 := by norm_num
    have hpow : (14 * 32 ^ 2 * (16 / 13 : ℚ) ^ 2) ^ k ≤ (21720 : ℚ) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have h16 : (16 / 13 : ℚ) ≤ 2 := by norm_num
    calc (16 / 13 : ℚ) * (14 * 32 ^ 2 * (16 / 13 : ℚ) ^ 2) ^ k
        ≤ 2 * (14 * 32 ^ 2 * (16 / 13 : ℚ) ^ 2) ^ k :=
          mul_le_mul_of_nonneg_right h16 (by positivity)
      _ ≤ 2 * (21720 : ℚ) ^ k := mul_le_mul_of_nonneg_left hpow (by positivity)
  exact_mod_cast hbound

end

end CollatzMCycles.Diophantine
