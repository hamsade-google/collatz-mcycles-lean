module

public import CollatzMCycles.Diophantine.Lcm
public import CollatzMCycles.Diophantine.PadeAlgebra

/-!
# Padé integrals, denominator clearing, and pointwise/integral bounds

We evaluate `J1 k = ∫ x in 35..40, F k x` and `J2 k = ∫ x in 35..42, F k x` via an explicit
antiderivative `Phi k` on `(0, 70)`, clear denominators by `70 · 4^k · D (2*k)`, and establish
the upper and lower integral bounds for odd `k`.
-/

@[expose] public section
namespace CollatzMCycles.Diophantine

open Polynomial Finset intervalIntegral

noncomputable section

/-! ### Part 1: Real kernel and polynomial evaluation -/

def N1_real (x : ℝ) : ℝ := (x - 28) * (x - 30) * (x - 35) ^ 2 * (x - 40) * (x - 42)

def F (k : ℕ) (x : ℝ) : ℝ := N1_real x ^ k / (x * (70 - x)) ^ (2 * k + 1)

theorem Pt_eq_sum (k : ℕ) : Pt k = ∑ j ∈ range (2 * k), C ((Pt k).coeff j) * X ^ j := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    exact Pt_coeff_eq_zero (by omega)

theorem Ut_eq_sum (k : ℕ) : Ut k = ∑ j ∈ range (2 * k + 1), C ((Ut k).coeff j) * X ^ j := by
  ext n
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [mem_range] at h
    rw [Ut_coeff, ite_eq_right_iff.mpr fun hle => absurd hle (by omega)]

theorem eval_N1 (x : ℝ) : (N1.map (Int.castRingHom ℝ)).eval x = N1_real x := by
  simp [N1, N1_real]

theorem eval_Pt (k : ℕ) (x : ℝ) :
    ((Pt k).map (Int.castRingHom ℝ)).eval x =
      ∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * x ^ j := by
  conv_lhs => rw [Pt_eq_sum k]
  simp [Polynomial.map_sum, Polynomial.eval_finsetSum]

theorem eval_Ut (k : ℕ) (x : ℝ) :
    ((Ut k).map (Int.castRingHom ℝ)).eval x =
      ∑ j ∈ range (2 * k + 1), ((Ut k).coeff j : ℝ) * x ^ j := by
  conv_lhs => rw [Ut_eq_sum k]
  simp [Polynomial.map_sum, Polynomial.eval_finsetSum]

theorem eval_Ut_comp_refl (k : ℕ) (x : ℝ) :
    (((Ut k).comp (C 70 - X)).map (Int.castRingHom ℝ)).eval x =
      ∑ j ∈ range (2 * k + 1), ((Ut k).coeff j : ℝ) * (70 - x) ^ j := by
  rw [Polynomial.map_comp, Polynomial.eval_comp]
  have h70 : ((C 70 - X : ℤ[X]).map (Int.castRingHom ℝ)).eval x = 70 - x := by simp
  rw [h70, eval_Ut]

/-- Real evaluation of `Num_eq`:
`70 * N1_real x ^ k = (x*(70-x))^{2k+1} * Pt(x) + Ut(x)*(70-x)^{2k+1} + Ut(70-x)*x^{2k+1}`. -/
theorem seventy_mul_N1_pow_eq (k : ℕ) (x : ℝ) :
    70 * N1_real x ^ k =
      (x * (70 - x)) ^ (2 * k + 1) * (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * x ^ j) +
      (∑ j ∈ range (2 * k + 1), ((Ut k).coeff j : ℝ) * x ^ j) * (70 - x) ^ (2 * k + 1) +
      (∑ j ∈ range (2 * k + 1), ((Ut k).coeff j : ℝ) * (70 - x) ^ j) * x ^ (2 * k + 1) := by
  have h := congrArg (fun p : ℤ[X] => (p.map (Int.castRingHom ℝ)).eval x) (Num_eq k)
  unfold Num at h
  have hC70 : ((C 70 : ℤ[X]).map (Int.castRingHom ℝ)).eval x = 70 := by simp
  have hcomp := eval_Ut_comp_refl k x
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, eval_N1, eval_Pt, eval_Ut, hC70, hcomp] at h
  linarith

/-! ### Part 2: Explicit antiderivative `Phi k` and FTC on `[35, C]` -/

def Phi (k : ℕ) (x : ℝ) : ℝ :=
  ((Uhat k).coeff (2 * k) : ℝ) * (Real.log x - Real.log (70 - x)) +
  (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * (x ^ (j + 1) / (j + 1 : ℝ))) +
  (∑ j ∈ range (2 * k), (((Ut k).coeff j : ℝ) / (2 * k - j : ℕ)) *
    (((70 - x) ^ (2 * k - j))⁻¹ - (x ^ (2 * k - j))⁻¹))

def rho_scaled (k : ℕ) (C : ℝ) : ℝ :=
  (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * ((C ^ (j + 1) - 35 ^ (j + 1)) / (j + 1 : ℝ))) +
  (∑ j ∈ range (2 * k), (((Ut k).coeff j : ℝ) / (2 * k - j : ℕ)) *
    (((70 - C) ^ (2 * k - j))⁻¹ - (C ^ (2 * k - j))⁻¹))

theorem Phi_sub_thirty_five (k : ℕ) (C : ℝ) :
    Phi k C - Phi k 35 =
      ((Uhat k).coeff (2 * k) : ℝ) * (Real.log C - Real.log (70 - C)) + rho_scaled k C := by
  unfold Phi rho_scaled
  have hlog : Real.log (35 : ℝ) - Real.log (70 - 35) = 0 := by norm_num
  have hpol : ∀ j ∈ range (2 * k),
      (((Ut k).coeff j : ℝ) / (2 * k - j : ℕ)) *
        (((70 - (35 : ℝ)) ^ (2 * k - j))⁻¹ - ((35 : ℝ) ^ (2 * k - j))⁻¹) = 0 := by
    intro j _
    norm_num
  rw [hlog, mul_zero, zero_add, sum_eq_zero hpol, add_zero]
  have hpt : (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * (C ^ (j + 1) / (j + 1 : ℝ))) -
      (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * ((35 : ℝ) ^ (j + 1) / (j + 1 : ℝ))) =
      ∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * ((C ^ (j + 1) - 35 ^ (j + 1)) / (j + 1 : ℝ)) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun j _ => by ring
  linarith

theorem hasDerivAt_inv_pow {x : ℝ} (hx : x ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    HasDerivAt (fun t : ℝ => (t ^ m)⁻¹) (-(m : ℝ) * (x ^ (m + 1))⁻¹) x := by
  have h1 := (hasDerivAt_pow m x).inv (pow_ne_zero m hx)
  refine h1.congr_deriv ?_
  have hxm : x ^ m = x ^ (m - 1) * x := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hx1 : x ^ (m + 1) = x ^ (m - 1) * x ^ 2 := by
    rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
  rw [hxm, hx1]
  have hy : x ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hx
  generalize x ^ (m - 1) = y at hy ⊢
  field_simp [hx, hy]

theorem hasDerivAt_inv_seventy_sub_pow {x : ℝ} (hx : 70 - x ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    HasDerivAt (fun t : ℝ => ((70 - t) ^ m)⁻¹) ((m : ℝ) * ((70 - x) ^ (m + 1))⁻¹) x := by
  have hsub : HasDerivAt (fun t : ℝ => 70 - t) (-1) x := by
    have h := (hasDerivAt_const x (70 : ℝ)).sub (hasDerivAt_id x)
    exact h.congr_deriv (by ring)
  have h1 : HasDerivAt (fun t : ℝ => ((70 - t) ^ m)⁻¹)
      (-(↑m * (70 - x) ^ (m - 1) * -1) / ((70 - x) ^ m) ^ 2) x :=
    (hsub.pow m).inv (pow_ne_zero m hx)
  refine h1.congr_deriv ?_
  have hxm : (70 - x) ^ m = (70 - x) ^ (m - 1) * (70 - x) := by
    rw [← pow_succ, show m - 1 + 1 = m by omega]
  have hx1 : (70 - x) ^ (m + 1) = (70 - x) ^ (m - 1) * (70 - x) ^ 2 := by
    rw [← pow_add, show m - 1 + 2 = m + 1 by omega]
  rw [hxm, hx1]
  have hy : (70 - x) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hx
  generalize (70 - x) ^ (m - 1) = y at hy ⊢
  field_simp [hx, hy]

theorem hasDerivAt_Phi (k : ℕ) {x : ℝ} (hx0 : 0 < x) (hx70 : x < 70) :
    HasDerivAt (Phi k) (70 * F k x) x := by
  have hne0 : x ≠ 0 := hx0.ne'
  have hne70 : 70 - x ≠ 0 := by linarith
  have hlog1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hne0
  have hlog2 : HasDerivAt (fun t : ℝ => Real.log (70 - t)) (-(70 - x)⁻¹) x := by
    have hsub : HasDerivAt (fun t : ℝ => 70 - t) (-1) x := by
      have h := (hasDerivAt_const x (70 : ℝ)).sub (hasDerivAt_id x)
      exact h.congr_deriv (by ring)
    have h := hsub.log hne70
    refine h.congr_deriv (by ring)
  have hA : HasDerivAt
      (fun t : ℝ => ((Uhat k).coeff (2 * k) : ℝ) * (Real.log t - Real.log (70 - t)))
      (((Uhat k).coeff (2 * k) : ℝ) * (x⁻¹ + (70 - x)⁻¹)) x := by
    have h := (hlog1.sub hlog2).const_mul ((Uhat k).coeff (2 * k) : ℝ)
    refine h.congr_deriv (by ring)
  have hB : HasDerivAt
      (fun t : ℝ => ∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * (t ^ (j + 1) / (j + 1 : ℝ)))
      (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * x ^ j) x := by
    have h := HasDerivAt.fun_sum fun j (_ : j ∈ range (2 * k)) =>
      ((hasDerivAt_pow (j + 1) x).div_const (j + 1 : ℝ)).const_mul ((Pt k).coeff j : ℝ)
    refine h.congr_deriv ?_
    refine sum_congr rfl fun j _ => ?_
    have hj : (j + 1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hj]
  have hC : HasDerivAt
      (fun t : ℝ => ∑ j ∈ range (2 * k), (((Ut k).coeff j : ℝ) / (2 * k - j : ℕ)) *
        (((70 - t) ^ (2 * k - j))⁻¹ - (t ^ (2 * k - j))⁻¹))
      (∑ j ∈ range (2 * k), ((Ut k).coeff j : ℝ) *
        (((70 - x) ^ (2 * k - j + 1))⁻¹ + (x ^ (2 * k - j + 1))⁻¹)) x := by
    have h := HasDerivAt.fun_sum fun j (hj : j ∈ range (2 * k)) => by
      have hm : 1 ≤ 2 * k - j := by rw [mem_range] at hj; omega
      exact ((hasDerivAt_inv_seventy_sub_pow hne70 (2 * k - j) hm).sub
        (hasDerivAt_inv_pow hne0 (2 * k - j) hm)).const_mul (((Ut k).coeff j : ℝ) / (2 * k - j : ℕ))
    refine h.congr_deriv ?_
    refine sum_congr rfl fun j hj => ?_
    have hm : (2 * k - j : ℕ) ≠ 0 := by rw [mem_range] at hj; omega
    have hmR : ((2 * k - j : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    field_simp [hmR]
    ring
  have hsum : HasDerivAt (Phi k)
      (((Uhat k).coeff (2 * k) : ℝ) * (x⁻¹ + (70 - x)⁻¹) +
        (∑ j ∈ range (2 * k), ((Pt k).coeff j : ℝ) * x ^ j) +
        (∑ j ∈ range (2 * k), ((Ut k).coeff j : ℝ) *
          (((70 - x) ^ (2 * k - j + 1))⁻¹ + (x ^ (2 * k - j + 1))⁻¹))) x :=
    (hA.add hB).add hC
  refine hsum.congr_deriv ?_
  have hprod_ne : (x * (70 - x)) ^ (2 * k + 1) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hne0 hne70)
  apply mul_right_cancel₀ hprod_ne
  unfold F
  rw [mul_assoc, div_mul_cancel₀ _ hprod_ne, seventy_mul_N1_pow_eq]
  have hUt_top : ((Ut k).coeff (2 * k) : ℝ) = ((Uhat k).coeff (2 * k) : ℝ) := by
    rw [Ut_coeff_of_le (le_rfl), Nat.sub_self, pow_zero, one_mul]
  rw [sum_range_succ (n := 2 * k), sum_range_succ (n := 2 * k), hUt_top]
  have hterm1 : (∑ j ∈ range (2 * k), ((Ut k).coeff j : ℝ) *
      (((70 - x) ^ (2 * k - j + 1))⁻¹ + (x ^ (2 * k - j + 1))⁻¹)) * (x * (70 - x)) ^ (2 * k + 1) =
      (∑ j ∈ range (2 * k), ((Ut k).coeff j : ℝ) * x ^ j) * (70 - x) ^ (2 * k + 1) +
      (∑ j ∈ range (2 * k), ((Ut k).coeff j : ℝ) * (70 - x) ^ j) * x ^ (2 * k + 1) := by
    rw [sum_mul, sum_mul, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have hj_eq : j + (2 * k - j + 1) = 2 * k + 1 := by omega
    have hx_split : x ^ (2 * k + 1) = x ^ j * x ^ (2 * k - j + 1) := by rw [← pow_add, hj_eq]
    have h70_split : (70 - x) ^ (2 * k + 1) = (70 - x) ^ j * (70 - x) ^ (2 * k - j + 1) := by
      rw [← pow_add, hj_eq]
    rw [mul_pow]
    have h1 : (x ^ (2 * k - j + 1))⁻¹ * (x ^ (2 * k + 1) * (70 - x) ^ (2 * k + 1)) =
        x ^ j * (70 - x) ^ (2 * k + 1) := by
      rw [hx_split]
      have ha : x ^ (2 * k - j + 1) ≠ 0 := pow_ne_zero _ hne0
      generalize x ^ (2 * k - j + 1) = a at ha ⊢
      field_simp [ha]
    have h2 : ((70 - x) ^ (2 * k - j + 1))⁻¹ * (x ^ (2 * k + 1) * (70 - x) ^ (2 * k + 1)) =
        (70 - x) ^ j * x ^ (2 * k + 1) := by
      rw [h70_split]
      have ha : (70 - x) ^ (2 * k - j + 1) ≠ 0 := pow_ne_zero _ hne70
      generalize (70 - x) ^ (2 * k - j + 1) = a at ha ⊢
      field_simp [ha]
    linear_combination ((Ut k).coeff j : ℝ) * h1 + ((Ut k).coeff j : ℝ) * h2
  have htop : (((Uhat k).coeff (2 * k) : ℝ) * (x⁻¹ + (70 - x)⁻¹)) * (x * (70 - x)) ^ (2 * k + 1) =
      ((Uhat k).coeff (2 * k) : ℝ) * x ^ (2 * k) * (70 - x) ^ (2 * k + 1) +
      ((Uhat k).coeff (2 * k) : ℝ) * (70 - x) ^ (2 * k) * x ^ (2 * k + 1) := by
    rw [mul_pow]
    have hx1 : x⁻¹ * (x ^ (2 * k + 1) * (70 - x) ^ (2 * k + 1)) =
        x ^ (2 * k) * (70 - x) ^ (2 * k + 1) := by
      rw [pow_succ' x (2 * k), mul_assoc, inv_mul_cancel_left₀ hne0]
    have h701 : (70 - x)⁻¹ * (x ^ (2 * k + 1) * (70 - x) ^ (2 * k + 1)) =
        (70 - x) ^ (2 * k) * x ^ (2 * k + 1) := by
      rw [pow_succ' (70 - x) (2 * k), mul_left_comm (x ^ (2 * k + 1)), ← mul_assoc,
        inv_mul_cancel₀ hne70, one_mul, mul_comm]
    linear_combination ((Uhat k).coeff (2 * k) : ℝ) * hx1 + ((Uhat k).coeff (2 * k) : ℝ) * h701
  rw [add_mul, add_mul, htop, hterm1]
  ring

theorem continuousOn_F (k : ℕ) {a b : ℝ} (ha : 0 < a) (hb : b < 70) (hab : a ≤ b) :
    ContinuousOn (F k) (Set.uIcc a b) := by
  rw [Set.uIcc_of_le hab]
  unfold F N1_real
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro x hx
  rcases hx with ⟨hxa, hxb⟩
  exact pow_ne_zero _ (mul_ne_zero (by linarith) (by linarith))

theorem integral_seventy_mul_F (k : ℕ) {C : ℝ} (hC1 : 35 ≤ C) (hC2 : C ≤ 42) :
    ∫ x in (35 : ℝ)..C, 70 * F k x =
      ((Uhat k).coeff (2 * k) : ℝ) * Real.log (C / (70 - C)) + rho_scaled k C := by
  have hderiv : ∀ x ∈ Set.uIcc (35 : ℝ) C, HasDerivAt (Phi k) (70 * F k x) x := by
    intro x hx
    rw [Set.uIcc_of_le hC1] at hx
    exact hasDerivAt_Phi k (by linarith [hx.1]) (by linarith [hx.2])
  have hint : IntervalIntegrable (fun x => 70 * F k x) MeasureTheory.volume 35 C :=
    ((continuousOn_const.mul (continuousOn_F k (by norm_num) (by linarith) hC1))).intervalIntegrable
  rw [integral_eq_sub_of_hasDerivAt hderiv hint, Phi_sub_thirty_five,
    Real.log_div (by linarith) (by linarith)]

/-! ### Part 3: Denominator clearing for `C = 40` and `C = 42` -/

def D_quot (k m : ℕ) : ℕ := D (2 * k) / m

theorem D_quot_cast_eq {k m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * k) :
    (D_quot k m : ℝ) = (D (2 * k) : ℝ) / (m : ℝ) := by
  unfold D_quot
  exact Nat.cast_div (dvd_D hm1 hm2) (Nat.cast_ne_zero.mpr (by omega))

def P1_int (k : ℕ) : ℤ :=
  -(∑ j ∈ range (2 * k), 4 ^ k * (Pt k).coeff j * (D_quot k (j + 1) : ℤ) *
      (40 ^ (j + 1) - 35 ^ (j + 1)) +
    ∑ j ∈ range (2 * k), (Uhat k).coeff j * (D_quot k (2 * k - j) : ℤ) *
      (4 ^ k * 14 ^ (2 * k - j) - 2 ^ j * 21 ^ (2 * k - j)))

def P2_int (k : ℕ) : ℤ :=
  -(∑ j ∈ range (2 * k), 4 ^ k * (Pt k).coeff j * (D_quot k (j + 1) : ℤ) *
      (42 ^ (j + 1) - 35 ^ (j + 1)) +
    ∑ j ∈ range (2 * k), (Uhat k).coeff j * (D_quot k (2 * k - j) : ℤ) *
      4 ^ k * (15 ^ (2 * k - j) - 10 ^ (2 * k - j)))

theorem P1_int_eq (k : ℕ) :
    -(P1_int k : ℝ) = 4 ^ k * (D (2 * k) : ℝ) * rho_scaled k 40 := by
  unfold P1_int rho_scaled
  push_cast
  rw [neg_neg, mul_add]
  congr 1
  · rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [D_quot_cast_eq (by omega) (by omega)]
    push_cast
    ring
  · rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [D_quot_cast_eq (by omega) (by omega), Ut_coeff_of_le (by omega)]
    push_cast
    set m := 2 * k - j
    have h4 : (4 : ℝ) ^ k = (2 : ℝ) ^ j * (2 : ℝ) ^ m := by
      have : 2 * k = j + m := by omega
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, this, pow_add]
    rw [show (70 - 40 : ℝ) = 30 by norm_num, ← inv_pow, ← inv_pow,
      show (14 : ℝ) = 420 * 30⁻¹ by norm_num, show (21 : ℝ) = 2 * (420 * 40⁻¹) by norm_num,
      mul_pow, mul_pow, mul_pow, h4]
    ring

theorem P2_int_eq (k : ℕ) :
    -(P2_int k : ℝ) = 4 ^ k * (D (2 * k) : ℝ) * rho_scaled k 42 := by
  unfold P2_int rho_scaled
  push_cast
  rw [neg_neg, mul_add]
  congr 1
  · rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [D_quot_cast_eq (by omega) (by omega)]
    push_cast
    ring
  · rw [mul_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [D_quot_cast_eq (by omega) (by omega), Ut_coeff_of_le (by omega)]
    push_cast
    set m := 2 * k - j
    rw [show (70 - 42 : ℝ) = 28 by norm_num, ← inv_pow, ← inv_pow,
      show (15 : ℝ) = 420 * 28⁻¹ by norm_num, show (10 : ℝ) = 420 * 42⁻¹ by norm_num,
      mul_pow, mul_pow]
    ring

/-! ### Part 4: Pointwise and integral bounds on `J1 k` and `J2 k` -/

def J1 (k : ℕ) : ℝ := ∫ x in (35 : ℝ)..40, F k x
def J2 (k : ℕ) : ℝ := ∫ x in (35 : ℝ)..42, F k x

theorem N1_real_eq_y (x : ℝ) :
    N1_real x = (x - 35) ^ 2 * ((x - 35) ^ 2 - 25) * ((x - 35) ^ 2 - 49) := by
  unfold N1_real; ring

theorem denom_eq_y (x : ℝ) : x * (70 - x) = 1225 - (x - 35) ^ 2 := by ring

theorem N1_real_nonneg {x : ℝ} (hx1 : 35 ≤ x) (hx2 : x ≤ 40) : 0 ≤ N1_real x := by
  rw [N1_real_eq_y]
  set y := (x - 35) ^ 2
  have hy0 : 0 ≤ y := sq_nonneg _
  have hy25 : y ≤ 25 := by nlinarith
  have : (y - 25) * (y - 49) = (25 - y) * (49 - y) := by ring
  rw [mul_assoc, this]
  exact mul_nonneg hy0 (mul_nonneg (by linarith) (by linarith))

theorem N1_real_upper_35_40 {x : ℝ} (hx1 : 35 ≤ x) (hx2 : x ≤ 40) :
    N1_real x ≤ (1 / 200 : ℝ) * (x * (70 - x)) ^ 2 := by
  rw [N1_real_eq_y, denom_eq_y]
  set y := (x - 35) ^ 2
  have hy0 : 0 ≤ y := sq_nonneg _
  have hy25 : y ≤ 25 := by nlinarith
  have h1 : 0 ≤ (10529 - 200 * y) * (3 * y - 32) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ (y - 8) ^ 2 := sq_nonneg _
  have hid : 9 * ((1225 - y) ^ 2 - 200 * (y * (y - 25) * (y - 49))) =
      (10529 - 200 * y) * (3 * y - 32) ^ 2 + 48 * (y - 8) ^ 2 + 86 * y + 2720857 := by ring
  linarith

theorem N1_real_lower_37_39 {x : ℝ} (hx1 : 37 ≤ x) (hx2 : x ≤ 39) :
    (1 / 500 : ℝ) * (x * (70 - x)) ^ 2 ≤ N1_real x := by
  rw [N1_real_eq_y, denom_eq_y]
  set y := (x - 35) ^ 2
  have hy4 : 4 ≤ y := by nlinarith
  have hy16 : y ≤ 16 := by nlinarith
  have h1 : 0 ≤ (27001 - 500 * y) * (y - 4) * (16 - y) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hid : 500 * (y * (y - 25) * (y - 49)) - (1225 - y) ^ 2 =
      (27001 - 500 * y) * (y - 4) * (16 - y) + 42930 * y + 227439 := by ring
  linarith

theorem N1_real_nonpos_40_42 {x : ℝ} (hx1 : 40 ≤ x) (hx2 : x ≤ 42) : N1_real x ≤ 0 := by
  rw [N1_real_eq_y]
  set y := (x - 35) ^ 2
  have hy25 : 25 ≤ y := by nlinarith
  have hy49 : y ≤ 49 := by nlinarith
  have : y * (y - 25) * (y - 49) = -(y * (y - 25) * (49 - y)) := by ring
  rw [this, neg_nonpos]
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem neg_N1_real_upper_40_42 {x : ℝ} (_hx1 : 40 ≤ x) (_hx2 : x ≤ 42) :
    -N1_real x ≤ (1 / 200 : ℝ) * (x * (70 - x)) ^ 2 := by
  rw [N1_real_eq_y, denom_eq_y]
  set y := (x - 35) ^ 2
  have hy0 : 0 ≤ y := sq_nonneg _
  have h1 : 0 ≤ (200 * y + 801) * (y - 39) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hid : (1225 - y) ^ 2 - 200 * (-(y * (y - 25) * (y - 49))) =
      (200 * y + 801) * (y - 39) ^ 2 + 828 * y + 282304 := by ring
  linarith

theorem F_nonneg_35_40 (k : ℕ) {x : ℝ} (hx1 : 35 ≤ x) (hx2 : x ≤ 40) : 0 ≤ F k x := by
  unfold F
  have h1 := N1_real_nonneg hx1 hx2
  have h2 : 0 < x * (70 - x) := mul_pos (by linarith) (by linarith)
  positivity

theorem F_upper_35_40 (k : ℕ) {x : ℝ} (hx1 : 35 ≤ x) (hx2 : x ≤ 40) :
    F k x ≤ (1 / 1200 : ℝ) * (1 / 200 : ℝ) ^ k := by
  unfold F
  have hd : 1200 ≤ x * (70 - x) := by
    rw [denom_eq_y]
    have : (x - 35) ^ 2 ≤ 25 := by nlinarith
    linarith
  have hd_pos : 0 < x * (70 - x) := by linarith
  have hnum : N1_real x ^ k ≤ (1 / 200 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k) := by
    calc N1_real x ^ k ≤ ((1 / 200 : ℝ) * (x * (70 - x)) ^ 2) ^ k :=
          pow_le_pow_left₀ (N1_real_nonneg hx1 hx2) (N1_real_upper_35_40 hx1 hx2) k
      _ = (1 / 200 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k) := by
          rw [mul_pow (1 / 200 : ℝ), ← pow_mul]
  rw [pow_succ (x * (70 - x)) (2 * k), ← div_div]
  have hdiv : N1_real x ^ k / (x * (70 - x)) ^ (2 * k) ≤ (1 / 200 : ℝ) ^ k :=
    (div_le_iff₀ (by positivity)).mpr hnum
  calc N1_real x ^ k / (x * (70 - x)) ^ (2 * k) / (x * (70 - x))
      ≤ (1 / 200 : ℝ) ^ k / (x * (70 - x)) := div_le_div_of_nonneg_right hdiv hd_pos.le
    _ ≤ (1 / 200 : ℝ) ^ k / 1200 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
    _ = (1 / 1200 : ℝ) * (1 / 200 : ℝ) ^ k := by ring

theorem F_lower_37_39 (k : ℕ) {x : ℝ} (hx1 : 37 ≤ x) (hx2 : x ≤ 39) :
    (1 / 1225 : ℝ) * (1 / 500 : ℝ) ^ k ≤ F k x := by
  unfold F
  have hd_le : x * (70 - x) ≤ 1225 := by
    rw [denom_eq_y]
    have : 0 ≤ (x - 35) ^ 2 := sq_nonneg _
    linarith
  have hd_pos : 0 < x * (70 - x) := mul_pos (by linarith) (by linarith)
  have hnum : (1 / 500 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k) ≤ N1_real x ^ k := by
    calc (1 / 500 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k)
        = ((1 / 500 : ℝ) * (x * (70 - x)) ^ 2) ^ k := by
          rw [mul_pow (1 / 500 : ℝ), ← pow_mul]
      _ ≤ N1_real x ^ k := pow_le_pow_left₀ (by positivity) (N1_real_lower_37_39 hx1 hx2) k
  rw [pow_succ (x * (70 - x)) (2 * k), ← div_div]
  have hdiv : (1 / 500 : ℝ) ^ k ≤ N1_real x ^ k / (x * (70 - x)) ^ (2 * k) :=
    (le_div_iff₀ (by positivity)).mpr hnum
  calc (1 / 1225 : ℝ) * (1 / 500 : ℝ) ^ k
      = (1 / 500 : ℝ) ^ k / 1225 := by ring
    _ ≤ (1 / 500 : ℝ) ^ k / (x * (70 - x)) :=
        div_le_div_of_nonneg_left (by positivity) hd_pos hd_le
    _ ≤ N1_real x ^ k / (x * (70 - x)) ^ (2 * k) / (x * (70 - x)) :=
        div_le_div_of_nonneg_right hdiv hd_pos.le

theorem F_nonpos_40_42 {k : ℕ} (hk : Odd k) {x : ℝ} (hx1 : 40 ≤ x) (hx2 : x ≤ 42) :
    F k x ≤ 0 := by
  unfold F
  have h1 : N1_real x ^ k ≤ 0 := Odd.pow_nonpos hk (N1_real_nonpos_40_42 hx1 hx2)
  have h2 : 0 < (x * (70 - x)) ^ (2 * k + 1) := by
    have : 0 < x * (70 - x) := mul_pos (by linarith) (by linarith)
    positivity
  exact div_nonpos_of_nonpos_of_nonneg h1 h2.le

theorem neg_F_upper_40_42 {k : ℕ} (hk : Odd k) {x : ℝ} (hx1 : 40 ≤ x) (hx2 : x ≤ 42) :
    -F k x ≤ (1 / 1176 : ℝ) * (1 / 200 : ℝ) ^ k := by
  unfold F
  rw [← neg_div, ← hk.neg_pow]
  have hd : 1176 ≤ x * (70 - x) := by
    rw [denom_eq_y]
    have : (x - 35) ^ 2 ≤ 49 := by nlinarith
    linarith
  have hd_pos : 0 < x * (70 - x) := by linarith
  have hneg_nonneg : 0 ≤ -N1_real x := neg_nonneg.mpr (N1_real_nonpos_40_42 hx1 hx2)
  have hnum : (-N1_real x) ^ k ≤ (1 / 200 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k) := by
    calc (-N1_real x) ^ k ≤ ((1 / 200 : ℝ) * (x * (70 - x)) ^ 2) ^ k :=
          pow_le_pow_left₀ hneg_nonneg (neg_N1_real_upper_40_42 hx1 hx2) k
      _ = (1 / 200 : ℝ) ^ k * (x * (70 - x)) ^ (2 * k) := by
          rw [mul_pow (1 / 200 : ℝ), ← pow_mul]
  rw [pow_succ (x * (70 - x)) (2 * k), ← div_div]
  have hdiv : (-N1_real x) ^ k / (x * (70 - x)) ^ (2 * k) ≤ (1 / 200 : ℝ) ^ k :=
    (div_le_iff₀ (by positivity)).mpr hnum
  calc (-N1_real x) ^ k / (x * (70 - x)) ^ (2 * k) / (x * (70 - x))
      ≤ (1 / 200 : ℝ) ^ k / (x * (70 - x)) := div_le_div_of_nonneg_right hdiv hd_pos.le
    _ ≤ (1 / 200 : ℝ) ^ k / 1176 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
    _ = (1 / 1176 : ℝ) * (1 / 200 : ℝ) ^ k := by ring

theorem J1_upper (k : ℕ) : J1 k ≤ (1 / 240 : ℝ) * (1 / 200 : ℝ) ^ k := by
  unfold J1
  have hint : IntervalIntegrable (F k) MeasureTheory.volume 35 40 :=
    (continuousOn_F k (a := 35) (b := 40) (by norm_num) (by norm_num)
      (by norm_num)).intervalIntegrable
  have hle := integral_mono_on (a := 35) (b := 40) (by norm_num) hint intervalIntegrable_const
    fun x hx => F_upper_35_40 k hx.1 hx.2
  rw [integral_const, smul_eq_mul] at hle
  linarith

theorem J1_lower (k : ℕ) : (2 / 1225 : ℝ) * (1 / 500 : ℝ) ^ k ≤ J1 k := by
  unfold J1
  have hcont := continuousOn_F k (a := 35) (b := 40) (by norm_num) (by norm_num) (by norm_num)
  rw [Set.uIcc_of_le (by norm_num)] at hcont
  have hint1 : IntervalIntegrable (F k) MeasureTheory.volume 35 37 :=
    (hcont.mono (Set.uIcc_subset_Icc (by norm_num) (by norm_num))).intervalIntegrable
  have hint2 : IntervalIntegrable (F k) MeasureTheory.volume 37 39 :=
    (hcont.mono (Set.uIcc_subset_Icc (by norm_num) (by norm_num))).intervalIntegrable
  have hint3 : IntervalIntegrable (F k) MeasureTheory.volume 39 40 :=
    (hcont.mono (Set.uIcc_subset_Icc (by norm_num) (by norm_num))).intervalIntegrable
  have hsplit1 := integral_add_adjacent_intervals hint1 (hint2.trans hint3)
  have hsplit2 := integral_add_adjacent_intervals hint2 hint3
  have hpos1 : 0 ≤ ∫ x in (35 : ℝ)..37, F k x :=
    integral_nonneg (by norm_num) fun x hx => F_nonneg_35_40 k hx.1 (by linarith [hx.2])
  have hpos3 : 0 ≤ ∫ x in (39 : ℝ)..40, F k x :=
    integral_nonneg (by norm_num) fun x hx => F_nonneg_35_40 k (by linarith [hx.1]) hx.2
  have hmid := integral_mono_on (a := 37) (b := 39) (by norm_num) intervalIntegrable_const hint2
    fun x hx => F_lower_37_39 k hx.1 hx.2
  rw [integral_const, smul_eq_mul] at hmid
  linarith

theorem J1_pos (k : ℕ) : 0 < J1 k :=
  lt_of_lt_of_le (by positivity) (J1_lower k)

theorem J1_sub_J2_bounds {k : ℕ} (hk : Odd k) :
    0 ≤ J1 k - J2 k ∧ J1 k - J2 k ≤ (1 / 588 : ℝ) * (1 / 200 : ℝ) ^ k := by
  unfold J1 J2
  have hcont := continuousOn_F k (a := 35) (b := 42) (by norm_num) (by norm_num) (by norm_num)
  rw [Set.uIcc_of_le (by norm_num)] at hcont
  have hint1 : IntervalIntegrable (F k) MeasureTheory.volume 35 40 :=
    (hcont.mono (Set.uIcc_subset_Icc (by norm_num) (by norm_num))).intervalIntegrable
  have hint2 : IntervalIntegrable (F k) MeasureTheory.volume 40 42 :=
    (hcont.mono (Set.uIcc_subset_Icc (by norm_num) (by norm_num))).intervalIntegrable
  have hsplit := integral_add_adjacent_intervals hint1 hint2
  have hsub : (∫ x in (35 : ℝ)..40, F k x) - (∫ x in (35 : ℝ)..42, F k x) =
      ∫ x in (40 : ℝ)..42, -F k x := by
    rw [integral_neg]
    linarith
  rw [hsub]
  refine ⟨?_, ?_⟩
  · exact integral_nonneg (by norm_num) fun x hx => neg_nonneg.mpr (F_nonpos_40_42 hk hx.1 hx.2)
  · have hint2_neg : IntervalIntegrable (fun x => -F k x) MeasureTheory.volume 40 42 := hint2.neg
    have hle := integral_mono_on (a := 40) (b := 42) (by norm_num)
      hint2_neg intervalIntegrable_const fun x hx => neg_F_upper_40_42 hk hx.1 hx.2
    rw [integral_const, smul_eq_mul] at hle
    linarith

end

end CollatzMCycles.Diophantine
