module

public import CollatzMCycles.Diophantine.PadeIntegrals

/-!
# Linear form in two logarithms via the Bad-Case Identity

We rewrite `Λ = (K + L) log 2 - K log 3 = L log(4/3) - (K - L) log(3/2)` and prove the
elementary Bad-Case / Good-Case Diophantine lower bound without any determinant non-vanishing
or contour integral hypothesis.
-/

@[expose] public section
namespace CollatzMCycles.Diophantine

noncomputable section

def l1 : ℝ := Real.log (4 / 3)
def l2 : ℝ := Real.log (3 / 2)

theorem lambda_eq (K L : ℕ) :
    ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 =
      (L : ℝ) * l1 - ((K : ℝ) - L) * l2 := by
  unfold l1 l2
  have h43 : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h32 : Real.log (3 / 2 : ℝ) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [h43, h32]
  ring

theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

theorem l1_ge : (1 / 4 : ℝ) ≤ l1 := by
  unfold l1
  have := one_sub_inv_le_log (x := 4 / 3) (by norm_num)
  linarith

theorem l2_le : l2 ≤ 1 / 2 := by
  unfold l2
  have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
  linarith

theorem l2_nonneg : 0 ≤ l2 := by
  unfold l2
  exact Real.log_nonneg (by norm_num)

theorem l2_sub_l1_ge : (1 / 9 : ℝ) ≤ l2 - l1 := by
  unfold l1 l2
  have h : Real.log (3 / 2 : ℝ) - Real.log (4 / 3) = Real.log (9 / 8) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  have h1 := one_sub_inv_le_log (x := 9 / 8) (by norm_num)
  linarith

theorem L_pos_and_lt_K {K L : ℕ}
    (h0 : 0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3)
    (h1 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 < (K : ℝ) / 4) :
    1 ≤ L ∧ L < K := by
  rw [lambda_eq] at h0 h1
  have hl1 := l1_ge
  have hl2 := l2_nonneg
  refine ⟨?_, ?_⟩
  · by_contra hL
    have hL0 : L = 0 := by omega
    subst hL0
    simp only [Nat.cast_zero, zero_mul, sub_zero, zero_sub] at h0
    have : 0 ≤ (K : ℝ) * l2 := mul_nonneg (Nat.cast_nonneg K) hl2
    linarith
  · by_contra hKL
    have hKL' : (K : ℝ) ≤ L := by exact_mod_cast (by omega : K ≤ L)
    have hsub : ((K : ℝ) - L) * l2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hl2
    have hL_ge : (K : ℝ) / 4 ≤ (L : ℝ) * l1 := by
      calc (K : ℝ) / 4 ≤ (L : ℝ) * (1 / 4) := by linarith
        _ ≤ (L : ℝ) * l1 := mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg L)
    linarith

/-- The elementary Bad-Case / Good-Case Diophantine lower bound. -/
theorem bad_case_bound {K L : ℕ} (hL1 : 1 ≤ L) (hLK : L < K)
    {r P1 P2 : ℤ} {J1_val J2_val D_val : ℝ}
    (hD : 0 < D_val) (hJ1 : 0 < J1_val) (hJ2 : J2_val ≤ J1_val)
    (he1 : (r : ℝ) * l1 - P1 = D_val * J1_val)
    (he2 : (r : ℝ) * l2 - P2 = D_val * J2_val)
    (hLam : 0 < (L : ℝ) * l1 - ((K : ℝ) - L) * l2)
    (hsmall : (K : ℝ) * (|((r : ℝ) * l1 - P1)| + |((r : ℝ) * l2 - P2)|) ≤ 1 / 2) :
    (2 / 9 : ℝ) * D_val * J1_val / (|(r : ℝ)| + 1) ≤
      (L : ℝ) * l1 - ((K : ℝ) - L) * l2 := by
  set Lam := (L : ℝ) * l1 - ((K : ℝ) - L) * l2
  set eps1 := (r : ℝ) * l1 - P1
  set eps2 := (r : ℝ) * l2 - P2
  rw [div_le_iff₀ (by positivity)]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hL_ge : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hKL_nonneg : 0 ≤ (K : ℝ) - L := by
    have : (L : ℝ) ≤ K := by exact_mod_cast hLK.le
    linarith
  have heps_nonneg : 0 ≤ |eps1| + |eps2| := by positivity
  have heps_sum : |eps1| + |eps2| ≤ 1 / 2 := by nlinarith
  have heps1 : |eps1| ≤ 1 / 2 := by linarith [abs_nonneg eps2]
  have heps2 : |eps2| ≤ 1 / 2 := by linarith [abs_nonneg eps1]
  have hcomb : |(L : ℝ) * eps1 - ((K : ℝ) - L) * eps2| ≤ 1 / 2 := by
    have htri : |(L : ℝ) * eps1 - ((K : ℝ) - L) * eps2| ≤
        (L : ℝ) * |eps1| + ((K : ℝ) - L) * |eps2| := by
      calc |(L : ℝ) * eps1 - ((K : ℝ) - L) * eps2|
          ≤ |(L : ℝ) * eps1| + |((K : ℝ) - L) * eps2| := abs_sub _ _
        _ = (L : ℝ) * |eps1| + ((K : ℝ) - L) * |eps2| := by
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg hKL_nonneg]
    have hleK : (L : ℝ) * |eps1| + ((K : ℝ) - L) * |eps2| ≤ (K : ℝ) * (|eps1| + |eps2|) := by
      have hid : (K : ℝ) * (|eps1| + |eps2|) - ((L : ℝ) * |eps1| + ((K : ℝ) - L) * |eps2|) =
          ((K : ℝ) - L) * |eps1| + (L : ℝ) * |eps2| := by ring
      have hpos : 0 ≤ ((K : ℝ) - L) * |eps1| + (L : ℝ) * |eps2| := by positivity
      linarith
    linarith
  set N : ℤ := (L : ℤ) * P1 - ((K : ℤ) - L) * P2
  rcases eq_or_ne N 0 with hN | hN
  · have hN_real : (L : ℝ) * (P1 : ℝ) - ((K : ℝ) - L) * (P2 : ℝ) = 0 := by
      have := congrArg (Int.cast : ℤ → ℝ) hN
      simpa [N] using this
    have hid : (P2 : ℝ) * Lam =
        (L : ℝ) * (l2 * eps1 - l1 * eps2) + l2 * ((L : ℝ) * (P1 : ℝ) - ((K : ℝ) - L) * (P2 : ℝ)) := by
      unfold Lam eps1 eps2
      ring
    rw [hN_real, mul_zero, add_zero] at hid
    have hW : (1 / 9 : ℝ) * D_val * J1_val ≤ l2 * eps1 - l1 * eps2 := by
      rw [he1, he2]
      have hl1 := l1_ge
      have hl21 := l2_sub_l1_ge
      have h1 : l1 * J2_val ≤ l1 * J1_val := mul_le_mul_of_nonneg_left hJ2 (by linarith)
      have h2 : (1 / 9 : ℝ) * J1_val ≤ (l2 - l1) * J1_val :=
        mul_le_mul_of_nonneg_right hl21 hJ1.le
      nlinarith
    have hW_pos : 0 < (1 / 9 : ℝ) * D_val * J1_val := by positivity
    have hP2Lam : (1 / 9 : ℝ) * D_val * J1_val ≤ (P2 : ℝ) * Lam := by nlinarith
    have hr_l2 : (r : ℝ) * l2 ≤ |(r : ℝ)| * (1 / 2) := by
      calc (r : ℝ) * l2 ≤ |(r : ℝ) * l2| := le_abs_self _
        _ = |(r : ℝ)| * l2 := by rw [abs_mul, abs_of_nonneg l2_nonneg]
        _ ≤ |(r : ℝ)| * (1 / 2) := mul_le_mul_of_nonneg_left l2_le (abs_nonneg _)
    have hneg_eps2 : -eps2 ≤ |eps2| := neg_le_abs _
    have hP2_eq : (P2 : ℝ) = (r : ℝ) * l2 - eps2 := by unfold eps2; ring
    have hP2_le : (P2 : ℝ) ≤ (|(r : ℝ)| + 1) / 2 := by linarith
    have hLam_mul : (P2 : ℝ) * Lam ≤ ((|(r : ℝ)| + 1) / 2) * Lam :=
      mul_le_mul_of_nonneg_right hP2_le hLam.le
    linarith
  · have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by exact_mod_cast Int.one_le_abs hN
    have hid : (N : ℝ) = (r : ℝ) * Lam + (-((L : ℝ) * eps1 - ((K : ℝ) - L) * eps2)) := by
      unfold Lam eps1 eps2 N
      push_cast
      ring
    have htri2 := abs_add_le ((r : ℝ) * Lam) (-((L : ℝ) * eps1 - ((K : ℝ) - L) * eps2))
    rw [← hid, abs_neg, abs_mul, abs_of_pos hLam] at htri2
    have hrLam : (1 / 2 : ℝ) ≤ |(r : ℝ)| * Lam := by linarith
    have hDJ1 : D_val * J1_val ≤ 1 / 2 := by
      rw [← he1]
      exact (le_abs_self eps1).trans heps1
    nlinarith

/-! ### Concrete instantiation at `k = 2 * m + 1` -/

def r_int (k : ℕ) : ℤ := 4 ^ k * (D (2 * k) : ℤ) * (Uhat k).coeff (2 * k)
def D_scale (k : ℕ) : ℝ := 70 * 4 ^ k * (D (2 * k) : ℝ)
def e1 (k : ℕ) : ℝ := (r_int k : ℝ) * l1 - P1_int k
def e2 (k : ℕ) : ℝ := (r_int k : ℝ) * l2 - P2_int k

theorem D_scale_pos (k : ℕ) : 0 < D_scale k := by
  unfold D_scale
  have : 0 < D (2 * k) := D_pos (2 * k)
  positivity

theorem e1_eq (k : ℕ) : e1 k = D_scale k * J1 k := by
  unfold e1 r_int l1 D_scale J1
  have hint := integral_seventy_mul_F k (C := 40) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_const_mul] at hint
  have hlog : (40 : ℝ) / (70 - 40) = 4 / 3 := by norm_num
  rw [hlog] at hint
  have hP1 := P1_int_eq k
  push_cast
  linear_combination (4 : ℝ) ^ k * (D (2 * k) : ℝ) * hint.symm + hP1

theorem e2_eq (k : ℕ) : e2 k = D_scale k * J2 k := by
  unfold e2 r_int l2 D_scale J2
  have hint := integral_seventy_mul_F k (C := 42) (by norm_num) (by norm_num)
  rw [intervalIntegral.integral_const_mul] at hint
  have hlog : (42 : ℝ) / (70 - 42) = 3 / 2 := by norm_num
  rw [hlog] at hint
  have hP2 := P2_int_eq k
  push_cast
  linear_combination (4 : ℝ) ^ k * (D (2 * k) : ℝ) * hint.symm + hP2

theorem smallness_bound (m : ℕ) :
    |e1 (2 * m + 1)| + |e2 (2 * m + 1)| ≤ 2 ^ 72 * (1 / 2 : ℝ) ^ m := by
  set k := 2 * m + 1
  have hk : Odd k := ⟨m, rfl⟩
  rw [e1_eq, e2_eq, abs_mul, abs_mul, abs_of_pos (D_scale_pos k), ← mul_add]
  have hJ1_pos := J1_pos k
  have hJ1_up := J1_upper k
  have hJ12 := J1_sub_J2_bounds hk
  have hJ1_abs : |J1 k| = J1 k := abs_of_pos hJ1_pos
  have hJ2_abs : |J2 k| ≤ J1 k + (J1 k - J2 k) := by
    have : J2 k = J1 k - (J1 k - J2 k) := by ring
    conv_lhs => rw [this]
    calc |J1 k - (J1 k - J2 k)| ≤ |J1 k| + |J1 k - J2 k| := abs_sub _ _
      _ = J1 k + (J1 k - J2 k) := by rw [hJ1_abs, abs_of_nonneg hJ12.1]
  have hJ_sum : |J1 k| + |J2 k| ≤ (1 / 70 : ℝ) * (1 / 200 : ℝ) ^ k := by
    have : (2 / 240 + 1 / 588 : ℝ) ≤ 1 / 70 := by norm_num
    have : (0 : ℝ) ≤ (1 / 200 : ℝ) ^ k := by positivity
    nlinarith
  have hD_le : (D (2 * k) : ℝ) ≤ 2 ^ 72 * 32 ^ k := by exact_mod_cast D_two_mul_le k
  have hscale : D_scale k * (|J1 k| + |J2 k|) ≤ 2 ^ 72 * (16 / 25 : ℝ) ^ k := by
    unfold D_scale
    calc 70 * 4 ^ k * (D (2 * k) : ℝ) * (|J1 k| + |J2 k|)
        ≤ 70 * 4 ^ k * (2 ^ 72 * 32 ^ k) * ((1 / 70 : ℝ) * (1 / 200 : ℝ) ^ k) := by
          refine mul_le_mul ?_ hJ_sum (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hD_le (by positivity)
      _ = 2 ^ 72 * ((4 : ℝ) * 32 * (1 / 200)) ^ k := by
          rw [mul_pow, mul_pow]
          ring
      _ = 2 ^ 72 * (16 / 25 : ℝ) ^ k := by norm_num
  refine hscale.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  change (16 / 25 : ℝ) ^ (2 * m + 1) ≤ (1 / 2 : ℝ) ^ m
  rw [pow_succ, pow_mul]
  have h1 : ((16 / 25 : ℝ) ^ 2) ^ m ≤ (1 / 2 : ℝ) ^ m :=
    pow_le_pow_left₀ (by positivity) (by norm_num) m
  have h2 : (16 / 25 : ℝ) ≤ 1 := by norm_num
  calc ((16 / 25 : ℝ) ^ 2) ^ m * (16 / 25)
      ≤ ((16 / 25 : ℝ) ^ 2) ^ m * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ m := by linarith

theorem measure_step_bound (m : ℕ) :
    (1 / 2 : ℝ) ^ (24 * (2 * m + 1) + 7) ≤
      (2 / 9 : ℝ) * D_scale (2 * m + 1) * J1 (2 * m + 1) / (|(r_int (2 * m + 1) : ℝ)| + 1) := by
  set k := 2 * m + 1
  have hD_pos : (1 : ℝ) ≤ D (2 * k) := by exact_mod_cast D_pos (2 * k)
  have h4D_pos : (1 : ℝ) ≤ 4 ^ k * (D (2 * k) : ℝ) := by
    have : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have h21720_pos : (1 : ℝ) ≤ (21720 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hr_abs : |(r_int k : ℝ)| + 1 ≤ 3 * (4 ^ k * (D (2 * k) : ℝ)) * (21720 : ℝ) ^ k := by
    unfold r_int
    push_cast
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ k * (D (2 * k) : ℝ))]
    have hcoeff : |((Uhat k).coeff (2 * k) : ℝ)| ≤ 2 * (21720 : ℝ) ^ k := by
      exact_mod_cast Uhat_top_coeff_abs_le k
    have h1 : (1 : ℝ) ≤ (4 ^ k * (D (2 * k) : ℝ)) * (21720 : ℝ) ^ k :=
      one_le_mul_of_one_le_of_one_le h4D_pos h21720_pos
    nlinarith
  have hnum : (8 / 315 : ℝ) * (4 ^ k * (D (2 * k) : ℝ)) * (1 / 500 : ℝ) ^ k ≤
      (2 / 9 : ℝ) * D_scale k * J1 k := by
    unfold D_scale
    have hJ1 := J1_lower k
    have : (0 : ℝ) ≤ 4 ^ k * (D (2 * k) : ℝ) := by positivity
    nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc (1 / 2 : ℝ) ^ (24 * k + 7) * (|(r_int k : ℝ)| + 1)
      ≤ (1 / 2 : ℝ) ^ (24 * k + 7) * (3 * (4 ^ k * (D (2 * k) : ℝ)) * (21720 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left hr_abs (by positivity)
    _ = 3 * (1 / 2 : ℝ) ^ 7 * (4 ^ k * (D (2 * k) : ℝ)) *
          ((1 / 2 : ℝ) ^ 24 * 21720) ^ k := by
        rw [pow_add, pow_mul, mul_pow]
        ring
    _ ≤ (8 / 315 : ℝ) * (4 ^ k * (D (2 * k) : ℝ)) * (1 / 500 : ℝ) ^ k := by
        have hconst : 3 * (1 / 2 : ℝ) ^ 7 ≤ 8 / 315 := by norm_num
        have hpow : ((1 / 2 : ℝ) ^ 24 * 21720) ^ k ≤ (1 / 500 : ℝ) ^ k :=
          pow_le_pow_left₀ (by positivity) (by norm_num) k
        refine mul_le_mul ?_ hpow (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hconst (by positivity)
    _ ≤ (2 / 9 : ℝ) * D_scale k * J1 k := hnum

/-- Combined irrationality measure bound at odd index `k = 2 * m + 1`:
if `(K : ℝ) * 2 ^ 72 * (1 / 2 : ℝ) ^ m ≤ 1 / 2`, then
`Λ ≥ (1 / 2) ^ (24 * (2 * m + 1) + 7)`. -/
theorem measure_bound (K L m : ℕ)
    (h0 : 0 < ((K : ℝ) + L) * Real.log 2 - K * Real.log 3)
    (h1 : ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 < (K : ℝ) / 4)
    (hsmall : (K : ℝ) * (2 ^ 72 * (1 / 2 : ℝ) ^ m) ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ (24 * (2 * m + 1) + 7) ≤ ((K : ℝ) + L) * Real.log 2 - K * Real.log 3 := by
  rcases L_pos_and_lt_K h0 h1 with ⟨hL1, hLK⟩
  rw [lambda_eq] at h0 ⊢
  set k := 2 * m + 1
  have hk : Odd k := ⟨m, rfl⟩
  have hsmall' : (K : ℝ) * (|e1 k| + |e2 k|) ≤ 1 / 2 := by
    refine (mul_le_mul_of_nonneg_left (smallness_bound m) (Nat.cast_nonneg K)).trans hsmall
  have hbad := bad_case_bound hL1 hLK (D_scale_pos k) (J1_pos k)
    (by linarith [(J1_sub_J2_bounds hk).1]) (e1_eq k) (e2_eq k) h0 hsmall'
  exact (measure_step_bound m).trans hbad

end

end CollatzMCycles.Diophantine
