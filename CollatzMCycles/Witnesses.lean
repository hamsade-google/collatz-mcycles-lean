module

public import CollatzMCycles.Unimodular

/-!
# Lemma 3.6 (shift-free): exact rational suffix bounds, integer witnesses, bootstrap budget
(owned by `bootstrap`)

Paper (latex.md, Lemma 3.6, with NO telescopic shift terms — sufficient for `m ≤ 91`):
on the Raney-rotated cycle, for `0 ≤ i < m` and `t := m − i`,
`log₂(n_i + 1) ≥ V_rat(t, K_stage, m) := ⌈t K_stage / m⌉ · g_lo(t)` where
`g_lo(t) ≤ (∑_{u<t} δ̄^u)⁻¹ ≤ (δ − 1)/(δ^t − 1)`. An integer witness `(e₂, e₃)` with
`(M − 1) ≤ 2^{e₂} 3^{e₃}` and `e₂ + e₃ δ̄ < V_rat` certifies `n_i + 1 ≥ M`.
Lemma 3.7 (bootstrap): if `∑_i 1/(M_i − 1) / ln2_lo ≤ d_lo(record)` then Lemma 3.1 gives
`0 < (K+L) − Kδ < d_lo` and Lemma 3.5 yields `K ≥ k_next(record)`.

All numerics are `ℕ`/`ℤ` numerators over `D = 2^220`, computed by the same recursions as
`generate_exact_bounds.py` (`precompute_geom_bounds`, `suffix_v_rat` with `level = none`,
`build_integer_witness`, `uniform_error_upper`, `run_uniform_bootstrap`), so that the certificate
data in `WitnessData.lean` is reproducible from the generator
(`scratch/bootstrap/gen_shiftfree.py`).

Index convention: `Fin m`, 0-based; index `i` is the paper's `n_{i+1}`; suffix length `t = m − i`.
-/

@[expose] public section
namespace CollatzMCycles

open Finset
open LogBounds (δ)

/-- `K_top = q₊ + q₋` of the terminal certified pair (Lemma 3.7). -/
def Ktop : ℕ := 2438425051595107335801557824

/-! ### Dyadic geometric-sum bounds (`precompute_geom_bounds`) -/

/-- `powHi t / D ≥ δ̄^t` (ceil-dyadic recursion `pow_hi = ceil_dyadic(pow_hi * delta_hi)`). -/
def powHi : ℕ → ℕ
  | 0 => D
  | t + 1 => (powHi t * deltaHiNum + (D - 1)) / D

/-- `sumHi t / D ≥ ∑_{u<t} δ̄^u` (`sum_hi = ceil_dyadic(sum_hi + pow_hi)`, exact for dyadics). -/
def sumHi : ℕ → ℕ
  | 0 => 0
  | t + 1 => sumHi t + powHi t

/-- `gLoNum t / D = floor_dyadic(1 / sum_hi(t)) ≤ (δ − 1)/(δ^t − 1)`. -/
def gLoNum (t : ℕ) : ℕ := D * D / sumHi t

/-- `k_rem = ⌈t K_stage / m⌉`. -/
def kRem (t kStage m : ℕ) : ℕ := (t * kStage + m - 1) / m

/-- `⌊2^{e₂} 3^{e₃}⌋` (`floor_prod` in `build_integer_witness`). -/
def floorProd (e2 : ℤ) (e3 : ℕ) : ℕ :=
  if 0 ≤ e2 then 3 ^ e3 * 2 ^ e2.toNat else 3 ^ e3 / 2 ^ (-e2).toNat

/-- Certified lower bound `M` on `n_i + 1` from a witness `(e₂, e₃)`
(`m_val = max(2^71 + 2, floor_prod + 1)`). -/
def witM (e2 : ℤ) (e3 : ℕ) : ℕ := max (2 ^ 71 + 2) (floorProd e2 e3 + 1)

/-- Witness check at suffix length `t`, stage `kStage`, cycle length `m`: either the unconditional
bound `n_i + 1 ≥ 2^71 + 2` already gives `M`, or `e₂ + e₃ δ̄ < V_rat = kRem · gLo(t)`
(multiplied through by `D`). -/
def witOK (t kStage m : ℕ) (w : ℤ × ℕ) : Bool :=
  decide (floorProd w.1 w.2 + 1 ≤ 2 ^ 71 + 2) ||
    decide (w.1 * (D : ℤ) + (w.2 : ℤ) * (deltaHiNum : ℤ) < ((kRem t kStage m * gLoNum t : ℕ) : ℤ))

/-- All witnesses of a list, index `i` starting at `i0`, suffix length `t = m − i`. -/
def witsOK (m kStage : ℕ) : ℕ → List (ℤ × ℕ) → Bool
  | _, [] => true
  | i, w :: ws => witOK (m - i) kStage m w && witsOK m kStage (i + 1) ws

/-- Exact `∑ 1/(M_i − 1)` as a fraction `(num, den)`. -/
def recipSum : List (ℤ × ℕ) → ℕ × ℕ
  | [] => (0, 1)
  | w :: ws =>
    let p := recipSum ws
    (p.1 * (witM w.1 w.2 - 1) + p.2, p.2 * (witM w.1 w.2 - 1))

/-- One bootstrap step: the record used and the `m` witnesses `(e₂, e₃)` for `i = 0, …, m − 1`. -/
structure StepCert where
  record : Record
  wits : List (ℤ × ℕ)
  deriving Repr

/-- Executable step check at stage `K ≥ kStage`: record valid, `m` witnesses all certified, and
budget `∑ 1/(M_i − 1) ≤ ln2_lo · d_lo` (i.e. `num · D² ≤ den · ln2LoNum · dLoNum`). -/
def StepCert.check (m kStage : ℕ) (c : StepCert) : Bool :=
  c.wits.length == m && c.record.valid && witsOK m kStage 0 c.wits &&
    decide (((recipSum c.wits).1 * D * D : ℤ) ≤ ((recipSum c.wits).2 * ln2LoNum : ℕ) * c.record.dLoNum)

/-- Chain check: consecutive steps from `K ≥ kcur`, ending at `K ≥ Ktop`. -/
def chainOK (m : ℕ) : ℕ → List StepCert → Bool
  | kcur, [] => decide (Ktop ≤ kcur)
  | kcur, c :: cs => c.check m kcur && chainOK m c.record.kNext cs

/-! ### Real-analytic soundness of the dyadic bounds -/

/-- `a / d ≤ ⌈a / d⌉ = (a + (d − 1)) / d` (Nat division). -/
theorem ceilDiv_ge (a d : ℕ) (hd : 0 < d) : (a : ℝ) / d ≤ (((a + (d - 1)) / d : ℕ) : ℝ) := by
  have h : a ≤ (a + (d - 1)) / d * d := by
    have h1 := Nat.div_add_mod (a + (d - 1)) d
    have h2 := Nat.mod_lt (a + (d - 1)) hd
    have h3 : a ≤ d * ((a + (d - 1)) / d) := by omega
    rwa [Nat.mul_comm] at h3
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_le_iff₀ hd']
  exact_mod_cast h

theorem powHi_ge (t : ℕ) : ((deltaHiNum : ℝ) / D) ^ t ≤ (powHi t : ℝ) / D := by
  induction t with
  | zero => simp [powHi, D_real_pos.ne']
  | succ t ih =>
    have hD := D_real_pos
    have h1 : ((deltaHiNum : ℝ) / D) ^ (t + 1) ≤ (powHi t : ℝ) / D * ((deltaHiNum : ℝ) / D) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_right ih (by positivity)
    have h2 : (powHi t : ℝ) / D * ((deltaHiNum : ℝ) / D) =
        ((powHi t * deltaHiNum : ℕ) : ℝ) / D / D := by push_cast; ring
    have h3 : ((powHi t * deltaHiNum : ℕ) : ℝ) / D ≤
        (((powHi t * deltaHiNum + (D - 1)) / D : ℕ) : ℝ) := ceilDiv_ge _ _ D_pos
    calc ((deltaHiNum : ℝ) / D) ^ (t + 1) ≤ _ := h1
      _ = _ := h2
      _ ≤ (((powHi t * deltaHiNum + (D - 1)) / D : ℕ) : ℝ) / D :=
          div_le_div_of_nonneg_right h3 hD.le
      _ = (powHi (t + 1) : ℝ) / D := by rfl

theorem sumHi_ge (t : ℕ) : ∑ u ∈ range t, ((deltaHiNum : ℝ) / D) ^ u ≤ (sumHi t : ℝ) / D := by
  induction t with
  | zero => simp [sumHi]
  | succ t ih =>
    rw [sum_range_succ]
    have : (sumHi (t + 1) : ℝ) / D = (sumHi t : ℝ) / D + (powHi t : ℝ) / D := by
      simp only [sumHi]; push_cast; ring
    rw [this]
    exact add_le_add ih (powHi_ge t)

theorem geom_le_sumHi (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhi : δ ≤ (deltaHiNum : ℝ) / D) (t : ℕ) :
    ∑ u ∈ range t, δ ^ u ≤ (sumHi t : ℝ) / D :=
  le_trans (sum_le_sum fun u _ => pow_le_pow_left₀ hδ0 hδhi u) (sumHi_ge t)

theorem sumHi_pos (t : ℕ) (ht : 1 ≤ t) : 0 < sumHi t := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' ht
  induction s with
  | zero => simp [sumHi, powHi, D_pos]
  | succ s ih => simp only [sumHi] at ih ⊢; omega

/-- `gLo(t) ≤ (δ − 1)/(δ^t − 1)` for `1 < δ ≤ δ̄`, `t ≥ 1`. -/
theorem gLo_le (δ : ℝ) (hδ1 : 1 < δ) (hδhi : δ ≤ (deltaHiNum : ℝ) / D) (t : ℕ) (ht : 1 ≤ t) :
    (gLoNum t : ℝ) / D ≤ (δ - 1) / (δ ^ t - 1) := by
  have hD := D_real_pos
  set G : ℝ := ∑ u ∈ range t, δ ^ u with hG
  have hGpos : 0 < G := by
    rw [hG]
    exact sum_pos (fun u _ => pow_pos (by linarith) u) (nonempty_range_iff.2 (by omega))
  have hgeom : G * (δ - 1) = δ ^ t - 1 := geom_sum_mul δ t
  have hδt : 0 < δ ^ t - 1 := by rw [← hgeom]; exact mul_pos hGpos (by linarith)
  have hS : (0 : ℝ) < sumHi t := by exact_mod_cast sumHi_pos t ht
  have hGS : G ≤ (sumHi t : ℝ) / D := geom_le_sumHi δ (by linarith) hδhi t
  have hNat : gLoNum t * sumHi t ≤ D * D := Nat.div_mul_le_self (D * D) (sumHi t)
  have hNat' : (gLoNum t : ℝ) * sumHi t ≤ (D : ℝ) * D := by exact_mod_cast hNat
  have hkey : (gLoNum t : ℝ) / D * G ≤ 1 := by
    calc (gLoNum t : ℝ) / D * G ≤ (gLoNum t : ℝ) / D * ((sumHi t : ℝ) / D) :=
          mul_le_mul_of_nonneg_left hGS (by positivity)
      _ = (gLoNum t : ℝ) * sumHi t / (D * D) := by ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact hNat'
  have : (δ - 1) / (δ ^ t - 1) = 1 / G := by
    rw [← hgeom]; field_simp
  rw [this, le_div_iff₀ hGpos]
  exact hkey

/-- `⌈t K_stage / m⌉ ≤ S` whenever `t K ≤ m S` and `K_stage ≤ K`. -/
theorem kRem_le (t kStage m K S : ℕ) (hm : 1 ≤ m) (hK : kStage ≤ K) (hS : t * K ≤ m * S) :
    kRem t kStage m ≤ S := by
  unfold kRem
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  have : t * kStage ≤ t * K := Nat.mul_le_mul_left t hK
  omega

/-- `⌊2^{e₂} 3^{e₃}⌋ ≤ 2^{e₂} 3^{e₃}` in `ℝ` (`zpow` for `e₂ : ℤ`). -/
theorem floorProd_le (e2 : ℤ) (e3 : ℕ) :
    (floorProd e2 e3 : ℝ) ≤ (2 : ℝ) ^ e2 * (3 : ℝ) ^ e3 := by
  unfold floorProd
  split_ifs with h
  · obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h
    subst hk
    simp only [Int.toNat_natCast, zpow_natCast]
    push_cast; ring_nf; exact le_refl _
  · have hneg : e2 < 0 := lt_of_not_ge h
    set k := (-e2).toNat with hkdef
    have hk : (k : ℤ) = -e2 := Int.toNat_of_nonneg (by omega)
    have he2 : e2 = -(k : ℤ) := by omega
    rw [he2, zpow_neg, zpow_natCast]
    calc ((3 ^ e3 / 2 ^ k : ℕ) : ℝ) ≤ ((3 ^ e3 : ℕ) : ℝ) / ((2 ^ k : ℕ) : ℝ) := Nat.cast_div_le
      _ = ((2 : ℝ) ^ k)⁻¹ * 3 ^ e3 := by push_cast; ring

/-! ### Lemma 3.6(3): integer witness soundness -/

/--
**Lemma 3.6 (2)+(3)** (shift-free). With `t ≥ 1`, `m ≥ 1`, `n > 2^71`, `K ≥ K_stage`,
`t K ≤ m S` (Raney), `(δ − 1) S / (δ^t − 1) ≤ log₂(n + 1)` (Lemma 3.4) and a certified witness
`w = (e₂, e₃)`: `n + 1 ≥ witM e₂ e₃`.
-/
theorem witness_lower_bound (m t kStage K S n : ℕ) (hm : 1 ≤ m) (ht : 1 ≤ t) (hn : 2 ^ 71 < n) (hK : kStage ≤ K)
    (hS : t * K ≤ m * S)
    (htel : (δ - 1) * S / (δ ^ t - 1) ≤ Real.logb 2 ((n : ℝ) + 1))
    (w : ℤ × ℕ) (hw : witOK t kStage m w = true) : witM w.1 w.2 ≤ n + 1 := by
  have hD := D_real_pos
  have hδhi := δ_le_deltaHi
  have hδ1 : 1 < δ := LogBounds.one_lt_δ
  unfold witOK at hw
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hw
  unfold witM
  rcases hw with hw | hw
  · exact max_le (by omega) (by omega)
  · refine max_le (by omega) ?_
    -- V_rat ≤ log₂(n + 1)
    have hkr : kRem t kStage m ≤ S := kRem_le t kStage m K S hm hK hS
    have hg : (gLoNum t : ℝ) / D ≤ (δ - 1) / (δ ^ t - 1) := gLo_le δ hδ1 hδhi t ht
    have hδt : 0 < δ ^ t - 1 := by
      have : (1 : ℝ) < δ ^ t := one_lt_pow₀ hδ1 (by omega)
      linarith
    have hV : (kRem t kStage m : ℝ) * ((gLoNum t : ℝ) / D) ≤ Real.logb 2 ((n : ℝ) + 1) := by
      calc (kRem t kStage m : ℝ) * ((gLoNum t : ℝ) / D)
          ≤ (S : ℝ) * ((δ - 1) / (δ ^ t - 1)) := by
            apply mul_le_mul (by exact_mod_cast hkr) hg (by positivity) (by positivity)
        _ = (δ - 1) * S / (δ ^ t - 1) := by ring
        _ ≤ _ := htel
    -- e₂ + e₃ δ < V_rat
    have hw' : (w.1 : ℝ) * D + (w.2 : ℝ) * deltaHiNum < (kRem t kStage m : ℝ) * gLoNum t := by
      have := hw
      push_cast at this ⊢
      exact_mod_cast this
    have hexp : (w.1 : ℝ) + w.2 * δ < Real.logb 2 ((n : ℝ) + 1) := by
      have h1 : (w.1 : ℝ) + w.2 * ((deltaHiNum : ℝ) / D) <
          (kRem t kStage m : ℝ) * ((gLoNum t : ℝ) / D) := by
        have := div_lt_div_of_pos_right hw' hD
        calc (w.1 : ℝ) + w.2 * ((deltaHiNum : ℝ) / D)
            = ((w.1 : ℝ) * D + (w.2 : ℝ) * deltaHiNum) / D := by
              field_simp
          _ < (kRem t kStage m : ℝ) * gLoNum t / D := this
          _ = (kRem t kStage m : ℝ) * ((gLoNum t : ℝ) / D) := by ring
      have h2 : (w.1 : ℝ) + w.2 * δ ≤ (w.1 : ℝ) + w.2 * ((deltaHiNum : ℝ) / D) := by
        have : (0 : ℝ) ≤ w.2 := by positivity
        nlinarith
      linarith
    -- 2^(e₂ + e₃ δ) = 2^e₂ 3^e₃ < n + 1
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hpow : (2 : ℝ) ^ ((w.1 : ℝ) + w.2 * δ) < (n : ℝ) + 1 := by
      have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hexp
      rwa [Real.rpow_logb (by norm_num) (by norm_num) hn1] at this
    have hδ3 : (2 : ℝ) ^ δ = 3 := Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
    have hsplit : (2 : ℝ) ^ ((w.1 : ℝ) + w.2 * δ) = (2 : ℝ) ^ w.1 * (3 : ℝ) ^ w.2 := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_intCast, mul_comm (w.2 : ℝ) δ,
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2), hδ3]
    have hfp : (floorProd w.1 w.2 : ℝ) < (n : ℝ) + 1 :=
      lt_of_le_of_lt (floorProd_le w.1 w.2) (hsplit ▸ hpow)
    have : floorProd w.1 w.2 < n + 1 := by exact_mod_cast hfp
    omega

/-! ### Soundness of `witsOK`, `recipSum`, `StepCert.check`, `chainOK` -/

theorem witsOK_sound (m kStage : ℕ) : ∀ (i0 : ℕ) (ws : List (ℤ × ℕ)),
    witsOK m kStage i0 ws = true →
    ∀ j < ws.length, witOK (m - (i0 + j)) kStage m (ws.getD j (0, 0)) = true
  | _, [], _, j, hj => absurd hj (by simp)
  | i0, w :: ws, h, j, hj => by
    simp only [witsOK, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := witsOK_sound m kStage (i0 + 1) ws h.2 j (by simpa using hj)
      rw [show i0 + (j + 1) = i0 + 1 + j by omega]
      simpa using this

theorem witM_ge (e2 : ℤ) (e3 : ℕ) : 2 ^ 71 + 2 ≤ witM e2 e3 := le_max_left _ _

theorem recipSum_den_pos : ∀ ws : List (ℤ × ℕ), 0 < (recipSum ws).2
  | [] => by simp [recipSum]
  | w :: ws => by
    simp only [recipSum]
    exact Nat.mul_pos (recipSum_den_pos ws) (by have := witM_ge w.1 w.2; omega)

/-- `∑_j 1/n_j ≤ ∑_j 1/(M_j − 1) = num/den` when `M_j ≤ n_j + 1`. -/
theorem recipSum_bound (n : ℕ → ℕ) : ∀ (i0 : ℕ) (ws : List (ℤ × ℕ)),
    (∀ j < ws.length, witM (ws.getD j (0, 0)).1 (ws.getD j (0, 0)).2 ≤ n (i0 + j) + 1) →
    ∑ j ∈ range ws.length, 1 / (n (i0 + j) : ℝ) ≤ ((recipSum ws).1 : ℝ) / (recipSum ws).2
  | _, [], _ => by simp [recipSum]
  | i0, w :: ws, h => by
    have ih := recipSum_bound n (i0 + 1) ws (fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rw [show i0 + 1 + j = i0 + (j + 1) by omega]
      simpa using this)
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero, add_zero] at h0
    simp only [List.length_cons, recipSum]
    set x := witM w.1 w.2 - 1 with hx
    have hxpos : 0 < x := by have := witM_ge w.1 w.2; omega
    have hn0 : (x : ℝ) ≤ n i0 := by exact_mod_cast (by omega : x ≤ n i0)
    have hden := recipSum_den_pos ws
    rw [sum_range_succ']
    simp only [add_zero]
    have h1 : 1 / (n i0 : ℝ) ≤ 1 / (x : ℝ) :=
      one_div_le_one_div_of_le (by exact_mod_cast hxpos) hn0
    have hsum : ∑ j ∈ range ws.length, 1 / (n (i0 + (j + 1)) : ℝ) =
        ∑ j ∈ range ws.length, 1 / (n (i0 + 1 + j) : ℝ) := by
      refine sum_congr rfl fun j _ => ?_
      rw [show i0 + (j + 1) = i0 + 1 + j by omega]
    rw [hsum]
    have hd : (0 : ℝ) < (recipSum ws).2 := by exact_mod_cast hden
    have hx' : (0 : ℝ) < x := by exact_mod_cast hxpos
    have heq : ((((recipSum ws).1 * x + (recipSum ws).2 : ℕ)) : ℝ) / (((recipSum ws).2 * x : ℕ) : ℝ)
        = ((recipSum ws).1 : ℝ) / (recipSum ws).2 + 1 / x := by
      push_cast; field_simp
    rw [heq]
    linarith

/--
**Lemma 3.7, one bootstrap step** (ℕ-indexed): a checked `StepCert` at stage `K ≥ kStage`, together
with the cycle data (Orbit bound, Raney, Lemma 3.4, Lemma 3.1), forces `K ≥ k_next(record)`.
-/
theorem step_sound_aux (m kStage : ℕ) (hm : 1 ≤ m) (c : StepCert) (hc : c.check m kStage = true)
    (K L : ℕ) (hK : kStage ≤ K) (hK1 : 1 ≤ K)
    (n S : ℕ → ℕ)
    (hn : ∀ j < m, 2 ^ 71 < n j)
    (hS : ∀ j < m, (m - j) * K ≤ m * S j)
    (htel : ∀ j < m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((n j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j ∈ range m, 1 / (n j : ℝ)) / Real.log 2) :
    c.record.kNext ≤ K := by
  unfold StepCert.check at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlen, hvalid⟩, hwits⟩, hbudget⟩ := hc
  have hw := witsOK_sound m kStage 0 c.wits hwits
  have hM : ∀ j < c.wits.length,
      witM (c.wits.getD j (0, 0)).1 (c.wits.getD j (0, 0)).2 ≤ n (0 + j) + 1 := by
    intro j hj
    rw [zero_add]
    have hjm : j < m := hlen ▸ hj
    exact witness_lower_bound m (m - j) kStage K (S j) (n j) hm (by omega) (hn j hjm) hK
      (hS j hjm) (htel j hjm) _ (by simpa using hw j hj)
  have hsum := recipSum_bound n 0 c.wits hM
  simp only [zero_add, hlen] at hsum
  have hden : (0 : ℝ) < (recipSum c.wits).2 := by exact_mod_cast recipSum_den_pos c.wits
  have hD := D_real_pos
  have hl2 := ln2Lo_pos
  have hlog2 := ln2Lo_le_log_two
  have hbudgetR : ((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2 ≤
      ((ln2LoNum : ℝ) / D) * c.record.dLo := by
    rw [Record.dLo_eq]
    have hb : ((recipSum c.wits).1 : ℝ) * D * D ≤
        ((recipSum c.wits).2 : ℝ) * ln2LoNum * c.record.dLoNum := by
      have := hbudget; push_cast at this ⊢; exact_mod_cast this
    rw [div_le_iff₀ hden]
    have : ((ln2LoNum : ℝ) / D) * ((c.record.dLoNum : ℝ) / D) * (recipSum c.wits).2 =
        ((recipSum c.wits).2 * ln2LoNum * c.record.dLoNum) / (D * D) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hlogpos := LogBounds.log_two_pos
  have hchain : (∑ j ∈ range m, 1 / (n j : ℝ)) / Real.log 2 ≤ c.record.dLo := by
    calc (∑ j ∈ range m, 1 / (n j : ℝ)) / Real.log 2
        ≤ (((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2) / Real.log 2 :=
          div_le_div_of_nonneg_right hsum hlogpos.le
      _ ≤ (((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2) / ((ln2LoNum : ℝ) / D) :=
          div_le_div_of_nonneg_left (by positivity) hl2 hlog2
      _ ≤ c.record.dLo := by rw [div_le_iff₀ hl2, mul_comm]; exact hbudgetR
  exact Record.step c.record hvalid (K + L) K hK1 h0 (lt_of_lt_of_le h1 hchain)

/-- **Lemma 3.7, chain** (ℕ-indexed): `chainOK m kcur certs = true` and `kcur ≤ K` give `Ktop ≤ K`. -/
theorem chain_sound_aux (m : ℕ) (hm : 1 ≤ m) (K L : ℕ) (hK1 : 1 ≤ K) (n S : ℕ → ℕ)
    (hn : ∀ j < m, 2 ^ 71 < n j)
    (hS : ∀ j < m, (m - j) * K ≤ m * S j)
    (htel : ∀ j < m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((n j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j ∈ range m, 1 / (n j : ℝ)) / Real.log 2) :
    ∀ (kcur : ℕ) (certs : List StepCert), chainOK m kcur certs = true → kcur ≤ K → Ktop ≤ K
  | kcur, [], h, hK => by simp only [chainOK, decide_eq_true_eq] at h; omega
  | kcur, c :: cs, h, hK => by
    simp only [chainOK, Bool.and_eq_true] at h
    have hnext := step_sound_aux m kcur hm c h.1 K L hK hK1 n S hn hS htel h0 h1
    exact chain_sound_aux m hm K L hK1 n S hn hS htel h0 h1 c.record.kNext cs h.2 hnext

/--
**Lemma 3.7 (lower bootstrap), `Fin m`-indexed.** Inputs (Raney-rotated indexing, `i ↦ n_{i+1}`,
suffix length `t = m − i`):
* `hn`: Orbit bound `nmin j > 2^71`;
* `hS`: Lemma 3.2, `S j` = suffix sum `∑_{u < m−j} k (j+u)`, `(m − j) K ≤ m S j`;
* `htel`: Lemma 3.4 closed form at `r = j`, `t = m − j`;
* `h0, h1`: Lemma 3.1 in `δ`-form;
* `hchain`: the kernel-checked certificate chain from `K ≥ 1`.
Conclusion: `K ≥ Ktop`.
-/
theorem chain_bound {m : ℕ} (hm : 1 ≤ m) (certs : List StepCert)
    (hchain : chainOK m 1 certs = true)
    (K L : ℕ) (hK1 : 1 ≤ K) (nmin S : Fin m → ℕ)
    (hn : ∀ j, 2 ^ 71 < nmin j)
    (hS : ∀ j : Fin m, (m - j) * K ≤ m * S j)
    (htel : ∀ j : Fin m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((nmin j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j, 1 / (nmin j : ℝ)) / Real.log 2) : Ktop ≤ K := by
  classical
  let n' : ℕ → ℕ := fun j => if h : j < m then nmin ⟨j, h⟩ else 0
  let S' : ℕ → ℕ := fun j => if h : j < m then S ⟨j, h⟩ else 0
  have hn' : ∀ j (h : j < m), n' j = nmin ⟨j, h⟩ := fun j h => by simp [n', h]
  have hS' : ∀ j (h : j < m), S' j = S ⟨j, h⟩ := fun j h => by simp [S', h]
  have hsum : ∑ j, 1 / (nmin j : ℝ) = ∑ j ∈ range m, 1 / (n' j : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => 1 / (n' j : ℝ)) m]
    refine sum_congr rfl fun j _ => ?_
    rw [hn' j j.isLt]
  rw [hsum] at h1
  exact chain_sound_aux m hm K L hK1 n' S'
    (fun j hj => by rw [hn' j hj]; exact hn _)
    (fun j hj => by rw [hS' j hj]; exact hS ⟨j, hj⟩)
    (fun j hj => by rw [hS' j hj, hn' j hj]; exact htel ⟨j, hj⟩)
    h0 h1 1 certs hchain hK1

/-- Chain check from `kcur` to an arbitrary target `kTarget`. -/
def chainToOK (m kTarget : ℕ) : ℕ → List StepCert → Bool
  | kcur, [] => decide (kTarget ≤ kcur)
  | kcur, c :: cs => c.check m kcur && chainToOK m kTarget c.record.kNext cs

/-- **Lemma 3.7, chain to `kTarget`** (ℕ-indexed). -/
theorem chainTo_sound_aux (m kTarget : ℕ) (hm : 1 ≤ m) (K L : ℕ) (hK1 : 1 ≤ K) (n S : ℕ → ℕ)
    (hn : ∀ j < m, 2 ^ 71 < n j)
    (hS : ∀ j < m, (m - j) * K ≤ m * S j)
    (htel : ∀ j < m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((n j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j ∈ range m, 1 / (n j : ℝ)) / Real.log 2) :
    ∀ (kcur : ℕ) (certs : List StepCert), chainToOK m kTarget kcur certs = true → kcur ≤ K → kTarget ≤ K
  | kcur, [], h, hK => by simp only [chainToOK, decide_eq_true_eq] at h; omega
  | kcur, c :: cs, h, hK => by
    simp only [chainToOK, Bool.and_eq_true] at h
    have hnext := step_sound_aux m kcur hm c h.1 K L hK hK1 n S hn hS htel h0 h1
    exact chainTo_sound_aux m kTarget hm K L hK1 n S hn hS htel h0 h1 c.record.kNext cs h.2 hnext

/-- **Lemma 3.7 (general `kStart → kTarget`), `Fin m`-indexed.** -/
theorem chainTo_bound {m : ℕ} (hm : 1 ≤ m) (kStart kTarget : ℕ) (certs : List StepCert)
    (hchain : chainToOK m kTarget kStart certs = true)
    (K L : ℕ) (hKstart : kStart ≤ K) (hK1 : 1 ≤ K) (nmin S : Fin m → ℕ)
    (hn : ∀ j, 2 ^ 71 < nmin j)
    (hS : ∀ j : Fin m, (m - j) * K ≤ m * S j)
    (htel : ∀ j : Fin m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((nmin j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j, 1 / (nmin j : ℝ)) / Real.log 2) : kTarget ≤ K := by
  classical
  let n' : ℕ → ℕ := fun j => if h : j < m then nmin ⟨j, h⟩ else 0
  let S' : ℕ → ℕ := fun j => if h : j < m then S ⟨j, h⟩ else 0
  have hn' : ∀ j (h : j < m), n' j = nmin ⟨j, h⟩ := fun j h => by simp [n', h]
  have hS' : ∀ j (h : j < m), S' j = S ⟨j, h⟩ := fun j h => by simp [S', h]
  have hsum : ∑ j, 1 / (nmin j : ℝ) = ∑ j ∈ range m, 1 / (n' j : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => 1 / (n' j : ℝ)) m]
    refine sum_congr rfl fun j _ => ?_
    rw [hn' j j.isLt]
  rw [hsum] at h1
  exact chainTo_sound_aux m kTarget hm K L hK1 n' S'
    (fun j hj => by rw [hn' j hj]; exact hn _)
    (fun j hj => by rw [hS' j hj]; exact hS ⟨j, hj⟩)
    (fun j hj => by rw [hS' j hj, hn' j hj]; exact htel ⟨j, hj⟩)
    h0 h1 kStart certs hchain hKstart

/-- Executable step check at stage `K ≥ kStage` when the first `r` witnesses (`j < r`) are certified
externally (e.g. by `Cascade`) and only `j ≥ r` are checked via `witsOK`. -/
def StepCert.checkPrefix (m kStage r : ℕ) (c : StepCert) : Bool :=
  c.wits.length == m && c.record.valid && witsOK m kStage r (c.wits.drop r) &&
    decide (((recipSum c.wits).1 * D * D : ℤ) ≤ ((recipSum c.wits).2 * ln2LoNum : ℕ) * c.record.dLoNum)

/-- **Cascade-boosted bootstrap step (`StepCert.checkPrefix`).**
If the first `r` local minima (`j < r`) have externally certified bounds `extB j ≤ nmin j + 1`
(e.g. from `Cascade`), and `c.wits` certifies `j ≥ r` with `witM ≤ extB j` for `j < r`, then
`c.checkPrefix m kStage r = true` forces `c.record.kNext ≤ K`. -/
theorem step_with_prefix_bound {m : ℕ} (hm : 1 ≤ m) (kStage r : ℕ) (c : StepCert)
    (hc : c.checkPrefix m kStage r = true)
    (extB : ℕ → ℕ)
    (hext_ge : ∀ j < r, witM (c.wits.getD j (0, 0)).1 (c.wits.getD j (0, 0)).2 ≤ extB j)
    (K L : ℕ) (hK : kStage ≤ K) (hK1 : 1 ≤ K) (nmin S : Fin m → ℕ)
    (hext_nmin : ∀ j (hj : j < m), j < r → extB j ≤ nmin ⟨j, hj⟩ + 1)
    (hn : ∀ j, 2 ^ 71 < nmin j)
    (hS : ∀ j : Fin m, (m - j) * K ≤ m * S j)
    (htel : ∀ j : Fin m, (δ - 1) * S j / (δ ^ (m - j) - 1) ≤ Real.logb 2 ((nmin j : ℝ) + 1))
    (h0 : 0 < ((K + L : ℕ) : ℝ) - K * δ)
    (h1 : ((K + L : ℕ) : ℝ) - K * δ < (∑ j, 1 / (nmin j : ℝ)) / Real.log 2) :
    c.record.kNext ≤ K := by
  classical
  let n' : ℕ → ℕ := fun j => if h : j < m then nmin ⟨j, h⟩ else 0
  have hn' : ∀ j (h : j < m), n' j = nmin ⟨j, h⟩ := fun j h => by simp [n', h]
  have hsum_eq : ∑ j, 1 / (nmin j : ℝ) = ∑ j ∈ range m, 1 / (n' j : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => 1 / (n' j : ℝ)) m]
    refine sum_congr rfl fun j _ => ?_
    rw [hn' j j.isLt]
  rw [hsum_eq] at h1
  unfold StepCert.checkPrefix at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hlen, hvalid⟩, hwits⟩, hbudget⟩ := hc
  have hw := witsOK_sound m kStage r (c.wits.drop r) hwits
  have hM : ∀ j < c.wits.length,
      witM (c.wits.getD j (0, 0)).1 (c.wits.getD j (0, 0)).2 ≤ n' (0 + j) + 1 := by
    intro j hj
    rw [zero_add]
    have hjm : j < m := hlen ▸ hj
    rw [hn' j hjm]
    by_cases hjr : j < r
    · exact le_trans (hext_ge j hjr) (hext_nmin j hjm hjr)
    · have hj_drop : j - r < (c.wits.drop r).length := by simp; omega
      have hwj := hw (j - r) hj_drop
      have hget : (c.wits.drop r).getD (j - r) (0, 0) = c.wits.getD j (0, 0) := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_of_le (Nat.not_lt.mp hjr)]
      rw [hget, Nat.add_sub_of_le (Nat.not_lt.mp hjr)] at hwj
      exact witness_lower_bound m (m - j) kStage K (S ⟨j, hjm⟩) (nmin ⟨j, hjm⟩) hm (by omega)
        (hn ⟨j, hjm⟩) hK (hS ⟨j, hjm⟩) (htel ⟨j, hjm⟩) _ hwj
  have hsum := recipSum_bound n' 0 c.wits hM
  simp only [zero_add, hlen] at hsum
  have hden : (0 : ℝ) < (recipSum c.wits).2 := by exact_mod_cast recipSum_den_pos c.wits
  have hD := D_real_pos
  have hl2 := ln2Lo_pos
  have hlog2 := ln2Lo_le_log_two
  have hbudgetR : ((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2 ≤
      ((ln2LoNum : ℝ) / D) * c.record.dLo := by
    rw [Record.dLo_eq]
    have hb : ((recipSum c.wits).1 : ℝ) * D * D ≤
        ((recipSum c.wits).2 : ℝ) * ln2LoNum * c.record.dLoNum := by
      have := hbudget; push_cast at this ⊢; exact_mod_cast this
    rw [div_le_iff₀ hden]
    have : ((ln2LoNum : ℝ) / D) * ((c.record.dLoNum : ℝ) / D) * (recipSum c.wits).2 =
        ((recipSum c.wits).2 * ln2LoNum * c.record.dLoNum) / (D * D) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  have hlogpos := LogBounds.log_two_pos
  have hchain : (∑ j ∈ range m, 1 / (n' j : ℝ)) / Real.log 2 ≤ c.record.dLo := by
    calc (∑ j ∈ range m, 1 / (n' j : ℝ)) / Real.log 2
        ≤ (((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2) / Real.log 2 :=
          div_le_div_of_nonneg_right hsum hlogpos.le
      _ ≤ (((recipSum c.wits).1 : ℝ) / (recipSum c.wits).2) / ((ln2LoNum : ℝ) / D) :=
          div_le_div_of_nonneg_left (by positivity) hl2 hlog2
      _ ≤ c.record.dLo := by rw [div_le_iff₀ hl2, mul_comm]; exact hbudgetR
  exact Record.step c.record hvalid (K + L) K hK1 h0 (lt_of_lt_of_le h1 hchain)
/-! ### Terminal input for `Diophantine.terminal` -/

/-- `gLo(m) ≥ 2^{-68}` for every `1 ≤ m ≤ 100` (kernel computation). -/
theorem gLoNum_ge : ∀ m < 101, 1 ≤ m → 2 ^ 152 ≤ gLoNum m := by decide +kernel

theorem Ktop_ge : 2 ^ 68 ≤ Ktop := by unfold Ktop; norm_num

/--
**Lemma 3.7, Part 1 input.** If `K ≥ Ktop`, `1 ≤ m ≤ 100`, and every
`log₂(nmin_j + 1) ≥ (δ − 1) K / (δ^m − 1)` (Lemma 3.4 over the full cycle, `t = m`), then
`∑_j 1/nmin_j ≤ 100 · 2^(1 − K/2^68)`.
-/
theorem terminal_sum_bound {m : ℕ} (hm : 1 ≤ m) (hm100 : m ≤ 100) (K : ℕ) (hK : Ktop ≤ K)
    (nmin : Fin m → ℕ) (hn : ∀ j, 0 < nmin j)
    (hfull : ∀ j, (δ - 1) * K / (δ ^ m - 1) ≤ Real.logb 2 ((nmin j : ℝ) + 1)) :
    ∑ j, 1 / (nmin j : ℝ) ≤ 100 * (2 : ℝ) ^ (1 - (K : ℝ) / 2 ^ 68) := by
  have hD := D_real_pos
  have hg : (gLoNum m : ℝ) / D ≤ (δ - 1) / (δ ^ m - 1) :=
    gLo_le δ LogBounds.one_lt_δ δ_le_deltaHi m hm
  have hg2 : (1 : ℝ) / 2 ^ 68 ≤ (gLoNum m : ℝ) / D := by
    have h := gLoNum_ge m (by omega) hm
    have h' : ((2 : ℝ) ^ 152) ≤ gLoNum m := by exact_mod_cast h
    rw [div_le_div_iff₀ (by positivity) hD]
    have : (D : ℝ) = 2 ^ 220 := by unfold D; push_cast; ring
    rw [this]
    nlinarith [h']
  set y : ℝ := (K : ℝ) / 2 ^ 68 with hy
  have hy1 : 1 ≤ y := by
    rw [hy, le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast le_trans Ktop_ge hK
  have hbound : ∀ j, 1 / (nmin j : ℝ) ≤ (2 : ℝ) ^ (1 - y) := by
    intro j
    have hx : y ≤ Real.logb 2 ((nmin j : ℝ) + 1) := by
      calc y = (K : ℝ) * (1 / 2 ^ 68) := by rw [hy]; ring
        _ ≤ (K : ℝ) * ((gLoNum m : ℝ) / D) := mul_le_mul_of_nonneg_left hg2 (by positivity)
        _ ≤ (K : ℝ) * ((δ - 1) / (δ ^ m - 1)) := mul_le_mul_of_nonneg_left hg (by positivity)
        _ = (δ - 1) * K / (δ ^ m - 1) := by ring
        _ ≤ _ := hfull j
    have hpos : (0 : ℝ) < (nmin j : ℝ) + 1 := by positivity
    have h2y : (2 : ℝ) ^ y ≤ (nmin j : ℝ) + 1 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hx
      rwa [Real.rpow_logb (by norm_num) (by norm_num) hpos] at this
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ y := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hy1
      rwa [Real.rpow_one] at this
    have hnj : (2 : ℝ) ^ y / 2 ≤ nmin j := by linarith
    have hnpos : (0 : ℝ) < nmin j := by exact_mod_cast hn j
    calc 1 / (nmin j : ℝ) ≤ 1 / ((2 : ℝ) ^ y / 2) :=
          one_div_le_one_div_of_le (by positivity) hnj
      _ = (2 : ℝ) ^ (1 - y) := by
          rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
          field_simp
  calc ∑ j, 1 / (nmin j : ℝ) ≤ ∑ _j : Fin m, (2 : ℝ) ^ (1 - y) := sum_le_sum fun j _ => hbound j
    _ = m * (2 : ℝ) ^ (1 - y) := by simp
    _ ≤ 100 * (2 : ℝ) ^ (1 - y) := by
        have : (m : ℝ) ≤ 100 := by exact_mod_cast hm100
        exact mul_le_mul_of_nonneg_right this (by positivity)

end CollatzMCycles
