module

public import SharpTailMatching.ProductAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Global product chords for the comparison envelopes

Every integer chord of the minimum-product polygon is a global lower bound.
This avoids choosing an inverse branch when deriving the probability envelopes.
-/

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.EnvelopeAlgebra

theorem geometric_chord_le_one (ℓ : ℕ) {q : ℝ} (hq0 : 0 ≤ q) :
    q^ℓ * (1 + (ℓ : ℝ) * (1-q)) ≤ 1 := by
  induction ℓ with
  | zero => simp
  | succ ℓ ih =>
    have hidentity : q^(ℓ+1) * (1 + ((ℓ+1 : ℕ) : ℝ) * (1-q)) =
        q^ℓ * (1 + (ℓ : ℝ) * (1-q)) - ((ℓ : ℝ)+1)*q^ℓ*(1-q)^2 := by
      rw [pow_succ]
      push_cast
      ring
    rw [hidentity]
    have hnonneg : 0 ≤ ((ℓ : ℝ)+1)*q^ℓ*(1-q)^2 := by positivity
    linarith

/-- Every integer chord is a global lower bound on the unit cube; no
restriction of the sum to the corresponding unit interval is needed. -/
theorem unit_cube_global_chord (n ℓ : ℕ) (a : Fin n → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    q^ℓ * (1-(1-q)*((∑ i, a i)-(ℓ : ℝ))) ≤ ∏ i, (1-(1-q)*a i) := by
  induction n generalizing ℓ with
  | zero =>
    simpa [mul_comm] using geometric_chord_le_one ℓ hq0
  | succ n ih =>
    let s : ℝ := ∑ i : Fin n, a i.succ
    have hs0 : 0 ≤ s := Finset.sum_nonneg (fun i _ => ha0 i.succ)
    have hsum : (∑ i : Fin (n+1), a i) = a 0 + s := Fin.sum_univ_succ a
    have hf : 0 ≤ 1-(1-q)*a 0 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr (ha1 0))]
    rw [hsum, Fin.prod_univ_succ]
    by_cases hsℓ : (ℓ : ℝ) ≤ s
    · have hrest := ih ℓ (fun i => a i.succ) (fun i => ha0 i.succ) (fun i => ha1 i.succ)
      have hmul := mul_le_mul_of_nonneg_left hrest hf
      have hid : (1-(1-q)*a 0) * (q^ℓ*(1-(1-q)*(s-ℓ))) -
          q^ℓ*(1-(1-q)*(a 0+s-ℓ)) = q^ℓ*(1-q)^2*a 0*(s-ℓ) := by ring
      have hpos : 0 ≤ q^ℓ*(1-q)^2*a 0*(s-ℓ) := by
        exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _))
          (ha0 0)) (sub_nonneg.mpr hsℓ)
      change (1-(1-q)*a 0) * (q^ℓ*(1-(1-q)*(s-ℓ))) ≤ _ at hmul
      linarith
    · cases ℓ with
      | zero => norm_num at hsℓ; linarith
      | succ ℓ =>
        have hsupper : s ≤ (ℓ : ℝ)+1 := by
          exact le_of_lt (by exact_mod_cast lt_of_not_ge hsℓ)
        have hrest := ih ℓ (fun i => a i.succ) (fun i => ha0 i.succ) (fun i => ha1 i.succ)
        have hmul := mul_le_mul_of_nonneg_left hrest hf
        have hid : (1-(1-q)*a 0) * (q^ℓ*(1-(1-q)*(s-ℓ))) -
            q^(ℓ+1)*(1-(1-q)*(a 0+s-((ℓ : ℝ)+1))) =
            q^ℓ*(1-q)^2*(1-a 0)*(1+ℓ-s) := by
          rw [pow_succ]
          ring
        have hpos : 0 ≤ q^ℓ*(1-q)^2*(1-a 0)*(1+ℓ-s) := by
          apply mul_nonneg
          · exact mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _)) (sub_nonneg.mpr (ha1 0))
          · linarith
        change (1-(1-q)*a 0) * (q^ℓ*(1-(1-q)*(s-ℓ))) ≤ _ at hmul
        norm_num only [Nat.cast_succ]
        linarith

theorem bounded_global_chord (n ℓ : ℕ) (z : Fin n → ℝ) {m r : ℝ}
    (hm : 0 < m) (hr : m < r) (hz0 : ∀ i, 0 ≤ z i) (hzm : ∀ i, z i ≤ m) :
    (1-m/r)^ℓ * (1-((∑ i, z i)-ℓ*m)/r) ≤ ∏ i, (1-z i/r) := by
  have hr0 : 0 < r := hm.trans hr
  let a : Fin n → ℝ := fun i => z i/m
  let q : ℝ := 1-m/r
  have hq0 : 0 ≤ q := sub_nonneg.mpr ((div_le_one hr0).mpr hr.le)
  have hq1 : q ≤ 1 := by dsimp [q]; linarith [div_nonneg hm.le hr0.le]
  have ha0 (i) : 0 ≤ a i := div_nonneg (hz0 i) hm.le
  have ha1 (i) : a i ≤ 1 := (div_le_one hm).mpr (hzm i)
  have h := unit_cube_global_chord n ℓ a hq0 hq1 ha0 ha1
  have hsum : (∑ i, a i) = (∑ i, z i)/m := by simp only [a, Finset.sum_div]
  have hfactor (i) : 1-(1-q)*a i = 1-z i/r := by dsimp [q,a]; field_simp; ring
  have hleft : q^ℓ*(1-(1-q)*((∑ i,a i)-ℓ)) =
      (1-m/r)^ℓ*(1-((∑ i,z i)-ℓ*m)/r) := by
    rw [hsum]
    dsimp [q]
    field_simp
    ring
  simpa only [hleft, hfactor] using h

noncomputable def failureCurve (T : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  u - T ^ (-(n : ℝ)⁻¹) * u ^ (1 + (n : ℝ)⁻¹)

noncomputable def successCurve (T : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  1 - failureCurve T n u

theorem failureCurve_eq_root_form (T u : ℝ) (n : ℕ) (hT : 0 < T)
    (hu : 0 ≤ u) (hn : 0 < n) :
    failureCurve T n u = u * (1 - (u/T) ^ (n : ℝ)⁻¹) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  by_cases hu0 : u = 0
  · simp [failureCurve, hu0, Real.zero_rpow (show 1 + (n : ℝ)⁻¹ ≠ 0 by positivity)]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    unfold failureCurve
    rw [Real.div_rpow hu hT.le, Real.rpow_add hup, Real.rpow_one, Real.rpow_neg hT.le]
    ring

/-- Taking a positive root in the global chord inequality produces the
comparison curve directly, without choosing an inverse branch. -/
theorem failureCurve_le_of_chord (T u p v : ℝ) (n : ℕ)
    (hT : 0 < T) (hn : 0 < n) (hp : 0 < p) (hv : 1 < v)
    (hu : u = p*v) (hchord : T/v * (1-1/v)^n ≤ p) :
    failureCurve T n u ≤ p := by
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hq0 : 0 ≤ 1-1/v := sub_nonneg.mpr ((div_le_one hv0).mpr hv.le)
  have hpow : (1-1/v)^n ≤ u/T := by
    apply (le_div_iff₀ hT).mpr
    have h := mul_le_mul_of_nonneg_right hchord hv0.le
    have hid : (T/v*(1-1/v)^n)*v = (1-1/v)^n*T := by field_simp
    rw [hid] at h
    simpa only [hu] using h
  have hroot := Real.rpow_le_rpow (pow_nonneg hq0 _) hpow (by positivity : 0 ≤ (n : ℝ)⁻¹)
  rw [Real.pow_rpow_inv_natCast hq0 (Nat.ne_of_gt hn)] at hroot
  rw [failureCurve_eq_root_form T u n hT hu0.le hn]
  have hmul := mul_le_mul_of_nonneg_left hroot hu0.le
  have hid : u*(1-1/v) = u-p := by rw [hu]; field_simp
  rw [hid] at hmul
  nlinarith

theorem failureCurve_le_of_deficit_le (T u p : ℝ) (n : ℕ)
    (hT : 0 < T) (hn : 0 < n) (hu : 0 ≤ u) (hup : u ≤ p) :
    failureCurve T n u ≤ p := by
  rw [failureCurve_eq_root_form T u n hT hu hn]
  have hroot := Real.rpow_nonneg (div_nonneg hu hT.le) ((n : ℝ)⁻¹)
  nlinarith [mul_nonneg hu hroot]

theorem failureCurve_strictConcave (T : ℝ) (n : ℕ) (hT : 0 < T) (hn : 0 < n) :
    StrictConcaveOn ℝ (Set.Ici 0) (failureCurve T n) := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : 1 < 1 + (n : ℝ)⁻¹ := by linarith [inv_pos.mpr hnR]
  have hpow := strictConvexOn_rpow hexp
  have hc : 0 < T ^ (-(n : ℝ)⁻¹) := Real.rpow_pos_of_pos hT _
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := mul_lt_mul_of_pos_left (hpow.2 hx hy hxy ha hb hab) hc
  simp only [smul_eq_mul, failureCurve] at h ⊢
  nlinarith

theorem successCurve_convex (T : ℝ) (n : ℕ) (hT : 0 < T) (hn : 0 < n) :
    ConvexOn ℝ (Set.Ici 0) (successCurve T n) :=
  (convexOn_const (1 : ℝ) (convex_Ici 0)).sub (failureCurve_strictConcave T n hT hn).concaveOn

end SharpTailMatching.EnvelopeAlgebra
