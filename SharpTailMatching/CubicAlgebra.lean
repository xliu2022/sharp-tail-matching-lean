module

public import Mathlib.Tactic

public section

/-!
# Pointwise inequality in the capped cubic test

This is the scalar estimate controlling negative observations in Lemma 4.4.
The probabilistic integral comparison is a separate obligation.
-/

namespace SharpTailMatching.CubicAlgebra

@[expose] noncomputable def clippedRamp (L c w : ℝ) : ℝ := min (max (w + c) 0) L

theorem clippedRamp_nonneg {L c w : ℝ} (hL : 0 ≤ L) :
    0 ≤ clippedRamp L c w := le_min (le_max_right _ _) hL

theorem clippedRamp_mono (L c : ℝ) : Monotone (clippedRamp L c) := by
  intro u v huv
  exact min_le_min (max_le_max (by linarith) le_rfl) le_rfl

theorem clippedRamp_sub_le {L c u v : ℝ} (huv : u ≤ v) :
    clippedRamp L c v - clippedRamp L c u ≤ v - u := by
  have h₁ := abs_min_sub_min_le_max (max (v + c) 0) L (max (u + c) 0) L
  have h₂ := abs_max_sub_max_le_abs (v + c) (u + c) 0
  have h₃ : |max (v + c) 0 - max (u + c) 0| ≤ v - u := by
    simpa only [add_sub_add_right_eq_sub, abs_of_nonneg (sub_nonneg.mpr huv)] using h₂
  dsimp [clippedRamp]
  exact (le_abs_self _).trans (h₁.trans (by simpa using h₃))

theorem cube_difference_bound {U V W : ℝ}
    (hU : 0 ≤ U) (hUV : U ≤ V) (hVW : V ≤ W) :
    V ^ 3 - U ^ 3 ≤ 3 * (V - U) * W ^ 2 := by
  have hV : 0 ≤ V := hU.trans hUV
  have hW : 0 ≤ W := hV.trans hVW
  have hUW : U ≤ W := hUV.trans hVW
  have hVV : V ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hV hVW 2
  have hUU : U ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ hU hUW 2
  have hUV' : U * V ≤ W ^ 2 := by nlinarith [mul_le_mul hUW hVW hV hW]
  have hprod := mul_le_mul_of_nonneg_left
    (show V ^ 2 + V * U + U ^ 2 ≤ 3 * W ^ 2 by nlinarith)
    (sub_nonneg.mpr hUV)
  nlinarith

/-- The clipped cubic test function, with a nonnegative clipping height. -/
@[expose] noncomputable def cappedCubic (b τ z w : ℝ) : ℝ :=
  (clippedRamp (max (τ + z - 2 * b) 0) (z - b) w) ^ 3 / 3

/-- The quadratic function used on the failure event. -/
@[expose] noncomputable def failureQuadratic (τ z w : ℝ) : ℝ :=
  if w < τ then (w + z) ^ 2 else 0

theorem cappedCubic_nonneg (b τ z w : ℝ) : 0 ≤ cappedCubic b τ z w := by
  unfold cappedCubic
  exact div_nonneg (pow_nonneg (clippedRamp_nonneg (le_max_right _ _)) _) (by norm_num)

theorem cappedCubic_le (b τ z w : ℝ) :
    cappedCubic b τ z w ≤ (max (τ + z - 2 * b) 0) ^ 3 / 3 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact pow_le_pow_left₀ (clippedRamp_nonneg (le_max_right _ _)) (min_le_right _ _) 3

theorem cappedCubic_const {b τ z w : ℝ} (hb : 0 ≤ b) (hw : τ ≤ w) :
    cappedCubic b τ z w = (max (τ + z - 2 * b) 0) ^ 3 / 3 := by
  unfold cappedCubic clippedRamp
  rw [min_eq_right]
  exact max_le_max (by linarith) le_rfl

/-- A one-sided secant estimate replaces differentiation at the two corners
of the test function. Both endpoints lie within distance `b` of `w`. -/
theorem cappedCubic_secant {b τ z u v w : ℝ}
    (huv : u ≤ v) (hu : w - b ≤ u) (hv : v ≤ w + b) :
    cappedCubic b τ z v - cappedCubic b τ z u ≤
      (v - u) * failureQuadratic τ z w := by
  by_cases hw : w < τ
  · rw [failureQuadratic, ite_eq_left hw]
    let U := clippedRamp (max (τ + z - 2 * b) 0) (z - b) u
    let V := clippedRamp (max (τ + z - 2 * b) 0) (z - b) v
    let W := max (w + z) 0
    have hU : 0 ≤ U := clippedRamp_nonneg (le_max_right _ _)
    have hUV : U ≤ V := clippedRamp_mono _ _ huv
    have hVW : V ≤ W := (min_le_left _ _).trans (max_le_max (by linarith) le_rfl)
    have hdiff : V - U ≤ v - u := clippedRamp_sub_le huv
    have hcube := cube_difference_bound hU hUV hVW
    have hWsq : W ^ 2 ≤ (w + z) ^ 2 := by
      dsimp [W]
      by_cases h : 0 ≤ w + z
      · rw [max_eq_left h]
      · rw [max_eq_right (le_of_not_ge h)]
        simpa using sq_nonneg (w + z)
    have hprod := mul_le_mul hdiff hWsq (sq_nonneg W) (sub_nonneg.mpr huv)
    change V ^ 3 / 3 - U ^ 3 / 3 ≤ _
    nlinarith
  · have hlow : τ + z - 2 * b ≤ u + (z - b) := by linarith
    have hhigh : τ + z - 2 * b ≤ v + (z - b) := by linarith
    simp only [cappedCubic, clippedRamp,
      min_eq_right (max_le_max hlow le_rfl),
      min_eq_right (max_le_max hhigh le_rfl),
      failureQuadratic, ite_eq_right hw, sub_self, mul_zero, le_refl]

theorem cappedCubic_test_pointwise {b τ z t x x' : ℝ}
    (hzero : |x'| ≤ b) (hpair : |x - x'| ≤ b) :
    x * (cappedCubic b τ z (t + x) - cappedCubic b τ z t) ≤
      x ^ 2 * failureQuadratic τ z (t + x') := by
  obtain ⟨hx'lo, hx'hi⟩ := abs_le.mp hzero
  obtain ⟨hxlo, hxhi⟩ := abs_le.mp hpair
  by_cases hx : 0 ≤ x
  · have h := cappedCubic_secant (b := b) (τ := τ) (z := z)
      (u := t) (v := t + x) (w := t + x') (by linarith) (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left h hx
    convert hm using 1 <;> ring
  · have h := cappedCubic_secant (b := b) (τ := τ) (z := z)
      (u := t + x) (v := t) (w := t + x') (by linarith) (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ -x)
    convert hm using 1 <;> ring

theorem negative_part_estimate {b w z : ℝ}
    (hb : 0 ≤ b) (hbw : b ≤ w) :
    (z - w) * (w - b) ^ 3 / 3 ≤ (z - b) ^ 2 * w ^ 2 / 12 := by
  have ha : (z - w) * (w - b) ≤ (z - b) ^ 2 / 4 := by
    nlinarith [sq_nonneg (z + b - 2 * w)]
  have hsq : (w - b) ^ 2 ≤ w ^ 2 := by nlinarith
  calc
    (z - w) * (w - b) ^ 3 / 3 =
        ((z - w) * (w - b)) * ((w - b) ^ 2) / 3 := by ring
    _ ≤ ((z - b) ^ 2 / 4) * w ^ 2 / 3 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact mul_le_mul ha hsq (sq_nonneg (w - b)) (by positivity)
    _ = (z - b) ^ 2 * w ^ 2 / 12 := by ring

/-- The lower estimate on the cubic test separates the upper tail and the
quadratic loss on the failure event. -/
theorem cappedCubic_lower {b τ z w : ℝ} (hb : 0 ≤ b) (hτ : 0 < τ) :
    (max (τ + z - 2 * b) 0) ^ 3 / 3 * (if τ ≤ w then w else 0) -
        (max (z - b) 0) ^ 2 / 12 * failureQuadratic τ z w ≤
      w * cappedCubic b τ z w := by
  by_cases hw : τ ≤ w
  · rw [ite_eq_left hw, failureQuadratic, ite_eq_right (not_lt.mpr hw),
      mul_zero, sub_zero, cappedCubic_const hb hw, mul_comm]
  · rw [ite_eq_right hw, failureQuadratic, ite_eq_left (lt_of_not_ge hw),
      mul_zero, zero_sub]
    by_cases hw0 : 0 ≤ w
    · exact le_trans (neg_nonpos.mpr (by positivity))
        (mul_nonneg hw0 (cappedCubic_nonneg _ _ _ _))
    · by_cases hwb : w + z ≤ b
      · have hz : w + (z - b) ≤ 0 := by linarith
        simp only [cappedCubic, clippedRamp, max_eq_right hz,
          min_eq_left (le_max_right _ _), zero_pow (by decide : 3 ≠ 0), zero_div, mul_zero]
        exact neg_nonpos.mpr (by positivity)
      · have hzb : 0 ≤ z - b := by linarith
        rw [max_eq_left hzb]
        have hclip : clippedRamp (max (τ + z - 2 * b) 0) (z - b) w ≤ w + z - b := by
          apply (min_le_left _ _).trans
          rw [max_eq_left (by linarith)]
          linarith
        have hcub := pow_le_pow_left₀
          (clippedRamp_nonneg (le_max_right (τ + z - 2 * b) 0)) hclip 3
        have hprod := mul_le_mul_of_nonpos_left
          (div_le_div_of_nonneg_right hcub (by norm_num : (0 : ℝ) ≤ 3)) (le_of_not_ge hw0)
        have hneg := negative_part_estimate (w := w + z) (z := z) hb (by linarith)
        dsimp [cappedCubic] at *
        nlinarith

end SharpTailMatching.CubicAlgebra
