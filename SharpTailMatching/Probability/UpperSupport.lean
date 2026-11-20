module

public import SharpTailMatching.Probability.CubicMoments

/-! # Positive mass in the upper separated support interval -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem maximizer_not_supported_on_lower_interval {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ) / 24 ≤ c)
    (hcritical : 1 - ((n+1 : ℕ) : ℝ)*x = c*x)
    (hprox : supportCutoff n x μ - conditionalDeficit n μ <
      (failureScale n x μ - 3*x)/20)
    (hsupp : ∀ᵐ y : ℝ≥0 ∂(μ : Measure ℝ≥0), (y : ℝ) ≤ x + failureScale n x μ / 16) : False := by
  let D := failureScale n x μ
  let B := failureExcessParameter n x μ
  let r := conditionalDeficit n μ
  let v := conditionalVariance n μ
  let M := supportCutoff n x μ
  let b := x + D/16
  have hD : 0 < D := maximizer_failureScale_pos hx hxlt hμ
  have hB : 0 < B := maximizer_failureExcessParameter_pos hx hxlt hμ
  have hv : 0 ≤ v := variance_nonneg _ _
  have hM : M-x = D := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hr : r ≤ M := maximizer_conditionalDeficit_le_cutoff hx hxlt hμ
  have hBx : B = r-c*x := by
    dsimp [B, failureExcessParameter, r]
    rw [hcritical]
  change M-r < (D-3*x)/20 at hprox
  have hxD : 3*x < D := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hBlt : B < 4*D/3 := by
    have hcx := mul_le_mul_of_nonneg_right hc hx.le
    linarith
  have hrb : 13*D/24 < r-2*b := by dsimp [b]; linarith
  have hm0 : 0 ≤ max (B-b) 0 := le_max_right _ _
  have hmB : max (B-b) 0 ≤ B := max_le (by linarith) hB.le
  have hmsq : (max (B-b) 0)^2 ≤ B^2 := pow_le_pow_left₀ hm0 hmB 2
  have hfactor : D*B + (max (B-b) 0)^2/12 ≤ (10/9)*D*B := by
    nlinarith [mul_le_mul_of_nonneg_right hBlt.le hB.le]
  have hcubic := maximizer_cubic_bound_of_ae_le hx hxlt hμ hb hsupp
  change (D*B + (max (B-b) 0)^2/12)*v ≥ (max (r-2*b) 0)^3/3*B at hcubic
  have hcube : (13*D/24)^3 < (max (r-2*b) 0)^3 := by
    exact pow_lt_pow_left₀ (hrb.trans_le (le_max_left _ _)) (by positivity) (by norm_num)
  have hupper := (maximizer_normalized_variance_upper hx hxlt hμ hc hcritical hprox).2
  change v / D^2 < 19/400 at hupper
  have hvlt : v < (19/400)*D^2 := (div_lt_iff₀ (sq_pos_of_pos hD)).mp hupper
  have hlow : (13*D/24)^3/3*B < (10/9)*D*B*v := by
    calc
      _ < (max (r-2*b) 0)^3/3*B := mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hcube (by norm_num)) hB
      _ ≤ (D*B+(max (B-b) 0)^2/12)*v := hcubic
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor hv
  have hhigh : (10/9)*D*B*v < (10/9)*D*B*((19/400)*D^2) :=
    mul_lt_mul_of_pos_left hvlt (by positivity)
  have hbad := hlow.trans hhigh
  have hpos : 0 < D^3*B := by positivity
  nlinarith

theorem maximizer_upper_support_positive {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ) / 24 ≤ c)
    (hcritical : 1 - ((n+1 : ℕ) : ℝ)*x = c*x)
    (hprox : supportCutoff n x μ - conditionalDeficit n μ <
      (failureScale n x μ - 3*x)/20) :
    0 < (μ : Measure ℝ≥0) {y : ℝ≥0 | x + 17*failureScale n x μ/20 < (y : ℝ)} := by
  by_contra h
  have hzero : (μ : Measure ℝ≥0) {y : ℝ≥0 | x + 17*failureScale n x μ/20 < (y : ℝ)} = 0 :=
    le_antisymm (le_of_not_gt h) zero_le
  have hup : ∀ᵐ y : ℝ≥0 ∂(μ : Measure ℝ≥0), (y : ℝ) ≤ x + 17*failureScale n x μ/20 := by
    rw [ae_iff]
    simpa only [not_le] using hzero
  apply maximizer_not_supported_on_lower_interval hx hxlt hμ hc hcritical hprox
  filter_upwards [hup, maximizer_ae_support_gap hx hxlt hμ hc hcritical hprox] with y hy hgap
  exact hgap.resolve_right (fun hright => (not_lt.mpr hy) hright.1)

end SharpTailMatching.Probability
