module

public import SharpTailMatching.Probability.ComponentCovariance

/-! # The strict covariance improvement from separated components -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem maximizer_refined_conditionalVariance {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 < q) (hq1 : q < 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hLac : (L : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    (hLb : ∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), (z : ℝ) ≤ x+failureScale n x μ/16)
    (hUb : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (z : ℝ) ∧
      (z : ℝ) ≤ supportCutoff n x μ)
    (hLpos : 0 < ∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) :
    conditionalVariance n μ + (63/80)*q*(essentialUpper L : ℝ)*
      (((n+1 : ℕ) : ℝ)*(x-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)))) <
        failureExcessParameter n x μ*(supportCutoff n x μ-conditionalDeficit n μ) := by
  let D := failureScale n x μ
  let p := 1-tailProbability (n+1) μ
  let b := essentialUpper L
  let Δ := (∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0))-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0))
  let C := p*(b : ℝ)/D
  let d := (63/80)*D
  have hD : 0 < D := maximizer_failureScale_pos hx hxlt hμ
  have hp : 0 < p := sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  let b₀ : ℝ≥0 := ⟨x+D/16, by positivity⟩
  have hLb₀ : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b₀ := hLb
  have hLb' : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b := ae_le_essentialUpper L hLb₀
  have hb₀ : (b : ℝ) ≤ x+D/16 := essentialUpper_le L hLb₀
  have hL2 := memLp_coe_of_ae_le L hLb 2
  have hU2 := memLp_coe_of_ae_le U (hUb.mono (fun _ h => h.2)) 2
  have hmeanb : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) ≤ (b : ℝ) := by
    have h := integral_mono_ae (hL2.integrable one_le_two) (integrable_const (b : ℝ)) hLb'
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hb : 0 < (b : ℝ) := hLpos.trans_le hmeanb
  have hC : 0 < C := div_pos (mul_pos hp hb) hD
  have hd : 0 < d := by dsimp [d]; positivity
  have hUgap : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), (b : ℝ)+d < (z : ℝ) := by
    filter_upwards [hUb] with z hz
    dsimp [d, D] at *
    linarith [hz.1]
  have hUb' : ∀ᵐ z ∂(U : Measure ℝ≥0), b ≤ z := by
    filter_upwards [hUgap] with z hz
    change (b : ℝ) ≤ z
    linarith
  have hcontact := maximizer_essentialUpper_contact hx hxlt hμ hLac hLb₀
  have hpointInt := maximizer_cross_integral_lower hx hxlt hμ hL2 hU2 hLb' hUb' hcontact
  have hprod := cross_product_integral_strict L U hL2 hU2 hd hLb' hUgap
  have hpair : C*(d*Δ) < ∫ z, covariancePair n μ z ∂(L : Measure ℝ≥0).prod (U : Measure ℝ≥0) :=
    (mul_lt_mul_of_pos_left hprod hC).trans_le hpointInt
  have hcross := maximizer_covarianceRemainder_cross hx hxlt hμ hq0.le hq1.le hmix
  have hqprod : 0 < 2*q*(1-q) := by positivity
  have hR : (2*q*(1-q))*(C*(d*Δ)) < covarianceRemainder n μ :=
    (mul_lt_mul_of_pos_left hpair hqprod).trans_le hcross
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hscale : 0 < ((n+1 : ℕ) : ℝ)/(2*p) := div_pos hk (by positivity)
  have hI := mul_lt_mul_of_pos_left hR hscale
  have hmeanμ : (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal, maximizer_mean_eq (by omega) hx.le hxlt hμ,
      ENNReal.toReal_ofReal hx.le]
  have hmean := mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0.le hq1.le hmix (fun z : ℝ≥0 => (z : ℝ)) (hL2.integrable one_le_two) (hU2.integrable one_le_two)
  rw [hmeanμ] at hmean
  have hdelta : (1-q)*Δ = x-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) := by dsimp [Δ]; nlinarith
  have halgebra : ((n+1 : ℕ) : ℝ)/(2*p)*((2*q*(1-q))*(C*(d*Δ))) =
      (63/80)*q*(b : ℝ)*(((n+1 : ℕ) : ℝ)*(x-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)))) := by
    rw [← hdelta]
    dsimp [C, d]
    field_simp
  rw [halgebra] at hI
  have hid := maximizer_covariance_identity hx hxlt hμ
  change failureExcessParameter n x μ*(supportCutoff n x μ-conditionalDeficit n μ) =
    conditionalVariance n μ+((n+1 : ℕ) : ℝ)/(2*p)*covarianceRemainder n μ at hid
  change conditionalVariance n μ+(63/80)*q*(b : ℝ)*
    (((n+1 : ℕ) : ℝ)*(x-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)))) < _
  linarith

end SharpTailMatching.Probability
