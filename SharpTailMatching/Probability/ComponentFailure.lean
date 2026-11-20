module

public import SharpTailMatching.Probability.UpperMass
public import SharpTailMatching.Probability.ProductConsequences

/-! # Failure from the lower component and the small-deviation obstruction -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem sectionFailure_mixture_ge (n : ℕ) (μ L U : ProbabilityMeasure ℝ≥0)
    {q : ℝ} (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (y : ℝ≥0) :
    q^n * sectionFailure n L y ≤ sectionFailure n μ y := by
  let : IsFiniteMeasure (ENNReal.ofReal q • (L : Measure ℝ≥0)) :=
    (L : Measure ℝ≥0).smul_finite ENNReal.ofReal_ne_top
  have hdom : ENNReal.ofReal q • (L : Measure ℝ≥0) ≤ (μ : Measure ℝ≥0) := by
    rw [hmix]
    intro s
    simp only [Measure.add_apply]
    exact le_add_of_nonneg_right zero_le
  have hpi := pi_const_mono n (ENNReal.ofReal q • (L : Measure ℝ≥0)) (μ : Measure ℝ≥0) hdom
  rw [pi_const_smul n (L : Measure ℝ≥0) _ ENNReal.ofReal_ne_top] at hpi
  have h := ENNReal.toReal_mono (measure_ne_top _ _)
    (hpi {w : Fin n → ℝ≥0 | y + ∑ i, w i < 1})
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hq, sectionFailure] using h

theorem small_deviation_iid (j : ℕ) (L : ProbabilityMeasure ℝ≥0) {x₀ ε : ℝ}
    (hx₀ : 0 < x₀) (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ε/(1+ε) ≤ (Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0))).real
      {w | iidSum j w < ((j : ℝ)+ε)*x₀} := by
  let Y : Fin j → (Fin j → ℝ≥0) → ℝ := fun i w => (w i : ℝ)/x₀
  have hY (i : Fin j) : Measurable (Y i) := by dsimp [Y]; fun_prop
  have hYi (i : Fin j) : Integrable (Y i) (Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0))) :=
    ((measurePreserving_eval (fun _ : Fin j => (L : Measure ℝ≥0)) i).integrable_comp_of_integrable hL).div_const x₀
  have hindep : iIndepFun Y (Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0))) :=
    iIndepFun_pi (X := fun _ : Fin j => fun z : ℝ≥0 => (z : ℝ)/x₀) (fun _ => by fun_prop)
  have hnonneg (i : Fin j) : ∀ᵐ w ∂Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0)), 0 ≤ Y i w :=
    ae_of_all _ (fun w => div_nonneg (w i).coe_nonneg hx₀.le)
  have hYmean (i : Fin j) : (∫ w, Y i w ∂Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0))) ≤ 1 := by
    have hi := integral_map (μ := Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0)))
      (f := fun z : ℝ≥0 => (z : ℝ)/x₀) (measurable_pi_apply i).aemeasurable (by fun_prop)
    rw [(measurePreserving_eval (fun _ : Fin j => (L : Measure ℝ≥0)) i).map_eq] at hi
    rw [← hi, integral_div, hmean, div_self hx₀.ne']
  have h := ProductBound.small_deviation (Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0)))
    j Y hY hYi hindep hnonneg hYmean ε hε hεhalf
  have hevent : {w : Fin j → ℝ≥0 | (∑ i, Y i w) < (j : ℝ)+ε} =
      {w | iidSum j w < ((j : ℝ)+ε)*x₀} := by
    ext w
    change (∑ i, (w i : ℝ)/x₀) < (j : ℝ)+ε ↔ _
    rw [← Finset.sum_div, div_lt_iff₀ hx₀]
    rfl
  rwa [hevent] at h

theorem sectionFailure_lower_of_mean (j : ℕ) (L : ProbabilityMeasure ℝ≥0) {x₀ ε : ℝ}
    (hx₀ : 0 < x₀) (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) {y : ℝ≥0}
    (hy : (y : ℝ)+((j : ℝ)+ε)*x₀ ≤ 1) : ε/(1+ε) ≤ sectionFailure j L y := by
  refine (small_deviation_iid j L hx₀ hL hmean hε hεhalf).trans ?_
  change _ ≤ (Measure.pi (fun _ : Fin j => (L : Measure ℝ≥0))).real
    {w : Fin j → ℝ≥0 | y+∑ i, w i < 1}
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro w hw
  change iidSum j w < ((j : ℝ)+ε)*x₀ at hw
  have hs : (y : ℝ)+iidSum j w < 1 := by linarith
  dsimp [iidSum] at hs
  exact_mod_cast hs

theorem maximizer_upper_contact_lower_failure {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hU : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0)) :
    ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), q^n * sectionFailure n L y ≤
      (1-tailProbability (n+1) μ)*(supportCutoff n x μ-(y : ℝ))/failureScale n x μ := by
  filter_upwards [hU.ae_le (maximizer_ae_failure_tilt hx hxlt hμ)] with y hy
  rw [← hy]
  exact sectionFailure_mixture_ge n μ L U hq hmix y

theorem maximizer_upper_component_threshold {n : ℕ} {x q x₀ ε : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hU : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    (hUb : ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (y : ℝ))
    (hx₀ : 0 < x₀) (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2)
    (hweight : (3/20)*(1-tailProbability (n+1) μ) ≤ q^n*(ε/(1+ε))) :
    ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), 1-((n : ℝ)+ε)*x₀ < (y : ℝ) := by
  have hD := maximizer_failureScale_pos hx hxlt hμ
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hp : 0 < 1-tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  filter_upwards [maximizer_upper_contact_lower_failure hx hxlt hμ hq hmix hU, hUb] with y hy hyupper
  by_contra hbad
  have hyle : (y : ℝ)+((n : ℝ)+ε)*x₀ ≤ 1 := by linarith
  have hfail := sectionFailure_lower_of_mean n L hx₀ hL hmean hε hεhalf hyle
  have hmul := mul_le_mul_of_nonneg_left hfail (pow_nonneg hq n)
  have hcombined := hweight.trans (hmul.trans hy)
  have hcleared := (le_div_iff₀ hD).mp hcombined
  have hgap : supportCutoff n x μ-(y : ℝ) < 3*failureScale n x μ/20 := by linarith
  have hstrict := mul_lt_mul_of_pos_left hgap hp
  nlinarith

theorem ae_zero_of_integral_coe_eq_zero (L : ProbabilityMeasure ℝ≥0)
    (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = 0) :
    ∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), z = 0 := by
  have h := (integral_eq_zero_iff_of_nonneg (fun z : ℝ≥0 => z.coe_nonneg) hL).mp hmean
  filter_upwards [h] with z hz
  change (z : ℝ) = 0 at hz
  exact_mod_cast hz

theorem sectionFailure_of_ae_zero (n : ℕ) (L : ProbabilityMeasure ℝ≥0)
    (hL : ∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), z = 0) {y : ℝ≥0} (hy : y < 1) :
    sectionFailure n L y = 1 := by
  have hcoords : ∀ᵐ w ∂Measure.pi (fun _ : Fin n => (L : Measure ℝ≥0)), ∀ i : Fin n, w i = 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => (L : Measure ℝ≥0)) i).quasiMeasurePreserving.ae hL
  have hset : {w : Fin n → ℝ≥0 | y+∑ i, w i < 1} =ᵐ[Measure.pi (fun _ : Fin n => (L : Measure ℝ≥0))] Set.univ := by
    filter_upwards [hcoords] with w hw
    simp [hw, hy]
  unfold sectionFailure
  rw [measure_congr hset, measure_univ, ENNReal.toReal_one]

end SharpTailMatching.Probability
