module

public import SharpTailMatching.Probability.ConditionalSplit
public import SharpTailMatching.Probability.CountBounds
public import SharpTailMatching.Probability.LowerVariance

/-! # Conditional moments of the actual all-lower failure event -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem failureMeasure_iidSum_memLp (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] (p : ℝ≥0∞) :
    MemLp (iidSum (n+1)) p (failureMeasure n μ) := by
  apply MemLp.of_bound (show Measurable (iidSum (n+1)) from by unfold iidSum; fun_prop).aestronglyMeasurable 1
  filter_upwards [ae_cond_mem (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
    (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1} by measurability)] with w hw
  rw [Real.norm_eq_abs,abs_of_nonneg (iidSum_nonneg (n+1) w)]
  have h : iidSum (n+1) w < 1 := by unfold iidSum; exact_mod_cast hw
  exact h.le

theorem integral_failureMeasure_iidSum (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    (∫w,iidSum (n+1) w ∂failureMeasure n μ) = 1-conditionalDeficit n μ := by
  have heq : iidSum (n+1) =ᵐ[failureMeasure n μ]
      (fun w => 1-max (1-iidSum (n+1) w) 0) := by
    filter_upwards [ae_cond_mem (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
      (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1} by measurability)] with w hw
    have h : iidSum (n+1) w < 1 := by unfold iidSum; exact_mod_cast hw
    rw [max_eq_left (by linarith)]
    ring
  rw [integral_congr_ae heq,integral_sub (integrable_const _)
    ((deficit_memLp n (failureMeasure n μ) 2).integrable one_le_two),
    integral_const,probReal_univ,one_smul,integral_failureMeasure_deficit]

theorem integral_failureMeasure_centered_square (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    (∫w,(iidSum (n+1) w-(1-conditionalDeficit n μ))^2 ∂failureMeasure n μ) =
      conditionalVariance n μ := by
  have h := variance_eq_integral (failureMeasure_iidSum_memLp n μ 2).aemeasurable
  rw [integral_failureMeasure_iidSum] at h
  exact h.symm

def lowerFailureQuadratic (n : ℕ) (μ L : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫w in {w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1},
    (iidSum (n+1) w-(1-conditionalDeficit n μ))^2
      ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))

theorem allLower_failure_quadratic_le {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    q^(n+1)*lowerFailureQuadratic n μ L ≤
      (1-tailProbability (n+1) μ)*conditionalVariance n μ := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  have hint : Integrable (fun w => (iidSum (n+1) w-(1-conditionalDeficit n μ))^2)
      (failureMeasure n μ) :=
    ((failureMeasure_iidSum_memLp n μ 2).sub (memLp_const _)).integrable_sq
  have h := setIntegral_le_integral (s := allLowerEvent (n+1) b) hint
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  rw [integral_failureMeasure_allLowerEvent n hq hmix hLb hUb,
    integral_failureMeasure_centered_square] at h
  have hp := sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  change q^(n+1)/(1-tailProbability (n+1) μ)*lowerFailureQuadratic n μ L ≤
    conditionalVariance n μ at h
  have hdiv : q^(n+1)*lowerFailureQuadratic n μ L/(1-tailProbability (n+1) μ) ≤
      conditionalVariance n μ := by
    convert h using 1 <;> ring
  have hmul := (div_le_iff₀ hp).mp hdiv
  nlinarith [hmul]

theorem allLower_conditional_mean_deviation {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 < q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z)
    (hγ : conditionalUpperProbability n μ b < 1) :
    (conditionalDeficit n L-conditionalDeficit n μ)^2 ≤
      conditionalVariance n μ*conditionalUpperProbability n μ b/(1-conditionalUpperProbability n μ b) := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  have hp : 0 < (failureMeasure n μ).real (allLowerEvent (n+1) b) := by
    rw [failureMeasure_allLowerEvent_real]
    exact sub_pos.mpr hγ
  have hcond := failureMeasure_cond_allLowerEvent hx hxlt hμ hq hmix hLb hUb
  let : IsProbabilityMeasure (ProbabilityTheory.cond (failureMeasure n μ) (allLowerEvent (n+1) b)) :=
    cond_isProbabilityMeasure ((measureReal_ne_zero_iff (measure_ne_top _ _)).mp hp.ne')
  have : IsProbabilityMeasure (failureMeasure n L) := hcond ▸ inferInstance
  have h := conditional_mean_deviation_le_variance (failureMeasure n μ) (iidSum (n+1))
    (failureMeasure_iidSum_memLp n μ 2) (measurableSet_allLowerEvent (n+1) b) hp
  rw [hcond,integral_failureMeasure_iidSum,integral_failureMeasure_iidSum,
    failureMeasure_allLowerEvent_real] at h
  change ((1-conditionalDeficit n L)-(1-conditionalDeficit n μ))^2 ≤
    conditionalVariance n μ*(1-(1-conditionalUpperProbability n μ b))/(1-conditionalUpperProbability n μ b) at h
  convert h using 1 <;> ring

end SharpTailMatching.Probability
