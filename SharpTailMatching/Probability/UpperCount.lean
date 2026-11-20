module

public import SharpTailMatching.Probability.UpperComponent
public import SharpTailMatching.Probability.RefinedCovariance

/-! # The actual number of upper observations under conditional failure -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def upperIndicator (b z : ℝ≥0) : ℝ := if b < z then 1 else 0
def upperCount (k : ℕ) (b : ℝ≥0) (w : Fin k → ℝ≥0) : ℕ := ∑ i, if b < w i then 1 else 0

theorem measurable_upperIndicator (b : ℝ≥0) : Measurable (upperIndicator b) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

theorem upperIndicator_bounds (b z : ℝ≥0) : 0 ≤ upperIndicator b z ∧ upperIndicator b z ≤ 1 := by
  unfold upperIndicator
  split_ifs <;> norm_num

theorem memLp_upperIndicator (b : ℝ≥0) (ν : Measure ℝ≥0) [IsFiniteMeasure ν] (p : ℝ≥0∞) :
    MemLp (upperIndicator b) p ν := by
  apply MemLp.of_bound (measurable_upperIndicator b).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (upperIndicator_bounds b z).1]
  exact (upperIndicator_bounds b z).2

theorem coe_upperCount (k : ℕ) (b : ℝ≥0) (w : Fin k → ℝ≥0) :
    (upperCount k b w : ℝ) = ∑ i, upperIndicator b (w i) := by
  simp [upperCount, upperIndicator, Nat.cast_sum]

theorem upperCount_le (k : ℕ) (b : ℝ≥0) (w : Fin k → ℝ≥0) : upperCount k b w ≤ k := by
  have h : upperCount k b w ≤ ∑ _ : Fin k, (1 : ℕ) := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs <;> omega
  simpa using h

theorem upperCount_zero_iff (k : ℕ) (b : ℝ≥0) (w : Fin k → ℝ≥0) :
    upperCount k b w = 0 ↔ ∀ i, w i ≤ b := by
  simp [upperCount, Finset.sum_eq_zero_iff, not_lt]

theorem measurable_upperCount (k : ℕ) (b : ℝ≥0) : Measurable (upperCount k b) := by
  unfold upperCount
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply i))
    measurable_const measurable_const

theorem memLp_upperCount (k : ℕ) (b : ℝ≥0) (ν : Measure (Fin k → ℝ≥0))
    [IsFiniteMeasure ν] (p : ℝ≥0∞) : MemLp (fun w => (upperCount k b w : ℝ)) p ν := by
  apply MemLp.of_bound (measurable_from_nat.comp (measurable_upperCount k b)).aestronglyMeasurable (k : ℝ)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (upperCount k b w : ℝ) ≤ (k : ℝ)
  exact_mod_cast upperCount_le k b w

theorem integral_failureMeasure_coordinate (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (φ : ℝ≥0 → ℝ) (i : Fin (n+1)) :
    (∫ w : Fin (n+1) → ℝ≥0, φ (w i) ∂failureMeasure n μ) =
      failureIntegral n μ φ/(1-tailProbability (n+1) μ) := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ j, w j < 1}
  have hF : MeasurableSet F := by measurability
  change (∫ w : Fin (n+1) → ℝ≥0, φ (w i)
    ∂((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F)⁻¹ •
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))).restrict F) = _
  rw [integral_smul_measure, ← integral_indicator hF, failureIntegral_coordinate]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rw [show ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).toReal =
    1-tailProbability (n+1) μ from failure_toReal_eq_one_sub_tail (n+1) μ]
  ring

def conditionalUpperMean (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0) : ℝ :=
  ∫ w : Fin (n+1) → ℝ≥0, (upperCount (n+1) b w : ℝ) ∂failureMeasure n μ

def conditionalUpperProbability (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0) : ℝ :=
  (failureMeasure n μ).real {w | 0 < upperCount (n+1) b w}

theorem conditionalUpperMean_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    conditionalUpperMean n μ b = ((n+1 : ℕ) : ℝ)*
      (failureIntegral n μ (upperIndicator b)/(1-tailProbability (n+1) μ)) := by
  unfold conditionalUpperMean
  simp_rw [coe_upperCount]
  have hint (i : Fin (n+1)) : Integrable (fun w : Fin (n+1) → ℝ≥0 => upperIndicator b (w i))
      (failureMeasure n μ) := by
    apply Integrable.of_bound ((measurable_upperIndicator b).comp (measurable_pi_apply i)).aestronglyMeasurable 1
    filter_upwards [] with w
    change ‖upperIndicator b (w i)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (upperIndicator_bounds b (w i)).1]
    exact (upperIndicator_bounds b (w i)).2
  rw [integral_finsetSum _ (fun i _ => hint i)]
  simp_rw [integral_failureMeasure_coordinate]
  simp [nsmul_eq_mul]

theorem conditionalUpperProbability_le_mean (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    conditionalUpperProbability n μ b ≤ conditionalUpperMean n μ b := by
  let E : Set (Fin (n+1) → ℝ≥0) := {w | 0 < upperCount (n+1) b w}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_upperCount (n+1) b)
  have hpoint (w : Fin (n+1) → ℝ≥0) : E.indicator (fun _ => (1 : ℝ)) w ≤ (upperCount (n+1) b w : ℝ) := by
    by_cases hw : w ∈ E
    · rw [Set.indicator_of_mem hw]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hw))
    · rw [Set.indicator_of_notMem hw]
      positivity
  have h := integral_mono ((integrable_const (1 : ℝ)).indicator hE)
    ((memLp_upperCount (n+1) b (failureMeasure n μ) 2).integrable one_le_two) hpoint
  rw [integral_indicator_const _ hE] at h
  change (failureMeasure n μ).real E ≤ ∫ w, (upperCount (n+1) b w : ℝ) ∂failureMeasure n μ
  simpa only [smul_eq_mul, mul_one] using h

theorem maximizer_conditionalUpperMean_tilt {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (b : ℝ≥0) :
    conditionalUpperMean n μ b = ((n+1 : ℕ) : ℝ)/failureScale n x μ *
      (∫ z : ℝ≥0, (supportCutoff n x μ-(z : ℝ))*upperIndicator b z ∂(μ : Measure ℝ≥0)) := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  rw [conditionalUpperMean_eq, maximizer_failure_tilt hx hxlt hμ (upperIndicator b)
    (measurable_upperIndicator b) ((memLp_upperIndicator b (μ : Measure ℝ≥0) 2).integrable one_le_two)]
  ring

theorem integral_weighted_upperIndicator_mixture {μ L U : ProbabilityMeasure ℝ≥0} {q M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hU : Integrable (fun z : ℝ≥0 => (z : ℝ)) (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b) (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (∫ z : ℝ≥0, (M-(z : ℝ))*upperIndicator b z ∂(μ : Measure ℝ≥0)) =
      (1-q)*(M-(∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0))) := by
  have hint (ν : ProbabilityMeasure ℝ≥0) (hν : Integrable (fun z : ℝ≥0 => (z : ℝ)) (ν : Measure ℝ≥0)) :
      Integrable (fun z : ℝ≥0 => (M-(z : ℝ))*upperIndicator b z) (ν : Measure ℝ≥0) := by
    apply ((integrable_const M).sub hν).mul_bdd (c := 1) (measurable_upperIndicator b).aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (upperIndicator_bounds b z).1]
    exact (upperIndicator_bounds b z).2
  rw [mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0 hq1 hmix _ (hint L hL) (hint U hU)]
  have hzero : (∫ z : ℝ≥0, (M-(z : ℝ))*upperIndicator b z ∂(L : Measure ℝ≥0)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hLb] with z hz
    simp [upperIndicator, not_lt.mpr hz]
  have hupper : (∫ z : ℝ≥0, (M-(z : ℝ))*upperIndicator b z ∂(U : Measure ℝ≥0)) =
      M-(∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0)) := by
    calc
      _ = ∫ z : ℝ≥0, M-(z : ℝ) ∂(U : Measure ℝ≥0) := by
        apply integral_congr_ae
        filter_upwards [hUb] with z hz
        simp [upperIndicator, hz]
      _ = _ := by rw [integral_sub (integrable_const _) hU, integral_const, probReal_univ, one_smul]
  rw [hzero, hupper]
  ring

theorem maximizer_conditionalUpperMean_eq {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hU : Integrable (fun z : ℝ≥0 => (z : ℝ)) (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b) (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    conditionalUpperMean n μ b = ((n+1 : ℕ) : ℝ)*(1-q)*
      (supportCutoff n x μ-(∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0)))/failureScale n x μ := by
  rw [maximizer_conditionalUpperMean_tilt hx hxlt hμ,
    integral_weighted_upperIndicator_mixture hq0 hq1 hmix hL hU hLb hUb]
  ring

end SharpTailMatching.Probability
