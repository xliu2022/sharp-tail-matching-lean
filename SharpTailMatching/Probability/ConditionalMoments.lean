module

public import SharpTailMatching.Probability.VarianceIdentity

/-! # The actual conditional law on the failure event -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def failureMeasure (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : Measure (Fin (n+1) → ℝ≥0) :=
  ProbabilityTheory.cond (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
    {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1}

def conditionalVariance (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  variance (iidSum (n+1)) (failureMeasure n μ)

theorem maximizer_failureMeasure_probability {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : IsProbabilityMeasure (failureMeasure n μ) := by
  apply cond_isProbabilityMeasure
  intro hz
  have h := failure_toReal_eq_one_sub_tail (n+1) μ
  rw [hz, ENNReal.toReal_zero] at h
  have hp := tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1
  linarith

theorem integral_failureMeasure_of_vanish (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (f : (Fin (n+1) → ℝ≥0) → ℝ)
    (hf : ∀ w : Fin (n+1) → ℝ≥0, 1 ≤ ∑ i, w i → f w = 0) :
    (∫ w, f w ∂failureMeasure n μ) =
      (∫ w, f w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) /
        (1 - tailProbability (n+1) μ) := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  have hF : MeasurableSet F := by measurability
  have hind : F.indicator f = f := by
    funext w
    by_cases hw : w ∈ F
    · simp [hw]
    · have hsum : 1 ≤ ∑ i, w i := le_of_not_gt hw
      simp [hw, hf w hsum]
  change (∫ w, f w ∂ProbabilityTheory.cond
    (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F) = _
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hF, hind]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rw [show ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).toReal =
    1 - tailProbability (n+1) μ from failure_toReal_eq_one_sub_tail (n+1) μ]
  ring

theorem deficit_vanishes (n : ℕ) (w : Fin (n+1) → ℝ≥0) (hw : 1 ≤ ∑ i, w i) :
    max (1 - iidSum (n+1) w) 0 = 0 := by
  have hs : 1 ≤ iidSum (n+1) w := by
    dsimp [iidSum]
    exact_mod_cast hw
  exact max_eq_right (sub_nonpos.mpr hs)

theorem integral_failureMeasure_deficit (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ w : Fin (n+1) → ℝ≥0, max (1 - iidSum (n+1) w) 0 ∂failureMeasure n μ) =
      conditionalDeficit n μ :=
  integral_failureMeasure_of_vanish n μ _ (deficit_vanishes n)

theorem maximizer_conditionalVariance_eq {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    conditionalVariance n μ =
      (∫ w : Fin (n+1) → ℝ≥0, (max (1 - iidSum (n+1) w) 0)^2
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) /
          (1 - tailProbability (n+1) μ) - (conditionalDeficit n μ)^2 := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  have hmeas : Measurable (iidSum (n+1)) := by
    change Measurable (fun w : Fin (n+1) → ℝ≥0 => ∑ i, (w i : ℝ))
    fun_prop
  have hae : (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) =ᵐ[failureMeasure n μ]
      (fun w => 1 - iidSum (n+1) w) := by
    filter_upwards [ae_cond_mem (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
      (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1} by measurability)] with w hw
    have hlt : iidSum (n+1) w < 1 := by dsimp [iidSum]; exact_mod_cast hw
    exact max_eq_left (sub_nonneg.mpr hlt.le)
  have hmem : MemLp (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) 2
      (failureMeasure n μ) := by
    apply MemLp.of_bound ((measurable_const.sub hmeas).max measurable_const).aestronglyMeasurable 1
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    change max (1 - iidSum (n+1) w) 0 ≤ 1
    exact max_le (by have := iidSum_nonneg (n+1) w; linarith) (by norm_num)
  have hvar : variance (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0)
      (failureMeasure n μ) = conditionalVariance n μ := by
    rw [variance_congr hae, variance_const_sub hmeas.aestronglyMeasurable]
    rfl
  rw [← hvar, variance_eq_sub hmem, integral_failureMeasure_deficit]
  congr 1
  exact integral_failureMeasure_of_vanish n μ _ (fun w hw => by simp [deficit_vanishes n w hw])

end SharpTailMatching.Probability
