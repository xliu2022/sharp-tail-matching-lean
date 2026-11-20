module

public import SharpTailMatching.Probability.ConditionalTails

/-! # Separation of maximizing laws from the comparison proximity estimate

The scalar critical-mean relation and the proximity estimate are the preceding
comparison conclusions. Contact, conditional moments, and Cantelli's inequality
are derived here from the original maximizing law.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem maximizer_normalized_variance_upper {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ) / 24 ≤ c)
    (hcritical : 1 - ((n+1 : ℕ) : ℝ) * x = c * x)
    (hprox : supportCutoff n x μ - conditionalDeficit n μ <
      (failureScale n x μ - 3*x) / 20) :
    conditionalVariance n μ / (failureScale n x μ)^2 ≤
      ((supportCutoff n x μ - conditionalDeficit n μ) / failureScale n x μ) *
        (1 + 13 * (x / failureScale n x μ) / 24 -
          (supportCutoff n x μ - conditionalDeficit n μ) / failureScale n x μ) ∧
      conditionalVariance n μ / (failureScale n x μ)^2 < 19 / 400 := by
  let D := failureScale n x μ
  let e := (supportCutoff n x μ - conditionalDeficit n μ) / D
  let u := x / D
  have hD : 0 < D := maximizer_failureScale_pos hx hxlt hμ
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hr := maximizer_conditionalDeficit_le_cutoff hx hxlt hμ
  have he : 0 ≤ e := div_nonneg (sub_nonneg.mpr hr) hD.le
  have hu : 0 < u := div_pos hx hD
  have hu1 : u < 1 / 3 := by
    apply (div_lt_iff₀ hD).mpr
    dsimp [D] at *
    linarith
  have he1 : e ≤ (1 - 3*u) / 20 := by
    apply (div_le_iff₀ hD).mpr
    have huD : u * D = x := div_mul_cancel₀ x hD.ne'
    dsimp [D] at *
    nlinarith
  have hB : failureExcessParameter n x μ = D + (1-c)*x -
      (supportCutoff n x μ - conditionalDeficit n μ) := by
    dsimp [failureExcessParameter, D]
    linarith
  have hBdiv : failureExcessParameter n x μ / D ≤ 1 + 13*u/24-e := by
    rw [hB, sub_div, add_div, div_self hD.ne', mul_div_assoc]
    change 1 + (1-c)*u-e ≤ 1+13*u/24-e
    nlinarith
  have hv := maximizer_conditionalVariance_bound hx hxlt hμ
  have hvnorm : conditionalVariance n μ / D^2 ≤ e * (1+13*u/24-e) := by
    calc
      _ ≤ failureExcessParameter n x μ * (supportCutoff n x μ - conditionalDeficit n μ) / D^2 :=
        div_le_div_of_nonneg_right hv (sq_nonneg D)
      _ = (failureExcessParameter n x μ / D) * e := by dsimp [e]; field_simp
      _ ≤ (1+13*u/24-e)*e := mul_le_mul_of_nonneg_right hBdiv he
      _ = _ := mul_comm _ _
  exact ⟨hvnorm, hvnorm.trans_lt ((SharpTailMatching.SupportAlgebra.conditional_variance_upper
    hu hu1 he he1).1.trans_lt (SharpTailMatching.SupportAlgebra.conditional_variance_upper
      hu hu1 he he1).2)⟩

theorem maximizer_no_intermediate_contact {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ) / 24 ≤ c)
    (hcritical : 1 - ((n+1 : ℕ) : ℝ) * x = c * x)
    (hprox : supportCutoff n x μ - conditionalDeficit n μ <
      (failureScale n x μ - 3*x) / 20) {y : ℝ≥0}
    (hcontact : sectionFailure n μ y = (1 - tailProbability (n+1) μ) *
      (supportCutoff n x μ - (y : ℝ)) / failureScale n x μ)
    (hy0 : x + failureScale n x μ / 16 ≤ (y : ℝ))
    (hy1 : (y : ℝ) ≤ x + 17 * failureScale n x μ / 20) : False := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  let D := failureScale n x μ
  let e := (supportCutoff n x μ - conditionalDeficit n μ) / D
  let u := x / D
  let ξ := ((y : ℝ) - x) / D
  have hD : 0 < D := maximizer_failureScale_pos hx hxlt hμ
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hr := maximizer_conditionalDeficit_le_cutoff hx hxlt hμ
  have he : 0 ≤ e := div_nonneg (sub_nonneg.mpr hr) hD.le
  have hu : 0 < u := div_pos hx hD
  have hu1 : u < 1 / 3 := by
    apply (div_lt_iff₀ hD).mpr
    dsimp [D] at *
    linarith
  have huD : u * D = x := div_mul_cancel₀ x hD.ne'
  have heD : e * D = supportCutoff n x μ - conditionalDeficit n μ :=
    div_mul_cancel₀ _ hD.ne'
  have hξD : ξ * D = (y : ℝ) - x := div_mul_cancel₀ _ hD.ne'
  have he1 : e ≤ (1 - 3*u) / 20 := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D] at *
    nlinarith
  have hξ0 : (1 : ℝ)/16 ≤ ξ := by
    apply (le_div_iff₀ hD).mpr
    dsimp [D] at *
    linarith
  have hξ1 : ξ ≤ 17/20 := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D] at *
    linarith
  have hyr : (y : ℝ) < conditionalDeficit n μ := by
    dsimp [D] at *
    linarith
  have hmass := maximizer_contact_deficit_mass hx hxlt hμ hcontact
  have hlower := cantelli_variance_lower_bound (deficit_memLp n (failureMeasure n μ) 2)
    (by simpa only [integral_failureMeasure_deficit] using hyr)
    (show ξ < 1 by linarith) hmass
  rw [integral_failureMeasure_deficit, variance_deficit_failureMeasure] at hlower
  have hid : conditionalDeficit n μ - (y : ℝ) = D * (1-e-ξ) := by
    dsimp [D] at *
    nlinarith
  rw [hid] at hlower
  have hnorm : ξ * (1-e-ξ)^2 / (1-ξ) ≤ conditionalVariance n μ / D^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
    convert hlower using 1 <;> ring
  exact SharpTailMatching.SupportAlgebra.no_intermediate_contact hu hu1 he he1 hξ0 hξ1
    (maximizer_normalized_variance_upper hx hxlt hμ hc hcritical hprox).1 hnorm

/-- Almost every value belongs to the separated lower or upper support interval.
The proof uses the original law's genuine first-variation contact relation. -/
theorem maximizer_ae_support_gap {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ) / 24 ≤ c)
    (hcritical : 1 - ((n+1 : ℕ) : ℝ) * x = c * x)
    (hprox : supportCutoff n x μ - conditionalDeficit n μ <
      (failureScale n x μ - 3*x) / 20) :
    ∀ᵐ y : ℝ≥0 ∂(μ : Measure ℝ≥0),
      (y : ℝ) ≤ x + failureScale n x μ / 16 ∨
        (x + 17 * failureScale n x μ / 20 < (y : ℝ) ∧ (y : ℝ) ≤ supportCutoff n x μ) := by
  filter_upwards [maximizer_ae_failure_tilt hx hxlt hμ,
    maximizer_ae_below_supportCutoff hx hxlt hμ] with y hy hbound
  by_cases hl : (y : ℝ) ≤ x + failureScale n x μ / 16
  · exact Or.inl hl
  · right
    refine ⟨?_, hbound⟩
    by_contra h
    exact maximizer_no_intermediate_contact hx hxlt hμ hc hcritical hprox hy
      (le_of_lt (lt_of_not_ge hl)) (le_of_not_gt h)

end SharpTailMatching.Probability
