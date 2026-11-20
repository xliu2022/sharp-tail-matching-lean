module

public import SharpTailMatching.Probability.FailureMoments
public import Mathlib.Probability.ConditionalProbability

/-! # The variance and conditional-deficit identity -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

/-- The exact identity `Var(S_k) = D B`, with all parameters derived from the
maximizing law and the genuine independent-sum distribution. -/
theorem maximizer_variance_identity {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    variance (iidSum (n+1)) (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      failureScale n x μ * failureExcessParameter n x μ := by
  have hm := maximizer_mean_eq (by omega : 1 ≤ n+1) hx.le hxlt hμ
  have hmfin : mean μ ≠ ∞ := by rw [hm]; exact ENNReal.ofReal_ne_top
  have hmem := maximizer_memLp_coe hx hxlt hμ 2
  have hint : Integrable (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) :=
    integrable_coe_of_mean_ne_top μ hmfin
  have hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal, hm, ENNReal.toReal_ofReal hx.le]
  have hweighted :
      (∫ z : ℝ≥0, (supportCutoff n x μ - (z : ℝ)) * (z : ℝ) ∂(μ : Measure ℝ≥0)) =
        supportCutoff n x μ * x - ∫ z : ℝ≥0, (z : ℝ)^2 ∂(μ : Measure ℝ≥0) := by
    calc
      _ = ∫ z : ℝ≥0, supportCutoff n x μ * (z : ℝ) - (z : ℝ)^2 ∂(μ : Measure ℝ≥0) := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = _ := by
        rw [integral_sub (hint.const_mul _) hmem.integrable_sq, integral_const_mul, hmean]
  have htilt := maximizer_failure_tilt hx hxlt hμ (fun z : ℝ≥0 => (z : ℝ)) (by fun_prop) hint
  rw [hweighted] at htilt
  have hp : 1 - tailProbability (n+1) μ ≠ 0 :=
    (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  have hD := (maximizer_failureScale_pos hx hxlt hμ).ne'
  have hsum := failure_sum_add_deficit n μ hmfin
  have hsumdiv : ((n+1 : ℕ) : ℝ) *
      (failureIntegral n μ (fun z => (z : ℝ)) / (1 - tailProbability (n+1) μ)) +
        conditionalDeficit n μ = 1 := by
    dsimp [conditionalDeficit]
    field_simp
    linarith
  rw [htilt] at hsumdiv
  have hcore := congrArg (fun r : ℝ => r * failureScale n x μ) hsumdiv
  field_simp at hcore
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  rw [variance_iidSum _ μ hmem, variance_eq_sub hmem, hmean]
  change ((n+1 : ℕ) : ℝ) *
      ((∫ z : ℝ≥0, (z : ℝ)^2 ∂(μ : Measure ℝ≥0)) - x^2) =
        failureScale n x μ * (conditionalDeficit n μ - (1 - ((n+1 : ℕ) : ℝ) * x))
  linear_combination -hcore + (((n+1 : ℕ) : ℝ) * x) * hM

theorem maximizer_failureExcessParameter_pos {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : 0 < failureExcessParameter n x μ := by
  have hvar : 0 < variance (iidSum (n+1))
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) := by
    rw [variance_iidSum _ μ (maximizer_memLp_coe hx hxlt hμ 2)]
    exact mul_pos (by positivity) (maximizer_variance_pos hx hxlt hμ)
  rw [maximizer_variance_identity hx hxlt hμ] at hvar
  exact (mul_pos_iff_of_pos_left (maximizer_failureScale_pos hx hxlt hμ)).mp hvar

end SharpTailMatching.Probability
