module

public import SharpTailMatching.Probability.Symmetrization

/-! # Quantitative secants for the retained covariance remainder

These inequalities give the cross-component lower bound directly, without
differentiating the stop-loss kernel at its corners.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem stopLoss_secant (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) {u v : ℝ≥0} (huv : u ≤ v) :
    stopLoss n μ u ≤ stopLoss n μ v + sectionFailure n μ u * ((v : ℝ)-(u : ℝ)) := by
  have huvR : (u : ℝ) ≤ v := huv
  let F : Set (Fin n → ℝ≥0) := {s | u + ∑ i, s i < 1}
  have hF : MeasurableSet F := by measurability
  have hpoint (s : Fin n → ℝ≥0) : stopLossIntegrand n u s ≤ stopLossIntegrand n v s +
      F.indicator (fun _ => (v : ℝ)-(u : ℝ)) s := by
    by_cases hs : s ∈ F
    · rw [Set.indicator_of_mem hs]
      apply max_le
      · have := le_max_left (1-(v : ℝ)-iidSum n s) 0
        change 1-(u : ℝ)-iidSum n s ≤ max (1-(v : ℝ)-iidSum n s) 0 + _
        linarith
      · have := le_max_right (1-(v : ℝ)-iidSum n s) 0
        change 0 ≤ max (1-(v : ℝ)-iidSum n s) 0 + _
        linarith
    · have hnn : 1 ≤ u + ∑ i, s i := le_of_not_gt hs
      have hreal : 1 ≤ (u : ℝ)+iidSum n s := by dsimp [iidSum]; exact_mod_cast hnn
      have hu0 : 1-(u : ℝ)-iidSum n s ≤ 0 := by linarith
      have hv0 : 1-(v : ℝ)-iidSum n s ≤ 0 := by linarith
      simp [stopLossIntegrand, hs, max_eq_right hu0, max_eq_right hv0]
  have h := integral_mono (integrable_stopLossIntegrand n μ u)
    ((integrable_stopLossIntegrand n μ v).add ((integrable_const _).indicator hF)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_stopLossIntegrand n μ v) ((integrable_const _).indicator hF),
    integral_indicator_const _ hF] at h
  exact h

theorem adjusted_stopLoss_secant (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) {u v : ℝ≥0} (huv : u ≤ v) :
    ((v : ℝ)-(u : ℝ)) * (sectionTail n μ u-tailProbability n μ) ≤
      stopLoss n μ v - stopLoss n μ u + (1-tailProbability n μ)*((v : ℝ)-(u : ℝ)) := by
  have h := stopLoss_secant n μ huv
  rw [sectionFailure_eq] at h
  nlinarith

theorem adjusted_stopLoss_cross_secant (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    {u b v : ℝ≥0} (hub : u ≤ b) (hbv : b ≤ v) :
    ((v : ℝ)-(b : ℝ)) * (sectionTail n μ b-tailProbability n μ) ≤
      stopLoss n μ v - stopLoss n μ u + (1-tailProbability n μ)*((v : ℝ)-(u : ℝ)) := by
  have h := adjusted_stopLoss_secant n μ hbv
  have hmono := monotone_adjusted_stopLoss n μ hub
  dsimp only at hmono
  nlinarith

theorem covariance_pair_cross_lower (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    {u b v : ℝ≥0} (hub : u ≤ b) (hbv : b ≤ v) :
    ((v : ℝ)-(u : ℝ)) * ((v : ℝ)-(b : ℝ)) * (sectionTail n μ b-tailProbability n μ) ≤
      ((u : ℝ)-(v : ℝ)) * (stopLoss n μ u-stopLoss n μ v +
        (1-tailProbability n μ)*((u : ℝ)-(v : ℝ))) := by
  have h := mul_le_mul_of_nonneg_left (adjusted_stopLoss_cross_secant n μ hub hbv)
    (sub_nonneg.mpr (show (u : ℝ) ≤ v from hub.trans hbv))
  nlinarith

theorem maximizer_contact_pair_cross_lower {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) {u b v : ℝ≥0} (hub : u ≤ b) (hbv : b ≤ v)
    (hb : sectionTail n μ b = tailProbability n μ +
      ((tailProbability (n+1) μ-tailProbability n μ)/x)*(b : ℝ)) :
    ((1-tailProbability (n+1) μ)*(b : ℝ)/failureScale n x μ) *
      ((v : ℝ)-(u : ℝ))*((v : ℝ)-(b : ℝ)) ≤
      ((u : ℝ)-(v : ℝ)) * (stopLoss n μ u-stopLoss n μ v +
        (1-tailProbability n μ)*((u : ℝ)-(v : ℝ))) := by
  have h := covariance_pair_cross_lower n μ hub hbv
  rw [hb, add_sub_cancel_left] at h
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  have hgap := (maximizer_tail_gap_pos hx hxlt hμ).ne'
  have hslope : (1-tailProbability (n+1) μ)/failureScale n x μ =
      (tailProbability (n+1) μ-tailProbability n μ)/x := by
    dsimp [failureScale]
    field_simp
  calc
    _ = ((v : ℝ)-(u : ℝ))*((v : ℝ)-(b : ℝ)) *
        (((1-tailProbability (n+1) μ)/failureScale n x μ)*(b : ℝ)) := by ring
    _ = _ := by rw [hslope]
    _ ≤ _ := h

end SharpTailMatching.Probability
