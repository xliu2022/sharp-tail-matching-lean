module

public import SharpTailMatching.Probability.Covariance

/-! # The exact independent-pair covariance remainder -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem covariance_symmetrization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ z : Ω × Ω, (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ) =
      2 * covariance f g μ := by
  have hf₁ := hf.comp_fst μ
  have hf₂ := hf.comp_snd μ
  have hg₁ := hg.comp_fst μ
  have hg₂ := hg.comp_snd μ
  have hfst : covariance (fun z : Ω × Ω => f z.1) (fun z => g z.1) (μ.prod μ) =
      covariance f g μ := by
    have hm : (μ.prod μ).map Prod.fst = μ := measurePreserving_fst.map_eq
    have h := covariance_map_fun (μ := μ.prod μ) (Z := Prod.fst)
      (by simpa only [hm] using hf.aestronglyMeasurable)
      (by simpa only [hm] using hg.aestronglyMeasurable) measurable_fst.aemeasurable
    simpa only [hm] using h.symm
  have hsnd : covariance (fun z : Ω × Ω => f z.2) (fun z => g z.2) (μ.prod μ) =
      covariance f g μ := by
    have hm : (μ.prod μ).map Prod.snd = μ := measurePreserving_snd.map_eq
    have h := covariance_map_fun (μ := μ.prod μ) (Z := Prod.snd)
      (by simpa only [hm] using hf.aestronglyMeasurable)
      (by simpa only [hm] using hg.aestronglyMeasurable) measurable_snd.aemeasurable
    simpa only [hm] using h.symm
  have hmean : (∫ z : Ω × Ω, f z.1 - f z.2 ∂μ.prod μ) = 0 := by
    rw [integral_sub (hf₁.integrable one_le_two) (hf₂.integrable one_le_two)]
    rw [integral_prod _ (hf₁.integrable one_le_two), integral_prod _ (hf₂.integrable one_le_two)]
    simp
  have hexpand := covariance_fun_sub_fun_sub hf₁ hf₂ hg₁ hg₂
  rw [hfst, hsnd, covariance_fst_snd_prod hf hg,
    covariance_comm (fun z : Ω × Ω => f z.2), covariance_fst_snd_prod hg hf] at hexpand
  have hcov := covariance_eq_sub (hf₁.sub hf₂) (hg₁.sub hg₂)
  change covariance (fun z : Ω × Ω => f z.1 - f z.2) (fun z => g z.1 - g z.2) (μ.prod μ) =
    (∫ z : Ω × Ω, (f z.1 - f z.2) * (g z.1 - g z.2) ∂μ.prod μ) -
      (∫ z : Ω × Ω, f z.1 - f z.2 ∂μ.prod μ) *
        (∫ z : Ω × Ω, g z.1 - g z.2 ∂μ.prod μ) at hcov
  rw [hmean, zero_mul, sub_zero] at hcov
  linarith

def covarianceRemainder (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫ z : ℝ≥0 × ℝ≥0, ((z.1 : ℝ) - (z.2 : ℝ)) *
    (stopLoss n μ z.1 - stopLoss n μ z.2 +
      (1 - tailProbability n μ) * ((z.1 : ℝ) - (z.2 : ℝ)))
      ∂(μ : Measure ℝ≥0).prod (μ : Measure ℝ≥0)

theorem covarianceRemainder_nonneg (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    0 ≤ covarianceRemainder n μ := by
  apply integral_nonneg
  intro z
  have hmono := monotone_adjusted_stopLoss n μ
  by_cases hz : z.1 ≤ z.2
  · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (show (z.1 : ℝ) ≤ z.2 from hz))
    have h := hmono hz
    dsimp only at h
    nlinarith
  · apply mul_nonneg (sub_nonneg.mpr (show (z.2 : ℝ) ≤ z.1 from le_of_not_ge hz))
    have h := hmono (le_of_not_ge hz)
    dsimp only at h
    nlinarith

theorem covarianceRemainder_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hX : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (μ : Measure ℝ≥0)) :
    covarianceRemainder n μ =
      2 * (covariance (fun z : ℝ≥0 => (z : ℝ)) (stopLoss n μ) (μ : Measure ℝ≥0) +
        (1 - tailProbability n μ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0)) := by
  have h := covariance_symmetrization (μ : Measure ℝ≥0) (fun z : ℝ≥0 => (z : ℝ))
    (fun z => stopLoss n μ z + (1 - tailProbability n μ) * (z : ℝ)) hX
      ((memLp_stopLoss n μ 2).add (hX.const_mul _))
  change _ = 2 * covariance (fun z : ℝ≥0 => (z : ℝ))
    (stopLoss n μ + fun z : ℝ≥0 => (1 - tailProbability n μ) * (z : ℝ)) (μ : Measure ℝ≥0) at h
  rw [covariance_add_right hX (memLp_stopLoss n μ 2) (hX.const_mul (1 - tailProbability n μ)),
    covariance_const_mul_right, covariance_self hX.aemeasurable] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with z
  ring

/-- The exact covariance identity, with its remainder expressed as a stop-loss
secant. This representation retains the full independent-pair contribution. -/
theorem maximizer_covariance_identity {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    failureExcessParameter n x μ * (supportCutoff n x μ - conditionalDeficit n μ) =
      conditionalVariance n μ + ((n+1 : ℕ) : ℝ) /
        (2 * (1 - tailProbability (n+1) μ)) * covarianceRemainder n μ := by
  have hp : 0 < 1 - tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  have hcov := maximizer_stopLoss_covariance hx hxlt hμ
  have hvar : ((n+1 : ℕ) : ℝ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) =
      failureScale n x μ * failureExcessParameter n x μ := by
    rw [← variance_iidSum _ μ (maximizer_memLp_coe hx hxlt hμ 2), maximizer_variance_identity hx hxlt hμ]
  have hbridge : (1 - tailProbability n μ) * failureScale n x μ =
      (1 - tailProbability (n+1) μ) * supportCutoff n x μ := by
    dsimp [supportCutoff, failureScale]
    field_simp
  rw [covarianceRemainder_eq n μ (maximizer_memLp_coe hx hxlt hμ 2)]
  have hsecond : ((n+1 : ℕ) : ℝ) *
      (covariance (fun z : ℝ≥0 => (z : ℝ)) (stopLoss n μ) (μ : Measure ℝ≥0) +
        (1 - tailProbability n μ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0)) =
      (1 - tailProbability (n+1) μ) *
        (failureExcessParameter n x μ * (supportCutoff n x μ - conditionalDeficit n μ) -
          conditionalVariance n μ) := by
    linear_combination hcov + (1 - tailProbability n μ) * hvar +
      (failureExcessParameter n x μ) * hbridge
  apply (mul_left_cancel₀ hp.ne')
  field_simp
  linear_combination -hsecond

end SharpTailMatching.Probability
