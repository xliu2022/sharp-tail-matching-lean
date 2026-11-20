module

public import SharpTailMatching.Probability.Sections

/-! # The support cutoff and the conditional failure tilt -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def supportCutoff (n : ℕ) (x : ℝ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  x * (1 - tailProbability n μ) / (tailProbability (n+1) μ - tailProbability n μ)

def failureScale (n : ℕ) (x : ℝ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  x * (1 - tailProbability (n+1) μ) / (tailProbability (n+1) μ - tailProbability n μ)

def sectionFailure (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) : ℝ :=
  ((Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0)))
    {y : Fin n → ℝ≥0 | z + ∑ i, y i < 1}).toReal

theorem sectionFailure_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    sectionFailure n μ z = 1 - sectionTail n μ z := by
  rw [sectionTail_eq]
  have h := probReal_compl_eq_one_sub (μ := Measure.pi
    (fun _ : Fin n => (μ : Measure ℝ≥0)))
    (show MeasurableSet {y : Fin n → ℝ≥0 | 1 ≤ z + ∑ i, y i} by measurability)
  simpa [sectionFailure, Measure.real, Set.compl_ofPred, not_le] using h

theorem maximizer_short_tail_lt_one {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : tailProbability n μ < 1 := by
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hkx : ((n+1 : ℕ) : ℝ) * x < 1 := by
    calc
      ((n+1 : ℕ) : ℝ) * x < ((n+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)⁻¹ :=
        mul_lt_mul_of_pos_left hxlt hk
      _ = 1 := mul_inv_cancel₀ hk.ne'
  refine (tailProbability_le_mul_mean n x hx.le μ hμ.1).trans_lt ?_
  push_cast at hkx
  nlinarith

theorem maximizer_tail_gap_pos {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : 0 < tailProbability (n+1) μ - tailProbability n μ := by
  have hH := maximizer_short_tail_lt_one hx hxlt hμ
  have hline := maximizer_supporting_line hx hxlt hμ 1
  simp only [sectionTail_one, sectionTail_zero, NNReal.coe_one, mul_one] at hline
  have hmul := mul_le_mul_of_nonneg_right hline hx.le
  have hdiv := div_mul_cancel₀ (tailProbability (n+1) μ - tailProbability n μ) hx.ne'
  nlinarith

theorem maximizer_supportCutoff_le_one {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : supportCutoff n x μ ≤ 1 := by
  have hgap := maximizer_tail_gap_pos hx hxlt hμ
  apply (div_le_one hgap).mpr
  have hline := maximizer_supporting_line hx hxlt hμ 1
  simp only [sectionTail_one, sectionTail_zero, NNReal.coe_one, mul_one] at hline
  have hmul := mul_le_mul_of_nonneg_right hline hx.le
  have hdiv := div_mul_cancel₀ (tailProbability (n+1) μ - tailProbability n μ) hx.ne'
  nlinarith

theorem maximizer_failureScale_pos {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : 0 < failureScale n x μ := by
  exact div_pos (mul_pos hx (sub_pos.mpr
    (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)))
    (maximizer_tail_gap_pos hx hxlt hμ)

theorem maximizer_supportCutoff_sub_mean {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : supportCutoff n x μ - x = failureScale n x μ := by
  have hgap := (maximizer_tail_gap_pos hx hxlt hμ).ne'
  dsimp [supportCutoff, failureScale]
  field_simp
  ring

theorem maximizer_ae_below_supportCutoff {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    ∀ᵐ z : ℝ≥0 ∂(μ : Measure ℝ≥0), (z : ℝ) ≤ supportCutoff n x μ := by
  have hgap := maximizer_tail_gap_pos hx hxlt hμ
  have hb : 0 < (tailProbability (n+1) μ - tailProbability n μ) / x := div_pos hgap hx
  have hbM : ((tailProbability (n+1) μ - tailProbability n μ) / x) * supportCutoff n x μ =
      1 - tailProbability n μ := by
    dsimp [supportCutoff]
    field_simp
  filter_upwards [maximizer_ae_contact hx hxlt hμ] with z hz
  have hupper := sectionTail_le_one n μ z
  apply le_of_mul_le_mul_left (a := (tailProbability (n+1) μ - tailProbability n μ) / x) _ hb
  rw [hbM]
  linarith

/-- Conditional failure weights are affine at almost every sampled value. -/
theorem maximizer_ae_failure_tilt {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    ∀ᵐ z ∂(μ : Measure ℝ≥0), sectionFailure n μ z =
      (1 - tailProbability (n+1) μ) * (supportCutoff n x μ - (z : ℝ)) / failureScale n x μ := by
  have hgap := (maximizer_tail_gap_pos hx hxlt hμ).ne'
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  filter_upwards [maximizer_ae_contact hx hxlt hμ] with z hz
  rw [sectionFailure_eq, hz]
  dsimp [supportCutoff, failureScale]
  field_simp
  ring

/-- The unnormalized expectation of a function of the first summand on the
failure event. -/
def failureIntegral (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (φ : ℝ≥0 → ℝ) : ℝ :=
  ∫ w : Fin (n+1) → ℝ≥0,
    {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1}.indicator (fun w => φ (w 0)) w
      ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))

theorem failureIntegral_eq_sections (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (φ : ℝ≥0 → ℝ) (hφ : Measurable φ) (hint : Integrable φ (μ : Measure ℝ≥0)) :
    failureIntegral n μ φ = ∫ z : ℝ≥0, sectionFailure n μ z * φ z ∂(μ : Measure ℝ≥0) := by
  let ψ : (Fin (n+1) → ℝ≥0) → ℝ :=
    {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1}.indicator (fun w => φ (w 0))
  have hψ : Measurable ψ := (hφ.comp (measurable_pi_apply 0)).indicator (by measurability)
  have hfamily : (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) =
      Fin.cons (μ : Measure ℝ≥0) (fun _ : Fin n => (μ : Measure ℝ≥0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change (∫ w, ψ w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = _
  rw [hfamily, ← pi_cons_map, integral_map (by fun_prop) hψ.aestronglyMeasurable]
  let A : Set (ℝ≥0 × (Fin n → ℝ≥0)) := {p | p.1 + ∑ i, p.2 i < 1}
  have hA : MeasurableSet A := by measurability
  have hfun : (fun p : ℝ≥0 × (Fin n → ℝ≥0) => ψ (Fin.cons p.1 p.2)) =
      A.indicator (fun p => φ p.1) := by
    funext p
    simp [ψ, A, Set.indicator_apply, Fin.sum_univ_succ]
  rw [hfun, integral_prod _ ((hint.comp_fst _).indicator hA)]
  apply integral_congr_ae
  filter_upwards [] with z
  change (∫ y : Fin n → ℝ≥0,
    {y : Fin n → ℝ≥0 | z + ∑ i, y i < 1}.indicator (fun _ => φ z) y
      ∂Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0))) = _
  rw [integral_indicator_const _ (by measurability)]
  rfl

/-- The full failure-tilt identity, valid for every integrable Borel test
function, hence in particular for every bounded Borel test function. -/
theorem maximizer_failure_tilt {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (φ : ℝ≥0 → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ (μ : Measure ℝ≥0)) :
    failureIntegral n μ φ / (1 - tailProbability (n+1) μ) =
      (∫ z : ℝ≥0, (supportCutoff n x μ - (z : ℝ)) * φ z ∂(μ : Measure ℝ≥0)) /
        failureScale n x μ := by
  have hp : 1 - tailProbability (n+1) μ ≠ 0 :=
    (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  have hD := (maximizer_failureScale_pos hx hxlt hμ).ne'
  rw [failureIntegral_eq_sections n μ φ hφ hint]
  have hfun : (fun z : ℝ≥0 => sectionFailure n μ z * φ z) =ᵐ[(μ : Measure ℝ≥0)]
      (fun z : ℝ≥0 => ((1 - tailProbability (n+1) μ) / failureScale n x μ) *
        ((supportCutoff n x μ - (z : ℝ)) * φ z)) := by
    filter_upwards [maximizer_ae_failure_tilt hx hxlt hμ] with z hz
    rw [hz]
    ring
  rw [integral_congr_ae hfun, integral_const_mul]
  field_simp

end SharpTailMatching.Probability
