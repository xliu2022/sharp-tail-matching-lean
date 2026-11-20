module

public import SharpTailMatching.Probability.UpperSupport
public import SharpTailMatching.Probability.StopLossSecants
public import Mathlib.MeasureTheory.Function.EssSup

/-! # Conditional lower and upper laws and their essential support endpoint -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def conditionalLaw (μ : ProbabilityMeasure ℝ≥0) (s : Set ℝ≥0)
    (hs : (μ : Measure ℝ≥0) s ≠ 0) : ProbabilityMeasure ℝ≥0 :=
  ⟨ProbabilityTheory.cond (μ : Measure ℝ≥0) s, cond_isProbabilityMeasure hs⟩

theorem conditionalLaw_absolutelyContinuous (μ : ProbabilityMeasure ℝ≥0) (s : Set ℝ≥0)
    (hs : (μ : Measure ℝ≥0) s ≠ 0) :
    (conditionalLaw μ s hs : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0) := cond_absolutelyContinuous

theorem conditionalLaw_ae_mem (μ : ProbabilityMeasure ℝ≥0) {s : Set ℝ≥0}
    (hs : MeasurableSet s) (hpos : (μ : Measure ℝ≥0) s ≠ 0) :
    ∀ᵐ z ∂(conditionalLaw μ s hpos : Measure ℝ≥0), z ∈ s := ae_cond_mem hs

theorem conditionalLaw_scaled (μ : ProbabilityMeasure ℝ≥0) (s : Set ℝ≥0)
    (hpos : (μ : Measure ℝ≥0) s ≠ 0) :
    (μ : Measure ℝ≥0) s • (conditionalLaw μ s hpos : Measure ℝ≥0) = (μ : Measure ℝ≥0).restrict s := by
  change (μ : Measure ℝ≥0) s • ((μ : Measure ℝ≥0) s)⁻¹ • (μ : Measure ℝ≥0).restrict s = _
  rw [smul_smul, ENNReal.mul_inv_cancel hpos (measure_ne_top _ _), one_smul]

theorem conditionalLaw_decomposition (μ : ProbabilityMeasure ℝ≥0) {s : Set ℝ≥0}
    (hs : MeasurableSet s) (hpos : (μ : Measure ℝ≥0) s ≠ 0)
    (hcpos : (μ : Measure ℝ≥0) sᶜ ≠ 0) :
    (μ : Measure ℝ≥0) =
      ENNReal.ofReal ((μ : Measure ℝ≥0).real s) • (conditionalLaw μ s hpos : Measure ℝ≥0) +
      ENNReal.ofReal (1-(μ : Measure ℝ≥0).real s) • (conditionalLaw μ sᶜ hcpos : Measure ℝ≥0) := by
  rw [← probReal_compl_eq_one_sub hs, Measure.real, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
    conditionalLaw_scaled, conditionalLaw_scaled, Measure.restrict_add_restrict_compl hs]

theorem conditionalLaw_integrable (μ : ProbabilityMeasure ℝ≥0) (s : Set ℝ≥0)
    (hpos : (μ : Measure ℝ≥0) s ≠ 0) (f : ℝ≥0 → ℝ) (hf : Integrable f (μ : Measure ℝ≥0)) :
    Integrable f (conditionalLaw μ s hpos : Measure ℝ≥0) := by
  exact hf.restrict.smul_measure (ENNReal.inv_ne_top.mpr hpos)

def essentialUpper (μ : ProbabilityMeasure ℝ≥0) : ℝ≥0 := essSup id (μ : Measure ℝ≥0)

theorem ae_le_essentialUpper (μ : ProbabilityMeasure ℝ≥0) {b : ℝ≥0}
    (hb : ∀ᵐ z ∂(μ : Measure ℝ≥0), z ≤ b) :
    ∀ᵐ z ∂(μ : Measure ℝ≥0), z ≤ essentialUpper μ :=
  ae_le_essSup ⟨b, hb⟩

theorem essentialUpper_le (μ : ProbabilityMeasure ℝ≥0) {b : ℝ≥0}
    (hb : ∀ᵐ z ∂(μ : Measure ℝ≥0), z ≤ b) : essentialUpper μ ≤ b :=
  essSup_le_of_ae_le b hb

/-- The essential upper endpoint of any bounded component of a maximizing law
is itself a contact point. Monotonicity and the defining essential-supremum
property replace an appeal to a sequence of contact points. -/
theorem maximizer_essentialUpper_contact {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ ν : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hν : (ν : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    {b : ℝ≥0} (hb : ∀ᵐ z ∂(ν : Measure ℝ≥0), z ≤ b) :
    sectionTail n μ (essentialUpper ν) = tailProbability n μ +
      ((tailProbability (n+1) μ-tailProbability n μ)/x) * (essentialUpper ν : ℝ) := by
  let s := (tailProbability (n+1) μ-tailProbability n μ)/x
  have hs : 0 < s := div_pos (maximizer_tail_gap_pos hx hxlt hμ) hx
  have hline := maximizer_supporting_line hx hxlt hμ (essentialUpper ν)
  simp only [sectionTail_zero] at hline
  apply le_antisymm hline
  have hnonneg : 0 ≤ (sectionTail n μ (essentialUpper ν)-tailProbability n μ)/s := by
    apply div_nonneg _ hs.le
    have hmon := monotone_sectionTail n μ (show (0 : ℝ≥0) ≤ essentialUpper ν from zero_le)
    simpa only [sectionTail_zero] using sub_nonneg.mpr hmon
  let a : ℝ≥0 := ⟨(sectionTail n μ (essentialUpper ν)-tailProbability n μ)/s, hnonneg⟩
  have hae : ∀ᵐ z ∂(ν : Measure ℝ≥0), z ≤ a := by
    filter_upwards [ae_le_essentialUpper ν hb, hν.ae_le (maximizer_ae_contact hx hxlt hμ)] with z hz hcontact
    have hmon := monotone_sectionTail n μ hz
    rw [hcontact] at hmon
    change (z : ℝ) ≤ (sectionTail n μ (essentialUpper ν)-tailProbability n μ)/s
    apply (le_div_iff₀ hs).mpr
    dsimp [s] at *
    linarith
  have hbnd := essentialUpper_le ν hae
  have hbndR : (essentialUpper ν : ℝ) ≤ (sectionTail n μ (essentialUpper ν)-tailProbability n μ)/s := hbnd
  have hmul := (le_div_iff₀ hs).mp hbndR
  dsimp [s] at *
  linarith

theorem maximizer_separated_components {n : ℕ} {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ)/24 ≤ c)
    (hcritical : 1-((n+1 : ℕ) : ℝ)*x = c*x)
    (hprox : supportCutoff n x μ-conditionalDeficit n μ < (failureScale n x μ-3*x)/20) :
    ∃ (q : ℝ) (L U : ProbabilityMeasure ℝ≥0), 0 < q ∧ q < 1 ∧
      (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) + ENNReal.ofReal (1-q) • (U : Measure ℝ≥0) ∧
      (L : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0) ∧ (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0) ∧
      (∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), (z : ℝ) ≤ x+failureScale n x μ/16) ∧
      (∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (z : ℝ) ∧
        (z : ℝ) ≤ supportCutoff n x μ) := by
  let s : Set ℝ≥0 := {z | (z : ℝ) ≤ x+failureScale n x μ/16}
  have hs : MeasurableSet s := by measurability
  have hD := maximizer_failureScale_pos hx hxlt hμ
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hkx : ((n+1 : ℕ) : ℝ)*x < 1 := by
    have h := mul_lt_mul_of_pos_left hxlt hk
    rwa [mul_inv_cancel₀ hk.ne'] at h
  have hdom := zero_atom_dominates μ (mul_nonneg hk.le hx.le)
    (maximizer_positive_mass_le (by omega) hx.le hxlt hμ)
  have hzero : 0 < (μ : Measure ℝ≥0) {0} := by
    apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hkx))
    simpa using hdom {0}
  have hspos : 0 < (μ : Measure ℝ≥0) s := by
    refine hzero.trans_le (measure_mono ?_)
    intro z hz
    have hz0 : z = 0 := hz
    subst z
    change (0 : ℝ) ≤ x+failureScale n x μ/16
    positivity
  have hcpos : 0 < (μ : Measure ℝ≥0) sᶜ := by
    refine (maximizer_upper_support_positive hx hxlt hμ hc hcritical hprox).trans_le (measure_mono ?_)
    intro z hz
    change ¬ (z : ℝ) ≤ x+failureScale n x μ/16
    change x+17*failureScale n x μ/20 < (z : ℝ) at hz
    linarith
  let L := conditionalLaw μ s hspos.ne'
  let U := conditionalLaw μ sᶜ hcpos.ne'
  have hL := conditionalLaw_absolutelyContinuous μ s hspos.ne'
  have hU := conditionalLaw_absolutelyContinuous μ sᶜ hcpos.ne'
  refine ⟨(μ : Measure ℝ≥0).real s, L, U, ?_, ?_,
    conditionalLaw_decomposition μ hs hspos.ne' hcpos.ne', hL, hU,
    conditionalLaw_ae_mem μ hs hspos.ne', ?_⟩
  · exact ENNReal.toReal_pos hspos.ne' (measure_ne_top _ _)
  · have hcomp := ENNReal.toReal_pos hcpos.ne' (measure_ne_top (μ : Measure ℝ≥0) sᶜ)
    change 0 < (μ : Measure ℝ≥0).real sᶜ at hcomp
    rw [probReal_compl_eq_one_sub hs] at hcomp
    linarith
  · filter_upwards [conditionalLaw_ae_mem μ hs.compl hcpos.ne',
      hU.ae_le (maximizer_ae_support_gap hx hxlt hμ hc hcritical hprox)] with z hz hgap
    exact hgap.resolve_left hz

end SharpTailMatching.Probability
