module

public import SharpTailMatching.Probability.Variation
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Tail sections and contact at maximizing laws -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem pi_cons_map (n : ℕ) (μ : Measure ℝ≥0) (ν : Fin n → Measure ℝ≥0)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (ν i)] :
    (μ.prod (Measure.pi ν)).map (fun p : ℝ≥0 × (Fin n → ℝ≥0) => Fin.cons p.1 p.2) =
      Measure.pi (Fin.cons μ ν : Fin (n+1) → Measure ℝ≥0) := by
  let (i : Fin (n+1)) : IsFiniteMeasure ((Fin.cons μ ν : Fin (n+1) → Measure ℝ≥0) i) := by
    refine Fin.cases (motive := fun i =>
      IsFiniteMeasure ((Fin.cons μ ν : Fin (n+1) → Measure ℝ≥0) i)) ?_ (fun j => ?_) i
    · exact (inferInstance : IsFiniteMeasure μ)
    · exact (inferInstance : IsFiniteMeasure (ν j))
  have h := (measurePreserving_piFinSuccAbove (α := fun _ : Fin (n+1) => ℝ≥0)
    (Fin.cons μ ν) 0).symm.map_eq
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero] using h

theorem tailForm_finCons (n : ℕ) (μ : Measure ℝ≥0) (ν : Fin n → Measure ℝ≥0)
    [IsFiniteMeasure μ] [∀ i, IsFiniteMeasure (ν i)] :
    tailForm (n+1) (Fin.cons μ ν) =
      (∫⁻ z : ℝ≥0, (Measure.pi ν) {y : Fin n → ℝ≥0 | 1 ≤ z + ∑ i, y i} ∂μ).toReal := by
  unfold tailForm
  rw [← pi_cons_map, Measure.map_apply (by fun_prop) (by measurability)]
  have hevent : (fun p : ℝ≥0 × (Fin n → ℝ≥0) => Fin.cons p.1 p.2) ⁻¹'
      {z : Fin (n+1) → ℝ≥0 | 1 ≤ ∑ i, z i} =
      {p : ℝ≥0 × (Fin n → ℝ≥0) | 1 ≤ p.1 + ∑ i, p.2 i} := by
    ext p
    simp [Fin.sum_univ_succ]
  rw [hevent, Measure.prod_apply (by measurability)]
  rfl

theorem sectionTail_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    sectionTail n μ z =
      ((Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0)))
        {y : Fin n → ℝ≥0 | 1 ≤ z + ∑ i, y i}).toReal := by
  have hfamily : Function.update (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) 0 (Measure.dirac z) =
      Fin.cons (Measure.dirac z) (fun _ : Fin n => (μ : Measure ℝ≥0)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [sectionTail, hfamily, tailForm_finCons, lintegral_dirac]

theorem measurable_sectionMass (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Measurable (fun z : ℝ≥0 => (Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0)))
      {y : Fin n → ℝ≥0 | 1 ≤ z + ∑ i, y i}) := by
  exact measurable_measure_prodMk_left
    (s := {p : ℝ≥0 × (Fin n → ℝ≥0) | 1 ≤ p.1 + ∑ i, p.2 i}) (by measurability)

theorem measurable_sectionTail (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Measurable (sectionTail n μ) := by
  convert (measurable_sectionMass n μ).ennreal_toReal using 1
  funext z
  exact sectionTail_eq n μ z

theorem sectionTail_nonneg (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    0 ≤ sectionTail n μ z := by
  rw [sectionTail_eq]
  exact ENNReal.toReal_nonneg

theorem sectionTail_le_one (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    sectionTail n μ z ≤ 1 := by
  rw [sectionTail_eq]
  exact measureReal_le_one

theorem monotone_sectionTail (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Monotone (sectionTail n μ) := by
  intro a b hab
  rw [sectionTail_eq, sectionTail_eq]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro y hy
  exact hy.trans (add_le_add hab le_rfl)

@[simp] theorem sectionTail_zero (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    sectionTail n μ 0 = tailProbability n μ := by
  simp [sectionTail_eq, tailProbability]

@[simp] theorem sectionTail_one (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    sectionTail n μ 1 = 1 := by
  rw [sectionTail_eq]
  have hevent : {y : Fin n → ℝ≥0 | 1 ≤ 1 + ∑ i, y i} = Set.univ := by
    ext y
    simp
  rw [hevent, measure_univ, ENNReal.toReal_one]

theorem integral_sectionTail (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ z : ℝ≥0, sectionTail n μ z ∂(μ : Measure ℝ≥0)) = tailProbability (n+1) μ := by
  simp_rw [sectionTail_eq]
  rw [integral_toReal (measurable_sectionMass n μ).aemeasurable
    (ae_of_all _ fun _ => measure_lt_top _ _)]
  have hfamily : Fin.cons (μ : Measure ℝ≥0) (fun _ : Fin n => (μ : Measure ℝ≥0)) =
      (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have h := tailForm_finCons n (μ : Measure ℝ≥0) (fun _ : Fin n => (μ : Measure ℝ≥0))
  rw [hfamily] at h
  exact h.symm

theorem integrable_sectionTail (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Integrable (sectionTail n μ) (μ : Measure ℝ≥0) := by
  apply Integrable.of_bound (measurable_sectionTail n μ).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sectionTail_nonneg n μ z)]
  exact sectionTail_le_one n μ z

theorem integrable_coe_of_mean_ne_top (μ : ProbabilityMeasure ℝ≥0) (hμ : mean μ ≠ ∞) :
    Integrable (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) := by
  exact integrable_toReal_of_lintegral_ne_top measurable_coe_nnreal_ennreal.aemeasurable hμ

theorem integral_coe_eq_mean_toReal (μ : ProbabilityMeasure ℝ≥0) :
    (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = (mean μ).toReal := by
  exact integral_toReal measurable_coe_nnreal_ennreal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.coe_lt_top)

/-- The affine majorant agrees with the section function at almost every
sampled value. This is an equality consequence of maximality, not an extra
support or stationarity hypothesis. -/
theorem maximizer_ae_contact {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    ∀ᵐ z ∂(μ : Measure ℝ≥0), sectionTail n μ z = tailProbability n μ +
      ((tailProbability (n+1) μ - tailProbability n μ) / x) * (z : ℝ) := by
  let b : ℝ := (tailProbability (n+1) μ - tailProbability n μ) / x
  have hm := maximizer_mean_eq (by omega : 1 ≤ n+1) hx.le hxlt hμ
  have hint : Integrable (fun z : ℝ≥0 => tailProbability n μ + b*(z : ℝ)) (μ : Measure ℝ≥0) :=
    (integrable_const _).add ((integrable_coe_of_mean_ne_top μ
      (by rw [hm]; exact ENNReal.ofReal_ne_top)).const_mul b)
  have hle : sectionTail n μ ≤ᵐ[(μ : Measure ℝ≥0)]
      (fun z : ℝ≥0 => tailProbability n μ + b*(z : ℝ)) := by
    filter_upwards [] with z
    simpa [b] using maximizer_supporting_line hx hxlt hμ z
  apply (integral_eq_iff_of_ae_le (integrable_sectionTail n μ) hint hle).mp
  rw [integral_sectionTail, integral_add (integrable_const _)
    ((integrable_coe_of_mean_ne_top μ (by rw [hm]; exact ENNReal.ofReal_ne_top)).const_mul b),
    integral_const, integral_const_mul, integral_coe_eq_mean_toReal, hm,
    ENNReal.toReal_ofReal hx.le]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  dsimp [b]
  field_simp
  ring

end SharpTailMatching.Probability
