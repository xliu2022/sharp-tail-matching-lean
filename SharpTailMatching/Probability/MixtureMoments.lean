module

public import SharpTailMatching.Probability.Components

/-! # Exact first and second moments of a two-component probability law -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem mixture_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω → ℝ) (hL : Integrable f L) (hU : Integrable f U) :
    (∫ z, f z ∂μ) = q*(∫ z, f z ∂L) + (1-q)*(∫ z, f z ∂U) := by
  rw [hmix, integral_add_measure (hL.smul_measure ENNReal.ofReal_ne_top)
    (hU.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1), smul_eq_mul, smul_eq_mul]

theorem mixture_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω → ℝ) (hμ : MemLp f 2 μ) (hL : MemLp f 2 L) (hU : MemLp f 2 U) :
    variance f μ = q*variance f L + (1-q)*variance f U +
      q*(1-q)*((∫ z, f z ∂U)-(∫ z, f z ∂L))^2 := by
  rw [variance_eq_sub hμ, variance_eq_sub hL, variance_eq_sub hU]
  simp only [Pi.pow_apply]
  rw [mixture_integral μ L U hq0 hq1 hmix (fun z => (f z)^2) hL.integrable_sq hU.integrable_sq,
    mixture_integral μ L U hq0 hq1 hmix f (hL.integrable one_le_two) (hU.integrable one_le_two)]
  ring

theorem mixture_between_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω → ℝ) (hμ : MemLp f 2 μ) (hL : MemLp f 2 L) (hU : MemLp f 2 U) :
    q*(1-q)*((∫ z, f z ∂U)-(∫ z, f z ∂L))^2 ≤ variance f μ := by
  rw [mixture_variance μ L U hq0 hq1 hmix f hμ hL hU]
  have hleft := mul_nonneg hq0 (variance_nonneg f L)
  have hright := mul_nonneg (sub_nonneg.mpr hq1) (variance_nonneg f U)
  linarith

theorem memLp_coe_of_ae_le (μ : ProbabilityMeasure ℝ≥0) {b : ℝ}
    (hb : ∀ᵐ z : ℝ≥0 ∂(μ : Measure ℝ≥0), (z : ℝ) ≤ b) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ≥0 => (z : ℝ)) p (μ : Measure ℝ≥0) := by
  apply MemLp.of_bound (by fun_prop) b
  filter_upwards [hb] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg z.coe_nonneg] using hz

theorem integral_const_lt_of_ae_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) {a : ℝ} (ha : ∀ᵐ z ∂μ, a < f z) :
    a < ∫ z, f z ∂μ := by
  have hle : (fun _ : Ω => a) ≤ᵐ[μ] f := ha.mono (fun _ h => h.le)
  have h := integral_mono_ae (integrable_const a) hf hle
  simp only [integral_const, probReal_univ, one_smul] at h
  apply lt_of_le_of_ne h
  intro heq
  have heq' : (∫ _ : Ω, a ∂μ) = ∫ z, f z ∂μ := by simpa using heq
  have he := (integral_eq_iff_of_ae_le (integrable_const a) hf hle).mp heq'
  obtain ⟨z, hz, hlt⟩ := (he.and ha).exists
  exact (ne_of_lt hlt) hz

theorem mixture_lower_mean_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q x : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω → ℝ) (hL : Integrable f L) (hU : Integrable f U)
    (hmean : (∫ z, f z ∂μ) = x) (hupper : ∀ᵐ z ∂U, x < f z) :
    (∫ z, f z ∂L) < x := by
  have hUmean := integral_const_lt_of_ae_lt U f hU hupper
  have h := mixture_integral μ L U hq0.le hq1.le hmix f hL hU
  rw [hmean] at h
  have hprod := mul_pos (sub_pos.mpr hq1) (sub_pos.mpr hUmean)
  have hlower : q*((∫ z, f z ∂L)-x) < 0 := by nlinarith
  apply lt_of_not_ge
  intro hn
  have hnprod := mul_nonneg hq0.le (sub_nonneg.mpr hn)
  linarith

theorem mixture_between_variance_le_upper_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω → ℝ) (hμ : MemLp f 2 μ) (hL : MemLp f 2 L) (hU : MemLp f 2 U) :
    (1-q)/q*((∫ z, f z ∂U)-(∫ z, f z ∂μ))^2 ≤ variance f μ := by
  have hmean := mixture_integral μ L U hq0.le hq1 hmix f
    (hL.integrable one_le_two) (hU.integrable one_le_two)
  have h := mixture_between_variance_le μ L U hq0.le hq1 hmix f hμ hL hU
  have heq : (1-q)/q*((∫ z, f z ∂U)-(∫ z, f z ∂μ))^2 =
      q*(1-q)*((∫ z, f z ∂U)-(∫ z, f z ∂L))^2 := by
    rw [hmean]
    field_simp
    ring
  rwa [heq]

end SharpTailMatching.Probability
