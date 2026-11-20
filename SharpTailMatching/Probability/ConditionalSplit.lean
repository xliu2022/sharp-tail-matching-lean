module

public import SharpTailMatching.Probability.MixtureMoments
public import SharpTailMatching.Probability.LowerEvent

/-! # Conditional mean separation and the variance between two events -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem cond_eq_of_restrict_eq_smul {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (E F : Set Ω) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞)
    (hrestrict : μ.restrict E = c • ν.restrict F) :
    ProbabilityTheory.cond μ E = ProbabilityTheory.cond ν F := by
  have hmass : μ E = c*ν F := by
    have h := congrArg (fun ρ : Measure Ω => ρ Set.univ) hrestrict
    simpa only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
      Measure.smul_apply,smul_eq_mul] using h
  unfold ProbabilityTheory.cond
  rw [hmass,hrestrict,smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
  calc
    c⁻¹*(ν F)⁻¹*c = (ν F)⁻¹*(c⁻¹*c) := by ac_rfl
    _ = (ν F)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hctop,mul_one]

theorem conditional_mean_deviation_le_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)
    {E : Set Ω} (hE : MeasurableSet E) (hp : 0 < μ.real E) :
    ((∫w,f w ∂ProbabilityTheory.cond μ E)-(∫w,f w ∂μ))^2 ≤
      variance f μ*(1-μ.real E)/(μ.real E) := by
  have hE0 : μ E ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).mp hp.ne'
  by_cases hEc0 : μ Eᶜ = 0
  · have hae : ∀ᵐ w ∂μ,w ∈ E := by
      apply ae_iff.mpr
      change μ Eᶜ = 0
      exact hEc0
    have hmass : μ E = 1 := by
      have heq : E =ᵐ[μ] Set.univ := eventuallyEqSet_univ.mpr hae
      exact (measure_congr heq).trans (measure_univ)
    have hcond : ProbabilityTheory.cond μ E = μ := by
      rw [ProbabilityTheory.cond,hmass,Measure.restrict_eq_self_of_ae_mem hae,inv_one,one_smul]
    rw [hcond,sub_self,zero_pow (by norm_num),Measure.real,hmass,ENNReal.toReal_one]
    simp
  · let L := ProbabilityTheory.cond μ Eᶜ
    let U := ProbabilityTheory.cond μ E
    let q := μ.real Eᶜ
    let : IsProbabilityMeasure L := cond_isProbabilityMeasure hEc0
    let : IsProbabilityMeasure U := cond_isProbabilityMeasure hE0
    have hq0 : 0 < q := ENNReal.toReal_pos hEc0 (measure_ne_top _ _)
    have hq1 : q ≤ 1 := measureReal_le_one
    have hpq : 1-q = μ.real E := by
      have h := probReal_compl_eq_one_sub (μ := μ) hE
      dsimp [q]
      linarith
    have hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U := by
      rw [hpq]
      dsimp [q,L,U,Measure.real]
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _),ENNReal.ofReal_toReal (measure_ne_top _ _)]
      unfold ProbabilityTheory.cond
      rw [smul_smul,smul_smul,ENNReal.mul_inv_cancel hEc0 (measure_ne_top _ _),
        ENNReal.mul_inv_cancel hE0 (measure_ne_top _ _),one_smul,one_smul,
        Measure.restrict_compl_add_restrict hE]
    have hL : MemLp f 2 L := (hf.restrict Eᶜ).smul_measure (ENNReal.inv_ne_top.mpr hEc0)
    have hU : MemLp f 2 U := (hf.restrict E).smul_measure (ENNReal.inv_ne_top.mpr hE0)
    have h := mixture_between_variance_le_upper_deviation μ L U hq0 hq1 hmix f hf hL hU
    rw [hpq] at h
    have hdiv : μ.real E*((∫w,f w ∂U)-(∫w,f w ∂μ))^2/q ≤ variance f μ := by
      convert h using 1 <;> ring
    have hmul := (div_le_iff₀ hq0).mp hdiv
    apply (le_div_iff₀ hp).mpr
    have hq : q = 1-μ.real E := by linarith
    rw [hq] at hmul
    nlinarith [hmul]

theorem failureMeasure_cond_allLowerEvent {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 < q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    ProbabilityTheory.cond (failureMeasure n μ) (allLowerEvent (n+1) b) = failureMeasure n L := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑i,w i < 1}
  let ρ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))
  have hF0 : ρ F ≠ 0 := by
    intro hz
    have h := failure_toReal_eq_one_sub_tail (n+1) μ
    change (ρ F).toReal = 1-tailProbability (n+1) μ at h
    rw [hz,ENNReal.toReal_zero] at h
    have hp := tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1
    linarith
  have hc0 : (ρ F)⁻¹*(ENNReal.ofReal q)^(n+1) ≠ 0 :=
    mul_ne_zero (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)) (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hq).ne')
  have hctop : (ρ F)⁻¹*(ENNReal.ofReal q)^(n+1) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hF0) (by finiteness)
  exact cond_eq_of_restrict_eq_smul (failureMeasure n μ)
    (Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) (allLowerEvent (n+1) b) F hc0 hctop
      (failureMeasure_restrict_allLowerEvent n hmix hLb hUb)

end SharpTailMatching.Probability
