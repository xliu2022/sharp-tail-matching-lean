module

public import SharpTailMatching.Probability.UpperCount

/-! # The exact lower-component variance identity -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def upperVarianceRemainder (k : ℕ) (M x₀ q : ℝ) (U : ProbabilityMeasure ℝ≥0) : ℝ :=
  (k : ℝ)*(1-q)*(∫z : ℝ≥0,(M-(z : ℝ))*((z : ℝ)-x₀) ∂(U : Measure ℝ≥0))

theorem integral_upperVariance_product (U : ProbabilityMeasure ℝ≥0)
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0)) (M x₀ : ℝ) :
    (∫z : ℝ≥0,(M-(z : ℝ))*((z : ℝ)-x₀) ∂(U : Measure ℝ≥0)) =
      (M+x₀)*(∫z : ℝ≥0,(z : ℝ) ∂(U : Measure ℝ≥0))-
      (∫z : ℝ≥0,(z : ℝ)^2 ∂(U : Measure ℝ≥0))-M*x₀ := by
  have heq : (fun z : ℝ≥0 => (M-(z : ℝ))*((z : ℝ)-x₀)) =
      (fun z : ℝ≥0 => (M+x₀)*(z : ℝ)-(z : ℝ)^2-M*x₀) := by funext z; ring
  have hlin : Integrable (fun z : ℝ≥0 => (M+x₀)*(z : ℝ)) (U : Measure ℝ≥0) :=
    (hU.integrable one_le_two).const_mul _
  have hsq : Integrable (fun z : ℝ≥0 => (z : ℝ)^2) (U : Measure ℝ≥0) := hU.integrable_sq
  have hdiff : Integrable (fun z : ℝ≥0 => (M+x₀)*(z : ℝ)-(z : ℝ)^2) (U : Measure ℝ≥0) := hlin.sub hsq
  rw [heq,integral_sub hdiff (integrable_const _),integral_sub hlin hsq,
    integral_const_mul,integral_const,probReal_univ,one_smul]

theorem mixture_lower_variance_identity (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q M : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hμ : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (μ : Measure ℝ≥0))
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0)) :
    q*(k : ℝ)*variance (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0) =
      (k : ℝ)*variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0)-
      (M-(∫z : ℝ≥0,(z : ℝ) ∂(μ : Measure ℝ≥0)))*
        ((k : ℝ)*((∫z : ℝ≥0,(z : ℝ) ∂(μ : Measure ℝ≥0))-
          (∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0))))+
      upperVarianceRemainder k M (∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) q U := by
  rw [mixture_variance (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0 hq1 hmix _ hμ hL hU]
  rw [mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0 hq1 hmix _ (hL.integrable one_le_two) (hU.integrable one_le_two)]
  rw [upperVarianceRemainder,integral_upperVariance_product U hU,variance_eq_sub hU]
  simp only [Pi.pow_apply]
  ring

theorem maximizer_lower_variance_identity {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0)) :
    q*((n+1 : ℕ) : ℝ)*variance (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0) =
      failureScale n x μ*(failureExcessParameter n x μ-
        ((n+1 : ℕ) : ℝ)*(x-(∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0))))+
      upperVarianceRemainder (n+1) (supportCutoff n x μ)
        (∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) q U := by
  have h := mixture_lower_variance_identity (n+1) (M := supportCutoff n x μ)
    hq0 hq1 hmix (maximizer_memLp_coe hx hxlt hμ 2) hL hU
  have hm : (∫z : ℝ≥0,(z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal,maximizer_mean_eq (by omega) hx.le hxlt hμ,
      ENNReal.toReal_ofReal hx.le]
  rw [hm,maximizer_supportCutoff_sub_mean hx hxlt hμ,
    ← variance_iidSum (n+1) μ (maximizer_memLp_coe hx hxlt hμ 2),
    maximizer_variance_identity hx hxlt hμ] at h
  nlinarith [h]

theorem upperVarianceRemainder_bounds (k : ℕ) {q M x₀ : ℝ} (hq1 : q ≤ 1)
    (U : ProbabilityMeasure ℝ≥0)
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0))
    (hUlo : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), x₀ ≤ (z : ℝ))
    (hUhi : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), (z : ℝ) ≤ M) :
    0 ≤ upperVarianceRemainder k M x₀ q U ∧
      upperVarianceRemainder k M x₀ q U ≤
        (M-x₀)*((k : ℝ)*(1-q)*(M-(∫z : ℝ≥0,(z : ℝ) ∂(U : Measure ℝ≥0)))) := by
  have hlam : 0 ≤ (k : ℝ)*(1-q) := mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hq1)
  have hint : Integrable (fun z : ℝ≥0 => (M-(z : ℝ))*((z : ℝ)-x₀)) (U : Measure ℝ≥0) :=
    ((memLp_const M).sub hU).integrable_mul (hU.sub (memLp_const x₀))
  have hnonneg : 0 ≤ ∫z : ℝ≥0,(M-(z : ℝ))*((z : ℝ)-x₀) ∂(U : Measure ℝ≥0) := by
    apply integral_nonneg_of_ae
    filter_upwards [hUlo,hUhi] with z hlo hhi
    exact mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hlo)
  refine ⟨mul_nonneg hlam hnonneg,?_⟩
  have hle : (∫z : ℝ≥0,(M-(z : ℝ))*((z : ℝ)-x₀) ∂(U : Measure ℝ≥0)) ≤
      (M-x₀)*(M-(∫z : ℝ≥0,(z : ℝ) ∂(U : Measure ℝ≥0))) := by
    calc
      _ ≤ ∫z : ℝ≥0,(M-x₀)*(M-(z : ℝ)) ∂(U : Measure ℝ≥0) := by
        apply integral_mono_ae hint (((integrable_const M).sub (hU.integrable one_le_two)).const_mul _)
        filter_upwards [hUhi] with z hz
        have h := mul_le_mul_of_nonneg_left (sub_le_sub_right hz x₀) (sub_nonneg.mpr hz)
        change (M-(z : ℝ))*((z : ℝ)-x₀) ≤ (M-x₀)*(M-(z : ℝ))
        nlinarith [h]
      _ = _ := by rw [integral_const_mul,integral_sub (integrable_const _) (hU.integrable one_le_two),
        integral_const,probReal_univ,one_smul]
  have h := mul_le_mul_of_nonneg_left hle hlam
  unfold upperVarianceRemainder
  nlinarith [h]

end SharpTailMatching.Probability
