module

public import SharpTailMatching.Probability.ComponentFailure
public import SharpTailMatching.Probability.Endpoints

/-! # Rigidity and quantitative bounds for the upper component -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem lt_one_of_subcritical {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) : x < 1 := by
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have h := mul_lt_mul_of_pos_left hxlt hk
  rw [mul_inv_cancel₀ hk.ne'] at h
  have hk1 : (1 : ℝ) ≤ (n+1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n+1)
  nlinarith

theorem maximizer_failure_le_bernoulli {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : 1-tailProbability (n+1) μ ≤ (1-x)^(n+1) := by
  have hx1 := (lt_one_of_subcritical hx hxlt).le
  have h := hμ.2 (unitBernoulliLaw x hx.le hx1) (by rw [mean_unitBernoulliLaw])
  rw [tailProbability_unitBernoulliLaw] at h
  linarith

theorem maximizer_component_weight_gt {n : ℕ} {x c q x₀ : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ)/24 ≤ c) (hc1 : c ≤ 1/2)
    (hcritical : 1-((n+1 : ℕ) : ℝ)*x = c*x) (hq0 : 0 < q) (hq1 : q < 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hU : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    (hUb : ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (y : ℝ) ∧
      (y : ℝ) ≤ supportCutoff n x μ)
    (hx₀ : 0 < x₀) (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmeanL : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hpower : (1-tailProbability (n+1) μ)/2 < q^n) : 1-x < q := by
  have hp : 0 < 1-tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  have hratio : (3 : ℝ)/10 < c/(1+c) := by
    apply (lt_div_iff₀ (by linarith : 0 < 1+c)).mpr
    linarith
  have hweight : (3/20)*(1-tailProbability (n+1) μ) ≤ q^n*(c/(1+c)) := by
    have h₁ := mul_lt_mul_of_pos_right hpower (by norm_num : (0 : ℝ) < 3/10)
    have h₂ := mul_le_mul_of_nonneg_left hratio.le (pow_nonneg hq0.le n)
    linarith
  have hthreshold := maximizer_upper_component_threshold hx hxlt hμ hq0.le hmix hU
    (hUb.mono (fun _ h => h.1)) hx₀ hL hmeanL (by linarith : 0 < c) hc1 hweight
  have hUint := (memLp_coe_of_ae_le U (hUb.mono (fun _ h => h.2)) 2).integrable one_le_two
  have hUmean := integral_const_lt_of_ae_lt (U : Measure ℝ≥0) _ hUint hthreshold
  have hmeanμ : (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal, maximizer_mean_eq (by omega) hx.le hxlt hμ,
      ENNReal.toReal_ofReal hx.le]
  have hD := maximizer_failureScale_pos hx hxlt hμ
  have hUabove : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), x < (z : ℝ) := by
    filter_upwards [hUb] with z hz
    linarith [hz.1]
  have hx₀x : x₀ < x := by
    simpa only [hmeanL] using mixture_lower_mean_lt (μ : Measure ℝ≥0)
      (L : Measure ℝ≥0) (U : Measure ℝ≥0) hq0 hq1 hmix _ hL hUint hmeanμ hUabove
  have hthresholdEq : 1-((n : ℝ)+c)*x₀ = x₀+(x-x₀)/x := by
    field_simp
    push_cast at hcritical
    linear_combination x₀*hcritical
  rw [hthresholdEq] at hUmean
  have hmean := mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0.le hq1.le hmix (fun z : ℝ≥0 => (z : ℝ)) hL hUint
  rw [hmeanμ, hmeanL] at hmean
  have hdelta : x-x₀ = (1-q)*((∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0))-x₀) := by nlinarith
  have hsmul := mul_lt_mul_of_pos_left (show (x-x₀)/x <
    (∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0))-x₀ by linarith) (sub_pos.mpr hq1)
  rw [← hdelta] at hsmul
  have hfrac : ((1-q)*(x-x₀))/x < x-x₀ := by convert hsmul using 1 <;> ring
  have hclear := (div_lt_iff₀ hx).mp hfrac
  have hq : 1-q < x := by
    apply (mul_lt_mul_iff_right₀ (sub_pos.mpr hx₀x)).mp
    nlinarith
  linarith

theorem lower_power_gt_bernoulli {n : ℕ} {x q : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hq : 1-x < q) : (1-x)^(n+1) < q^n := by
  have hb : 0 < 1-x := sub_pos.mpr hx1
  calc
    _ < (1-x)^n := by
      rw [pow_succ]
      nlinarith [pow_pos hb n]
    _ ≤ q^n := pow_le_pow_left₀ hb.le hq.le n

theorem maximizer_upper_component_sharp_threshold {n : ℕ} {x q x₀ : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq : 1-x < q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hU : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    (hUb : ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (y : ℝ))
    (hx₀ : 0 < x₀) (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmeanL : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = x₀) :
    ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), 1-((n : ℝ)+3/17)*x₀ < (y : ℝ) := by
  have hpower := (maximizer_failure_le_bernoulli hx hxlt hμ).trans_lt
    (lower_power_gt_bernoulli hx (lt_one_of_subcritical hx hxlt) hq)
  apply maximizer_upper_component_threshold hx hxlt hμ hq0 hmix hU hUb hx₀ hL hmeanL
    (by norm_num : (0 : ℝ) < 3/17) (by norm_num)
  norm_num
  nlinarith

theorem maximizer_zero_lower_component_rigid {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) (hU : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0))
    (hUb : ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (y : ℝ) ∧
      (y : ℝ) ≤ supportCutoff n x μ)
    (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0))
    (hmeanL : (∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0)) = 0)
    (hpower : (1-tailProbability (n+1) μ)/2 < q^n) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  have hLzero := ae_zero_of_integral_coe_eq_zero L hL hmeanL
  have hp : 0 < 1-tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  have hD := maximizer_failureScale_pos hx hxlt hμ
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hM1 := maximizer_supportCutoff_le_one hx hxlt hμ
  have hUone : ∀ᵐ y : ℝ≥0 ∂(U : Measure ℝ≥0), y = 1 := by
    filter_upwards [hUb, maximizer_upper_contact_lower_failure hx hxlt hμ hq0 hmix hU] with y hy hcontact
    have hy1 : (y : ℝ) ≤ 1 := hy.2.trans hM1
    by_contra hne
    have hylt : y < 1 := lt_of_le_of_ne (show y ≤ 1 from hy1) hne
    rw [sectionFailure_of_ae_zero n L hLzero hylt, mul_one] at hcontact
    have hcleared := (le_div_iff₀ hD).mp hcontact
    have hgap : supportCutoff n x μ-(y : ℝ) < 3*failureScale n x μ/20 := by linarith [hy.1]
    have hsmall := mul_lt_mul_of_pos_left hgap hp
    have hlarge := mul_lt_mul_of_pos_right hpower hD
    nlinarith
  have hLdirac : (L : Measure ℝ≥0) = Measure.dirac 0 := by
    have h : (L : Measure ℝ≥0).map (fun z : ℝ≥0 => z) =
        (L : Measure ℝ≥0).map (fun _ => (0 : ℝ≥0)) := Measure.map_congr hLzero
    simpa using h
  have hUdirac : (U : Measure ℝ≥0) = Measure.dirac 1 := by
    have h : (U : Measure ℝ≥0).map (fun z : ℝ≥0 => z) =
        (U : Measure ℝ≥0).map (fun _ => (1 : ℝ≥0)) := Measure.map_congr hUone
    simpa using h
  have hUint := (memLp_coe_of_ae_le U (hUb.mono (fun _ h => h.2)) 2).integrable one_le_two
  have hmean := mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0 hq1 hmix (fun z : ℝ≥0 => (z : ℝ)) hL hUint
  rw [integral_coe_eq_mean_toReal, maximizer_mean_eq (by omega) hx.le hxlt hμ,
    ENNReal.toReal_ofReal hx.le, hLdirac, hUdirac] at hmean
  simp only [integral_dirac, NNReal.coe_zero, NNReal.coe_one, mul_zero, zero_add, mul_one] at hmean
  rw [hLdirac, hUdirac] at hmix
  have hqeq : q = 1-x := by linarith
  simpa only [unitBernoulliMeasure, hqeq, sub_sub_cancel] using hmix

end SharpTailMatching.Probability
