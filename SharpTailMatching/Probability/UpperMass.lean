module

public import SharpTailMatching.Probability.MixtureMoments
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Quantitative mass bounds for the separated components -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem maximizer_mixture_mass_ratio {n : ℕ} {x c q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hc : (11 : ℝ)/24 ≤ c)
    (hcritical : 1-((n+1 : ℕ) : ℝ)*x = c*x)
    (hprox : supportCutoff n x μ-conditionalDeficit n μ < (failureScale n x μ-3*x)/20)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hLb : ∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), (z : ℝ) ≤ x+failureScale n x μ/16)
    (hUb : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (z : ℝ) ∧
      (z : ℝ) ≤ supportCutoff n x μ) : ((n+1 : ℕ) : ℝ)*(1-q)/q < 250/153 := by
  let D := failureScale n x μ
  let B := failureExcessParameter n x μ
  let mU := ∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0)
  have hD : 0 < D := maximizer_failureScale_pos hx hxlt hμ
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have hr := maximizer_conditionalDeficit_le_cutoff hx hxlt hμ
  have hxD : 3*x < D := by dsimp [D]; linarith
  have hBlt : B < (85/72)*D := by
    have hcx := mul_le_mul_of_nonneg_right hc hx.le
    have hBx : B = conditionalDeficit n μ-c*x := by
      dsimp [B, failureExcessParameter]
      rw [hcritical]
    dsimp [D] at *
    linarith
  have hL2 := memLp_coe_of_ae_le L hLb 2
  have hU2 := memLp_coe_of_ae_le U (hUb.mono (fun _ h => h.2)) 2
  have hUmean : x+17*D/20 < mU :=
    integral_const_lt_of_ae_lt (U : Measure ℝ≥0) _ (hU2.integrable one_le_two)
      (hUb.mono (fun _ h => h.1))
  have hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal, maximizer_mean_eq (by omega) hx.le hxlt hμ,
      ENNReal.toReal_ofReal hx.le]
  have hbetween := mixture_between_variance_le_upper_deviation (μ : Measure ℝ≥0)
    (L : Measure ℝ≥0) (U : Measure ℝ≥0) hq0 hq1.le hmix (fun z : ℝ≥0 => (z : ℝ))
      (maximizer_memLp_coe hx hxlt hμ 2) hL2 hU2
  rw [hmean] at hbetween
  have hvar : ((n+1 : ℕ) : ℝ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) = D*B := by
    rw [← variance_iidSum _ μ (maximizer_memLp_coe hx hxlt hμ 2), maximizer_variance_identity hx hxlt hμ]
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbetween hk.le
  rw [hvar] at hscaled
  have hsquare : (17*D/20)^2 < (mU-x)^2 :=
    pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
  have hweight : 0 < ((n+1 : ℕ) : ℝ)*(1-q)/q := div_pos (mul_pos hk (sub_pos.mpr hq1)) hq0
  have hlow : (((n+1 : ℕ) : ℝ)*(1-q)/q)*(17*D/20)^2 < D*B := by
    have hstrict := mul_lt_mul_of_pos_left hsquare hweight
    change ((n+1 : ℕ) : ℝ)*((1-q)/q*(mU-x)^2) ≤ D*B at hscaled
    refine hstrict.trans_le ?_
    convert hscaled using 1 <;> ring
  have hBD := mul_lt_mul_of_pos_left hBlt hD
  apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos hD)).mp
  nlinarith

theorem log_lower_mixture_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    -(1-q)/q < Real.log q := by
  have hinv : q⁻¹ ≠ 1 := by
    intro h
    have hmul := congrArg (fun r : ℝ => r*q) h
    rw [inv_mul_cancel₀ hq0.ne', one_mul] at hmul
    linarith
  have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr hq0) hinv
  rw [Real.log_inv] at h
  have hid : -(1-q)/q = 1-q⁻¹ := by field_simp; ring
  rw [hid]
  linarith

theorem exp_neg_97_153_gt_half : (1 : ℝ)/2 < Real.exp (-97/153) := by
  have hlog : -Real.log 2 < (-97 : ℝ)/153 := by linarith [Real.log_two_gt_d9]
  have h := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  norm_num at h ⊢
  exact h

theorem lower_component_power_gt_half {n : ℕ} {q p₀ : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hratio : ((n+1 : ℕ) : ℝ)*(1-q)/q < 250/153)
    (hp₀ : p₀ < Real.exp (-1)) : p₀/2 < q^n := by
  have hlog := log_lower_mixture_weight hq0 hq1
  have htimes := mul_le_mul_of_nonneg_left hlog.le (Nat.cast_nonneg n)
  have hgap : 0 < (1-q)/q := div_pos (sub_pos.mpr hq1) hq0
  have hlogn : (-250 : ℝ)/153 < (n : ℝ)*Real.log q := by
    push_cast at hratio
    ring_nf at hratio htimes hgap
    nlinarith
  rw [← Real.log_pow] at hlogn
  have hpow : Real.exp (-250/153) < q^n := by
    have h := Real.exp_lt_exp.mpr hlogn
    rwa [Real.exp_log (pow_pos hq0 n)] at h
  have heq : Real.exp (-250/153) = Real.exp (-1)*Real.exp (-97/153) := by
    rw [← Real.exp_add]
    congr 1
    norm_num
  have hhalf := mul_lt_mul_of_pos_left exp_neg_97_153_gt_half (Real.exp_pos (-1))
  rw [heq] at hpow
  linarith

end SharpTailMatching.Probability
