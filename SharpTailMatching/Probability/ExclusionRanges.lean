module

public import SharpTailMatching.Probability.ExclusionIdentities
public import SharpTailMatching.ExclusionEstimates

/-! # Genuine probability and support ranges for the normalized objects -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability.ExclusionData

variable {n : ℕ} (C : ExclusionData n)

theorem u_pos : 0 < C.u := div_pos C.lower_mean_pos C.A_pos

theorem α_pos : 0 < C.α := div_pos C.m_pos (mul_pos C.k_pos C.A_pos)

theorem d_pos : 0 < C.d := div_pos C.D_pos C.A_pos

theorem d_lt_one : C.d < 1 := (div_lt_one C.A_pos).mpr C.D_lt_A

theorem e_nonneg : 0 ≤ C.e := by
  exact div_nonneg (sub_nonneg.mpr (maximizer_conditionalDeficit_le_cutoff
    C.mean_pos C.mean_subcritical C.maximizes)) C.A_pos.le

theorem u_le_b : C.u ≤ C.b := div_le_div_of_nonneg_right C.x₀_le_b₀ C.A_pos.le

theorem b_nonneg : 0 ≤ C.b := C.u_pos.le.trans C.u_le_b

theorem v_nonneg : 0 ≤ C.v := div_nonneg (variance_nonneg _ _) (sq_nonneg _)

theorem b_bound : C.b ≤ C.u+1/16+15*C.α/16 := by
  have h := div_le_div_of_nonneg_right C.b₀_le C.A_pos.le
  change C.b ≤ (C.x+C.D/16)/C.A at h
  have heq : C.D/16/C.A = C.d/16 := by dsimp only [d]; ring
  rw [add_div,heq,C.x_div_A,C.d_eq] at h
  linarith

theorem e_bound : C.e < (1-3*C.u-4*C.α)/20 := by
  have h := div_lt_div_of_pos_right C.proximity C.A_pos
  change C.e < ((C.D-3*C.x)/20)/C.A at h
  have heq : ((C.D-3*C.x)/20)/C.A = (C.d-3*(C.x/C.A))/20 := by
    dsimp only [d]
    ring
  rw [heq,C.x_div_A,C.d_eq] at h
  linarith

theorem nu_nonneg : 0 ≤ C.nu := div_nonneg (sub_nonneg.mpr C.y₀_le_M) C.A_pos.le

theorem nu_lt : C.nu < 3*C.d/20 := by
  have h := C.upper_mean_gap
  have hM := C.M_sub_x
  have hb : C.M-C.y₀ < 3*C.D/20 := by linarith
  have hd := div_lt_div_of_pos_right hb C.A_pos
  convert hd using 1 <;> dsimp only [nu,d] <;> ring

theorem θ_lt_one : C.θ < 1 := by
  have h := div_pos C.m_pos (mul_pos C.a_pos C.A_pos)
  dsimp only [θ]
  linarith

theorem power_lower (hc : (11:ℝ)/24 ≤ C.c) (hp₀ : C.p₀ < Real.exp (-1)) : C.p/2 < C.q^n := by
  have hratio := maximizer_mixture_mass_ratio C.mean_pos C.mean_subcritical C.maximizes hc
    C.critical C.proximity C.weight_pos C.weight_lt_one C.mixture C.lower_support C.upper_support
  have h := lower_component_power_gt_half C.weight_pos C.weight_lt_one hratio hp₀
  linarith [C.p_le_p₀]

theorem weight_gt (hc : (11:ℝ)/24 ≤ C.c) (hc1 : C.c ≤ 1/2)
    (hp₀ : C.p₀ < Real.exp (-1)) : 1-C.x < C.q :=
  maximizer_component_weight_gt C.mean_pos C.mean_subcritical C.maximizes hc hc1 C.critical
    C.weight_pos C.weight_lt_one C.mixture C.upper_ac C.upper_support C.lower_mean_pos
    ((C.lower_memLp 2).integrable one_le_two) rfl (C.power_lower hc hp₀)

theorem rate_lt_a (hq : 1-C.x < C.q) : C.rate < C.a := by
  have h := mul_lt_mul_of_pos_left (show 1-C.q < C.x by linarith) C.k_pos
  exact h

theorem ell_pos (hq : 1-C.x < C.q) : 0 < C.ell := sub_pos.mpr (C.rate_lt_a hq)

theorem θ_pos (hq : 1-C.x < C.q) : 0 < C.θ := by
  have h := C.rate_mass
  have hn := mul_nonneg C.rate_pos.le C.nu_nonneg
  have ha := C.rate_lt_a hq
  have hmul : C.a*(1-C.θ) < C.a := by nlinarith only [h,hn,ha]
  have hapos := C.a_pos
  nlinarith only [hmul,hapos]

theorem g_nonneg : 0 ≤ C.g := conditionalUpperMean_nonneg n C.μ C.b₀

theorem γ_nonneg : 0 ≤ C.γ := conditionalUpperProbability_nonneg n C.μ C.b₀

theorem γ_le_g : C.γ ≤ C.g := by
  letI := maximizer_failureMeasure_probability C.mean_pos C.mean_subcritical C.maximizes
  exact conditionalUpperProbability_le_mean n C.μ C.b₀

theorem γ_lower (hq : 1-C.x < C.q) : 5*C.g/8 ≤ C.γ := by
  have hrate : C.rate ≤ 1 := (C.rate_lt_a hq).le.trans C.a_lt_one.le
  have h := conditionalUpperProbability_lower C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos.le C.weight_lt_one C.mixture C.lower_support_b₀ C.upper_above_b₀ hrate
  change (5/8)*C.g ≤ C.γ at h
  linarith

theorem g_bound (hq : 1-C.x < C.q) : C.g < (1-C.θ)/5 :=
  (ExclusionAlgebra.upper_count_ranges C.a_lt_one (C.θ_pos hq) C.θ_lt_one C.rate_pos
    C.nu_nonneg C.d_pos C.d_lt_one.le C.nu_lt C.rate_mass C.d_mul_g
    C.γ_nonneg C.γ_le_g).2.2.2.2

theorem x_lt_sixth (hk : 6 ≤ C.k) : C.x < 1/6 := by
  have h := mul_le_mul_of_nonneg_right hk C.mean_pos.le
  have ha := C.a_lt_one
  change C.k*C.x < 1 at ha
  linarith

theorem α_bound (hk : 6 ≤ C.k) : C.α ≤ (1-C.θ)/6 := by
  rw [C.α_eq_theta]
  have h := mul_le_mul_of_nonneg_right (C.x_lt_sixth hk).le (sub_nonneg.mpr C.θ_lt_one.le)
  nlinarith

theorem weight_gt_five_sixths (hk : 6 ≤ C.k) (hq : 1-C.x < C.q) : 5/6 < C.q := by
  linarith [C.x_lt_sixth hk]

theorem upper_mean_sharp (hq : 1-C.x < C.q) : 1-((n:ℝ)+3/17)*C.x₀ < C.y₀ := by
  exact integral_const_lt_of_ae_lt (C.U : Measure ℝ≥0) _ ((C.upper_memLp 2).integrable one_le_two)
    (maximizer_upper_component_sharp_threshold C.mean_pos C.mean_subcritical C.maximizes
      C.weight_pos.le hq C.mixture C.upper_ac (C.upper_support.mono (fun _ h => h.1))
      C.lower_mean_pos ((C.lower_memLp 2).integrable one_le_two) rfl)

theorem normalized_sharp_threshold (hq : 1-C.x < C.q) : C.τ-3*C.u/17 < 1-C.nu := by
  have h := C.upper_mean_sharp hq
  have hraw : 1-C.k*C.x₀-3*C.x₀/17 < C.y₀-C.x₀ := by
    dsimp only [k]
    push_cast
    linarith
  have hd := div_lt_div_of_pos_right hraw C.A_pos
  convert hd using 1 <;> dsimp only [τ,u,nu,A] <;>
    field_simp [show C.M-C.x₀ ≠ 0 from C.A_pos.ne'] <;> ring

theorem u_ell_bound (hq : 1-C.x < C.q) : C.a*(C.c-3/17)*C.u < C.ell := by
  have ht := C.normalized_sharp_threshold hq
  rw [C.τ_eq] at ht
  have h := mul_lt_mul_of_pos_left ht C.a_pos
  have hid := C.theta_identity
  have hg := C.d_mul_g
  have he := mul_nonneg (C.ell_pos hq).le C.nu_nonneg
  have hell : C.rate = C.a-C.ell := by dsimp only [ell]; ring
  rw [hell] at hg
  nlinarith only [h,hid,hg,he]

theorem R_lt_one (hq : 1-C.x < C.q) : C.R < 1 := by
  have hpow : (1-C.x)^(n+1) < C.q^(n+1) :=
    pow_lt_pow_left₀ hq (sub_nonneg.mpr C.x_lt_one.le) (by omega)
  exact (div_lt_one (pow_pos C.weight_pos (n+1))).mpr (C.p_le_p₀.trans_lt hpow)

theorem reciprocal_R (hq : 1-C.x < C.q) : 1+C.ell < 1/C.R := by
  have h := ExclusionAlgebra.lower_tail_mass_factor (k := n+1) (by omega)
    C.mean_pos C.x_lt_one C.p_pos C.p_le_p₀ (C.ell_pos hq) C.q_eq_ell
  convert h using 1
  dsimp only [R]
  field_simp [C.p_pos.ne',ne_of_gt (pow_pos C.weight_pos (n+1))]

end SharpTailMatching.Probability.ExclusionData
