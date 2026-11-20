module

public import SharpTailMatching.Probability.ExclusionRanges

/-! # Normalization of the actual all-lower moments and cubic bound -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability.ExclusionData

variable {n : ℕ} (C : ExclusionData n)

theorem δL_pos : 0 < 1-C.k*C.x₀ := by
  have h := mul_lt_mul_of_pos_left C.x₀_lt_x C.k_pos
  have ha := C.a_lt_one
  change C.k*C.x < 1 at ha
  linarith

theorem τ_pos : 0 < C.τ := div_pos C.δL_pos C.A_pos

theorem lower_failure_identity : 1-tailProbability (n+1) C.L = C.R*(1-C.γ) := by
  have h := allLower_failure_probability C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos.le C.mixture C.lower_support_b₀ C.upper_above_b₀
  change C.q^(n+1)*(1-tailProbability (n+1) C.L) = C.p*(1-C.γ) at h
  dsimp only [R]
  field_simp [ne_of_gt (pow_pos C.weight_pos (n+1))]
  nlinarith only [h]

theorem K0_identity : C.K0 = 1/C.R-1+C.γ := by
  have h := C.lower_failure_identity
  dsimp only [K0]
  field_simp [C.R_pos.ne']
  nlinarith only [h]

theorem K0_nonneg : 0 ≤ C.K0 := div_nonneg (tailProbability_nonneg _ _) C.R_pos.le

theorem K0_lower (hq : 1-C.x < C.q) : C.ell+5*C.g/8 < C.K0 :=
  ExclusionAlgebra.lower_tail_mass C.K0_identity (C.reciprocal_R hq) (C.γ_lower hq)

theorem K1_identity : C.K1 = (1-C.γ)*C.dL := by
  have h := lowerTailFirstMoment_eq C.L (C.lower_memLp 2) (rfl : _ = C.x₀) C.lower_failure_pos
  rw [C.lower_failure_identity] at h
  dsimp only [K1,dL]
  rw [h]
  field_simp [C.R_pos.ne',C.A_pos.ne']

theorem K1_ge_tail : C.τ*C.K0 ≤ C.K1 := by
  have h := lowerTailFirstMoment_ge_tail (n := n) (x₀ := C.x₀) C.L (C.lower_memLp 2)
  have hd := div_le_div_of_nonneg_right h (mul_pos C.R_pos C.A_pos).le
  convert hd using 1 <;> dsimp only [τ,K0,K1,k] <;> field_simp [C.R_pos.ne',C.A_pos.ne']

theorem K1_nonneg : 0 ≤ C.K1 :=
  (mul_nonneg C.τ_pos.le C.K0_nonneg).trans C.K1_ge_tail

theorem dL_sub_z : C.dL-C.z = (conditionalDeficit n C.L-C.r)/C.A := by
  dsimp only [dL,z,B,failureExcessParameter,m,r,k]
  ring

theorem conditional_mean_bound : (C.dL-C.z)^2 ≤ C.v*C.γ/(1-C.γ) := by
  have h := allLower_conditional_mean_deviation C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos C.mixture C.lower_support_b₀ C.upper_above_b₀ C.γ_lt_one
  change (conditionalDeficit n C.L-C.r)^2 ≤ conditionalVariance n C.μ*C.γ/(1-C.γ) at h
  have hd := div_le_div_of_nonneg_right h (sq_nonneg C.A)
  rw [C.dL_sub_z]
  change ((conditionalDeficit n C.L-C.r)/C.A)^2 ≤
    (conditionalVariance n C.μ/C.A^2)*C.γ/(1-C.γ)
  convert hd using 1 <;> ring

theorem cubic_capped :
    (C.V+(max (C.z-C.b) 0)^2/12)*C.v ≥ (max (C.τ+C.z-2*C.b) 0)^3/3*C.K1 := by
  have hc := maximizer_lower_cubic_bound C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos.le C.mixture C.lower_support_b₀ C.upper_above_b₀ (rfl : _ = C.x₀) C.δL_pos
  have hz : C.z-C.b = (C.r-(1-C.k*C.x₀)-(C.b₀ : ℝ))/C.A := by
    dsimp only [z,b,B,failureExcessParameter,m,r,k]
    ring
  have hτz : C.τ+C.z-2*C.b = (C.r-2*(C.b₀ : ℝ))/C.A := by
    dsimp only [τ,z,b,B,failureExcessParameter,m,r,k]
    ring
  have hmz : max (C.z-C.b) 0 = max (C.r-(1-C.k*C.x₀)-(C.b₀ : ℝ)) 0/C.A := by
    rw [hz]
    simpa only [zero_div] using max_div_div_right C.A_pos.le (C.r-(1-C.k*C.x₀)-(C.b₀ : ℝ)) 0
  have hmt : max (C.τ+C.z-2*C.b) 0 = max (C.r-2*(C.b₀ : ℝ)) 0/C.A := by
    rw [hτz]
    simpa only [zero_div] using max_div_div_right C.A_pos.le (C.r-2*(C.b₀ : ℝ)) 0
  have hd := div_le_div_of_nonneg_right hc (pow_nonneg C.A_pos.le 4)
  rw [hmz,hmt]
  convert hd using 1 <;> dsimp only [V,v,K1,R,p,r,k] <;>
    field_simp [C.A_pos.ne',ne_of_gt (pow_pos C.weight_pos (n+1)),
      show 1-tailProbability (n+1) C.μ ≠ 0 from C.p_pos.ne'] <;> ring

theorem cubic_ratio :
    (C.K1/(3*C.V))*(C.τ+C.z-2*C.b)^3/(1+(max (C.z-C.b) 0)^2/(12*C.V)) ≤ C.v := by
  have hcube : (C.τ+C.z-2*C.b)^3 ≤ (max (C.τ+C.z-2*C.b) 0)^3 :=
    (show Odd 3 by decide).pow_le_pow.mpr (le_max_left _ _)
  have hm := mul_le_mul_of_nonneg_right hcube C.K1_nonneg
  have hc := C.cubic_capped
  have hcoef : 0 < C.V+(max (C.z-C.b) 0)^2/12 := by
    have := C.V_pos
    positivity
  have hden : 0 < 1+(max (C.z-C.b) 0)^2/(12*C.V) := by
    have := C.V_pos
    positivity
  calc
    _ = (C.K1/3*(C.τ+C.z-2*C.b)^3)/(C.V+(max (C.z-C.b) 0)^2/12) := by
      field_simp [C.V_pos.ne',hcoef.ne',hden.ne']
    _ ≤ C.v := by
      apply (div_le_iff₀ hcoef).mpr
      nlinarith only [hm,hc]

end SharpTailMatching.Probability.ExclusionData
