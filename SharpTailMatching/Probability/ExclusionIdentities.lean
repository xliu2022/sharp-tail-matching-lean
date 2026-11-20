module

public import SharpTailMatching.Probability.ExclusionObjects

/-! # Normalized identities of the actual component laws -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability.ExclusionData

variable {n : ℕ} (C : ExclusionData n)

theorem x_lt_one : C.x < 1 := lt_one_of_subcritical C.mean_pos C.mean_subcritical

theorem m_eq_rate : C.m = C.rate*(C.y₀-C.x₀) := by
  dsimp only [m,rate]
  rw [C.mixture_mean]
  ring

theorem α_eq : C.α = (C.x-C.x₀)/C.A := by
  dsimp only [α,m]
  field_simp [C.k_pos.ne']

theorem d_eq : C.d = 1-C.α := by
  rw [C.α_eq]
  change C.D/C.A = 1-(C.x-C.x₀)/C.A
  field_simp [C.A_pos.ne']
  have h := C.M_sub_x
  dsimp only [A]
  linarith

theorem α_eq_theta : C.α = C.x*(1-C.θ) := by
  dsimp only [α,θ,a]
  field_simp [C.k_pos.ne',C.mean_pos.ne',C.A_pos.ne']
  ring

theorem m_div_A : C.m/C.A = C.a*(1-C.θ) := by
  dsimp only [θ]
  field_simp [C.a_pos.ne',C.A_pos.ne']
  ring

theorem x_div_A : C.x/C.A = C.u+C.α := by
  rw [C.α_eq]
  dsimp only [u]
  ring

theorem δL_eq : 1-C.k*C.x₀ = C.m+C.c*C.x := by
  have h := C.critical
  change 1-C.k*C.x = C.c*C.x at h
  dsimp only [m]
  linarith

theorem τ_eq : C.τ = 1-C.θ+C.c*C.u := by
  dsimp only [τ]
  rw [C.δL_eq]
  have hc := C.critical
  change 1-C.a = C.c*C.x at hc
  have hm := C.m_div_A
  have hα := C.α_eq_theta
  have hx := C.x_div_A
  dsimp only [u] at *
  rw [add_div,mul_div_assoc]
  rw [hm,hx,hα]
  nlinarith [congrArg (fun t : ℝ => t*(1-C.θ)) hc]

theorem τ_add_z : C.τ+C.z = 1+C.u-C.e := by
  dsimp only [τ,z,B,failureExcessParameter,m,e,u,A,r,k]
  field_simp [show C.M-C.x₀ ≠ 0 from C.A_pos.ne']
  ring

theorem z_eq : C.z = C.θ+(1-C.c)*C.u-C.e := by
  have h := C.τ_add_z
  rw [C.τ_eq] at h
  linarith

theorem B_div_A : C.B/C.A = 1+(1-C.c)*C.u-C.c*C.α-C.e := by
  have h := C.z_eq
  have hm := C.m_div_A
  have hc := C.critical
  change 1-C.a = C.c*C.x at hc
  have hα := C.α_eq_theta
  dsimp only [z] at h
  rw [sub_div,hm] at h
  rw [hα]
  nlinarith [congrArg (fun t : ℝ => t*(1-C.θ)) hc]

theorem rate_mass : C.rate*(1-C.nu) = C.a*(1-C.θ) := by
  rw [← C.m_div_A,C.m_eq_rate]
  dsimp only [nu,A]
  field_simp [show C.M-C.x₀ ≠ 0 from C.A_pos.ne']
  ring

theorem d_eq_mixture : C.d = C.q+(1-C.q)*C.nu := by
  have hm := C.mixture_mean
  dsimp only [d,nu,A]
  field_simp [show C.M-C.x₀ ≠ 0 from C.A_pos.ne']
  have h := C.M_sub_x
  nlinarith

theorem g_eq : C.g = C.rate*(C.M-C.y₀)/C.D :=
  maximizer_conditionalUpperMean_eq C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos.le C.weight_lt_one.le C.mixture
    ((C.lower_memLp 2).integrable one_le_two) ((C.upper_memLp 2).integrable one_le_two)
    C.lower_support_b₀ C.upper_above_b₀

theorem d_mul_g : C.d*C.g = C.rate*C.nu := by
  rw [C.g_eq]
  dsimp only [d,nu]
  field_simp [C.D_pos.ne']

theorem q_div_d : C.q/C.d = 1-C.g/C.k := by
  have hd : C.d ≠ 0 := (show 0 < C.d from div_pos C.D_pos C.A_pos).ne'
  apply (div_eq_iff hd).mpr
  have h := C.d_eq_mixture
  have hg := C.d_mul_g
  dsimp only [rate] at hg
  field_simp [C.k_pos.ne']
  nlinarith [congrArg (fun t : ℝ => C.k*t) h]

theorem theta_identity : C.a*C.θ = C.ell+C.d*C.g := by
  rw [C.d_mul_g]
  have h := C.rate_mass
  dsimp only [ell]
  nlinarith

theorem q_eq_ell : C.q = 1-C.x+C.ell/C.k := by
  dsimp only [ell,a,rate]
  field_simp [C.k_pos.ne']
  ring

theorem q_mul_V : C.q*C.V = C.d*C.z+C.Θ := by
  have h := maximizer_lower_variance_identity C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos.le C.weight_lt_one.le C.mixture (C.lower_memLp 2) (C.upper_memLp 2)
  change C.q*C.k*variance (fun t : ℝ≥0 => (t : ℝ)) (C.L : Measure ℝ≥0) =
    C.D*(C.B-C.m)+upperVarianceRemainder (n+1) C.M C.x₀ C.q C.U at h
  dsimp only [V,d,z,Θ]
  field_simp [C.A_pos.ne']
  nlinarith only [h]

theorem Θ_bounds : 0 ≤ C.Θ ∧ C.Θ ≤ C.d*C.g := by
  have hUlo : ∀ᵐ t : ℝ≥0 ∂(C.U : Measure ℝ≥0), C.x₀ ≤ (t : ℝ) := by
    filter_upwards [C.upper_above_x] with t ht
    exact C.x₀_lt_x.le.trans ht.le
  have h := upperVarianceRemainder_bounds (n+1) C.weight_lt_one.le C.U (C.upper_memLp 2)
    hUlo (C.upper_support.mono (fun _ h => h.2))
  change 0 ≤ upperVarianceRemainder (n+1) C.M C.x₀ C.q C.U ∧
    upperVarianceRemainder (n+1) C.M C.x₀ C.q C.U ≤ C.A*(C.rate*(C.M-C.y₀)) at h
  constructor
  · exact div_nonneg h.1 (sq_nonneg _)
  · rw [C.d_mul_g]
    dsimp only [Θ,nu]
    apply (div_le_iff₀ (sq_pos_of_pos C.A_pos)).mpr
    have heq : C.rate*((C.M-C.y₀)/C.A)*C.A^2 = C.A*(C.rate*(C.M-C.y₀)) := by
      field_simp [C.A_pos.ne']
    rw [heq]
    exact h.2

theorem refined_variance : C.v+(63/80)*C.q*C.a*(1-C.θ)*C.b < (C.B/C.A)*C.e := by
  have h := maximizer_refined_conditionalVariance C.mean_pos C.mean_subcritical C.maximizes
    C.weight_pos C.weight_lt_one C.mixture C.lower_ac C.lower_support C.upper_support C.lower_mean_pos
  change conditionalVariance n C.μ+(63/80)*C.q*(C.b₀ : ℝ)*C.m < C.B*(C.M-C.r) at h
  have hm := C.m_div_A
  have hd := (div_lt_div_iff_of_pos_right (sq_pos_of_pos C.A_pos)).mpr h
  calc
    C.v+(63/80)*C.q*C.a*(1-C.θ)*C.b =
      (conditionalVariance n C.μ+(63/80)*C.q*(C.b₀ : ℝ)*C.m)/C.A^2 := by
      calc
        _ = C.v+(63/80)*C.q*(C.a*(1-C.θ))*C.b := by ring
        _ = _ := by rw [← hm]; dsimp only [v,b]; field_simp [C.A_pos.ne']
    _ < (C.B*(C.M-C.r))/C.A^2 := hd
    _ = (C.B/C.A)*C.e := by dsimp only [e]; field_simp [C.A_pos.ne']

end SharpTailMatching.Probability.ExclusionData
