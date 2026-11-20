module

public import SharpTailMatching.Probability.ExclusionMoments
public import SharpTailMatching.ExclusionMoments

/-! # Exclusion of a positive-mean lower component

The numerical contradiction is applied only after each scalar variable has been
identified with the actual conditional law, moment, or count from ExclusionData.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

namespace ExclusionData

variable {n : ℕ} (C : ExclusionData n)

theorem impossible (hk : 6 ≤ C.k) (ha : 12/13 < C.a)
    (hc0 : 11/24 < C.c) (hc1 : C.c ≤ 1/2) (hp₀ : C.p₀ < Real.exp (-1)) : False := by
  have hq := C.weight_gt hc0.le hc1 hp₀
  have hcov := C.refined_variance
  rw [C.B_div_A] at hcov
  exact ExclusionAlgebra.complete_normalized_exclusion hk ha hc0 hc1 (C.θ_pos hq) C.θ_lt_one C.u_pos
    C.α_pos.le (C.α_bound hk) C.d_pos C.d_lt_one.le C.e_nonneg C.e_bound C.u_le_b C.b_bound
    (C.weight_gt_five_sixths hk hq) C.v_nonneg C.V_pos hcov C.z_eq C.τ_eq C.g_nonneg
    (C.g_bound hq) C.γ_nonneg C.γ_le_g (C.ell_pos hq) C.theta_identity (C.u_ell_bound hq)
    C.q_div_d C.Θ_bounds.1 C.Θ_bounds.2 C.q_mul_V (C.K0_lower hq) C.K1_ge_tail
    C.conditional_mean_bound C.K1_identity C.cubic_ratio

end ExclusionData

/-- The full Section 5 conclusion for an arbitrary maximizing probability law.
There is no finite-support assumption or unproved conditional-moment premise. -/
theorem maximizer_proximity_rigid {n : ℕ} (hn : 6 ≤ n+1) {x c : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (ha : 12/13 < ((n+1 : ℕ) : ℝ)*x)
    (hc0 : 11/24 < c) (hc1 : c ≤ 1/2)
    (hcritical : 1-((n+1 : ℕ) : ℝ)*x = c*x)
    (hp₀ : (1-x)^(n+1) < Real.exp (-1))
    (hprox : supportCutoff n x μ-conditionalDeficit n μ < (failureScale n x μ-3*x)/20) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  obtain ⟨q,L,U,hq0,hq1,hmix,hLac,hUac,hLb,hUb⟩ :=
    maximizer_separated_components hx hxlt hμ hc0.le hcritical hprox
  by_cases hLpos : 0 < ∫t : ℝ≥0,(t : ℝ) ∂(L : Measure ℝ≥0)
  · let C : ExclusionData n :=
      { x := x, c := c, q := q, μ := μ, L := L, U := U,
        mean_pos := hx, mean_subcritical := hxlt, maximizes := hμ, critical := hcritical,
        proximity := hprox, weight_pos := hq0, weight_lt_one := hq1, mixture := hmix,
        lower_ac := hLac, upper_ac := hUac, lower_support := hLb, upper_support := hUb,
        lower_mean_pos := hLpos }
    exact (C.impossible (by dsimp only [ExclusionData.k]; exact_mod_cast hn) ha hc0 hc1 hp₀).elim
  · have hLmean : (∫t : ℝ≥0,(t : ℝ) ∂(L : Measure ℝ≥0)) = 0 :=
      le_antisymm (le_of_not_gt hLpos) (integral_nonneg (fun t => t.coe_nonneg))
    have hratio := maximizer_mixture_mass_ratio hx hxlt hμ hc0.le hcritical hprox
      hq0 hq1 hmix hLb hUb
    have hpower := lower_component_power_gt_half hq0 hq1 hratio hp₀
    have hple := maximizer_failure_le_bernoulli hx hxlt hμ
    exact maximizer_zero_lower_component_rigid hx hxlt hμ hq0.le hq1.le hmix hUac hUb
      ((memLp_coe_of_ae_le L hLb 2).integrable one_le_two) hLmean (by linarith)

end SharpTailMatching.Probability
