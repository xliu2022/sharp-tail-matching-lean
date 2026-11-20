module

public import SharpTailMatching.Probability.LowerCubic

/-! # Actual objects used in the exclusion argument

Every real parameter below is defined from the maximizing law and its two
conditional component laws. This structure assumes no count, moment, variance,
or cubic estimate: those are proved in the subsequent normalization modules.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

structure ExclusionData (n : ℕ) where
  x : ℝ
  c : ℝ
  q : ℝ
  μ : ProbabilityMeasure ℝ≥0
  L : ProbabilityMeasure ℝ≥0
  U : ProbabilityMeasure ℝ≥0
  mean_pos : 0 < x
  mean_subcritical : x < ((n+1 : ℕ) : ℝ)⁻¹
  maximizes : Maximizes (n+1) x μ
  critical : 1-((n+1 : ℕ) : ℝ)*x = c*x
  proximity : supportCutoff n x μ-conditionalDeficit n μ < (failureScale n x μ-3*x)/20
  weight_pos : 0 < q
  weight_lt_one : q < 1
  mixture : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
    ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)
  lower_ac : (L : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0)
  upper_ac : (U : Measure ℝ≥0) ≪ (μ : Measure ℝ≥0)
  lower_support : ∀ᵐ t : ℝ≥0 ∂(L : Measure ℝ≥0), (t : ℝ) ≤ x+failureScale n x μ/16
  upper_support : ∀ᵐ t : ℝ≥0 ∂(U : Measure ℝ≥0), x+17*failureScale n x μ/20 < (t : ℝ) ∧
    (t : ℝ) ≤ supportCutoff n x μ
  lower_mean_pos : 0 < ∫t : ℝ≥0,(t : ℝ) ∂(L : Measure ℝ≥0)

namespace ExclusionData

variable {n : ℕ} (C : ExclusionData n)

abbrev k (_C : ExclusionData n) : ℝ := ((n+1 : ℕ) : ℝ)
def x₀ : ℝ := ∫t : ℝ≥0,(t : ℝ) ∂(C.L : Measure ℝ≥0)
def y₀ : ℝ := ∫t : ℝ≥0,(t : ℝ) ∂(C.U : Measure ℝ≥0)
def M : ℝ := supportCutoff n C.x C.μ
def D : ℝ := failureScale n C.x C.μ
def B : ℝ := failureExcessParameter n C.x C.μ
def r : ℝ := conditionalDeficit n C.μ
def p : ℝ := 1-tailProbability (n+1) C.μ
def p₀ : ℝ := (1-C.x)^(n+1)
def A : ℝ := C.M-C.x₀
def m : ℝ := C.k*(C.x-C.x₀)
def rate : ℝ := C.k*(1-C.q)
def a : ℝ := C.k*C.x
def θ : ℝ := 1-C.m/(C.a*C.A)
def u : ℝ := C.x₀/C.A
def α : ℝ := C.m/(C.k*C.A)
def d : ℝ := C.D/C.A
def e : ℝ := (C.M-C.r)/C.A
def b₀ : ℝ≥0 := essentialUpper C.L
def b : ℝ := (C.b₀ : ℝ)/C.A
def v : ℝ := conditionalVariance n C.μ/C.A^2
def V : ℝ := C.k*variance (fun t : ℝ≥0 => (t : ℝ)) (C.L : Measure ℝ≥0)/C.A^2
def z : ℝ := (C.B-C.m)/C.A
def τ : ℝ := (1-C.k*C.x₀)/C.A
def nu : ℝ := (C.M-C.y₀)/C.A
def g : ℝ := conditionalUpperMean n C.μ C.b₀
def γ : ℝ := conditionalUpperProbability n C.μ C.b₀
def ell : ℝ := C.a-C.rate
def R : ℝ := C.p/C.q^(n+1)
def K0 : ℝ := tailProbability (n+1) C.L/C.R
def K1 : ℝ := lowerTailFirstMoment n C.x₀ C.L/(C.R*C.A)
def dL : ℝ := failureExcessParameter n C.x₀ C.L/C.A
def Θ : ℝ := upperVarianceRemainder (n+1) C.M C.x₀ C.q C.U/C.A^2

theorem k_pos : 0 < C.k := by dsimp [k]; positivity

theorem D_pos : 0 < C.D := maximizer_failureScale_pos C.mean_pos C.mean_subcritical C.maximizes

theorem M_sub_x : C.M-C.x = C.D :=
  maximizer_supportCutoff_sub_mean C.mean_pos C.mean_subcritical C.maximizes

theorem p_pos : 0 < C.p :=
  sub_pos.mpr (tailProbability_lt_one (by omega) C.mean_pos.le C.mean_subcritical C.μ C.maximizes.1)

theorem p_le_p₀ : C.p ≤ C.p₀ :=
  maximizer_failure_le_bernoulli C.mean_pos C.mean_subcritical C.maximizes

theorem a_pos : 0 < C.a := mul_pos C.k_pos C.mean_pos

theorem a_lt_one : C.a < 1 := by
  have h := mul_lt_mul_of_pos_left C.mean_subcritical C.k_pos
  rwa [mul_inv_cancel₀ C.k_pos.ne'] at h

theorem lower_memLp (s : ℝ≥0∞) : MemLp (fun t : ℝ≥0 => (t : ℝ)) s (C.L : Measure ℝ≥0) :=
  memLp_coe_of_ae_le C.L C.lower_support s

theorem upper_memLp (s : ℝ≥0∞) : MemLp (fun t : ℝ≥0 => (t : ℝ)) s (C.U : Measure ℝ≥0) :=
  memLp_coe_of_ae_le C.U (C.upper_support.mono (fun _ h => h.2)) s

theorem integral_μ : (∫t : ℝ≥0,(t : ℝ) ∂(C.μ : Measure ℝ≥0)) = C.x := by
  rw [integral_coe_eq_mean_toReal,maximizer_mean_eq (by omega) C.mean_pos.le C.mean_subcritical C.maximizes,
    ENNReal.toReal_ofReal C.mean_pos.le]

theorem mixture_mean : C.x = C.q*C.x₀+(1-C.q)*C.y₀ := by
  have h := mixture_integral (C.μ : Measure ℝ≥0) (C.L : Measure ℝ≥0) (C.U : Measure ℝ≥0)
    C.weight_pos.le C.weight_lt_one.le C.mixture (fun t : ℝ≥0 => (t : ℝ))
    ((C.lower_memLp 2).integrable one_le_two) ((C.upper_memLp 2).integrable one_le_two)
  rw [C.integral_μ] at h
  exact h

theorem upper_above_x : ∀ᵐ t : ℝ≥0 ∂(C.U : Measure ℝ≥0), C.x < (t : ℝ) := by
  filter_upwards [C.upper_support] with t ht
  have hD := C.D_pos
  change 0 < failureScale n C.x C.μ at hD
  linarith [ht.1]

theorem x₀_lt_x : C.x₀ < C.x :=
  mixture_lower_mean_lt (C.μ : Measure ℝ≥0) (C.L : Measure ℝ≥0) (C.U : Measure ℝ≥0)
    C.weight_pos C.weight_lt_one C.mixture (fun t : ℝ≥0 => (t : ℝ))
    ((C.lower_memLp 2).integrable one_le_two) ((C.upper_memLp 2).integrable one_le_two)
    C.integral_μ C.upper_above_x

theorem D_lt_A : C.D < C.A := by
  have hM := C.M_sub_x
  have hx := C.x₀_lt_x
  dsimp [A]
  linarith

theorem A_pos : 0 < C.A := C.D_pos.trans C.D_lt_A

theorem m_pos : 0 < C.m := mul_pos C.k_pos (sub_pos.mpr C.x₀_lt_x)

theorem rate_pos : 0 < C.rate := mul_pos C.k_pos (sub_pos.mpr C.weight_lt_one)

theorem lower_support_b₀ : ∀ᵐ t ∂(C.L : Measure ℝ≥0), t ≤ C.b₀ := by
  let t₀ : ℝ≥0 := ⟨C.x+C.D/16,by have := C.mean_pos; have := C.D_pos; positivity⟩
  exact ae_le_essentialUpper C.L (b := t₀) C.lower_support

theorem b₀_le : (C.b₀ : ℝ) ≤ C.x+C.D/16 := by
  let t₀ : ℝ≥0 := ⟨C.x+C.D/16,by have := C.mean_pos; have := C.D_pos; positivity⟩
  exact essentialUpper_le C.L (b := t₀) C.lower_support

theorem upper_above_b₀ : ∀ᵐ t ∂(C.U : Measure ℝ≥0), C.b₀ < t := by
  filter_upwards [C.upper_support] with t ht
  have hb := C.b₀_le
  have hD := C.D_pos
  change (C.b₀ : ℝ) < (t : ℝ)
  change C.x+17*C.D/20 < (t : ℝ) ∧ (t : ℝ) ≤ C.M at ht
  linarith [ht.1]

theorem x₀_le_b₀ : C.x₀ ≤ (C.b₀ : ℝ) := by
  have h := integral_mono_ae ((C.lower_memLp 2).integrable one_le_two) (integrable_const (C.b₀ : ℝ)) C.lower_support_b₀
  simpa only [x₀,y₀,integral_const,probReal_univ,one_smul] using h

theorem y₀_le_M : C.y₀ ≤ C.M := by
  have h := integral_mono_ae ((C.upper_memLp 2).integrable one_le_two) (integrable_const C.M)
    (C.upper_support.mono (fun _ h => h.2))
  simpa only [x₀,y₀,integral_const,probReal_univ,one_smul] using h

theorem upper_mean_gap : C.x+17*C.D/20 < C.y₀ :=
  integral_const_lt_of_ae_lt (C.U : Measure ℝ≥0) _ ((C.upper_memLp 2).integrable one_le_two)
    (C.upper_support.mono (fun _ h => h.1))

theorem lower_failure_pos : 0 < 1-tailProbability (n+1) C.L := by
  apply failure_probability_pos_of_integral C.L (C.lower_memLp 2)
  have h := mul_lt_mul_of_pos_left C.x₀_lt_x C.k_pos
  exact h.trans C.a_lt_one

theorem lower_variance_pos : 0 < variance (fun t : ℝ≥0 => (t : ℝ)) (C.L : Measure ℝ≥0) := by
  apply maximizer_lower_variance_pos C.mean_pos C.mean_subcritical C.maximizes C.mixture (C.lower_memLp 2)
  · filter_upwards [C.upper_above_x] with t ht
    change (0 : ℝ) < (t : ℝ)
    exact C.mean_pos.trans ht
  · exact C.lower_mean_pos

theorem V_pos : 0 < C.V :=
  div_pos (mul_pos C.k_pos C.lower_variance_pos) (sq_pos_of_pos C.A_pos)

theorem γ_lt_one : C.γ < 1 := by
  have h := allLower_failure_probability C.mean_pos C.mean_subcritical C.maximizes C.weight_pos.le
    C.mixture C.lower_support_b₀ C.upper_above_b₀
  have hprod := mul_pos (pow_pos C.weight_pos (n+1)) C.lower_failure_pos
  rw [h] at hprod
  have hp := C.p_pos
  change 0 < C.p*(1-C.γ) at hprod
  have hpos : 0 < 1-C.γ := (mul_pos_iff.mp hprod).resolve_right (by intro h; exact hp.not_gt h.1)
    |>.2
  linarith

theorem R_pos : 0 < C.R := div_pos C.p_pos (pow_pos C.weight_pos (n+1))

end ExclusionData
end SharpTailMatching.Probability
