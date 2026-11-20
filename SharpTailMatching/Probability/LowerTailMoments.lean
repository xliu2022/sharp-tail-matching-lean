module

public import SharpTailMatching.Probability.LowerConditionalMoments

/-! # First moments of the genuine lower-component upper tail -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem integral_iidSum_eq_mul_integral (k : ℕ) (L : ProbabilityMeasure ℝ≥0)
    (hL : Integrable (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0)) :
    (∫w,iidSum k w ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) =
      (k : ℝ)*(∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) := by
  have hint (i : Fin k) : Integrable (fun w : Fin k → ℝ≥0 => (w i : ℝ))
      (Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) :=
    (measurePreserving_eval (fun _ : Fin k => (L : Measure ℝ≥0)) i).integrable_comp_of_integrable hL
  unfold iidSum
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have hi (i : Fin k) : (∫w : Fin k → ℝ≥0,(w i : ℝ)
      ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) = ∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0) :=
    integral_comp_eval (μ := fun _ : Fin k => (L : Measure ℝ≥0)) (i := i) (by fun_prop)
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem failure_probability_pos_of_integral {n : ℕ} (L : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hmean : ((n+1 : ℕ) : ℝ)*(∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) < 1) :
    0 < 1-tailProbability (n+1) L := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑i,w i < 1}
  let ρ := Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))
  have hp : ρ.real F = 1-tailProbability (n+1) L := failure_toReal_eq_one_sub_tail (n+1) L
  by_contra hn
  have hzero : ρ.real F = 0 := by rw [hp]; linarith [tailProbability_le_one (n+1) L]
  have hFzero : ρ F = 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hzero
  have hae : ∀ᵐ w ∂ρ,1 ≤ iidSum (n+1) w := by
    have hnot : ∀ᵐ w ∂ρ, w ∉ F := by
      apply ae_iff.mpr
      simp only [not_not]
      change ρ F = 0
      exact hFzero
    filter_upwards [hnot] with w hw
    have hNN : 1 ≤ ∑i,w i := le_of_not_gt hw
    unfold iidSum
    exact_mod_cast hNN
  have hi := integral_mono_ae (integrable_const (1 : ℝ))
    ((memLp_iidSum (n+1) L 2 hL).integrable one_le_two) hae
  rw [integral_const,probReal_univ,one_smul,integral_iidSum_eq_mul_integral (n+1) L
    (hL.integrable one_le_two)] at hi
  linarith

theorem failureMeasure_probability_of_tail_lt_one (n : ℕ) (L : ProbabilityMeasure ℝ≥0)
    (hp : 0 < 1-tailProbability (n+1) L) : IsProbabilityMeasure (failureMeasure n L) := by
  apply cond_isProbabilityMeasure
  intro hz
  have h := failure_toReal_eq_one_sub_tail (n+1) L
  rw [hz,ENNReal.toReal_zero] at h
  linarith

def lowerTailFirstMoment (n : ℕ) (x₀ : ℝ) (L : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫w in {w : Fin (n+1) → ℝ≥0 | 1 ≤ ∑i,w i},centeredSum (n+1) x₀ w
    ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))

theorem lowerTailFirstMoment_eq {n : ℕ} {x₀ : ℝ} (L : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hmean : (∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hp : 0 < 1-tailProbability (n+1) L) :
    lowerTailFirstMoment n x₀ L =
      (1-tailProbability (n+1) L)*failureExcessParameter n x₀ L := by
  let : IsProbabilityMeasure (failureMeasure n L) := failureMeasure_probability_of_tail_lt_one n L hp
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑i,w i < 1}
  have hF : MeasurableSet F := by measurability
  have hZ : Integrable (centeredSum (n+1) x₀)
      (Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) :=
    ((memLp_iidSum (n+1) L 2 hL).sub (memLp_const _)).integrable one_le_two
  have hmeanZ : (∫w,centeredSum (n+1) x₀ w
      ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) = 0 := by
    change (∫w,iidSum (n+1) w-((n+1 : ℕ) : ℝ)*x₀
      ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) = 0
    rw [integral_sub ((memLp_iidSum (n+1) L 2 hL).integrable one_le_two) (integrable_const _),
      integral_iidSum_eq_mul_integral (n+1) L (hL.integrable one_le_two),hmean,
      integral_const,probReal_univ,one_smul,sub_self]
  have hcond : (∫w,centeredSum (n+1) x₀ w ∂failureMeasure n L) =
      1-conditionalDeficit n L-((n+1 : ℕ) : ℝ)*x₀ := by
    change (∫w,iidSum (n+1) w-((n+1 : ℕ) : ℝ)*x₀ ∂failureMeasure n L) = _
    rw [integral_sub ((failureMeasure_iidSum_memLp n L 2).integrable one_le_two) (integrable_const _),
      integral_failureMeasure_iidSum,integral_const,probReal_univ,one_smul]
  have hscale := integral_failureMeasure_eq n L (centeredSum (n+1) x₀)
  rw [hcond,integral_indicator hF] at hscale
  have hmul := (eq_div_iff hp.ne').mp hscale
  have hsum := integral_add_compl hF hZ
  rw [hmeanZ] at hsum
  have hc : Fᶜ = {w : Fin (n+1) → ℝ≥0 | 1 ≤ ∑i,w i} := by ext w; simp [F]
  rw [hc] at hsum
  change (∫w in F,centeredSum (n+1) x₀ w
    ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0)))+lowerTailFirstMoment n x₀ L = 0 at hsum
  unfold failureExcessParameter
  nlinarith [hmul]

theorem lowerTailFirstMoment_ge_tail {n : ℕ} {x₀ : ℝ} (L : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0)) :
    (1-((n+1 : ℕ) : ℝ)*x₀)*tailProbability (n+1) L ≤ lowerTailFirstMoment n x₀ L := by
  let A : Set (Fin (n+1) → ℝ≥0) := {w | 1 ≤ ∑i,w i}
  have hA : MeasurableSet A := by measurability
  have hZ : Integrable (centeredSum (n+1) x₀)
      (Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) :=
    ((memLp_iidSum (n+1) L 2 hL).sub (memLp_const _)).integrable one_le_two
  have h := setIntegral_mono_on (integrable_const (1-((n+1 : ℕ) : ℝ)*x₀)) hZ.restrict hA (by
    intro w hw
    have hNN : 1 ≤ ∑i,w i := hw
    have hR : 1 ≤ iidSum (n+1) w := by unfold iidSum; exact_mod_cast hNN
    change 1-((n+1 : ℕ) : ℝ)*x₀ ≤ iidSum (n+1) w-((n+1 : ℕ) : ℝ)*x₀
    linarith)
  rw [setIntegral_const,smul_eq_mul] at h
  change tailProbability (n+1) L*(1-((n+1 : ℕ) : ℝ)*x₀) ≤ lowerTailFirstMoment n x₀ L at h
  nlinarith [h]

end SharpTailMatching.Probability
