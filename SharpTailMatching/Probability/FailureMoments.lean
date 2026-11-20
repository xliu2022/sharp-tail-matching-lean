module

public import SharpTailMatching.Probability.FailureTilt
public import Mathlib.Probability.Moments.Variance

/-! # Moments of a maximizing law and of its independent sum -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def iidSum (k : ℕ) (w : Fin k → ℝ≥0) : ℝ := ∑ i, (w i : ℝ)

theorem iidSum_nonneg (k : ℕ) (w : Fin k → ℝ≥0) : 0 ≤ iidSum k w :=
  Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _

theorem maximizer_memLp_coe {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ≥0 => (z : ℝ)) p (μ : Measure ℝ≥0) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [maximizer_ae_below_supportCutoff hx hxlt hμ] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg z.coe_nonneg]
  exact hz.trans (maximizer_supportCutoff_le_one hx hxlt hμ)

theorem integral_iidSum (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) (hm : mean μ ≠ ∞) :
    (∫ w, iidSum k w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
      (k : ℝ) * (mean μ).toReal := by
  have hcoord (i : Fin k) : Integrable (fun w : Fin k → ℝ≥0 => (w i : ℝ))
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) :=
    (measurePreserving_eval (fun _ : Fin k => (μ : Measure ℝ≥0)) i).integrable_comp_of_integrable
      (integrable_coe_of_mean_ne_top μ hm)
  unfold iidSum
  rw [integral_finsetSum _ (fun i _ => hcoord i)]
  have hcoordMean (i : Fin k) :
      (∫ w : Fin k → ℝ≥0, (w i : ℝ) ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
      (mean μ).toReal := by
    have h := integral_map (μ := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
      (f := fun z : ℝ≥0 => (z : ℝ)) (measurable_pi_apply i).aemeasurable (by fun_prop)
    rw [(measurePreserving_eval (fun _ : Fin k => (μ : Measure ℝ≥0)) i).map_eq] at h
    exact h.symm.trans (integral_coe_eq_mean_toReal μ)
  simp [hcoordMean, nsmul_eq_mul]

theorem variance_iidSum (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hμ : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (μ : Measure ℝ≥0)) :
    variance (iidSum k) (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
      (k : ℝ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) := by
  have h := variance_sum_pi (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
    (X := fun _ : Fin k => fun z : ℝ≥0 => (z : ℝ)) (fun _ => hμ)
  have hfun : (∑ i : Fin k, fun w : Fin k → ℝ≥0 => (w i : ℝ)) = iidSum k := by
    funext w
    simp [iidSum]
  rw [hfun] at h
  simpa [nsmul_eq_mul] using h

theorem maximizer_variance_pos {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    0 < variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) := by
  have hkpos : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hkx : ((n+1 : ℕ) : ℝ) * x < 1 := by
    calc
      ((n+1 : ℕ) : ℝ) * x < ((n+1 : ℕ) : ℝ) * ((n+1 : ℕ) : ℝ)⁻¹ :=
        mul_lt_mul_of_pos_left hxlt hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hdom := zero_atom_dominates μ (mul_nonneg hkpos.le hx.le)
    (maximizer_positive_mass_le (by omega) hx.le hxlt hμ)
  have hmass : 0 < (μ : Measure ℝ≥0) {0} := by
    apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hkx))
    simpa using hdom {0}
  by_contra hvar
  have hzero : variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) = 0 :=
    le_antisymm (le_of_not_gt hvar) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero (maximizer_memLp_coe hx hxlt hμ 2) hzero
  rw [integral_coe_eq_mean_toReal, maximizer_mean_eq (by omega) hx.le hxlt hμ,
    ENNReal.toReal_ofReal hx.le] at hae
  have hnull : (μ : Measure ℝ≥0) {0} = 0 := by
    apply measure_mono_null (t := {z : ℝ≥0 | ¬(z : ℝ) = x})
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      simpa using hx.ne
    · exact ae_iff.mp hae
  exact hmass.ne' hnull

theorem failureIntegral_coordinate (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (φ : ℝ≥0 → ℝ) (i : Fin (n+1)) :
    (∫ w : Fin (n+1) → ℝ≥0,
      {w : Fin (n+1) → ℝ≥0 | ∑ j, w j < 1}.indicator (fun w => φ (w i)) w
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = failureIntegral n μ φ := by
  let e := Equiv.swap (0 : Fin (n+1)) i
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => ℝ≥0) e
  have hsum (w : Fin (n+1) → ℝ≥0) : ∑ j, E w j = ∑ j, w j := by
    rw [← Equiv.sum_comp e (fun j => E w j)]
    simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
  have hzero (w : Fin (n+1) → ℝ≥0) : E w 0 = w i := by
    simpa [e, E] using MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin (n+1) => ℝ≥0) e w i
  have hp := measurePreserving_piCongrLeft (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) e
  have hh := hp.integral_comp'
    ({w : Fin (n+1) → ℝ≥0 | ∑ j, w j < 1}.indicator (fun w => φ (w 0)))
  change (∫ w : Fin (n+1) → ℝ≥0,
    {w : Fin (n+1) → ℝ≥0 | ∑ j, w j < 1}.indicator (fun w => φ (w 0)) (E w)
      ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = failureIntegral n μ φ at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [] with w
  simp [Set.indicator_apply, hsum w, hzero w]

theorem failure_sum_integral (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (hm : mean μ ≠ ∞) :
    (∫ w : Fin (n+1) → ℝ≥0,
      {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1}.indicator (iidSum (n+1)) w
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      ((n+1 : ℕ) : ℝ) * failureIntegral n μ (fun z => (z : ℝ)) := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  have hF : MeasurableSet F := by measurability
  have hfun : F.indicator (iidSum (n+1)) =
      (fun w : Fin (n+1) → ℝ≥0 => ∑ i : Fin (n+1), F.indicator (fun w => (w i : ℝ)) w) := by
    funext w
    by_cases hw : w ∈ F <;> simp [hw, iidSum]
  change (∫ w, F.indicator (iidSum (n+1)) w ∂Measure.pi (fun _ : Fin (n+1) =>
    (μ : Measure ℝ≥0))) = _
  rw [hfun, integral_finsetSum]
  · simp [F, failureIntegral_coordinate, nsmul_eq_mul]
  · intro i _
    exact ((measurePreserving_eval (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) i).integrable_comp_of_integrable
      (integrable_coe_of_mean_ne_top μ hm)).indicator hF

/-- The unconditional expectation of the positive failure deficit. -/
def failureDeficit (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫ w : Fin (n+1) → ℝ≥0, max (1 - iidSum (n+1) w) 0
    ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))

/-- The mean deficit conditional on failure. -/
def conditionalDeficit (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  failureDeficit n μ / (1 - tailProbability (n+1) μ)

def failureExcessParameter (n : ℕ) (x : ℝ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  conditionalDeficit n μ - (1 - ((n+1 : ℕ) : ℝ) * x)

theorem integrable_failure_deficit (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Integrable (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0)
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) := by
  apply Integrable.of_bound (show Measurable
    (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) from by
      dsimp [iidSum]; fun_prop).aestronglyMeasurable 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by have := iidSum_nonneg (n+1) w; linarith) (by norm_num)

theorem failure_sum_add_deficit (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (hm : mean μ ≠ ∞) :
    ((n+1 : ℕ) : ℝ) * failureIntegral n μ (fun z => (z : ℝ)) + failureDeficit n μ =
      1 - tailProbability (n+1) μ := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  have hF : MeasurableSet F := by measurability
  have hsumInt : Integrable (iidSum (n+1))
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) := by
    apply integrable_finsetSum
    intro i _
    exact (measurePreserving_eval (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) i).integrable_comp_of_integrable
      (integrable_coe_of_mean_ne_top μ hm)
  rw [← failure_sum_integral n μ hm]
  change (∫ w, F.indicator (iidSum (n+1)) w ∂_) + (∫ w, max (1 - iidSum (n+1) w) 0 ∂_) = _
  rw [← integral_add (hsumInt.indicator hF) (integrable_failure_deficit n μ)]
  have hfun : (fun w : Fin (n+1) → ℝ≥0 =>
      F.indicator (iidSum (n+1)) w + max (1 - iidSum (n+1) w) 0) = F.indicator (fun _ => 1) := by
    funext w
    have hiff : w ∈ F ↔ iidSum (n+1) w < 1 := by
      change (∑ i, w i < 1) ↔ (∑ i, (w i : ℝ) < 1)
      exact_mod_cast Iff.rfl
    by_cases hw : w ∈ F
    · have hlt := hiff.mp hw
      simp [hw, max_eq_left (sub_nonneg.mpr hlt.le)]
    · have hle : 1 ≤ iidSum (n+1) w := le_of_not_gt (fun h => hw (hiff.mpr h))
      simp [hw, max_eq_right (sub_nonpos.mpr hle)]
  rw [hfun, integral_indicator_const (1 : ℝ) hF]
  simp only [smul_eq_mul, mul_one]
  exact failure_toReal_eq_one_sub_tail (n+1) μ

end SharpTailMatching.Probability
