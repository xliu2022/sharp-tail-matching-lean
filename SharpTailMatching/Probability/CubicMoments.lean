module

public import SharpTailMatching.Probability.SupportGap
public import SharpTailMatching.Probability.Cubic

/-! # Applying the cubic inequality to the actual iid maximizing sum -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def centeredSum (k : ℕ) (x : ℝ) (w : Fin k → ℝ≥0) : ℝ := iidSum k w - (k : ℝ)*x

theorem memLp_iidSum (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) (p : ℝ≥0∞)
    (hμ : MemLp (fun z : ℝ≥0 => (z : ℝ)) p (μ : Measure ℝ≥0)) :
    MemLp (iidSum k) p (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) := by
  change MemLp (fun w : Fin k → ℝ≥0 => ∑ i, (w i : ℝ)) p _
  apply memLp_finsetSum
  intro i _
  exact hμ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => (μ : Measure ℝ≥0)) i)

theorem maximizer_centeredSum_integral {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    (∫ w, centeredSum (n+1) x w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = 0 := by
  have hm := maximizer_mean_eq (by omega : 1 ≤ n+1) hx.le hxlt hμ
  have hmfin : mean μ ≠ ∞ := by rw [hm]; exact ENNReal.ofReal_ne_top
  have hint := (memLp_iidSum (n+1) μ 2 (maximizer_memLp_coe hx hxlt hμ 2)).integrable one_le_two
  change (∫ w, iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x
    ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = 0
  rw [integral_sub hint (integrable_const _), integral_iidSum _ μ hmfin,
    integral_const, probReal_univ, one_smul, hm, ENNReal.toReal_ofReal hx.le, sub_self]

theorem maximizer_cubic_failure_quadratic {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    (∫ w, if centeredSum (n+1) x w < 1-((n+1 : ℕ) : ℝ)*x then
      (centeredSum (n+1) x w + failureExcessParameter n x μ)^2 else 0
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      (1-tailProbability (n+1) μ) * conditionalVariance n μ := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  let f : (Fin (n+1) → ℝ≥0) → ℝ := fun w =>
    if centeredSum (n+1) x w < 1-((n+1 : ℕ) : ℝ)*x then
      (centeredSum (n+1) x w + failureExcessParameter n x μ)^2 else 0
  have hvanish (w : Fin (n+1) → ℝ≥0) (hw : 1 ≤ ∑ i, w i) : f w = 0 := by
    have hs : 1 ≤ iidSum (n+1) w := by dsimp [iidSum]; exact_mod_cast hw
    have hnot : ¬ centeredSum (n+1) x w < 1-((n+1 : ℕ) : ℝ)*x := by
      change ¬ iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x < 1-((n+1 : ℕ) : ℝ)*x
      linarith
    simp only [f, if_neg hnot]
  have hcond := integral_failureMeasure_of_vanish n μ f hvanish
  have hvar := variance_eq_integral (deficit_memLp n (failureMeasure n μ) 2).aemeasurable
  rw [variance_deficit_failureMeasure, integral_failureMeasure_deficit] at hvar
  have hsame : (∫ w, f w ∂failureMeasure n μ) = conditionalVariance n μ := by
    rw [hvar]
    apply integral_congr_ae
    filter_upwards [ae_cond_mem (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
      (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1} by measurability)] with w hw
    have hs : iidSum (n+1) w < 1 := by dsimp [iidSum]; exact_mod_cast hw
    have hyes : centeredSum (n+1) x w < 1-((n+1 : ℕ) : ℝ)*x := by
      change iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x < 1-((n+1 : ℕ) : ℝ)*x
      linarith
    simp only [f, if_pos hyes]
    rw [max_eq_left (by linarith)]
    dsimp [centeredSum, failureExcessParameter]
    ring
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  rw [hsame] at hcond
  change (∫ w, f w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = _
  exact (eq_div_iff hp).mp hcond |>.symm.trans (mul_comm _ _)

theorem maximizer_cubic_upper_first_moment {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    (∫ w, if 1-((n+1 : ℕ) : ℝ)*x ≤ centeredSum (n+1) x w then
      centeredSum (n+1) x w else 0
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      (1-tailProbability (n+1) μ) * failureExcessParameter n x μ := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  have hF : MeasurableSet F := by measurability
  have hZ : Integrable (centeredSum (n+1) x)
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) :=
    ((memLp_iidSum (n+1) μ 2 (maximizer_memLp_coe hx hxlt hμ 2)).sub
      (memLp_const (((n+1 : ℕ) : ℝ)*x))).integrable one_le_two
  have hI := (integrable_const (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
    (1-((n+1 : ℕ) : ℝ)*x)).indicator hF
  have hpoint (w : Fin (n+1) → ℝ≥0) :
      (if 1-((n+1 : ℕ) : ℝ)*x ≤ centeredSum (n+1) x w then centeredSum (n+1) x w else 0) =
        centeredSum (n+1) x w + max (1-iidSum (n+1) w) 0 -
          F.indicator (fun _ => 1-((n+1 : ℕ) : ℝ)*x) w := by
    by_cases hw : w ∈ F
    · have hs : iidSum (n+1) w < 1 := by dsimp [iidSum]; exact_mod_cast hw
      simp only [Set.indicator_of_mem hw]
      have hnot : ¬ 1-((n+1 : ℕ) : ℝ)*x ≤ centeredSum (n+1) x w := by
        change ¬ 1-((n+1 : ℕ) : ℝ)*x ≤ iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x
        linarith
      rw [if_neg hnot, max_eq_left (by linarith)]
      dsimp [centeredSum]
      ring
    · have hs : 1 ≤ iidSum (n+1) w := by
        have hnn : 1 ≤ ∑ i, w i := le_of_not_gt hw
        dsimp [iidSum]
        exact_mod_cast hnn
      simp only [Set.indicator_of_notMem hw]
      have hyes : 1-((n+1 : ℕ) : ℝ)*x ≤ centeredSum (n+1) x w := by
        change 1-((n+1 : ℕ) : ℝ)*x ≤ iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x
        linarith
      rw [if_pos hyes, max_eq_right (by linarith)]
      dsimp [centeredSum]
      ring
  simp_rw [hpoint]
  have hZd : Integrable (fun w : Fin (n+1) → ℝ≥0 =>
      centeredSum (n+1) x w + max (1-iidSum (n+1) w) 0)
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) :=
    hZ.add (integrable_failure_deficit n μ)
  rw [integral_sub hZd hI,
    integral_add hZ (integrable_failure_deficit n μ), maximizer_centeredSum_integral hx hxlt hμ,
    integral_indicator_const _ hF]
  change 0 + failureDeficit n μ -
    ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).toReal *
      (1-((n+1 : ℕ) : ℝ)*x) = _
  rw [show ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).toReal =
    1-tailProbability (n+1) μ from failure_toReal_eq_one_sub_tail (n+1) μ]
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  dsimp [failureExcessParameter, conditionalDeficit]
  field_simp
  ring

theorem maximizer_cubic_bound_of_ae_le {n : ℕ} {x b : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hb : 0 ≤ b)
    (hsupp : ∀ᵐ z : ℝ≥0 ∂(μ : Measure ℝ≥0), (z : ℝ) ≤ b) :
    (failureScale n x μ * failureExcessParameter n x μ +
      (max (failureExcessParameter n x μ - b) 0)^2 / 12) * conditionalVariance n μ ≥
        (max (conditionalDeficit n μ - 2*b) 0)^3 / 3 * failureExcessParameter n x μ := by
  let X : Fin (n+1) → (Fin (n+1) → ℝ≥0) → ℝ := fun i w => (w i : ℝ)-x
  have hX (i : Fin (n+1)) : Measurable (X i) := by dsimp [X]; fun_prop
  have hindep : iIndepFun X (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) :=
    iIndepFun_pi (X := fun _ : Fin (n+1) => fun z : ℝ≥0 => (z : ℝ)-x) (fun _ => by fun_prop)
  have hsupport (i : Fin (n+1)) : ∀ᵐ w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)),
      X i w ∈ Set.Icc (-x) (-x+b) := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) i).quasiMeasurePreserving.ae hsupp] with w hw
    exact ⟨by dsimp [X]; have := (w i).coe_nonneg; linarith,
      by dsimp [X]; linarith⟩
  have hm := maximizer_mean_eq (by omega : 1 ≤ n+1) hx.le hxlt hμ
  have hmfin : mean μ ≠ ∞ := by rw [hm]; exact ENNReal.ofReal_ne_top
  have hcenter (i : Fin (n+1)) :
      (∫ w, X i w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = 0 := by
    have hi := integral_map (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
      (f := fun z : ℝ≥0 => (z : ℝ)-x) (measurable_pi_apply i).aemeasurable (by fun_prop)
    rw [(measurePreserving_eval (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) i).map_eq] at hi
    rw [← hi, integral_sub (integrable_coe_of_mean_ne_top μ hmfin) (integrable_const _),
      integral_coe_eq_mean_toReal, hm, ENNReal.toReal_ofReal hx.le,
      integral_const, probReal_univ, one_smul, sub_self]
  have hδ : 0 < 1-((n+1 : ℕ) : ℝ)*x := by
    have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
    have hh := mul_lt_mul_of_pos_left hxlt hk
    rw [mul_inv_cancel₀ hk.ne'] at hh
    linarith
  have h := capped_cubic_inequality (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
    X hX hindep hb hsupport hcenter hδ (failureExcessParameter n x μ)
  have hsum : (fun w : Fin (n+1) → ℝ≥0 => ∑ i, X i w) = centeredSum (n+1) x := by
    funext w
    simp [X, centeredSum, iidSum, Finset.sum_sub_distrib, nsmul_eq_mul]
  have hsumPt (w : Fin (n+1) → ℝ≥0) : ∑ i, X i w = centeredSum (n+1) x w := congrFun hsum w
  simp_rw [hsumPt] at h
  have hvar : variance (centeredSum (n+1) x) (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      failureScale n x μ * failureExcessParameter n x μ := by
    change variance (fun w : Fin (n+1) → ℝ≥0 => iidSum (n+1) w - ((n+1 : ℕ) : ℝ)*x) _ = _
    rw [variance_sub_const (show Measurable (iidSum (n+1)) from by unfold iidSum; fun_prop).aestronglyMeasurable,
      maximizer_variance_identity hx hxlt hμ]
  rw [hvar, maximizer_cubic_failure_quadratic hx hxlt hμ,
    maximizer_cubic_upper_first_moment hx hxlt hμ] at h
  have harg : 1-((n+1 : ℕ) : ℝ)*x + failureExcessParameter n x μ - 2*b =
      conditionalDeficit n μ - 2*b := by dsimp [failureExcessParameter]; ring
  rw [harg] at h
  have hp : 0 < 1-tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  apply le_of_mul_le_mul_left (a := 1-tailProbability (n+1) μ) _ hp
  nlinarith [h]

end SharpTailMatching.Probability
