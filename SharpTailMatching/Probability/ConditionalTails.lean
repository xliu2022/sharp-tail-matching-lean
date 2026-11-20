module

public import SharpTailMatching.Probability.Covariance
public import SharpTailMatching.Probability.Cantelli
public import SharpTailMatching.SupportAlgebra

/-! # Conditional deficit tails and exclusion of intermediate contact points -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem deficit_memLp (n : ℕ) (ν : Measure (Fin (n+1) → ℝ≥0)) [IsFiniteMeasure ν]
    (p : ℝ≥0∞) : MemLp (fun w => max (1 - iidSum (n+1) w) 0) p ν := by
  apply MemLp.of_bound (show Measurable (fun w => max (1 - iidSum (n+1) w) 0)
    from by unfold iidSum; fun_prop).aestronglyMeasurable 1
  filter_upwards [] with w
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by have := iidSum_nonneg (n+1) w; linarith) (by norm_num)

theorem variance_deficit_failureMeasure (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    variance (fun w => max (1 - iidSum (n+1) w) 0) (failureMeasure n μ) =
      conditionalVariance n μ := by
  have hmeas : Measurable (iidSum (n+1)) := by unfold iidSum; fun_prop
  have hae : (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) =ᵐ[failureMeasure n μ]
      (fun w => 1 - iidSum (n+1) w) := by
    filter_upwards [ae_cond_mem (μ := Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
      (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | ∑ i, w i < 1} by measurability)] with w hw
    have hlt : iidSum (n+1) w < 1 := by dsimp [iidSum]; exact_mod_cast hw
    exact max_eq_left (sub_nonneg.mpr hlt.le)
  rw [variance_congr hae, variance_const_sub hmeas.aestronglyMeasurable]
  rfl

theorem deficit_mass_le_sectionFailure (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (y : ℝ≥0) :
    (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))).real
      {w | (y : ℝ) < max (1 - iidSum (n+1) w) 0} ≤ sectionFailure n μ y := by
  have hfamily : (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) =
      Fin.cons (μ : Measure ℝ≥0) (fun _ : Fin n => (μ : Measure ℝ≥0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hmeas : MeasurableSet {w : Fin (n+1) → ℝ≥0 |
      (y : ℝ) < max (1 - iidSum (n+1) w) 0} := by
    unfold iidSum
    measurability
  unfold Measure.real
  rw [hfamily, ← pi_cons_map, Measure.map_apply (by fun_prop) hmeas]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  calc
    _ ≤ (μ : Measure ℝ≥0).prod (Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0)))
        (Set.univ ×ˢ {w : Fin n → ℝ≥0 | y + ∑ i, w i < 1}) := by
      apply measure_mono
      intro p hp
      refine ⟨Set.mem_univ _, ?_⟩
      have h0 : ¬ (y : ℝ) < 0 := not_lt.mpr y.coe_nonneg
      have hs : (y : ℝ) < 1 - iidSum (n+1) (Fin.cons p.1 p.2) :=
        (lt_max_iff.mp hp).resolve_right h0
      have hsum : iidSum (n+1) (Fin.cons p.1 p.2) = (p.1 : ℝ) + iidSum n p.2 := by
        simp [iidSum, Fin.sum_univ_succ]
      rw [hsum] at hs
      have hR : (y : ℝ) + ∑ i, (p.2 i : ℝ) < 1 := by
        dsimp [iidSum] at hs
        have := p.1.coe_nonneg
        linarith
      exact_mod_cast hR
    _ = _ := by rw [Measure.prod_prod, measure_univ, one_mul]

theorem failureMeasure_deficit_gt_le (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (y : ℝ≥0) :
    (failureMeasure n μ).real {w | (y : ℝ) < max (1 - iidSum (n+1) w) 0} ≤
      sectionFailure n μ y / (1 - tailProbability (n+1) μ) := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  let A : Set (Fin (n+1) → ℝ≥0) := {w | (y : ℝ) < max (1 - iidSum (n+1) w) 0}
  have hF : MeasurableSet F := by measurability
  have hsub : A ⊆ F := by
    intro w hw
    have hs : (y : ℝ) < 1 - iidSum (n+1) w :=
      (lt_max_iff.mp hw).resolve_right (not_lt.mpr y.coe_nonneg)
    have hR : iidSum (n+1) w < 1 := by have := y.coe_nonneg; linarith
    dsimp [iidSum] at hR
    exact_mod_cast hR
  change (ProbabilityTheory.cond (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).real A ≤ _
  rw [Measure.real, cond_apply hF, Set.inter_eq_right.mpr hsub, ENNReal.toReal_mul,
    ENNReal.toReal_inv]
  rw [show ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) F).toReal =
    1 - tailProbability (n+1) μ from failure_toReal_eq_one_sub_tail (n+1) μ]
  have h := deficit_mass_le_sectionFailure n μ y
  change ((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) A).toReal ≤ sectionFailure n μ y at h
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (sub_nonneg.mpr
    (tailProbability_le_one (n+1) μ)))).trans_eq (by ring)

theorem maximizer_contact_deficit_mass {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) {y : ℝ≥0}
    (hy : sectionFailure n μ y = (1 - tailProbability (n+1) μ) *
      (supportCutoff n x μ - (y : ℝ)) / failureScale n x μ) :
    ((y : ℝ) - x) / failureScale n x μ ≤
      (failureMeasure n μ).real {w | max (1 - iidSum (n+1) w) 0 ≤ (y : ℝ)} := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  have hD := (maximizer_failureScale_pos hx hxlt hμ).ne'
  have hM := maximizer_supportCutoff_sub_mean hx hxlt hμ
  have h := failureMeasure_deficit_gt_le n μ y
  rw [hy] at h
  have hsimp : (1 - tailProbability (n+1) μ) * (supportCutoff n x μ - (y : ℝ)) /
      failureScale n x μ / (1 - tailProbability (n+1) μ) =
      (supportCutoff n x μ - (y : ℝ)) / failureScale n x μ := by field_simp
  rw [hsimp] at h
  have hc := probReal_compl_eq_one_sub (μ := failureMeasure n μ)
    (show MeasurableSet {w : Fin (n+1) → ℝ≥0 | max (1 - iidSum (n+1) w) 0 ≤ (y : ℝ)}
      by unfold iidSum; measurability)
  simp only [Set.compl_ofPred, not_le] at hc
  rw [hc] at h
  have hid : ((y : ℝ) - x) / failureScale n x μ =
      1 - (supportCutoff n x μ - (y : ℝ)) / failureScale n x μ := by
    apply (div_eq_iff hD).mpr
    field_simp
    linarith
  rw [hid]
  linarith

end SharpTailMatching.Probability
