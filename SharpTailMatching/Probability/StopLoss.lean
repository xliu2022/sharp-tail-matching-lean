module

public import SharpTailMatching.Probability.ConditionalMoments

/-! # The stop-loss kernel and its weighted Fubini identity -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def stopLossIntegrand (n : ℕ) (z : ℝ≥0) (y : Fin n → ℝ≥0) : ℝ :=
  max (1 - (z : ℝ) - iidSum n y) 0

def stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) : ℝ :=
  ∫ y : Fin n → ℝ≥0, stopLossIntegrand n z y
    ∂Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0))

theorem stopLossIntegrand_bounds (n : ℕ) (z : ℝ≥0) (y : Fin n → ℝ≥0) :
    0 ≤ stopLossIntegrand n z y ∧ stopLossIntegrand n z y ≤ 1 := by
  refine ⟨le_max_right _ _, ?_⟩
  apply max_le
  · have := iidSum_nonneg n y
    have := z.coe_nonneg
    linarith
  · norm_num

theorem integrable_stopLossIntegrand (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    Integrable (stopLossIntegrand n z) (Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0))) := by
  apply Integrable.of_bound (show Measurable (stopLossIntegrand n z) from by
    unfold stopLossIntegrand iidSum; fun_prop).aestronglyMeasurable 1
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (stopLossIntegrand_bounds n z y).1]
  exact (stopLossIntegrand_bounds n z y).2

theorem measurable_stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) : Measurable (stopLoss n μ) := by
  have hf : StronglyMeasurable (fun p : ℝ≥0 × (Fin n → ℝ≥0) => stopLossIntegrand n p.1 p.2) := by
    apply Measurable.stronglyMeasurable
    unfold stopLossIntegrand iidSum
    fun_prop
  exact hf.integral_prod_right'.measurable

theorem stopLoss_bounds (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) :
    0 ≤ stopLoss n μ z ∧ stopLoss n μ z ≤ 1 := by
  constructor
  · exact integral_nonneg (fun y => (stopLossIntegrand_bounds n z y).1)
  · have h := integral_mono (integrable_stopLossIntegrand n μ z) (integrable_const (1 : ℝ))
      (fun y => (stopLossIntegrand_bounds n z y).2)
    simpa [stopLoss] using h

theorem memLp_stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (p : ℝ≥0∞) :
    MemLp (stopLoss n μ) p (μ : Measure ℝ≥0) := by
  apply MemLp.of_bound (measurable_stopLoss n μ).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (stopLoss_bounds n μ z).1]
  exact (stopLoss_bounds n μ z).2

theorem integral_mul_stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (φ : ℝ≥0 → ℝ) (hφ : Measurable φ) (hint : Integrable φ (μ : Measure ℝ≥0)) :
    (∫ z : ℝ≥0, φ z * stopLoss n μ z ∂(μ : Measure ℝ≥0)) =
      ∫ w : Fin (n+1) → ℝ≥0, φ (w 0) * max (1 - iidSum (n+1) w) 0
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) := by
  symm
  let ψ : (Fin (n+1) → ℝ≥0) → ℝ := fun w => φ (w 0) * max (1 - iidSum (n+1) w) 0
  have hψ : Measurable ψ := by unfold ψ iidSum; fun_prop
  have hfamily : (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) =
      Fin.cons (μ : Measure ℝ≥0) (fun _ : Fin n => (μ : Measure ℝ≥0)) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  change (∫ w, ψ w ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = _
  rw [hfamily, ← pi_cons_map, integral_map (by fun_prop) hψ.aestronglyMeasurable]
  have hfun : (fun p : ℝ≥0 × (Fin n → ℝ≥0) => ψ (Fin.cons p.1 p.2)) =
      (fun p => φ p.1 * stopLossIntegrand n p.1 p.2) := by
    funext p
    simp [ψ, iidSum, stopLossIntegrand, Fin.sum_univ_succ, sub_add_eq_sub_sub]
  have hj : Measurable (fun p : ℝ≥0 × (Fin n → ℝ≥0) => stopLossIntegrand n p.1 p.2) := by
    unfold stopLossIntegrand iidSum
    fun_prop
  have hintj : Integrable (fun p : ℝ≥0 × (Fin n → ℝ≥0) => φ p.1 * stopLossIntegrand n p.1 p.2)
      ((μ : Measure ℝ≥0).prod (Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0)))) := by
    apply (hint.comp_fst _).mul_bdd hj.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (stopLossIntegrand_bounds n p.1 p.2).1]
    exact (stopLossIntegrand_bounds n p.1 p.2).2
  rw [hfun, integral_prod _ hintj]
  simp_rw [integral_const_mul]
  rfl

theorem integral_stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ z : ℝ≥0, stopLoss n μ z ∂(μ : Measure ℝ≥0)) = failureDeficit n μ := by
  simpa [failureDeficit] using integral_mul_stopLoss n μ (fun _ => 1) measurable_const (integrable_const 1)

/-- The kernel plus its maximal possible linear decrease is nondecreasing. -/
theorem monotone_adjusted_stopLoss (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    Monotone (fun z : ℝ≥0 => stopLoss n μ z + (1 - tailProbability n μ) * (z : ℝ)) := by
  intro u v huv
  have huvR : (u : ℝ) ≤ v := huv
  let F : Set (Fin n → ℝ≥0) := {y | ∑ i, y i < 1}
  have hF : MeasurableSet F := by measurability
  have hpoint (y : Fin n → ℝ≥0) : stopLossIntegrand n u y ≤ stopLossIntegrand n v y +
      F.indicator (fun _ => (v : ℝ) - (u : ℝ)) y := by
    by_cases hy : y ∈ F
    · simp only [Set.indicator_of_mem hy]
      apply max_le
      · have := le_max_left (1 - (v : ℝ) - iidSum n y) 0
        dsimp [stopLossIntegrand]
        linarith
      · have := le_max_right (1 - (v : ℝ) - iidSum n y) 0
        dsimp [stopLossIntegrand]
        linarith
    · have hsum : 1 ≤ iidSum n y := by
        have hs : 1 ≤ ∑ i, y i := le_of_not_gt hy
        dsimp [iidSum]
        exact_mod_cast hs
      have hu0 : 1 - (u : ℝ) - iidSum n y ≤ 0 := by have := u.coe_nonneg; linarith
      have hv0 : 1 - (v : ℝ) - iidSum n y ≤ 0 := by have := v.coe_nonneg; linarith
      simp [stopLossIntegrand, hy, max_eq_right hu0, max_eq_right hv0]
  have h := integral_mono (integrable_stopLossIntegrand n μ u)
    ((integrable_stopLossIntegrand n μ v).add ((integrable_const _).indicator hF)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_stopLossIntegrand n μ v) ((integrable_const _).indicator hF),
    integral_indicator_const _ hF] at h
  change stopLoss n μ u ≤ stopLoss n μ v +
    ((Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0))) F).toReal * ((v : ℝ) - (u : ℝ)) at h
  rw [show ((Measure.pi (fun _ : Fin n => (μ : Measure ℝ≥0))) F).toReal = 1 - tailProbability n μ
    from failure_toReal_eq_one_sub_tail n μ] at h
  nlinarith

end SharpTailMatching.Probability
