module

public import SharpTailMatching.Probability.UpperCount

/-! # Exact restriction to the event that every observation is lower -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def allLowerEvent (k : ℕ) (b : ℝ≥0) : Set (Fin k → ℝ≥0) := {w | upperCount k b w = 0}

theorem allLowerEvent_eq_pi (k : ℕ) (b : ℝ≥0) :
    allLowerEvent k b = Set.univ.pi (fun _ : Fin k => Set.Iic b) := by
  ext w
  simp [allLowerEvent, upperCount_zero_iff, Pi.le_def]

theorem measurableSet_allLowerEvent (k : ℕ) (b : ℝ≥0) : MeasurableSet (allLowerEvent k b) :=
  (measurable_upperCount k b) (measurableSet_singleton 0)

theorem mixture_restrict_lower {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (μ : Measure ℝ≥0).restrict (Set.Iic b) = ENNReal.ofReal q • (L : Measure ℝ≥0) := by
  have hL : (L : Measure ℝ≥0).restrict (Set.Iic b) = (L : Measure ℝ≥0) :=
    Measure.restrict_eq_self_of_ae_mem hLb
  have hU : (U : Measure ℝ≥0).restrict (Set.Iic b) = 0 := by
    apply Measure.restrict_eq_zero.mpr
    change (U : Measure ℝ≥0) {a | a ≤ b} = 0
    simpa only [not_lt] using (ae_iff.mp hUb)
  rw [hmix, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul, hL, hU,
    smul_zero, add_zero]

theorem pi_restrict_allLowerEvent (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))).restrict (allLowerEvent k b) =
      (ENNReal.ofReal q)^k • Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0)) := by
  rw [allLowerEvent_eq_pi, Measure.restrict_pi_pi]
  simp_rw [mixture_restrict_lower hmix hLb hUb]
  exact pi_const_smul k (L : Measure ℝ≥0) _ ENNReal.ofReal_ne_top

theorem failureMeasure_restrict_allLowerEvent (n : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (failureMeasure n μ).restrict (allLowerEvent (n+1) b) =
      (((Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))
        {w | ∑ i, w i < 1})⁻¹ * (ENNReal.ofReal q)^(n+1)) •
      (Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))).restrict {w | ∑ i, w i < 1} := by
  let F : Set (Fin (n+1) → ℝ≥0) := {w | ∑ i, w i < 1}
  have hF : MeasurableSet F := by measurability
  unfold failureMeasure ProbabilityTheory.cond
  rw [Measure.restrict_smul, Measure.restrict_comm,
    pi_restrict_allLowerEvent (n+1) hmix hLb hUb, Measure.restrict_smul, smul_smul]
  exact measurableSet_allLowerEvent (n+1) b

theorem integral_failureMeasure_allLowerEvent (n : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) (f : (Fin (n+1) → ℝ≥0) → ℝ) :
    (∫ w in allLowerEvent (n+1) b, f w ∂failureMeasure n μ) =
      q^(n+1)/(1-tailProbability (n+1) μ) *
        (∫ w in {w | ∑ i, w i < 1}, f w ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) := by
  rw [failureMeasure_restrict_allLowerEvent n hmix hLb hUb, integral_smul_measure,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofReal hq,
    failure_toReal_eq_one_sub_tail, smul_eq_mul]
  ring

theorem failureMeasure_allLowerEvent_real (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0)
    [IsProbabilityMeasure (failureMeasure n μ)] :
    (failureMeasure n μ).real (allLowerEvent (n+1) b) = 1-conditionalUpperProbability n μ b := by
  have h := probReal_compl_eq_one_sub (μ := failureMeasure n μ)
    (measurableSet_allLowerEvent (n+1) b)
  have hc : (allLowerEvent (n+1) b)ᶜ = {w | 0 < upperCount (n+1) b w} := by
    ext w
    simp [allLowerEvent, Nat.pos_iff_ne_zero]
  rw [hc] at h
  change conditionalUpperProbability n μ b = 1-(failureMeasure n μ).real (allLowerEvent (n+1) b) at h
  linarith

theorem allLower_failure_probability {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    q^(n+1)*(1-tailProbability (n+1) L) =
      (1-tailProbability (n+1) μ)*(1-conditionalUpperProbability n μ b) := by
  let : IsProbabilityMeasure (failureMeasure n μ) := maximizer_failureMeasure_probability hx hxlt hμ
  have h := integral_failureMeasure_allLowerEvent n hq hmix hLb hUb (fun _ => (1 : ℝ))
  rw [setIntegral_const, smul_eq_mul, mul_one, failureMeasure_allLowerEvent_real,
    setIntegral_const, smul_eq_mul, mul_one] at h
  change 1-conditionalUpperProbability n μ b =
    q^(n+1)/(1-tailProbability (n+1) μ)*
      ((Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) {w | ∑ i, w i < 1}).toReal at h
  rw [failure_toReal_eq_one_sub_tail] at h
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  field_simp at h
  nlinarith [h]

end SharpTailMatching.Probability
