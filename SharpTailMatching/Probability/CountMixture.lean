module

public import SharpTailMatching.Probability.CountAntitone

/-! # Exact finite-mixture formulas for the upper count -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def binaryWeight (k : ℕ) (q : ℝ) (S : Finset (Fin k)) : ℝ :=
  (1-q)^S.card*q^(k-S.card)

theorem binaryWeight_nonneg (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (S : Finset (Fin k)) : 0 ≤ binaryWeight k q S :=
  mul_nonneg (pow_nonneg (sub_nonneg.mpr hq1) _) (pow_nonneg hq0 _)

theorem binaryWeight_empty (k : ℕ) (q : ℝ) : binaryWeight k q ∅ = q^k := by
  simp [binaryWeight]

theorem integral_binary_mixture (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (f : (Fin k → ℝ≥0) → ℝ)
    (hf : ∀S : Finset (Fin k), Integrable f
      (Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S))) :
    (∫w,f w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
      ∑S : Finset (Fin k),binaryWeight k q S*
        (∫w,f w ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)) := by
  have hm : (μ : Measure ℝ≥0) = ENNReal.ofReal (1-q) • (U : Measure ℝ≥0) +
      ENNReal.ofReal q • (L : Measure ℝ≥0) := hmix.trans (add_comm _ _)
  rw [hm,pi_binary_expansion_general k (U : Measure ℝ≥0) (L : Measure ℝ≥0) _ _
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
  rw [integral_finsetSum_measure (fun S _ => (hf S).smul_measure (by finiteness))]
  simp only [integral_smul_measure,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hq0,ENNReal.toReal_ofReal (sub_nonneg.mpr hq1),smul_eq_mul,binaryWeight]

theorem upperCount_eq_card_binary (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) (S : Finset (Fin k)) :
    ∀ᵐ w ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S),
      upperCount k b w = S.card := by
  classical
  have hcoord (i : Fin k) : ∀ᵐ z ∂binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S i,
      (if b < z then (1 : ℕ) else 0) = if i ∈ S then 1 else 0 := by
    by_cases hi : i ∈ S
    · simp only [binaryMeasure,ite_eq_left hi]
      filter_upwards [hUb] with z hz
      simp only [ite_eq_left hz]
    · simp only [binaryMeasure,ite_eq_right hi]
      filter_upwards [hLb] with z hz
      simp only [ite_eq_right (not_lt.mpr hz)]
  have hall : ∀ᵐ w ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S),
      ∀i,(if b < w i then (1 : ℕ) else 0) = if i ∈ S then 1 else 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)
      (i := i)).eventually (hcoord i)
  filter_upwards [hall] with w hw
  unfold upperCount
  simp only [hw]
  simp

theorem integral_upperCount_binary (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) (S : Finset (Fin k)) :
    (∫w,(upperCount k b w : ℝ)
      ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)) = S.card := by
  rw [integral_congr_ae ((upperCount_eq_card_binary k U L hLb hUb S).mono (fun _ h => congrArg Nat.cast h)),
    integral_const,probReal_univ,one_smul]

theorem integral_upperIndicator_mixture {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (∫z,upperIndicator b z ∂(μ : Measure ℝ≥0)) = 1-q := by
  rw [mixture_integral (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0) hq0 hq1 hmix _
    ((memLp_upperIndicator b (L : Measure ℝ≥0) 2).integrable one_le_two)
    ((memLp_upperIndicator b (U : Measure ℝ≥0) 2).integrable one_le_two)]
  have hL : (∫z,upperIndicator b z ∂(L : Measure ℝ≥0)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hLb] with z hz
    simp [upperIndicator,not_lt.mpr hz]
  have hU : (∫z,upperIndicator b z ∂(U : Measure ℝ≥0)) = 1 := by
    calc
      _ = ∫_ : ℝ≥0,(1 : ℝ) ∂(U : Measure ℝ≥0) := by
        apply integral_congr_ae
        filter_upwards [hUb] with z hz
        simp [upperIndicator,hz]
      _ = 1 := by simp
  rw [hL,hU]
  ring

theorem integral_upperCount_mixture (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (∫w,(upperCount k b w : ℝ) ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
      (k : ℝ)*(1-q) := by
  simp_rw [coe_upperCount]
  have hint (i : Fin k) : Integrable (fun w : Fin k → ℝ≥0 => upperIndicator b (w i))
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) :=
    (measurePreserving_eval (fun _ : Fin k => (μ : Measure ℝ≥0)) i).integrable_comp_of_integrable
      ((memLp_upperIndicator b (μ : Measure ℝ≥0) 2).integrable one_le_two)
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have hi (i : Fin k) : (∫w : Fin k → ℝ≥0,upperIndicator b (w i)
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = 1-q := by
    rw [integral_comp_eval (μ := fun _ : Fin k => (μ : Measure ℝ≥0)) (i := i)
      (measurable_upperIndicator b).aestronglyMeasurable]
    exact integral_upperIndicator_mixture hq0 hq1 hmix hLb hUb
  simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem binaryWeight_sum (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) :
    (∑S : Finset (Fin k),binaryWeight k q S) = 1 := by
  have h := integral_binary_mixture k hq0 hq1 hmix (fun _ => (1 : ℝ)) (fun _ => integrable_const _)
  simpa using h.symm

theorem binaryWeight_card_sum (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (∑S : Finset (Fin k),binaryWeight k q S*(S.card : ℝ)) = (k : ℝ)*(1-q) := by
  have h := integral_binary_mixture k hq0 hq1 hmix (fun w => (upperCount k b w : ℝ))
    (fun S => (memLp_upperCount k b _ 2).integrable one_le_two)
  rw [integral_upperCount_mixture k hq0 hq1 hmix hLb hUb] at h
  simpa only [integral_upperCount_binary k U L hLb hUb] using h.symm

theorem integral_failureMeasure_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (f : (Fin (n+1) → ℝ≥0) → ℝ) :
    (∫w,f w ∂failureMeasure n μ) =
      (∫w,({w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1}).indicator f w
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)))/(1-tailProbability (n+1) μ) := by
  unfold failureMeasure ProbabilityTheory.cond
  rw [integral_smul_measure,← integral_indicator (by measurability),ENNReal.toReal_inv,
    failure_toReal_eq_one_sub_tail,smul_eq_mul]
  ring

theorem integral_failure_upperCount_binary (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) (S : Finset (Fin k)) :
    (∫w,({w : Fin k → ℝ≥0 | ∑i,w i < 1}).indicator (fun w => (upperCount k b w : ℝ)) w
      ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)) =
      (S.card : ℝ)*binaryFailure k U L S := by
  calc
    _ = ∫w,({w : Fin k → ℝ≥0 | ∑i,w i < 1}).indicator (fun _ => (S.card : ℝ)) w
      ∂Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S) := by
      apply integral_congr_ae
      filter_upwards [upperCount_eq_card_binary k U L hLb hUb S] with w hw
      by_cases hF : ∑i,w i < 1 <;> simp [hF,hw]
    _ = _ := by rw [integral_indicator_const _ (by measurability),smul_eq_mul]; exact mul_comm _ _

end SharpTailMatching.Probability
