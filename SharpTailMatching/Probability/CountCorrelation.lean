module

public import SharpTailMatching.Probability.CountMixture

/-! # Negative correlation of failure with the positive upper count -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem binaryFailure_empty (k : ℕ) (U L : ProbabilityMeasure ℝ≥0) :
    binaryFailure k U L ∅ = 1-tailProbability k L := by
  have hf : binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) ∅ =
      (fun _ : Fin k => (L : Measure ℝ≥0)) := by
    funext i
    simp [binaryMeasure]
  unfold binaryFailure
  rw [hf]
  exact failure_toReal_eq_one_sub_tail k L

theorem binaryFailure_sum (k : ℕ) {μ L U : ProbabilityMeasure ℝ≥0} {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) :
    (∑S : Finset (Fin k),binaryWeight k q S*binaryFailure k U L S) =
      1-tailProbability k μ := by
  let F : Set (Fin k → ℝ≥0) := {w | ∑i,w i < 1}
  have hF : MeasurableSet F := by measurability
  have h := integral_binary_mixture k hq0 hq1 hmix (F.indicator (fun _ => (1 : ℝ)))
    (fun S => (integrable_const (1 : ℝ)).indicator hF)
  simp only [integral_indicator_const _ hF,smul_eq_mul,mul_one] at h
  exact h.symm.trans (failure_toReal_eq_one_sub_tail k μ)

theorem conditionalUpperMean_binary_sum {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (1-tailProbability (n+1) μ)*conditionalUpperMean n μ b =
      ∑S : Finset (Fin (n+1)),binaryWeight (n+1) q S*(S.card : ℝ)*binaryFailure (n+1) U L S := by
  unfold conditionalUpperMean
  rw [integral_failureMeasure_eq,integral_binary_mixture (n+1) hq0 hq1 hmix _
    (fun S => ((memLp_upperCount (n+1) b _ 2).integrable one_le_two).indicator (by measurability))]
  simp_rw [integral_failure_upperCount_binary (n+1) U L hLb hUb]
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  rw [mul_div_cancel₀ _ hp]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Conditional failure suppresses large positive upper counts. The conclusion
is proved from the full mixture expansion and a common coupling of all binary
component choices; no monotonicity of conditional probabilities is assumed. -/
theorem conditionalUpperMean_correlation {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    (1-q^(n+1))*conditionalUpperMean n μ b ≤
      ((n+1 : ℕ) : ℝ)*(1-q)*conditionalUpperProbability n μ b := by
  classical
  let s : Finset (Finset (Fin (n+1))) := Finset.univ.erase ∅
  let w := binaryWeight (n+1) q
  let f : Finset (Fin (n+1)) → ℝ := fun S => S.card
  let g := binaryFailure (n+1) U L
  have hcov := weighted_antitone_covariance s w f g
    (fun S _ => binaryWeight_nonneg (n+1) hq0 hq1 S) (by
      intro S _ T _
      by_cases hST : S.card ≤ T.card
      · apply mul_nonpos_of_nonpos_of_nonneg
        · exact sub_nonpos.mpr (Nat.cast_le.mpr hST)
        · exact sub_nonneg.mpr (binaryFailure_antitone_card (n+1) U L hLb hUb S T hST)
      · apply mul_nonpos_of_nonneg_of_nonpos
        · exact sub_nonneg.mpr (Nat.cast_le.mpr (le_of_not_ge hST))
        · exact sub_nonpos.mpr (binaryFailure_antitone_card (n+1) U L hLb hUb T S (le_of_not_ge hST)))
  have hmass : (∑S∈s,w S) = 1-q^(n+1) := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin (n+1)))))
      (a := ∅) w (Finset.mem_univ _)
    dsimp [w] at h
    rw [binaryWeight_sum (n+1) hq0 hq1 hmix,binaryWeight_empty] at h
    dsimp [s,w]
    linarith
  have hcount : (∑S∈s,w S*f S) = ((n+1 : ℕ) : ℝ)*(1-q) := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin (n+1)))))
      (a := ∅) (fun S => w S*f S) (Finset.mem_univ _)
    have hz : w ∅*f ∅ = 0 := by simp [f]
    rw [hz,add_zero] at h
    exact h.trans (binaryWeight_card_sum (n+1) hq0 hq1 hmix hLb hUb)
  have hcountF : (∑S∈s,w S*f S*g S) =
      (1-tailProbability (n+1) μ)*conditionalUpperMean n μ b := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin (n+1)))))
      (a := ∅) (fun S => w S*f S*g S) (Finset.mem_univ _)
    have hz : w ∅*f ∅*g ∅ = 0 := by simp [f]
    rw [hz,add_zero] at h
    exact h.trans (conditionalUpperMean_binary_sum hx hxlt hμ hq0 hq1 hmix hLb hUb).symm
  have hmassF : (∑S∈s,w S*g S) =
      (1-tailProbability (n+1) μ)*conditionalUpperProbability n μ b := by
    have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Finset (Fin (n+1)))))
      (a := ∅) (fun S => w S*g S) (Finset.mem_univ _)
    have hempty : w ∅*g ∅ = q^(n+1)*(1-tailProbability (n+1) L) := by
      rw [show w ∅ = q^(n+1) from binaryWeight_empty _ _,show g ∅ = 1-tailProbability (n+1) L
        from binaryFailure_empty _ _ _]
    rw [hempty,binaryFailure_sum (n+1) hq0 hq1 hmix,
      allLower_failure_probability hx hxlt hμ hq0 hmix hLb hUb] at h
    dsimp [s] at *
    nlinarith
  rw [hmass,hcount,hcountF,hmassF] at hcov
  have hp := sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith [hcov]

end SharpTailMatching.Probability
