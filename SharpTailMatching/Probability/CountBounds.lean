module

public import SharpTailMatching.Probability.CountCorrelation
public import SharpTailMatching.CriticalProbabilityEstimates
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Quantitative comparison of the upper-count probability and mean -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem conditionalUpperMean_nonneg (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0) :
    0 ≤ conditionalUpperMean n μ b :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem conditionalUpperProbability_nonneg (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (b : ℝ≥0) :
    0 ≤ conditionalUpperProbability n μ b := ENNReal.toReal_nonneg

theorem exp_neg_chord_five_eighths {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (-t) ≤ 1-(5/8)*t := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
    (sub_nonneg.mpr ht1) ht0 (show (1-t)+t=1 by ring)
  simp only [smul_eq_mul,mul_zero,zero_add,mul_neg_one,Real.exp_zero,mul_one] at h
  have he := mul_le_mul_of_nonneg_right CriticalEstimates.exp_neg_one_lt_three_eighths.le ht0
  nlinarith

theorem power_failure_mass_lower (k : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlam : (k : ℝ)*(1-q) ≤ 1) :
    (5/8)*((k : ℝ)*(1-q)) ≤ 1-q^k := by
  have hqexp : q ≤ Real.exp (q-1) := by linarith [Real.add_one_le_exp (q-1)]
  have hp := pow_le_pow_left₀ hq0 hqexp k
  rw [← Real.exp_nat_mul] at hp
  have harg : (k : ℝ)*(q-1) = -((k : ℝ)*(1-q)) := by ring
  rw [harg] at hp
  have h := exp_neg_chord_five_eighths (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hq1)) hlam
  linarith

/-- The factor 5/8 is obtained from the actual binomial component mixture,
not introduced as a condition on its conditional count. -/
theorem conditionalUpperProbability_lower {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z)
    (hlam : ((n+1 : ℕ) : ℝ)*(1-q) ≤ 1) :
    (5/8)*conditionalUpperMean n μ b ≤ conditionalUpperProbability n μ b := by
  have hc := conditionalUpperMean_correlation hx hxlt hμ hq0 hq1.le hmix hLb hUb
  have hp := mul_le_mul_of_nonneg_right (power_failure_mass_lower (n+1) hq0 hq1.le hlam)
    (conditionalUpperMean_nonneg n μ b)
  have hlampos : 0 < ((n+1 : ℕ) : ℝ)*(1-q) := mul_pos (by positivity) (sub_pos.mpr hq1)
  apply (mul_le_mul_iff_right₀ hlampos).mp
  nlinarith

end SharpTailMatching.Probability
