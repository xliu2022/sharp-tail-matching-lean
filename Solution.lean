module

public import SharpTailMatching

/-!
# Complete headline declarations

All nine intended Challenge declarations are exported with complete proofs.
There is no import of Challenge, no proof placeholder, and no assumption of a
remaining mathematical theorem. Protected Comparator verification is tracked
separately in the validation report; a successful build alone is not that check.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace SharpTailMatching

theorem sharp_tail_bound (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ sharpTailValue k x := by
  exact Probability.sharp_tail_bound k hk x hx μ hmean

theorem sharp_tail_attained (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    ∃ μ : ProbabilityMeasure ℝ≥0,
      mean μ ≤ ENNReal.ofReal x ∧ tailProbability k μ = sharpTailValue k x := by
  exact Probability.sharp_tail_attained k hk x hx

theorem sharp_tail_equality (k : ℕ) (hk : 2 ≤ k)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < (k : ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k : ℝ)*β)^k)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ (k : ℝ)⁻¹)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ = sharpTailValue k x ↔
      (x < β ∧ (μ : Measure ℝ≥0) = unitBernoulliMeasure x) ∨
      (x = β ∧ ((μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)) ∨
      (β < x ∧ (μ : Measure ℝ≥0) = smallBernoulliMeasure k x) := by
  exact Probability.sharp_tail_equality k hk β hβpos hβlt hβcross x hx hxle μ hmean

theorem zero_mean_iff (μ : ProbabilityMeasure ℝ≥0) :
    mean μ = 0 ↔ (μ : Measure ℝ≥0) = Measure.dirac 0 := by
  exact Probability.mean_eq_zero_iff μ

theorem one_sample_equality (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability 1 μ = sharpTailValue 1 x ↔
      (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  exact Probability.one_sample_equality x hx hxle μ hmean

theorem tail_eq_one_iff (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ = 1 ↔
      (μ : Measure ℝ≥0) (Set.Iio ((k : ℝ≥0)⁻¹)) = 0 := by
  exact Probability.tail_eq_one_iff k hk μ

-- `critical_mean_exists_unique` is already exported by Probability.CriticalMean.
-- The two matching targets are exported by Matching.Main.

end SharpTailMatching
