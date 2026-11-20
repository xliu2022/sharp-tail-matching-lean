module

public import SharpTailMatching.Probability.CriticalClassification

/-! # The full sharp i.i.d. tail theorem and all equality cases

The laws here are arbitrary Borel probability measures on the nonnegative
reals. The mean is an extended integral and independence is represented by
the finite product measure. All critical comparison estimates have been proved
in the imported development; neither result has an auxiliary theorem premise.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace SharpTailMatching.Probability

theorem sharp_tail_bound (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ sharpTailValue k x := by
  by_cases hk1 : k = 1
  · subst k
    exact one_sample_bound x hx μ hmean
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨β, hβ, _⟩ := critical_mean_exists_unique k hk2
    apply sharp_tail_bound_of_critical_bound k hk2 β hβ.1 hβ.2.1 hβ.2.2 _ x hx μ hmean
    exact critical_bound_of_maximizer_classification hk2 hβ.1 hβ.2.1 hβ.2.2
      (fun ν hν => critical_maximizer_classification hk2 hβ.1 hβ.2.1 hβ.2.2 hν)

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
  have hclass := fun ν hν =>
    critical_maximizer_classification hk hβpos hβlt hβcross (μ := ν) hν
  exact sharp_tail_equality_of_critical k hk β hβpos hβlt hβcross
    (critical_bound_of_maximizer_classification hk hβpos hβlt hβcross hclass)
    (critical_equality_of_maximizer_classification hk hβpos hβlt hβcross hclass)
    x hx hxle μ hmean

end SharpTailMatching.Probability
