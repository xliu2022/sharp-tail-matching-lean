module

public import SharpTailMatching.Matching.LawRigidity
public import SharpTailMatching.Probability.Main

/-! # Unconditional uniform probability stability

The exact rigidity input of the compactness argument is discharged by the
fully proved sharp tail theorem and its complete equality classification.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Matching

open Probability

theorem unit_law_exact_rigidity (k : ℕ) (hk : 1 ≤ k) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ (k : ℝ)⁻¹)
    (μ : ProbabilityMeasure UnitInterval) (hm : realUnitMean μ ≤ x)
    (ht : max (1-(1-x)^k) (((k : ℝ)*x)^k) ≤ (unitTail k μ).toReal) :
    realUnitMean μ = x ∧ (unitAtomCost 1 μ = 0 ∨ unitAtomCost (k : ℝ)⁻¹ μ = 0) := by
  apply unit_rigidity_of_classification k hk _ x hx0 hx1 μ hm ht
  intro x hx hxle ρ hmean htail
  have heq : tailProbability k ρ = sharpTailValue k x := by
    apply le_antisymm (Probability.sharp_tail_bound k hk x hx.le ρ hmean)
    simpa only [sharpTailValue,ite_eq_left hxle] using htail
  by_cases hk1 : k = 1
  · subst k
    left
    exact (Probability.one_sample_equality x hx.le (by simpa using hxle) ρ hmean).mp heq
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨β,⟨hβ0,hβlt,hβcross⟩,_⟩ := SharpTailMatching.critical_mean_exists_unique k hk2
    have h := (Probability.sharp_tail_equality k hk2 β hβ0 hβlt hβcross x hx hxle ρ hmean).mp heq
    rcases h with ⟨_,hu⟩ | ⟨_,hu | hs⟩ | ⟨_,hs⟩
    · exact Or.inl hu
    · exact Or.inl hu
    · exact Or.inr hs
    · exact Or.inr hs

/-- An unconditional modulus, uniform over the full compact mean interval. -/
theorem law_stability (k : ℕ) (hk : 1 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ℝ), 0 ≤ x → x ≤ (k : ℝ)⁻¹ →
      ∀ μ : ProbabilityMeasure UnitInterval, realUnitMean μ ≤ x+δ →
        max (1-(1-x)^k) (((k : ℝ)*x)^k)-δ ≤ (unitTail k μ).toReal →
        |realUnitMean μ-x| < η ∧
          (unitAtomCost 1 μ < η ∨ unitAtomCost (k : ℝ)⁻¹ μ < η) :=
  compact_law_stability k (unit_law_exact_rigidity k hk) hη

end SharpTailMatching.Matching
