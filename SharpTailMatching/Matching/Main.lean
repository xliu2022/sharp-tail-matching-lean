module

public import SharpTailMatching.Matching.Stability
public import SharpTailMatching.Matching.ExactAssembly
public import SharpTailMatching.Matching.BranchSeparation

/-! # The exact large matching theorem and its equality cases -/

@[expose] public section

noncomputable section

namespace SharpTailMatching.Matching

theorem global_extremal_edit_stability (k : ℕ) (hk : 3 ≤ k) : GlobalExtremalEditStability k := by
  intro ε hε
  obtain ⟨δ,hδ,s₀,hs₀⟩ := matching_stability hk hε
  refine ⟨s₀,?_⟩
  intro s n hs hn H hu hν hlarge
  have hlargeR : (max (coverSize k n s) (cliqueSize k s) : ℝ) ≤ H.card := by
    exact_mod_cast hlarge
  have herr : 0 ≤ δ*(n : ℝ)^k := mul_nonneg hδ.le (pow_nonneg (Nat.cast_nonneg n) _)
  have hnear : (max (coverSize k n s) (cliqueSize k s) : ℝ)-δ*(n : ℝ)^k ≤ H.card := by
    linarith only [hlargeR,herr]
  have h := hs₀ s hs (α := Fin n) (by simpa only [Fintype.card_fin] using hn) H hu hν
    (by simpa only [Fintype.card_fin] using hnear)
  simpa only [Fintype.card_fin] using h

theorem large_matching_bound_and_equality (k : ℕ) (hk : 3 ≤ k) :
    ∃ s₀ : ℕ,∀ s n : ℕ,s₀ ≤ s → k*(s+1) ≤ n →
      ∀ H : Finset (Finset (Fin n)),SharpTailMatching.IsUniform k H →
        SharpTailMatching.MatchingNumberAtMost s H →
        H.card ≤ max (coverSize k n s) (cliqueSize k s) ∧
        (H.card = max (coverSize k n s) (cliqueSize k s) ↔
          (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
          (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) :=
  exact_matching_of_stability k hk (global_extremal_edit_stability k hk) (matching_branch_separation k hk)

end SharpTailMatching.Matching

namespace SharpTailMatching

/-- The exact Erdős matching bound, uniformly over all admissible ambient
vertex counts once the matching parameter is sufficiently large. -/
theorem large_matching_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ s₀ : ℕ,∀ s n : ℕ,s₀ ≤ s → k*(s+1) ≤ n →
      ∀ H : Finset (Finset (Fin n)),IsUniform k H → MatchingNumberAtMost s H →
        H.card ≤ max (coverSize k n s) (cliqueSize k s) := by
  obtain ⟨s₀,hs₀⟩ := Matching.large_matching_bound_and_equality k hk
  exact ⟨s₀,fun s n hs hn H hu hν => (hs₀ s n hs hn H hu hν).1⟩

/-- Equality holds precisely for a standard construction whose size is the
larger of the two candidate sizes, including both forms at a tie. -/
theorem large_matching_equality (k : ℕ) (hk : 3 ≤ k) :
    ∃ s₀ : ℕ,∀ s n : ℕ,s₀ ≤ s → k*(s+1) ≤ n →
      ∀ H : Finset (Finset (Fin n)),IsUniform k H → MatchingNumberAtMost s H →
        (H.card = max (coverSize k n s) (cliqueSize k s) ↔
          (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
          (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) := by
  obtain ⟨s₀,hs₀⟩ := Matching.large_matching_bound_and_equality k hk
  exact ⟨s₀,fun s n hs hn H hu hν => (hs₀ s n hs hn H hu hν).2⟩

end SharpTailMatching
