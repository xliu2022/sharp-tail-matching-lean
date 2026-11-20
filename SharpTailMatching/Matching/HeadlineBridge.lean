module

public import SharpTailMatching.Matching.Basic
public import Mathlib.Data.Fintype.Fin

/-! # The independent matching statement surface

The six definitions in the outer namespace are identical to Challenge.lean.
The equivalences below connect that fixed vertex-label surface to the general
finite-family development without changing the matching or equality notions.
-/

@[expose] public section

namespace SharpTailMatching

def IsUniform (k : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = k

def MatchingNumberAtMost (s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ M : Finset (Finset (Fin n)), M ⊆ H →
    (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) → M.card ≤ s

def coverSize (k n s : ℕ) : ℕ :=
  Nat.choose n k - Nat.choose (n-s) k

def cliqueSize (k s : ℕ) : ℕ :=
  Nat.choose (k*(s+1)-1) k

def IsCompleteCover (k s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = s ∧
    ∀ e : Finset (Fin n), e ∈ H ↔ e.card = k ∧ ¬ Disjoint e S

def IsStandardClique (k s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ Q : Finset (Fin n), Q.card = k*(s+1)-1 ∧
    ∀ e : Finset (Fin n), e ∈ H ↔ e.card = k ∧ e ⊆ Q

namespace Matching

theorem headline_uniform_iff {k n : ℕ} {H : Finset (Finset (Fin n))} :
    SharpTailMatching.IsUniform k H ↔ IsUniform k H := Iff.rfl

theorem headline_matching_iff {s n : ℕ} {H : Finset (Finset (Fin n))} :
    SharpTailMatching.MatchingNumberAtMost s H ↔ MatchingNumberAtMost s H := Iff.rfl

theorem headline_cover_iff {k s n : ℕ} {H : Finset (Finset (Fin n))} :
    IsCompleteCover k s H ↔
      ∃ S : Finset (Fin n), S.card = s ∧ H = coverFamily k Finset.univ S := by
  constructor
  · rintro ⟨S, hS, hH⟩
    refine ⟨S, hS, Finset.ext fun e => ?_⟩
    simpa only [mem_coverFamily, Finset.subset_univ, true_and] using hH e
  · rintro ⟨S, hS, rfl⟩
    refine ⟨S, hS, fun e => ?_⟩
    simp only [mem_coverFamily, Finset.subset_univ, true_and]

theorem headline_clique_iff {k s n : ℕ} {H : Finset (Finset (Fin n))} :
    IsStandardClique k s H ↔
      ∃ Q : Finset (Fin n), Q.card = k*(s+1)-1 ∧ H = cliqueFamily k Q := by
  constructor
  · rintro ⟨Q, hQ, hH⟩
    refine ⟨Q, hQ, Finset.ext fun e => ?_⟩
    simpa only [mem_cliqueFamily, and_comm] using hH e
  · rintro ⟨Q, hQ, rfl⟩
    refine ⟨Q, hQ, fun e => ?_⟩
    simp only [mem_cliqueFamily, and_comm]

theorem headline_cover_card {k s n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsCompleteCover k s H) : H.card = coverSize k n s := by
  obtain ⟨S, hS, rfl⟩ := headline_cover_iff.mp hH
  rw [card_coverFamily k (Finset.subset_univ S), hS]
  simp only [Finset.card_univ, Fintype.card_fin, coverSize]

theorem headline_clique_card {k s n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsStandardClique k s H) : H.card = cliqueSize k s := by
  obtain ⟨Q, hQ, rfl⟩ := headline_clique_iff.mp hH
  simp only [card_cliqueFamily, hQ, cliqueSize]

theorem headline_cover_feasible {k s n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : IsCompleteCover k s H) :
    SharpTailMatching.IsUniform k H ∧ SharpTailMatching.MatchingNumberAtMost s H := by
  obtain ⟨S, hS, rfl⟩ := headline_cover_iff.mp hH
  refine ⟨coverFamily_uniform k Finset.univ S, ?_⟩
  rw [← hS]
  exact coverFamily_matchingNumberAtMost k Finset.univ S

theorem headline_clique_feasible {k s n : ℕ} (hk : 0 < k)
    {H : Finset (Finset (Fin n))} (hH : IsStandardClique k s H) :
    SharpTailMatching.IsUniform k H ∧ SharpTailMatching.MatchingNumberAtMost s H := by
  obtain ⟨Q, hQ, rfl⟩ := headline_clique_iff.mp hH
  exact ⟨cliqueFamily_uniform k Q, standardClique_matchingNumberAtMost hk hQ⟩

theorem headline_standard_equality {k s n : ℕ} {H : Finset (Finset (Fin n))}
    (hH : (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
      (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) :
    H.card = max (coverSize k n s) (cliqueSize k s) := by
  rcases hH with ⟨hcover, hle⟩ | ⟨hclique, hle⟩
  · rw [headline_cover_card hcover, max_eq_left hle]
  · rw [headline_clique_card hclique, max_eq_right hle]

theorem headline_equality_of_classification {k s n : ℕ}
    {H : Finset (Finset (Fin n))}
    (hclass : H.card = max (coverSize k n s) (cliqueSize k s) →
      IsCompleteCover k s H ∨ IsStandardClique k s H) :
    (H.card = max (coverSize k n s) (cliqueSize k s) ↔
      (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
      (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) := by
  constructor
  · intro heq
    rcases hclass heq with hcover | hclique
    · exact Or.inl ⟨hcover, by
        have h := le_max_right (coverSize k n s) (cliqueSize k s)
        rw [← heq, headline_cover_card hcover] at h
        exact h⟩
    · exact Or.inr ⟨hclique, by
        have h := le_max_left (coverSize k n s) (cliqueSize k s)
        rw [← heq, headline_clique_card hclique] at h
        exact h⟩
  · exact headline_standard_equality

end Matching
end SharpTailMatching
