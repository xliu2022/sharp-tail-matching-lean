/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite combinatorial foundations for the two standard extremal families.
These declarations make no use of a probabilistic extremal theorem.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

/-- A finite family is a matching when its distinct edges are disjoint. -/
def IsMatching (M : Finset (Finset α)) : Prop :=
  (M : Set (Finset α)).Pairwise Disjoint

/-- Every member of a uniform family has the specified cardinality. -/
def IsUniform (k : ℕ) (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, e.card = k

/-- A matching bound stated directly, without choosing a maximum matching. -/
def MatchingNumberAtMost (s : ℕ) (H : Finset (Finset α)) : Prop :=
  ∀ M : Finset (Finset α), M ⊆ H → IsMatching M → M.card ≤ s

/-- The complete `k`-graph on `Q`, with the ambient vertices left implicit. -/
def cliqueFamily (k : ℕ) (Q : Finset α) : Finset (Finset α) :=
  Q.powersetCard k

/-- All `k`-subsets of `V` that meet the prescribed center set `S`. -/
def coverFamily (k : ℕ) (V S : Finset α) : Finset (Finset α) :=
  V.powersetCard k \ (V \ S).powersetCard k

omit [DecidableEq α] in
theorem IsMatching.mono {M N : Finset (Finset α)}
    (hN : IsMatching N) (hMN : M ⊆ N) : IsMatching M := by
  intro e he f hf hef
  exact hN (hMN he) (hMN hf) hef

omit [DecidableEq α] in
theorem IsUniform.mono {k : ℕ} {H G : Finset (Finset α)}
    (hG : IsUniform k G) (hHG : H ⊆ G) : IsUniform k H := by
  intro e he
  exact hG e (hHG he)

omit [DecidableEq α] in
@[simp]
theorem mem_cliqueFamily {k : ℕ} {Q e : Finset α} :
    e ∈ cliqueFamily k Q ↔ e ⊆ Q ∧ e.card = k := by
  exact Finset.mem_powersetCard

@[simp]
theorem mem_coverFamily {k : ℕ} {V S e : Finset α} :
    e ∈ coverFamily k V S ↔ e ⊆ V ∧ e.card = k ∧ ¬ Disjoint e S := by
  simp only [coverFamily, Finset.mem_sdiff, Finset.mem_powersetCard,
    Finset.subset_sdiff]
  constructor
  · rintro ⟨⟨hV, hk⟩, hnot⟩
    exact ⟨hV, hk, fun hd ↦ hnot ⟨⟨hV, hd⟩, hk⟩⟩
  · rintro ⟨hV, hk, hd⟩
    exact ⟨⟨hV, hk⟩, fun h ↦ hd h.1.2⟩

theorem mem_coverFamily_iff {k : ℕ} {V S e : Finset α} :
    e ∈ coverFamily k V S ↔
      e ⊆ V ∧ e.card = k ∧ ∃ v ∈ e, v ∈ S := by
  rw [mem_coverFamily, Finset.not_disjoint_iff]

omit [DecidableEq α] in
theorem cliqueFamily_uniform (k : ℕ) (Q : Finset α) :
    IsUniform k (cliqueFamily k Q) := by
  intro e he
  exact (mem_cliqueFamily.mp he).2

theorem coverFamily_uniform (k : ℕ) (V S : Finset α) :
    IsUniform k (coverFamily k V S) := by
  intro e he
  exact (mem_coverFamily.mp he).2.1

omit [DecidableEq α] in
@[simp]
theorem card_cliqueFamily (k : ℕ) (Q : Finset α) :
    (cliqueFamily k Q).card = Q.card.choose k := by
  exact Finset.card_powersetCard k Q

theorem card_coverFamily_eq (k : ℕ) (V S : Finset α) :
    (coverFamily k V S).card = V.card.choose k - (V \ S).card.choose k := by
  unfold coverFamily
  rw [Finset.card_sdiff_of_subset
    (Finset.powersetCard_mono (Finset.sdiff_subset : V \ S ⊆ V))]
  rw [Finset.card_powersetCard, Finset.card_powersetCard]

theorem card_coverFamily (k : ℕ) {V S : Finset α} (hSV : S ⊆ V) :
    (coverFamily k V S).card = V.card.choose k - (V.card - S.card).choose k := by
  rw [card_coverFamily_eq, Finset.card_sdiff_of_subset hSV]

/-- Select one center in each edge. Disjointness makes this selection injective. -/
theorem IsMatching.card_le_of_hitting_set {M : Finset (Finset α)} {S : Finset α}
    (hM : IsMatching M) (hS : ∀ e ∈ M, ∃ v ∈ e, v ∈ S) : M.card ≤ S.card := by
  classical
  let f : M → S := fun e ↦
    ⟨Classical.choose (hS e.1 e.2), (Classical.choose_spec (hS e.1 e.2)).2⟩
  have hf : ∀ e : M, (f e : α) ∈ (e : Finset α) :=
    fun e ↦ (Classical.choose_spec (hS e.1 e.2)).1
  apply Finset.card_le_card_of_injective (f := f)
  intro e e' hee'
  apply Subtype.ext
  by_contra hne
  have hdis := hM e.2 e'.2 hne
  have hv : (f e : α) = (f e' : α) := congrArg Subtype.val hee'
  have hmem : (f e : α) ∈ (e' : Finset α) := by
    rw [hv]
    exact hf e'
  exact Finset.disjoint_left.mp hdis (hf e) hmem

/-- The union of a uniform matching contains exactly `k` vertices per edge. -/
theorem IsMatching.card_biUnion {k : ℕ} {M : Finset (Finset α)}
    (hM : IsMatching M) (hu : IsUniform k M) :
    (M.biUnion id).card = k * M.card := by
  change (M.biUnion fun e ↦ e).card = k * M.card
  rw [Finset.card_biUnion hM]
  calc
    ∑ e ∈ M, (id e).card = ∑ _e ∈ M, k := by
      apply Finset.sum_congr rfl
      intro e he
      exact hu e he
    _ = k * M.card := by simp [Nat.mul_comm]

/-- A `k`-uniform matching contained in `Q` uses at most `Q.card` vertices. -/
theorem IsMatching.mul_card_le_of_subset {k : ℕ} {M : Finset (Finset α)}
    {Q : Finset α} (hM : IsMatching M) (hu : IsUniform k M)
    (hQ : ∀ e ∈ M, e ⊆ Q) : k * M.card ≤ Q.card := by
  rw [← hM.card_biUnion hu]
  apply Finset.card_le_card
  exact Finset.biUnion_subset.mpr hQ

theorem coverFamily_matchingNumberAtMost (k : ℕ) (V S : Finset α) :
    MatchingNumberAtMost S.card (coverFamily k V S) := by
  intro M hsub hM
  apply hM.card_le_of_hitting_set
  intro e he
  exact (mem_coverFamily_iff.mp (hsub he)).2.2

theorem cliqueFamily_matchingNumberAtMost {k s : ℕ} {Q : Finset α}
    (hQ : Q.card < k * (s + 1)) :
    MatchingNumberAtMost s (cliqueFamily k Q) := by
  intro M hsub hM
  have hcard : k * M.card ≤ Q.card :=
    hM.mul_card_le_of_subset ((cliqueFamily_uniform k Q).mono hsub)
      (fun e he ↦ (mem_cliqueFamily.mp (hsub he)).1)
  by_contra hnot
  have hs : s + 1 ≤ M.card := Nat.succ_le_of_lt (lt_of_not_ge hnot)
  exact (not_lt_of_ge (Nat.mul_le_mul_left k hs)) (lt_of_le_of_lt hcard hQ)

theorem standardClique_matchingNumberAtMost {k s : ℕ} {Q : Finset α}
    (hk : 0 < k) (hQ : Q.card = k * (s + 1) - 1) :
    MatchingNumberAtMost s (cliqueFamily k Q) := by
  apply cliqueFamily_matchingNumberAtMost
  rw [hQ]
  exact Nat.sub_lt (Nat.mul_pos hk (Nat.succ_pos s)) Nat.zero_lt_one

end SharpTailMatching.Matching
