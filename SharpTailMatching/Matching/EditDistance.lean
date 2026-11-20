/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite counting tools for stability. Changing r vertices of a prescribed
cover or clique changes at most r n^(k-1) edges. A near-extremal edge count
then turns a one-sided containment estimate into symmetric difference.
-/
module

public import SharpTailMatching.Matching.ApproximateCover

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem degree_le_pow {k : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H) (v : α) :
    degree H v ≤ Fintype.card α ^ (k - 1) := by
  have h := degree_le_choose (V := Finset.univ) (fun e _ ↦ Finset.subset_univ e) hu
    (Finset.mem_univ v)
  simp only [Finset.card_univ] at h
  exact h.trans ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _))

theorem card_le_card_hitting_mul_pow {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) {S : Finset α} (hS : ∀ e ∈ H, ∃ v ∈ e, v ∈ S) :
    H.card ≤ S.card * Fintype.card α ^ (k - 1) := by
  apply (card_le_sum_degrees_of_hitting_set hS).trans
  calc
    ∑ v ∈ S, degree H v ≤ ∑ _v ∈ S, Fintype.card α ^ (k - 1) :=
      Finset.sum_le_sum fun v _ ↦ degree_le_pow hu v
    _ = S.card * Fintype.card α ^ (k - 1) := by simp

theorem coverFamily_sdiff_card_le (k : ℕ) (S T : Finset α) :
    (coverFamily k Finset.univ S \ coverFamily k Finset.univ T).card ≤
      (S \ T).card * Fintype.card α ^ (k - 1) := by
  apply card_le_card_hitting_mul_pow ((coverFamily_uniform k Finset.univ S).mono Finset.sdiff_subset)
  intro e he
  obtain ⟨heS, heT⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heV, hek, v, hve, hvS⟩ := mem_coverFamily_iff.mp heS
  refine ⟨v, hve, Finset.mem_sdiff.mpr ⟨hvS, ?_⟩⟩
  intro hvT
  exact heT (mem_coverFamily_iff.mpr ⟨heV, hek, v, hve, hvT⟩)

theorem cliqueFamily_sdiff_card_le (k : ℕ) (S T : Finset α) :
    (cliqueFamily k S \ cliqueFamily k T).card ≤
      (S \ T).card * Fintype.card α ^ (k - 1) := by
  apply card_le_card_hitting_mul_pow ((cliqueFamily_uniform k S).mono Finset.sdiff_subset)
  intro e he
  obtain ⟨heS, heT⟩ := Finset.mem_sdiff.mp he
  obtain ⟨heSub, hek⟩ := mem_cliqueFamily.mp heS
  have hn : ¬e ⊆ T := fun h ↦ heT (mem_cliqueFamily.mpr ⟨h, hek⟩)
  obtain ⟨v, hve, hvT⟩ := Finset.not_subset.mp hn
  exact ⟨v, hve, Finset.mem_sdiff.mpr ⟨heSub hve, hvT⟩⟩

theorem exists_adjusted_set (S : Finset α) {s : ℕ} (hs : s ≤ Fintype.card α) :
    ∃ T : Finset α, T.card = s ∧
      (((S \ T).card + (T \ S).card : ℕ) : ℝ) = |(S.card : ℝ) - s| := by
  by_cases h : S.card ≤ s
  · obtain ⟨T, hST, _, hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ S) h
      (by simpa only [Finset.card_univ] using hs)
    refine ⟨T, hT, ?_⟩
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hST, Finset.card_empty, zero_add,
      Finset.card_sdiff_of_subset hST, hT, Nat.cast_sub h]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · have h' : s ≤ S.card := le_of_not_ge h
    obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq h'
    refine ⟨T, hT, ?_⟩
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hTS, Finset.card_empty, add_zero,
      Finset.card_sdiff_of_subset hTS, hT, Nat.cast_sub h']
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h'))]

omit [Fintype α] in
theorem sdiff_card_le_sum (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  have hsub : A \ C ⊆ (A \ B) ∪ (B \ C) := by
    intro x hx
    obtain ⟨hxA, hxC⟩ := Finset.mem_sdiff.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxB, hxC⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxA, hxB⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

omit [Fintype α] in
theorem sdiff_real_card_identity (A B : Finset α) :
    ((B \ A).card : ℝ) = B.card - A.card + (A \ B).card := by
  have hA := Finset.card_inter_add_card_sdiff A B
  have hB := Finset.card_inter_add_card_sdiff B A
  rw [Finset.inter_comm B A] at hB
  have hA' : ((A ∩ B).card : ℝ) + (A \ B).card = A.card := by exact_mod_cast hA
  have hB' : ((A ∩ B).card : ℝ) + (B \ A).card = B.card := by exact_mod_cast hB
  linarith only [hA', hB']

omit [Fintype α] in
theorem symmetric_difference_bound_of_one_sided (A B : Finset α) {D δ E : ℝ}
    (hA : D - δ ≤ A.card) (hB : (B.card : ℝ) ≤ D) (hE : ((A \ B).card : ℝ) ≤ E) :
    ((A \ B).card : ℝ) + (B \ A).card ≤ δ + 2 * E := by
  rw [sdiff_real_card_identity A B]
  linarith only [hA, hB, hE]

end SharpTailMatching.Matching
