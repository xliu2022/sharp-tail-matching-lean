/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Construct disjoint indexed blocks from explicit vertex capacities.
-/
module

public import SharpTailMatching.Matching.Clique
public import Mathlib.Data.Set.PowersetCard

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

/-- The zero-size case is included: many indexed empty blocks are allowed. -/
theorem exists_disjoint_indexed_blocks (I : Type*) [Fintype I] (q : ℕ) (Q : Finset α)
    (hsize : q * Fintype.card I ≤ Q.card) :
    ∃ B : I → Finset α, (∀ i, B i ⊆ Q ∧ (B i).card = q) ∧
      ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
  classical
  by_cases hq : q = 0
  · subst q
    exact ⟨fun _ ↦ ∅, by simp, by simp⟩
  obtain ⟨M, hMQ, hM, hMcard⟩ := exists_matching_in_clique (Nat.pos_of_ne_zero hq) hsize
  let e : I ≃ M := Fintype.equivOfCardEq (by simpa using hMcard.symm)
  refine ⟨fun i ↦ (e i).val, ?_, ?_⟩
  · intro i
    exact mem_cliqueFamily.mp (hMQ (e i).property)
  · intro i j hij
    apply hM (e i).property (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))

/-- Simultaneously pack two indexed collections, ensuring all cross pairs of
blocks are disjoint. -/
theorem exists_two_disjoint_block_collections (I J : Type*) [Fintype I] [Fintype J]
    (r t : ℕ) (Q : Finset α) (hsize : r * Fintype.card I + t * Fintype.card J ≤ Q.card) :
    ∃ B : I → Finset α, ∃ C : J → Finset α,
      (∀ i, B i ⊆ Q ∧ (B i).card = r) ∧
      (∀ j, C j ⊆ Q ∧ (C j).card = t) ∧
      (∀ i i', i ≠ i' → Disjoint (B i) (B i')) ∧
      (∀ j j', j ≠ j' → Disjoint (C j) (C j')) ∧
      ∀ i j, Disjoint (B i) (C j) := by
  classical
  obtain ⟨B, hB, hBdis⟩ := exists_disjoint_indexed_blocks I r Q (by omega)
  let U := Finset.univ.biUnion B
  have hUQ : U ⊆ Q := Finset.biUnion_subset.mpr (fun i _ ↦ (hB i).1)
  have hUcard : U.card = r * Fintype.card I := by
    have hpair : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint B := fun i _ j _ hij ↦ hBdis i j hij
    change (Finset.univ.biUnion B).card = r * Fintype.card I
    rw [Finset.card_biUnion hpair]
    have hcards : ∀ i, (B i).card = r := fun i ↦ (hB i).2
    simp only [hcards, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hleft : t * Fintype.card J ≤ (Q \ U).card := by
    rw [Finset.card_sdiff_of_subset hUQ, hUcard]
    omega
  obtain ⟨C, hC, hCdis⟩ := exists_disjoint_indexed_blocks J t (Q \ U) hleft
  refine ⟨B, C, hB, fun j ↦ ⟨(hC j).1.trans Finset.sdiff_subset, (hC j).2⟩,
    hBdis, hCdis, ?_⟩
  intro i j
  apply Finset.disjoint_left.mpr
  intro v hvB hvC
  exact (Finset.mem_sdiff.mp ((hC j).1 hvC)).2
    (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvB⟩)

/-- Complete a prescribed collection of disjoint blocks without changing any
of its blocks. -/
theorem exists_clique_matching_extending {r t : ℕ} {Q : Finset α}
    {M : Finset (Finset α)} (hr : 0 < r) (hMQ : M ⊆ cliqueFamily r Q)
    (hM : IsMatching M) (hMt : M.card ≤ t) (hsize : r * t ≤ Q.card) :
    ∃ N : Finset (Finset α), M ⊆ N ∧ N ⊆ cliqueFamily r Q ∧ IsMatching N ∧ N.card = t := by
  let U := M.biUnion id
  have hUQ : U ⊆ Q := Finset.biUnion_subset.mpr
    (fun e he ↦ (mem_cliqueFamily.mp (hMQ he)).1)
  have hUcard : U.card = r * M.card :=
    hM.card_biUnion ((cliqueFamily_uniform r Q).mono hMQ)
  have hcapacity : r * (t - M.card) ≤ (Q \ U).card := by
    rw [Finset.card_sdiff_of_subset hUQ, hUcard]
    rw [Nat.mul_sub_left_distrib]
    exact Nat.sub_le_sub_right hsize (r * M.card)
  obtain ⟨P, hPQ, hP, hPcard⟩ := exists_matching_in_clique hr hcapacity
  have hPQ' : P ⊆ cliqueFamily r Q := by
    intro e he
    obtain ⟨hesub, hecard⟩ := mem_cliqueFamily.mp (hPQ he)
    exact mem_cliqueFamily.mpr ⟨hesub.trans Finset.sdiff_subset, hecard⟩
  have hcross : ∀ e ∈ M, ∀ f ∈ P, Disjoint e f := by
    intro e he f hf
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    exact (Finset.mem_sdiff.mp ((mem_cliqueFamily.mp (hPQ hf)).1 hvf)).2
      (Finset.mem_biUnion.mpr ⟨e, he, hve⟩)
  have hMP : Disjoint M P := by
    apply Finset.disjoint_left.mpr
    intro e heM heP
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [(mem_cliqueFamily.mp (hMQ heM)).2]; exact hr)
    exact Finset.disjoint_left.mp (hcross e heM e heP) hv hv
  refine ⟨M ∪ P, Finset.subset_union_left, Finset.union_subset hMQ hPQ', hM.union hP hcross, ?_⟩
  rw [Finset.card_union_of_disjoint hMP, hPcard]
  omega

/-- Extend a prescribed matching to an indexed block collection of a specified
cardinality, retaining every prescribed block in the range. -/
theorem exists_indexed_blocks_containing_matching (I : Type*) [Fintype I]
    {r : ℕ} {Q : Finset α} {M : Finset (Finset α)}
    (hr : 0 < r) (hMQ : M ⊆ cliqueFamily r Q) (hM : IsMatching M)
    (hMI : M.card ≤ Fintype.card I) (hsize : r * Fintype.card I ≤ Q.card) :
    ∃ B : I → Finset α, (∀ i, B i ⊆ Q ∧ (B i).card = r) ∧
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
      ∀ e ∈ M, ∃ i, B i = e := by
  classical
  obtain ⟨N, hMN, hNQ, hN, hNcard⟩ := exists_clique_matching_extending hr hMQ hM hMI hsize
  let e : I ≃ N := Fintype.equivOfCardEq (by simpa using hNcard.symm)
  refine ⟨fun i ↦ (e i).val, fun i ↦ mem_cliqueFamily.mp (hNQ (e i).property), ?_, ?_⟩
  · intro i j hij
    apply hN (e i).property (e j).property
    intro heq
    exact hij (e.injective (Subtype.ext heq))
  · intro A hA
    refine ⟨e.symm ⟨A, hMN hA⟩, ?_⟩
    simp only [Equiv.apply_symm_apply]

/-- Complete any two equal-size blocks by the same other indexed blocks.
The blocks being compared need not be disjoint. -/
theorem exists_common_block_completion {A W : Type*} [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W] {r : ℕ} (C D : Set.powersetCard A r) (c : W)
    (hsize : r * (Fintype.card W + 1) ≤ Fintype.card A) :
    ∃ B B' : W → Set.powersetCard A r,
      B c = C ∧ B' c = D ∧ (∀ i, i ≠ c → B i = B' i) ∧
      (∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A)) ∧
      ∀ i j, i ≠ j → Disjoint (B' i : Finset A) (B' j : Finset A) := by
  classical
  let J := ↥((Finset.univ : Finset W).erase c)
  let U : Finset A := (C : Finset A) ∪ (D : Finset A)
  let Q : Finset A := Finset.univ \ U
  have hJ : Fintype.card J = Fintype.card W - 1 := by
    simp only [J, Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]
  have hU : U.card ≤ 2 * r := by
    have h := Finset.card_union_le (C : Finset A) (D : Finset A)
    simpa only [U, Set.powersetCard.card_eq, two_mul] using h
  have hUle : U.card ≤ Fintype.card A := Finset.card_le_univ U
  have hN : 1 ≤ Fintype.card W := by
    have : Nonempty W := ⟨c⟩
    exact Fintype.card_pos
  have hcapacity : r * Fintype.card J ≤ Q.card := by
    have hsub := Nat.sub_add_cancel hN
    have hsub' := Nat.sub_add_cancel hUle
    simp only [Q, Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, hJ]
    nlinarith
  obtain ⟨E, hE, hEdis⟩ := exists_disjoint_indexed_blocks J r Q hcapacity
  let make (X : Set.powersetCard A r) (i : W) : Set.powersetCard A r :=
    if hi : i = c then X else
      ⟨E ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩,
        (hE ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩).2⟩
  have hXE : ∀ (X : Set.powersetCard A r), (X : Finset A) ⊆ U →
      ∀ t : J, Disjoint (X : Finset A) (E t) := by
    intro X hX t
    apply Finset.disjoint_left.mpr
    intro a haX haE
    exact (Finset.mem_sdiff.mp ((hE t).1 haE)).2 (hX haX)
  have hmake : ∀ X : Set.powersetCard A r, (X : Finset A) ⊆ U →
      ∀ i j, i ≠ j → Disjoint (make X i : Finset A) (make X j : Finset A) := by
    intro X hX i j hij
    by_cases hic : i = c
    · subst i
      have hjc : j ≠ c := hij.symm
      simp only [make, dite_eq_left rfl, dite_eq_right hjc]
      exact hXE X hX _
    · by_cases hjc : j = c
      · subst j
        simp only [make, dite_eq_left rfl, dite_eq_right hic]
        exact (hXE X hX _).symm
      · simp only [make, dite_eq_right hic, dite_eq_right hjc]
        apply hEdis
        intro heq
        exact hij (congrArg Subtype.val heq)
  refine ⟨make C, make D, by simp [make], by simp [make], ?_,
    hmake C Finset.subset_union_left, hmake D Finset.subset_union_right⟩
  intro i hic
  simp only [make, dite_eq_right hic]

end SharpTailMatching.Matching
