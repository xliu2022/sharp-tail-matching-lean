/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Structural equality in the local clique argument. Any two inside blocks can
be completed by the same other blocks, so extremal matrix rigidity avoids a
separate connectivity argument by one-vertex changes.
-/
module

public import SharpTailMatching.Matching.CliqueLayerBounds

@[expose] public section

namespace SharpTailMatching.Matching

variable {A W : Type*} [DecidableEq A] [DecidableEq W] [Fintype A] [Fintype W]

def outsideLink (H : Finset (Finset (A ⊕ W))) (C : Finset A) : Finset W :=
  Finset.univ.filter fun v ↦ C.disjSum {v} ∈ H

section Group

variable [AddGroup W]

theorem outsideLinks_eq_of_singleton_equality {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (heq : (edgeLayer 1 H).card = (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1))
    (hd : 0 < k * (s + 1) - 1 - Fintype.card A)
    (hdN : k * (s + 1) - 1 - Fintype.card A < Fintype.card W)
    (hcapacity : (k - 1) * (Fintype.card W + 1) ≤ Fintype.card A)
    (C D : Set.powersetCard A (k - 1)) : outsideLink H C = outsideLink H D := by
  obtain ⟨B, B', hBc, hB'c, hsame, hB, hB'⟩ := exists_common_block_completion C D (0 : W) hcapacity
  have hE := sampledGraph_rows_or_columns_of_singleton_eq hk hu hν hQ heq B hB (1 : Equiv.Perm A)
  have hF := sampledGraph_rows_or_columns_of_singleton_eq hk hu hν hQ heq B' hB' (1 : Equiv.Perm A)
  have hsame' : ∀ i j, j ≠ (0 : W) →
      ((i, j) ∈ sampledGraph H B (1 : Equiv.Perm A) ↔
        (i, j) ∈ sampledGraph H B' (1 : Equiv.Perm A)) := by
    intro i j hj
    simp only [sampledGraph, Finset.mem_filter, Finset.mem_univ, true_and, one_smul, hsame j hj]
  have hcol := rows_columns_column_rigidity hE hF hd hdN (0 : W) hsame'
  ext i
  simpa only [outsideLink, sampledGraph, Finset.mem_filter, Finset.mem_univ, true_and,
    one_smul, hBc, hB'c] using hcol i

theorem exists_common_outside_link_of_singleton_equality {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (heq : (edgeLayer 1 H).card = (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1))
    (hd : 0 < k * (s + 1) - 1 - Fintype.card A)
    (hdN : k * (s + 1) - 1 - Fintype.card A < Fintype.card W)
    (hcapacity : (k - 1) * (Fintype.card W + 1) ≤ Fintype.card A) :
    ∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
      ∀ C : Set.powersetCard A (k - 1), outsideLink H C = T := by
  have hcap : (k - 1) * Fintype.card W ≤ Fintype.card A :=
    (Nat.mul_le_mul_left (k - 1) (Nat.le_succ (Fintype.card W))).trans hcapacity
  obtain ⟨B₀, hB₀, hBdis⟩ := exists_disjoint_indexed_blocks W (k - 1) (Finset.univ : Finset A)
    (by simpa using hcap)
  let B (i : W) : Set.powersetCard A (k - 1) := ⟨B₀ i, (hB₀ i).2⟩
  let T := outsideLink H (B 0)
  have hlinks : ∀ C : Set.powersetCard A (k - 1), outsideLink H C = T := by
    intro C
    exact outsideLinks_eq_of_singleton_equality hk hu hν hQ heq hd hdN hcapacity C (B 0)
  have hshape : sampledGraph H B (1 : Equiv.Perm A) = T ×ˢ Finset.univ := by
    ext p
    have h := Finset.ext_iff.mp (hlinks (B p.2)) p.1
    simpa only [outsideLink, sampledGraph, Finset.mem_filter, Finset.mem_univ,
      true_and, one_smul, Finset.mem_product, and_true] using h
  have hcard := sampledGraph_card_eq_of_singleton_eq hk hu hν hQ heq B hBdis (1 : Equiv.Perm A)
  rw [hshape, Finset.card_product, Finset.card_univ] at hcard
  refine ⟨T, ?_, hlinks⟩
  have hN : 0 < Fintype.card W := Fintype.card_pos
  nlinarith only [hcard, hN]

end Group

omit [Fintype W] in
/-- Complete singleton links already force every edge to use only the same
outside vertices, provided there is room to complete those singleton links
away from one prescribed edge. -/
theorem edge_toRight_subset_of_complete_links {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))} {T : Finset W}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hT : T.card = k * (s + 1) - 1 - Fintype.card A)
    (hlinks : ∀ C : Set.powersetCard A (k - 1), ∀ v ∈ T,
      (C : Finset A).disjSum {v} ∈ H)
    (hcapacity : (k - 1) * (T.card + 1) ≤ Fintype.card A) :
    ∀ e ∈ H, e.toRight ⊆ T := by
  classical
  intro e he w hw
  by_contra hwT
  have hright : 0 < e.toRight.card := Finset.card_pos.mpr ⟨w, hw⟩
  have hsplit := e.card_toLeft_add_card_toRight
  have hecard := hu e he
  have hleft : e.toLeft.card ≤ k - 1 := by omega
  let G := T \ e.toRight
  have hG : Fintype.card ↥G ≤ T.card := by
    simpa only [Fintype.card_coe, G] using
      (Finset.card_le_card (Finset.sdiff_subset : T \ e.toRight ⊆ T))
  have hcap : (k - 1) * Fintype.card ↥G ≤
      ((Finset.univ : Finset A) \ e.toLeft).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hmul := Nat.mul_le_mul_left (k - 1) hG
    have hsum : (k - 1) * Fintype.card ↥G + e.toLeft.card ≤ Fintype.card A := by
      nlinarith only [hmul, hleft, hcapacity]
    omega
  obtain ⟨B, hB, hBdis⟩ := exists_disjoint_indexed_blocks ↥G (k - 1)
    ((Finset.univ : Finset A) \ e.toLeft) hcap
  let E (v : G) : Finset (A ⊕ W) := (B v).disjSum {v.val}
  let M := Finset.univ.image E
  have hMH : M ⊆ H := by
    intro f hf
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    exact hlinks ⟨B v, (hB v).2⟩ v (Finset.mem_sdiff.mp v.property).1
  have hM : IsMatching M := by
    intro f hf f' hf' hff'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp hf'
    have hvv' : v ≠ v' := fun h ↦ hff' (h ▸ rfl)
    apply disjSum_disjoint (hBdis v v' hvv')
    simpa only [Finset.disjoint_singleton] using
      (show v.val ≠ v'.val from fun h ↦ hvv' (Subtype.ext h))
  have hcross : ∀ f ∈ M, Disjoint e f := by
    intro f hf
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hf
    apply Finset.disjoint_left.mpr
    intro x hxe hxE
    cases x with
    | inl a =>
      have haB : a ∈ B v := by simpa only [E, Finset.inl_mem_disjSum] using hxE
      have hae : a ∈ e.toLeft := by simpa using hxe
      exact (Finset.mem_sdiff.mp ((hB v).1 haB)).2 hae
    | inr a =>
      have hav : a = v.val := by simpa only [E, Finset.inr_mem_disjSum,
        Finset.mem_singleton] using hxE
      subst a
      exact (Finset.mem_sdiff.mp v.property).2 (by simpa using hxe)
  have houtside : (insert w T).map Function.Embedding.inr ⊆
      ((insert e M).biUnion id) \
        ((Finset.univ : Finset A).map Function.Embedding.inl) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    refine Finset.mem_sdiff.mpr ⟨?_, by simp⟩
    by_cases hve : v ∈ e.toRight
    · exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_insert_self _ _, by simpa using hve⟩
    · have hvT : v ∈ T := by
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact (hve hw).elim
        · exact hv
      let v' : G := ⟨v, Finset.mem_sdiff.mpr ⟨hvT, hve⟩⟩
      refine Finset.mem_biUnion.mpr ⟨E v', Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨v', Finset.mem_univ _, rfl⟩), ?_⟩
      simp [E, v']
  have hupper := matching_outside_clique_le hk hu hν hQ
    (Finset.insert_subset he hMH) (hM.insert hcross)
  have hlower := Finset.card_le_card houtside
  rw [Finset.card_map, Finset.card_insert_of_notMem hwT, hT] at hlower
  simp only [Finset.card_map, Finset.card_univ] at hupper
  omega

section Group

variable [AddGroup W]

/-- Full finite clique bound and equality classification, with the numerical
weight and packing estimates stated explicitly. These estimates are discharged
from the manuscript's asymptotic range in the numerical layer. -/
theorem clique_bound_and_equality_of_weight {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 2 ≤ k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hN : k ≤ Fintype.card W)
    (hd : 0 < k * (s + 1) - 1 - Fintype.card A)
    (hdN : k * (s + 1) - 1 - Fintype.card A < Fintype.card W)
    (hcapacity : (k - 1) * (Fintype.card W + 1) ≤ Fintype.card A)
    (hpack : ∀ j ∈ Finset.Icc 2 k, (k - 1) * Fintype.card W +
      (k - j) * (Fintype.card W / j) ≤ Fintype.card A)
    (hweight : cliqueWeightSum k (Fintype.card A) (Fintype.card W) <
      (Fintype.card A).choose (k - 1)) :
    H.card ≤ (Fintype.card A + (k * (s + 1) - 1 - Fintype.card A)).choose k ∧
      (H.card = (Fintype.card A + (k * (s + 1) - 1 - Fintype.card A)).choose k ↔
        ∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
          H = cliqueFamily k ((Finset.univ : Finset A).disjSum T)) := by
  obtain ⟨hbound, heqSingle⟩ := clique_bound_and_singleton_equality_of_weight hk hu hν hQ hN
    hpack hweight
  refine ⟨hbound, ?_⟩
  constructor
  · intro heq
    obtain ⟨T, hT, hlinks⟩ := exists_common_outside_link_of_singleton_equality (by omega)
      hu hν hQ (heqSingle heq) hd hdN hcapacity
    have hcomplete : ∀ C : Set.powersetCard A (k - 1), ∀ v ∈ T,
        (C : Finset A).disjSum {v} ∈ H := by
      intro C v hv
      rw [← hlinks C] at hv
      exact (Finset.mem_filter.mp hv).2
    have hcapT : (k - 1) * (T.card + 1) ≤ Fintype.card A := by
      rw [hT]
      exact (Nat.mul_le_mul_left (k - 1) (by omega :
        k * (s + 1) - 1 - Fintype.card A + 1 ≤ Fintype.card W + 1)).trans hcapacity
    have hsupport := edge_toRight_subset_of_complete_links (by omega) hu hν hQ hT hcomplete hcapT
    have hsub : H ⊆ cliqueFamily k ((Finset.univ : Finset A).disjSum T) := by
      intro e he
      apply mem_cliqueFamily.mpr ⟨?_, hu e he⟩
      intro x hx
      cases x with
      | inl a => simp
      | inr w => exact Finset.inr_mem_disjSum.mpr (hsupport e he (by simpa using hx))
    refine ⟨T, hT, Finset.eq_of_subset_of_card_le hsub ?_⟩
    rw [card_cliqueFamily, Finset.card_disjSum, Finset.card_univ, hT, heq]
  · rintro ⟨T, hT, rfl⟩
    rw [card_cliqueFamily, Finset.card_disjSum, Finset.card_univ, hT]

end Group

end SharpTailMatching.Matching
