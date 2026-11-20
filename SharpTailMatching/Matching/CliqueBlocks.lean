/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Counting hyperedges by their number of outside vertices, and exact marginal
probabilities for independently permuted inside/outside blocks.
-/
module

public import SharpTailMatching.Matching.CliqueSampling
public import Mathlib.Data.Finset.Sum

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {A W : Type*} [DecidableEq A] [DecidableEq W]

def edgeLayer (j : ℕ) (H : Finset (Finset (A ⊕ W))) : Finset (Finset (A ⊕ W)) :=
  H.filter fun e ↦ e.toRight.card = j

omit [DecidableEq A] [DecidableEq W] in
theorem sum_edgeLayer_cards {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H) : ∑ j ∈ Finset.range (k + 1), (edgeLayer j H).card = H.card := by
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro e he
  apply Finset.mem_range.mpr
  have hle := e.card_toRight_le
  rw [hu e he] at hle
  change e.toRight.card < k + 1
  omega

section Finite

variable [Fintype A] [Fintype W]

theorem combination_pairs_card_eq_layer {k j : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H) :
    (Finset.univ.filter (fun p : Set.powersetCard A (k - j) × Set.powersetCard W j ↦
      (p.1 : Finset A).disjSum (p.2 : Finset W) ∈ H)).card = (edgeLayer j H).card := by
  apply Finset.card_bij (fun p _ ↦ (p.1 : Finset A).disjSum (p.2 : Finset W))
  · intro p hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, ?_⟩
    simp
  · intro p _ q _ hpq
    apply Prod.ext
    · apply Subtype.ext
      simpa only [Finset.toLeft_disjSum] using congrArg Finset.toLeft hpq
    · apply Subtype.ext
      simpa only [Finset.toRight_disjSum] using congrArg Finset.toRight hpq
  · intro e he
    obtain ⟨heH, heR⟩ := Finset.mem_filter.mp he
    have heL : e.toLeft.card = k - j := by
      have hsum := e.card_toLeft_add_card_toRight
      rw [hu e heH, heR] at hsum
      omega
    let p : Set.powersetCard A (k - j) × Set.powersetCard W j :=
      (⟨e.toLeft, heL⟩, ⟨e.toRight, heR⟩)
    refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [p, Finset.toLeft_disjSum_toRight] using heH
    · exact Finset.toLeft_disjSum_toRight

/-- Each tested pair of independently permuted blocks has the exact layer
density, irrespective of any dependencies between other sampled blocks. -/
theorem average_tested_block {k j : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H) (C : Set.powersetCard A (k - j))
    (D : Set.powersetCard W j) :
    finiteAverage (fun p : Equiv.Perm A × Equiv.Perm W ↦
      if (((p.1 • C : Set.powersetCard A (k - j)) : Finset A).disjSum
        ((p.2 • D : Set.powersetCard W j) : Finset W)) ∈ H then (1 : ℝ) else 0) =
      ((edgeLayer j H).card : ℝ) /
        (((Fintype.card A).choose (k - j) : ℝ) * ((Fintype.card W).choose j : ℝ)) := by
  classical
  have := Set.powersetCard.isPretransitive (α := A) (n := k - j)
  have := Set.powersetCard.isPretransitive (α := W) (n := j)
  have havg := finiteAverage_two_transitive_actions
    (G := Equiv.Perm A) (K := Equiv.Perm W)
    (fun (C : Set.powersetCard A (k - j)) (D : Set.powersetCard W j) ↦
      if (C : Finset A).disjSum (D : Finset W) ∈ H then (1 : ℝ) else 0) C D
  refine havg.trans ?_
  rw [finiteAverage_indicator, combination_pairs_card_eq_layer hu]
  have hA : Fintype.card (Set.powersetCard A (k - j)) = (Fintype.card A).choose (k - j) := by
    simpa only [Nat.card_eq_fintype_card] using (Set.powersetCard.card A (k - j))
  have hW : Fintype.card (Set.powersetCard W j) = (Fintype.card W).choose j := by
    simpa only [Nat.card_eq_fintype_card] using (Set.powersetCard.card W j)
  simp only [Fintype.card_prod, hA, hW, Nat.cast_mul]

omit [DecidableEq A] [DecidableEq W] [Fintype W] in
theorem edgeLayer_zero_eq_clique {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H) :
    edgeLayer 0 H = cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) := by
  ext e
  constructor
  · intro he
    obtain ⟨heH, heR⟩ := Finset.mem_filter.mp he
    apply mem_cliqueFamily.mpr
    refine ⟨Finset.subset_map_inl.mpr ⟨Finset.subset_univ _, ?_⟩, hu e heH⟩
    exact Finset.card_eq_zero.mp heR
  · intro he
    refine Finset.mem_filter.mpr ⟨hQ he, ?_⟩
    have hright := (Finset.subset_map_inl.mp (mem_cliqueFamily.mp he).1).2
    simp only [hright, Finset.card_empty]

omit [DecidableEq A] [DecidableEq W] [Fintype W] in
theorem card_edgeLayer_zero {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H) :
    (edgeLayer 0 H).card = (Fintype.card A).choose k := by
  rw [edgeLayer_zero_eq_clique hu hQ, card_cliqueFamily]
  simp

theorem singleton_pairs_card_eq_layer {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H) :
    (Finset.univ.filter (fun p : W × Set.powersetCard A (k - 1) ↦
      (p.2 : Finset A).disjSum {p.1} ∈ H)).card = (edgeLayer 1 H).card := by
  apply Finset.card_bij (fun p _ ↦ (p.2 : Finset A).disjSum {p.1})
  · intro p hp
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2, by simp⟩
  · intro p _ q _ hpq
    apply Prod.ext
    · have h := congrArg Finset.toRight hpq
      simpa only [Finset.toRight_disjSum, Finset.singleton_inj] using h
    · apply Subtype.ext
      simpa only [Finset.toLeft_disjSum] using congrArg Finset.toLeft hpq
  · intro e he
    obtain ⟨heH, heR⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hev⟩ := Finset.card_eq_one.mp heR
    have heL : e.toLeft.card = k - 1 := by
      have hsum := e.card_toLeft_add_card_toRight
      rw [hu e heH, heR] at hsum
      omega
    let p : W × Set.powersetCard A (k - 1) := (v, ⟨e.toLeft, heL⟩)
    have heq : (p.2 : Finset A).disjSum {p.1} = e := by
      change e.toLeft.disjSum {v} = e
      rw [← hev]
      exact Finset.toLeft_disjSum_toRight
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm ▸ heH⟩, heq⟩

/-- The bipartite graph formed by singleton outside vertices and one sampled
collection of inside blocks. -/
def sampledGraph {k : ℕ} (H : Finset (Finset (A ⊕ W)))
    (B : W → Set.powersetCard A (k - 1)) (π : Equiv.Perm A) : Finset (W × W) :=
  Finset.univ.filter fun p ↦
    (((π • B p.2 : Set.powersetCard A (k - 1)) : Finset A).disjSum {p.1}) ∈ H

theorem average_sampledGraph_card {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hu : IsUniform k H) (B : W → Set.powersetCard A (k - 1)) :
    finiteAverage (fun π : Equiv.Perm A ↦ ((sampledGraph H B π).card : ℝ)) =
      (Fintype.card W : ℝ) * (edgeLayer 1 H).card / (Fintype.card A).choose (k - 1) := by
  classical
  have := Set.powersetCard.isPretransitive (α := A) (n := k - 1)
  let f (v : W) (C : Set.powersetCard A (k - 1)) : ℝ :=
    if (C : Finset A).disjSum {v} ∈ H then 1 else 0
  have hcard : ∀ π : Equiv.Perm A, ((sampledGraph H B π).card : ℝ) =
      ∑ v : W, ∑ w : W, f v (π • B w) := by
    intro π
    calc
      ((sampledGraph H B π).card : ℝ) = ∑ p : W × W, f p.1 (π • B p.2) := by
        simp only [f, Finset.sum_boole, sampledGraph]
      _ = ∑ v : W, ∑ w : W, f v (π • B w) :=
        Fintype.sum_prod_type (fun p : W × W ↦ f p.1 (π • B p.2))
  have htotal : (∑ v : W, ∑ C : Set.powersetCard A (k - 1), f v C) =
      ((edgeLayer 1 H).card : ℝ) := by
    calc
      (∑ v : W, ∑ C : Set.powersetCard A (k - 1), f v C) =
          ∑ p : W × Set.powersetCard A (k - 1), f p.1 p.2 :=
        (Fintype.sum_prod_type (fun p : W × Set.powersetCard A (k - 1) ↦ f p.1 p.2)).symm
      _ = ((edgeLayer 1 H).card : ℝ) := by
        simp only [f, Finset.sum_boole, singleton_pairs_card_eq_layer hu]
  have hcomb : Fintype.card (Set.powersetCard A (k - 1)) = (Fintype.card A).choose (k - 1) := by
    simpa only [Nat.card_eq_fintype_card] using (Set.powersetCard.card A (k - 1))
  calc
    finiteAverage (fun π : Equiv.Perm A ↦ ((sampledGraph H B π).card : ℝ)) =
        finiteAverage (fun π : Equiv.Perm A ↦ ∑ v : W, ∑ w : W, f v (π • B w)) :=
      finiteAverage_congr hcard
    _ = ∑ v : W, ∑ w : W, finiteAverage (fun π : Equiv.Perm A ↦ f v (π • B w)) := by
      simp_rw [finiteAverage_sum]
    _ = ∑ v : W, ∑ _w : W, finiteAverage (f v) := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      exact finiteAverage_transitive_action (f v) (B w)
    _ = (Fintype.card W : ℝ) * (∑ v : W, finiteAverage (f v)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    _ = (Fintype.card W : ℝ) * (edgeLayer 1 H).card / (Fintype.card A).choose (k - 1) := by
      simp only [finiteAverage, ← Finset.sum_div, htotal, hcomb]
      ring

omit [Fintype A] in
theorem permuted_subset_val_eq_map {r : ℕ} (π : Equiv.Perm A) (C : Set.powersetCard A r) :
    ((π • C : Set.powersetCard A r) : Finset A) = (C : Finset A).map π.toEmbedding := by
  simp only [Set.powersetCard.coe_smul, Finset.smul_finset_def,
    Equiv.Perm.smul_def, Finset.map_eq_image, Equiv.coe_toEmbedding]

theorem sampledGraph_matchingNumberAtMost {k s : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A))
    (π : Equiv.Perm A) :
    BipartiteMatchingNumberAtMost (k * (s + 1) - 1 - Fintype.card A) (sampledGraph H B π) := by
  let blocks (j : W) : Finset (A ⊕ W) :=
    (((π • B j : Set.powersetCard A (k - 1)) : Finset A).map Function.Embedding.inl)
  have hblocks : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j) := by
    intro i j hij
    apply (Finset.disjoint_map Function.Embedding.inl).mpr
    rw [permuted_subset_val_eq_map, permuted_subset_val_eq_map]
    exact (Finset.disjoint_map π.toEmbedding).mpr (hB i j hij)
  have hedge (p : W × W) : singletonLinkEdge (Sum.inr : W → A ⊕ W) blocks p =
      (((π • B p.2 : Set.powersetCard A (k - 1)) : Finset A).disjSum {p.1}) := by
    ext x
    cases x <;> simp [singletonLinkEdge, blocks]
  have hbound := sampled_bipartite_matching_bound (E := sampledGraph H B π)
    hk hu hν hQ Sum.inr_injective
    (fun i ↦ by simp) (fun j ↦ Finset.map_subset_map.mpr (Finset.subset_univ _)) hblocks
    (fun p hp ↦ by rw [hedge]; exact (Finset.mem_filter.mp hp).2)
  simpa only [Finset.card_map, Finset.card_univ] using hbound

section Group

variable [AddGroup W]

/-- The exact singleton-outside bound `E₁ ≤ d * choose(u,k-1)`. -/
theorem singleton_layer_bound {k s : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A)) :
    (edgeLayer 1 H).card ≤ (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1) := by
  let d := k * (s + 1) - 1 - Fintype.card A
  have hpoint : ∀ π : Equiv.Perm A, ((sampledGraph H B π).card : ℝ) ≤
      (Fintype.card W : ℝ) * d := by
    intro π
    exact_mod_cast bipartite_card_le (sampledGraph_matchingNumberAtMost hk hu hν hQ B hB π)
  have hmean := finiteAverage_le hpoint
  rw [average_sampledGraph_card hu B, finiteAverage_const] at hmean
  have hN : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hfrac : ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1) ≤ d :=
    (mul_le_mul_iff_right₀ hN).mp (by simpa only [mul_div_assoc] using hmean)
  have hr : k - 1 ≤ Fintype.card A := by
    simpa only [Set.powersetCard.card_eq] using Finset.card_le_univ (B 0 : Finset A)
  have hC : (0 : ℝ) < (Fintype.card A).choose (k - 1) := by
    exact_mod_cast Nat.choose_pos hr
  have hbound := (div_le_iff₀ hC).mp hfrac
  exact_mod_cast hbound

/-- Choose an actual maximum matching in every sampled graph. Its mean deficit
is bounded by the normalized singleton edge deficit, exactly as in (8.4). -/
theorem exists_sampled_matchings_with_deficit_bound {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A)) :
    ∃ M : Equiv.Perm A → Finset (W × W),
      (∀ π, M π ⊆ sampledGraph H B π ∧ IsBipartiteMatching (M π) ∧
        BipartiteMatchingNumberAtMost (M π).card (sampledGraph H B π)) ∧
      finiteAverage (fun π : Equiv.Perm A ↦
        ((k * (s + 1) - 1 - Fintype.card A - (M π).card : ℕ) : ℝ)) ≤
        (k * (s + 1) - 1 - Fintype.card A : ℕ) -
          ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1) := by
  classical
  let d := k * (s + 1) - 1 - Fintype.card A
  choose M hMsub hMmatch hMmax using
    (fun π : Equiv.Perm A ↦ exists_maximum_bipartite_matching (sampledGraph H B π))
  have hMle : ∀ π, (M π).card ≤ d := by
    intro π
    exact sampledGraph_matchingNumberAtMost hk hu hν hQ B hB π (M π) (hMsub π) (hMmatch π)
  have hpoint : ∀ π : Equiv.Perm A,
      ((d - (M π).card : ℕ) : ℝ) * Fintype.card W + ((sampledGraph H B π).card : ℝ) ≤
        (Fintype.card W : ℝ) * d := by
    intro π
    rw [Nat.cast_sub (hMle π)]
    have hE : ((sampledGraph H B π).card : ℝ) ≤ (Fintype.card W : ℝ) * (M π).card := by
      exact_mod_cast bipartite_card_le (hMmax π)
    nlinarith only [hE]
  have hmean := finiteAverage_le hpoint
  rw [finiteAverage_add, finiteAverage_mul_const, average_sampledGraph_card hu B,
    finiteAverage_const, mul_div_assoc] at hmean
  have hN : 0 < (Fintype.card W : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : finiteAverage (fun π : Equiv.Perm A ↦ ((d - (M π).card : ℕ) : ℝ)) +
      ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1) ≤ d := by
    apply (mul_le_mul_iff_right₀ hN).mp
    nlinarith only [hmean]
  refine ⟨M, fun π ↦ ⟨hMsub π, hMmatch π, hMmax π⟩, ?_⟩
  change finiteAverage (fun π : Equiv.Perm A ↦ ((d - (M π).card : ℕ) : ℝ)) ≤
    (d : ℝ) - ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1)
  linarith only [hsum]

theorem sampledGraph_card_eq_of_singleton_eq {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (heq : (edgeLayer 1 H).card = (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1))
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A))
    (π : Equiv.Perm A) :
    (sampledGraph H B π).card = Fintype.card W * (k * (s + 1) - 1 - Fintype.card A) := by
  have hpoint : ∀ π : Equiv.Perm A, ((sampledGraph H B π).card : ℝ) ≤
      (Fintype.card W : ℝ) * (k * (s + 1) - 1 - Fintype.card A : ℕ) := by
    intro π
    exact_mod_cast bipartite_card_le (sampledGraph_matchingNumberAtMost hk hu hν hQ B hB π)
  have hr : k - 1 ≤ Fintype.card A := by
    simpa only [Set.powersetCard.card_eq] using Finset.card_le_univ (B 0 : Finset A)
  have hC : (0 : ℝ) < (Fintype.card A).choose (k - 1) := by exact_mod_cast Nat.choose_pos hr
  have hmean : finiteAverage (fun π : Equiv.Perm A ↦ ((sampledGraph H B π).card : ℝ)) =
      (Fintype.card W : ℝ) * (k * (s + 1) - 1 - Fintype.card A : ℕ) := by
    rw [average_sampledGraph_card hu B, heq, Nat.cast_mul]
    field_simp
  have h := eq_const_of_finiteAverage_eq hpoint hmean π
  exact_mod_cast h

theorem sampledGraph_rows_or_columns_of_singleton_eq {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (heq : (edgeLayer 1 H).card = (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1))
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A))
    (π : Equiv.Perm A) :
    (∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
      sampledGraph H B π = T ×ˢ Finset.univ) ∨
    (∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
      sampledGraph H B π = Finset.univ ×ˢ T) := by
  exact bipartite_equality_rows_or_columns (sampledGraph_matchingNumberAtMost hk hu hν hQ B hB π)
    (sampledGraph_card_eq_of_singleton_eq hk hu hν hQ heq B hB π)

end Group

end Finite

end SharpTailMatching.Matching
