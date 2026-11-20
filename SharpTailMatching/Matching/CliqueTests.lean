/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Disjoint block tests and their replacement/averaging inequalities.
-/
module

public import SharpTailMatching.Matching.CliqueBlocks

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {A W : Type*} [DecidableEq A] [DecidableEq W] [Fintype A] [Fintype W]

omit [Fintype W] in
theorem disjSum_sdiff_leftGround (C : Finset A) (D : Finset W) :
    C.disjSum D \ ((Finset.univ : Finset A).map Function.Embedding.inl) =
      D.map Function.Embedding.inr := by
  ext x
  cases x <;> simp

omit [DecidableEq A] [DecidableEq W] [Fintype A] [Fintype W] in
theorem disjSum_disjoint {C C' : Finset A} {D D' : Finset W}
    (hC : Disjoint C C') (hD : Disjoint D D') : Disjoint (C.disjSum D) (C'.disjSum D') := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  cases x with
  | inl a =>
    exact Finset.disjoint_left.mp hC (by simpa using hx) (by simpa using hx')
  | inr w =>
    exact Finset.disjoint_left.mp hD (by simpa using hx) (by simpa using hx')

theorem average_contained_permuted_subset {j : ℕ} (D : Set.powersetCard W j) (T : Finset W) :
    finiteAverage (fun σ : Equiv.Perm W ↦ if (σ • D : Set.powersetCard W j).val ⊆ T then
      (1 : ℝ) else 0) = (T.card.choose j : ℝ) / (Fintype.card W).choose j := by
  have havg := finiteAverage_permuted_subset D (fun C : Finset W ↦ if C ⊆ T then (1 : ℝ) else 0)
  have hsets : ((Finset.univ : Finset W).powersetCard j).filter (fun C ↦ C ⊆ T) =
      T.powersetCard j := by
    ext C
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  simpa only [Finset.sum_boole, hsets, Finset.card_powersetCard] using havg

def sampledMatchingEdges {k : ℕ} (B : W → Set.powersetCard A (k - 1))
    (π : Equiv.Perm A) (M : Finset (W × W)) : Finset (Finset (A ⊕ W)) :=
  M.image fun p ↦ ((π • B p.2 : Set.powersetCard A (k - 1)) : Finset A).disjSum {p.1}

omit [Fintype W] in
theorem sampledMatching_outside {k : ℕ} (B : W → Set.powersetCard A (k - 1))
    (π : Equiv.Perm A) (M : Finset (W × W)) :
    ((sampledMatchingEdges B π M).biUnion id) \
        ((Finset.univ : Finset A).map Function.Embedding.inl) =
      (M.image Prod.fst).map Function.Embedding.inr := by
  ext x
  cases x with
  | inl a => simp
  | inr w => simp [sampledMatchingEdges, Finset.mem_biUnion, eq_comm]

theorem sampledMatching_properties {k : ℕ} {H : Finset (Finset (A ⊕ W))}
    (B : W → Set.powersetCard A (k - 1))
    (hB : ∀ i j, i ≠ j → Disjoint (B i : Finset A) (B j : Finset A))
    (π : Equiv.Perm A) {M : Finset (W × W)} (hME : M ⊆ sampledGraph H B π)
    (hM : IsBipartiteMatching M) :
    sampledMatchingEdges B π M ⊆ H ∧ IsMatching (sampledMatchingEdges B π M) ∧
      (M.image Prod.fst).card = M.card ∧
      ∀ e ∈ sampledMatchingEdges B π M,
        (e \ ((Finset.univ : Finset A).map Function.Embedding.inl)).card = 1 := by
  have hsub : sampledMatchingEdges B π M ⊆ H := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp (hME hp)).2
  have hmatch : IsMatching (sampledMatchingEdges B π M) := by
    intro e he f hf hef
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
    have hpq : p ≠ q := fun h ↦ hef (h ▸ rfl)
    obtain ⟨hrow, hcol⟩ := hM hp hq hpq
    apply disjSum_disjoint
    · rw [permuted_subset_val_eq_map, permuted_subset_val_eq_map]
      exact (Finset.disjoint_map π.toEmbedding).mpr (hB p.2 q.2 hcol)
    · simpa using hrow
  have hcard : (M.image Prod.fst).card = M.card := by
    apply Finset.card_image_of_injOn
    intro p hp q hq heq
    by_contra hne
    exact (hM hp hq hne).1 heq
  refine ⟨hsub, hmatch, hcard, ?_⟩
  intro e he
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  rw [disjSum_sdiff_leftGround, Finset.card_map, Finset.card_singleton]

theorem disjoint_block_tests_bound {L : Type*} [Fintype L] {k s j : ℕ}
    {H : Finset (Finset (A ⊕ W))} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (C : L → Set.powersetCard A (k - j)) (D : L → Set.powersetCard W j)
    (hB : ∀ i i', i ≠ i' → Disjoint (B i : Finset A) (B i' : Finset A))
    (hC : ∀ l l', l ≠ l' → Disjoint (C l : Finset A) (C l' : Finset A))
    (hD : ∀ l l', l ≠ l' → Disjoint (D l : Finset W) (D l' : Finset W))
    (hBC : ∀ i l, Disjoint (B i : Finset A) (C l : Finset A))
    (π : Equiv.Perm A) (σ : Equiv.Perm W) {M : Finset (W × W)}
    (hME : M ⊆ sampledGraph H B π) (hM : IsBipartiteMatching M) :
    (Finset.univ.filter fun l ↦
      (((π • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
        ((σ • D l : Set.powersetCard W j) : Finset W)) ∈ H).card ≤
      (Finset.univ.filter fun l ↦ ((σ • D l : Set.powersetCard W j) : Finset W) ⊆
        M.image Prod.fst).card + (k * (s + 1) - 1 - Fintype.card A - M.card) := by
  classical
  let Q : Finset (A ⊕ W) := (Finset.univ : Finset A).map Function.Embedding.inl
  let N := sampledMatchingEdges B π M
  let F (l : L) : Finset (A ⊕ W) :=
    ((π • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
      ((σ • D l : Set.powersetCard W j) : Finset W)
  obtain ⟨hNH, hN, hcard, hsingle⟩ := sampledMatching_properties B hB π hME hM
  have hF : ∀ l l', l ≠ l' → Disjoint (F l) (F l') := by
    intro l l' hll'
    apply disjSum_disjoint
    · rw [permuted_subset_val_eq_map, permuted_subset_val_eq_map]
      exact (Finset.disjoint_map π.toEmbedding).mpr (hC l l' hll')
    · rw [permuted_subset_val_eq_map, permuted_subset_val_eq_map]
      exact (Finset.disjoint_map σ.toEmbedding).mpr (hD l l' hll')
  have hinside : ∀ l, Disjoint ((N.biUnion id) ∩ Q) (F l ∩ Q) := by
    intro l
    apply Finset.disjoint_left.mpr
    intro x hxN hxF
    obtain ⟨hxU, hxQ⟩ := Finset.mem_inter.mp hxN
    cases x with
    | inr w => simp [Q] at hxQ
    | inl a =>
      obtain ⟨e, heN, hae⟩ := Finset.mem_biUnion.mp hxU
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp heN
      have haB : a ∈ ((π • B p.2 : Set.powersetCard A (k - 1)) : Finset A) := by simpa using hae
      have haC : a ∈ ((π • C l : Set.powersetCard A (k - j)) : Finset A) := by
        simpa [F] using (Finset.mem_inter.mp hxF).1
      have hd : Disjoint ((π • B p.2 : Set.powersetCard A (k - 1)) : Finset A)
          ((π • C l : Set.powersetCard A (k - j)) : Finset A) := by
        rw [permuted_subset_val_eq_map, permuted_subset_val_eq_map]
        exact (Finset.disjoint_map π.toEmbedding).mpr (hBC p.2 l)
      exact Finset.disjoint_left.mp hd haB haC
  have htest := successful_tests_le_contained_add_deficit hk hu hν hQ hNH hN hsingle F hF hinside
  simpa only [F, N, Q, disjSum_sdiff_leftGround, sampledMatching_outside,
    Finset.map_subset_map, Finset.card_map, Finset.card_univ, hcard] using htest

theorem average_successful_tests_card {L : Type*} [Fintype L] {k j : ℕ}
    {H : Finset (Finset (A ⊕ W))} (hu : IsUniform k H)
    (C : L → Set.powersetCard A (k - j)) (D : L → Set.powersetCard W j) :
    finiteAverage (fun p : Equiv.Perm A × Equiv.Perm W ↦
      ((Finset.univ.filter fun l ↦
        (((p.1 • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
          ((p.2 • D l : Set.powersetCard W j) : Finset W)) ∈ H).card : ℝ)) =
      (Fintype.card L : ℝ) * (edgeLayer j H).card /
        (((Fintype.card A).choose (k - j) : ℝ) * ((Fintype.card W).choose j : ℝ)) := by
  classical
  have hcard : ∀ p : Equiv.Perm A × Equiv.Perm W,
      ((Finset.univ.filter fun l ↦
        (((p.1 • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
          ((p.2 • D l : Set.powersetCard W j) : Finset W)) ∈ H).card : ℝ) =
        ∑ l : L, if (((p.1 • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
          ((p.2 • D l : Set.powersetCard W j) : Finset W)) ∈ H then (1 : ℝ) else 0 := by
    intro p
    simp only [Finset.sum_boole]
  rw [finiteAverage_congr hcard, finiteAverage_sum]
  simp only [average_tested_block hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_div_assoc]

theorem average_contained_tests_card {L : Type*} [Fintype L] {j : ℕ}
    (D : L → Set.powersetCard W j) (T : Finset W) :
    finiteAverage (fun σ : Equiv.Perm W ↦
      ((Finset.univ.filter fun l ↦ ((σ • D l : Set.powersetCard W j) : Finset W) ⊆ T).card : ℝ)) =
      (Fintype.card L : ℝ) * T.card.choose j / (Fintype.card W).choose j := by
  classical
  have hcard : ∀ σ : Equiv.Perm W,
      ((Finset.univ.filter fun l ↦ ((σ • D l : Set.powersetCard W j) : Finset W) ⊆ T).card : ℝ) =
      ∑ l : L, if ((σ • D l : Set.powersetCard W j) : Finset W) ⊆ T then (1 : ℝ) else 0 := by
    intro σ
    simp only [Finset.sum_boole]
  rw [finiteAverage_congr hcard, finiteAverage_sum]
  simp only [average_contained_permuted_subset, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_div_assoc]

section Group

variable [AddGroup W]

/-- The averaged block-test inequality in the local clique proof, before
clearing its positive combinatorial denominators. -/
theorem multiple_layer_normalized_bound {L : Type*} [Fintype L] {k s j : ℕ}
    {H : Finset (Finset (A ⊕ W))} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (C : L → Set.powersetCard A (k - j)) (D : L → Set.powersetCard W j)
    (hB : ∀ i i', i ≠ i' → Disjoint (B i : Finset A) (B i' : Finset A))
    (hC : ∀ l l', l ≠ l' → Disjoint (C l : Finset A) (C l' : Finset A))
    (hD : ∀ l l', l ≠ l' → Disjoint (D l : Finset W) (D l' : Finset W))
    (hBC : ∀ i l, Disjoint (B i : Finset A) (C l : Finset A)) :
    (Fintype.card L : ℝ) * (edgeLayer j H).card /
        (((Fintype.card A).choose (k - j) : ℝ) * ((Fintype.card W).choose j : ℝ)) ≤
      (Fintype.card L : ℝ) * (k * (s + 1) - 1 - Fintype.card A).choose j /
        (Fintype.card W).choose j +
      ((k * (s + 1) - 1 - Fintype.card A : ℕ) -
        ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1)) := by
  classical
  let d := k * (s + 1) - 1 - Fintype.card A
  obtain ⟨M, hM, hdefect⟩ := exists_sampled_matchings_with_deficit_bound hk hu hν hQ B hB
  let T (π : Equiv.Perm A) := (M π).image Prod.fst
  let defect (π : Equiv.Perm A) : ℝ := ((d - (M π).card : ℕ) : ℝ)
  have hT : ∀ π : Equiv.Perm A, (T π).card ≤ d := by
    intro π
    have hcard := (sampledMatching_properties B hB π (hM π).1 (hM π).2.1).2.2.1
    change ((M π).image Prod.fst).card ≤ d
    rw [hcard]
    exact sampledGraph_matchingNumberAtMost hk hu hν hQ B hB π (M π) (hM π).1 (hM π).2.1
  let contained (π : Equiv.Perm A) (σ : Equiv.Perm W) : ℝ :=
    ((Finset.univ.filter fun l ↦ ((σ • D l : Set.powersetCard W j) : Finset W) ⊆ T π).card : ℝ)
  have hcontained : finiteAverage (fun p : Equiv.Perm A × Equiv.Perm W ↦ contained p.1 p.2) ≤
      (Fintype.card L : ℝ) * d.choose j / (Fintype.card W).choose j := by
    rw [finiteAverage_product]
    calc
      finiteAverage (fun π : Equiv.Perm A ↦ finiteAverage (contained π)) ≤
          finiteAverage (fun _π : Equiv.Perm A ↦
            (Fintype.card L : ℝ) * d.choose j / (Fintype.card W).choose j) := by
        apply finiteAverage_le
        intro π
        change finiteAverage (fun σ : Equiv.Perm W ↦
          ((Finset.univ.filter fun l ↦ ((σ • D l : Set.powersetCard W j) : Finset W) ⊆ T π).card : ℝ)) ≤ _
        rw [average_contained_tests_card]
        have hchoose : ((T π).card.choose j : ℝ) ≤ d.choose j := by
          exact_mod_cast Nat.choose_le_choose j (hT π)
        gcongr
      _ = (Fintype.card L : ℝ) * d.choose j / (Fintype.card W).choose j := finiteAverage_const _
  have hdefect' : finiteAverage (fun p : Equiv.Perm A × Equiv.Perm W ↦ defect p.1) =
      finiteAverage defect := by
    rw [finiteAverage_product]
    apply finiteAverage_congr
    intro π
    exact finiteAverage_const (defect π)
  have hpoint : ∀ p : Equiv.Perm A × Equiv.Perm W,
      ((Finset.univ.filter fun l ↦
        (((p.1 • C l : Set.powersetCard A (k - j)) : Finset A).disjSum
          ((p.2 • D l : Set.powersetCard W j) : Finset W)) ∈ H).card : ℝ) ≤
        contained p.1 p.2 + defect p.1 := by
    intro p
    dsimp only [contained, defect, T, d]
    exact_mod_cast disjoint_block_tests_bound hk hu hν hQ B C D hB hC hD hBC p.1 p.2
      (hM p.1).1 (hM p.1).2.1
  have havg := finiteAverage_le hpoint
  rw [average_successful_tests_card hu C D, finiteAverage_add, hdefect'] at havg
  change finiteAverage defect ≤ (d : ℝ) -
    ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1) at hdefect
  change (Fintype.card L : ℝ) * (edgeLayer j H).card /
        (((Fintype.card A).choose (k - j) : ℝ) * ((Fintype.card W).choose j : ℝ)) ≤
      (Fintype.card L : ℝ) * d.choose j / (Fintype.card W).choose j +
        ((d : ℝ) - ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1))
  linarith only [havg, hcontained, hdefect]

/-- The exact layer inequality (8.5), with the number of tested blocks kept as
a parameter. The subsequent packing step chooses this number as `floor(N/j)`. -/
theorem multiple_layer_bound {L : Type*} [Fintype L] [Nonempty L] {k s j : ℕ}
    {H : Finset (Finset (A ⊕ W))} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (B : W → Set.powersetCard A (k - 1))
    (C : L → Set.powersetCard A (k - j)) (D : L → Set.powersetCard W j)
    (hB : ∀ i i', i ≠ i' → Disjoint (B i : Finset A) (B i' : Finset A))
    (hC : ∀ l l', l ≠ l' → Disjoint (C l : Finset A) (C l' : Finset A))
    (hD : ∀ l l', l ≠ l' → Disjoint (D l : Finset W) (D l' : Finset W))
    (hBC : ∀ i l, Disjoint (B i : Finset A) (C l : Finset A)) :
    ((edgeLayer j H).card : ℝ) ≤
      ((k * (s + 1) - 1 - Fintype.card A).choose j : ℝ) * (Fintype.card A).choose (k - j) +
      (((Fintype.card W).choose j : ℝ) / Fintype.card L) * (Fintype.card A).choose (k - j) *
        ((k * (s + 1) - 1 - Fintype.card A : ℕ) -
          ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1)) := by
  classical
  have hnormal := multiple_layer_normalized_bound hk hu hν hQ B C D hB hC hD hBC
  let l : L := Classical.choice inferInstance
  have hc : (0 : ℝ) < (Fintype.card A).choose (k - j) := by
    apply Nat.cast_pos.mpr
    apply Nat.choose_pos
    simpa only [Set.powersetCard.card_eq] using Finset.card_le_univ (C l : Finset A)
  have hw : (0 : ℝ) < (Fintype.card W).choose j := by
    apply Nat.cast_pos.mpr
    apply Nat.choose_pos
    simpa only [Set.powersetCard.card_eq] using Finset.card_le_univ (D l : Finset W)
  have hb : 0 < (Fintype.card L : ℝ) := by exact_mod_cast Fintype.card_pos
  generalize hδ : ((k * (s + 1) - 1 - Fintype.card A : ℕ) : ℝ) -
    ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1) = δ at hnormal ⊢
  have hclear : (Fintype.card L : ℝ) * (edgeLayer j H).card ≤
      (Fintype.card L : ℝ) * (k * (s + 1) - 1 - Fintype.card A).choose j *
        (Fintype.card A).choose (k - j) +
      δ * (Fintype.card A).choose (k - j) * (Fintype.card W).choose j := by
    have h := (div_le_iff₀ (mul_pos hc hw)).mp hnormal
    calc
      (Fintype.card L : ℝ) * (edgeLayer j H).card ≤
          ((Fintype.card L : ℝ) * (k * (s + 1) - 1 - Fintype.card A).choose j /
              (Fintype.card W).choose j + δ) *
            ((Fintype.card A).choose (k - j) * (Fintype.card W).choose j) := h
      _ = _ := by field_simp
  apply (mul_le_mul_iff_right₀ hb).mp
  calc
    (Fintype.card L : ℝ) * (edgeLayer j H).card ≤
        (Fintype.card L : ℝ) * (k * (s + 1) - 1 - Fintype.card A).choose j *
          (Fintype.card A).choose (k - j) +
        δ * (Fintype.card A).choose (k - j) * (Fintype.card W).choose j := hclear
    _ = _ := by field_simp

end Group

end SharpTailMatching.Matching
