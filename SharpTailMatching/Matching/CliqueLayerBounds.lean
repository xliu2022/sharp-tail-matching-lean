/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Discharge the block-family inputs of the clique sampling inequalities using
only the explicit vertex capacity conditions.
-/
module

public import SharpTailMatching.Matching.CliqueTests
public import SharpTailMatching.Matching.DisjointBlocks
public import Mathlib.Data.Nat.Choose.Vandermonde

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

theorem sum_range_split_two {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k + 1), f j) = f 0 + f 1 + ∑ j ∈ Finset.Icc 2 k, f j := by
  have h₀ : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have h₁ : 1 ∈ (Finset.range (k + 1)).erase 0 :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  have hrest : ((Finset.range (k + 1)).erase 0).erase 1 = Finset.Icc 2 k := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  have hs₀ := (Finset.range (k + 1)).sum_erase_add f h₀
  have hs₁ := ((Finset.range (k + 1)).erase 0).sum_erase_add f h₁
  rw [hrest] at hs₁
  linarith only [hs₀, hs₁]

theorem vandermonde_split_two {k : ℕ} (hk : 1 ≤ k) (u d : ℕ) :
    ((u + d).choose k : ℝ) = (u.choose k : ℝ) + (d : ℝ) * u.choose (k - 1) +
      ∑ j ∈ Finset.Icc 2 k, (d.choose j : ℝ) * u.choose (k - j) := by
  have hnat : (∑ j ∈ Finset.range (k + 1), d.choose j * u.choose (k - j)) =
      (u + d).choose k := by
    simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Nat.add_comm d u] using
      (Nat.add_choose_eq d u k).symm
  have hreal : (∑ j ∈ Finset.range (k + 1), (d.choose j : ℝ) * u.choose (k - j)) =
      ((u + d).choose k : ℝ) := by exact_mod_cast hnat
  rw [sum_range_split_two hk] at hreal
  simpa only [Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero, Nat.cast_one, one_mul] using
    hreal.symm

noncomputable def cliqueLayerWeight (k u N j : ℕ) : ℝ :=
  ((N.choose j : ℝ) / (N / j : ℕ)) * u.choose (k - j)

noncomputable def cliqueWeightSum (k u N : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 2 k, cliqueLayerWeight k u N j

theorem cliqueWeightSum_nonneg (k u N : ℕ) : 0 ≤ cliqueWeightSum k u N := by
  apply Finset.sum_nonneg
  intro j _
  unfold cliqueLayerWeight
  positivity

variable {A W : Type*} [DecidableEq A] [DecidableEq W] [Fintype A] [Fintype W]

theorem exists_clique_block_samples (L : Type*) [Fintype L] {k j : ℕ}
    (hinside : (k - 1) * Fintype.card W + (k - j) * Fintype.card L ≤ Fintype.card A)
    (houtside : j * Fintype.card L ≤ Fintype.card W) :
    ∃ B : W → Set.powersetCard A (k - 1),
    ∃ C : L → Set.powersetCard A (k - j),
    ∃ D : L → Set.powersetCard W j,
      (∀ i i', i ≠ i' → Disjoint (B i : Finset A) (B i' : Finset A)) ∧
      (∀ l l', l ≠ l' → Disjoint (C l : Finset A) (C l' : Finset A)) ∧
      (∀ l l', l ≠ l' → Disjoint (D l : Finset W) (D l' : Finset W)) ∧
      ∀ i l, Disjoint (B i : Finset A) (C l : Finset A) := by
  obtain ⟨B, C, hB, hC, hBdis, hCdis, hBC⟩ := exists_two_disjoint_block_collections W L
    (k - 1) (k - j) (Finset.univ : Finset A) (by simpa using hinside)
  obtain ⟨D, hD, hDdis⟩ := exists_disjoint_indexed_blocks L j (Finset.univ : Finset W)
    (by simpa using houtside)
  exact ⟨fun i ↦ ⟨B i, (hB i).2⟩, fun l ↦ ⟨C l, (hC l).2⟩,
    fun l ↦ ⟨D l, (hD l).2⟩, hBdis, hCdis, hDdis, hBC⟩

section Group

variable [AddGroup W]

theorem singleton_layer_bound_of_capacity {k s : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hcapacity : (k - 1) * Fintype.card W ≤ Fintype.card A) :
    (edgeLayer 1 H).card ≤ (k * (s + 1) - 1 - Fintype.card A) *
      (Fintype.card A).choose (k - 1) := by
  obtain ⟨B, hB, hBdis⟩ := exists_disjoint_indexed_blocks W (k - 1) (Finset.univ : Finset A)
    (by simpa using hcapacity)
  exact singleton_layer_bound hk hu hν hQ (fun i ↦ ⟨B i, (hB i).2⟩) hBdis

/-- The manuscript's multiple-outside edge bound with `b = floor(N/j)`, now
under actual matching and clique hypotheses and the required vertex capacity. -/
theorem multiple_layer_bound_of_capacity {k s j : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hj : 0 < j) (hjN : j ≤ Fintype.card W)
    (hcapacity : (k - 1) * Fintype.card W +
      (k - j) * (Fintype.card W / j) ≤ Fintype.card A) :
    ((edgeLayer j H).card : ℝ) ≤
      ((k * (s + 1) - 1 - Fintype.card A).choose j : ℝ) * (Fintype.card A).choose (k - j) +
      (((Fintype.card W).choose j : ℝ) / (Fintype.card W / j : ℕ)) *
        (Fintype.card A).choose (k - j) *
        ((k * (s + 1) - 1 - Fintype.card A : ℕ) -
          ((edgeLayer 1 H).card : ℝ) / (Fintype.card A).choose (k - 1)) := by
  have hb : 0 < Fintype.card W / j := Nat.div_pos hjN hj
  have : NeZero (Fintype.card W / j) := ⟨Nat.ne_of_gt hb⟩
  obtain ⟨B, C, D, hB, hC, hD, hBC⟩ := exists_clique_block_samples
    (Fin (Fintype.card W / j)) (by simpa only [Fintype.card_fin] using hcapacity)
    (by simpa only [Fintype.card_fin, Nat.mul_comm] using Nat.div_mul_le_self (Fintype.card W) j)
  simpa only [Fintype.card_fin] using multiple_layer_bound hk hu hν hQ B C D hB hC hD hBC

/-- Exact finite clique bound from the explicitly stated numerical weight
condition. The structural equality step and the eventual numerical estimate
are separate subsequent results. -/
theorem clique_bound_and_singleton_equality_of_weight {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 2 ≤ k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hN : k ≤ Fintype.card W)
    (hpack : ∀ j ∈ Finset.Icc 2 k, (k - 1) * Fintype.card W +
      (k - j) * (Fintype.card W / j) ≤ Fintype.card A)
    (hweight : cliqueWeightSum k (Fintype.card A) (Fintype.card W) <
      (Fintype.card A).choose (k - 1)) :
    H.card ≤ (Fintype.card A + (k * (s + 1) - 1 - Fintype.card A)).choose k ∧
      (H.card = (Fintype.card A + (k * (s + 1) - 1 - Fintype.card A)).choose k →
        (edgeLayer 1 H).card = (k * (s + 1) - 1 - Fintype.card A) *
          (Fintype.card A).choose (k - 1)) := by
  let u := Fintype.card A
  let N := Fintype.card W
  let d := k * (s + 1) - 1 - u
  let C : ℝ := u.choose (k - 1)
  let δ : ℝ := (d : ℝ) - (edgeLayer 1 H).card / C
  have hC : 0 < C := (cliqueWeightSum_nonneg k u N).trans_lt hweight
  have hcapacity : (k - 1) * Fintype.card W ≤ Fintype.card A := by
    have hp := hpack 2 (Finset.mem_Icc.mpr ⟨by omega, hk⟩)
    omega
  have hsingle := singleton_layer_bound_of_capacity (by omega) hu hν hQ hcapacity
  have hsingle' : ((edgeLayer 1 H).card : ℝ) ≤ (d : ℝ) * C := by
    dsimp only [d, C, u]
    exact_mod_cast hsingle
  have hδ : 0 ≤ δ := sub_nonneg.mpr ((div_le_iff₀ hC).mpr hsingle')
  have hδeq : ((edgeLayer 1 H).card : ℝ) + δ * C = (d : ℝ) * C := by
    dsimp only [δ]
    rw [sub_mul, div_mul_cancel₀ _ hC.ne']
    ring
  have hHsum : (H.card : ℝ) = (u.choose k : ℝ) + (edgeLayer 1 H).card +
      ∑ j ∈ Finset.Icc 2 k, ((edgeLayer j H).card : ℝ) := by
    have hsum : (∑ j ∈ Finset.range (k + 1), ((edgeLayer j H).card : ℝ)) = H.card := by
      exact_mod_cast sum_edgeLayer_cards hu
    rw [sum_range_split_two (by omega), card_edgeLayer_zero hu hQ] at hsum
    exact hsum.symm
  have hlayers : (∑ j ∈ Finset.Icc 2 k, ((edgeLayer j H).card : ℝ)) ≤
      (∑ j ∈ Finset.Icc 2 k, (d.choose j : ℝ) * u.choose (k - j)) +
        cliqueWeightSum k u N * δ := by
    have hpoint : ∀ j ∈ Finset.Icc 2 k, ((edgeLayer j H).card : ℝ) ≤
        (d.choose j : ℝ) * u.choose (k - j) + cliqueLayerWeight k u N j * δ := by
      intro j hj
      obtain ⟨hjlow, hjhigh⟩ := Finset.mem_Icc.mp hj
      exact multiple_layer_bound_of_capacity (by omega) hu hν hQ (by omega)
        (hjhigh.trans hN) (hpack j hj)
    have hsum := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, cliqueWeightSum] using hsum
  have hV := vandermonde_split_two (by omega : 1 ≤ k) u d
  have hdeficit : (H.card : ℝ) ≤ ((u + d).choose k : ℝ) - (C - cliqueWeightSum k u N) * δ := by
    change ((u + d).choose k : ℝ) = (u.choose k : ℝ) + (d : ℝ) * C + _ at hV
    linarith only [hHsum, hlayers, hδeq, hV]
  have hgap : 0 < C - cliqueWeightSum k u N := sub_pos.mpr hweight
  have hbound : H.card ≤ (u + d).choose k := by
    have hreal := hdeficit.trans (sub_le_self _ (mul_nonneg hgap.le hδ))
    exact_mod_cast hreal
  refine ⟨hbound, ?_⟩
  intro heq
  have heq' : (H.card : ℝ) = ((u + d).choose k : ℝ) := by exact_mod_cast heq
  have hδzero : δ = 0 := by nlinarith only [hdeficit, heq', hgap, hδ]
  rw [hδzero, zero_mul, add_zero] at hδeq
  dsimp only [C, d, u] at hδeq
  exact_mod_cast hδeq

end Group

end SharpTailMatching.Matching
