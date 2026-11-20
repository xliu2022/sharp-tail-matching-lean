/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A bounded-size initial coloring and the repeated-cluster edge estimate.
The estimate survives every refinement used in weak regularity.
-/
module

public import SharpTailMatching.Matching.HypergraphTuples
public import SharpTailMatching.Matching.Sparse

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I] [Fintype α]

omit [DecidableEq α] in
theorem exists_initial_coloring {t : ℕ} (ht : 0 < t) :
    ∃ c : α → Fin t, ∀ i, (labelFiber c i).card ≤ Fintype.card α / t + 1 := by
  classical
  let n := Fintype.card α
  let m := n / t + 1
  have hm : 0 < m := Nat.zero_lt_succ _
  let e := Fintype.equivFin α
  have hbound : n < t * m := Nat.lt_mul_div_succ n ht
  let c (v : α) : Fin t := ⟨(e v).val / m, (Nat.div_lt_iff_lt_mul hm).mpr (by
    have hv := (e v).isLt
    dsimp only [n] at hbound
    omega)⟩
  refine ⟨c, ?_⟩
  intro i
  let f (v : α) : Fin m := ⟨(e v).val % m, Nat.mod_lt _ hm⟩
  have hcard : (labelFiber c i).card ≤ (Finset.univ : Finset (Fin m)).card := by
    apply Finset.card_le_card_of_injOn f (fun _ _ ↦ Finset.mem_univ _)
    intro v hv w hw hmod
    have hc : c v = c w := (Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm
    have hquot : (e v).val / m = (e w).val / m := congrArg Fin.val hc
    have hrem : (e v).val % m = (e w).val % m := congrArg Fin.val hmod
    have hvsplit := Nat.div_add_mod (e v).val m
    have hwsplit := Nat.div_add_mod (e w).val m
    rw [hquot, hrem] at hvsplit
    apply e.injective
    apply Fin.ext
    omega
  simpa only [Finset.card_univ, Fintype.card_fin, m, n] using hcard

noncomputable def noncrossingFamily (c : α → I) (H : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact H.filter fun e ↦ ¬IsCrossing c e

theorem noncrossing_edges_bound {k m : ℕ} {c : α → I} {H : Finset (Finset α)}
    (hu : IsUniform k H) (hparts : ∀ i, (labelFiber c i).card ≤ m) :
    (noncrossingFamily c H).card ≤ Fintype.card α * m * Fintype.card α ^ (k - 2) := by
  classical
  let P : Finset (α × α) := Finset.univ.filter fun p ↦ p.1 ≠ p.2 ∧ c p.1 = c p.2
  have hPcard : P.card ≤ m * Fintype.card α := by
    have h := Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) (s := P)
      (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _) m
    apply h
    intro v _
    have hcell : (P.filter fun p ↦ p.1 = v).card ≤ (labelFiber c (c v)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        obtain ⟨hpP, hpv⟩ := Finset.mem_filter.mp hp
        have hcolor := (Finset.mem_filter.mp hpP).2.2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor.symm.trans (congrArg c hpv)⟩
      · intro p hp q hq heq
        exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) heq
    exact hcell.trans (hparts (c v))
  let A := fun p : α × α ↦ H.filter fun e ↦ p.1 ∈ e ∧ p.2 ∈ e
  have hsub : noncrossingFamily c H ⊆ P.biUnion A := by
    intro e he
    obtain ⟨heH, hnot⟩ := Finset.mem_filter.mp he
    obtain ⟨v, hv⟩ := not_forall.mp hnot
    obtain ⟨hve, hnot'⟩ := not_imp.mp hv
    obtain ⟨w, hw⟩ := not_forall.mp hnot'
    obtain ⟨hwe, hnot''⟩ := not_imp.mp hw
    obtain ⟨hcolor, hne⟩ := not_imp.mp hnot''
    exact Finset.mem_biUnion.mpr ⟨(v, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hcolor⟩,
      Finset.mem_filter.mpr ⟨heH, hve, hwe⟩⟩
  have hcodegree : ∀ p ∈ P, (A p).card ≤ Fintype.card α ^ (k - 2) := by
    intro p hp
    have h := codegree_le_choose (V := Finset.univ) (fun e _ ↦ Finset.subset_univ e) hu
      (Finset.mem_univ p.1) (Finset.mem_univ p.2) (Finset.mem_filter.mp hp).2.1
    have hchoose : (Fintype.card α - 2).choose (k - 2) ≤ Fintype.card α ^ (k - 2) :=
      (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
    have h' : (A p).card ≤ (Fintype.card α - 2).choose (k - 2) := by
      simpa only [Finset.card_univ] using h
    exact h'.trans hchoose
  calc
    (noncrossingFamily c H).card ≤ (P.biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (A p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, Fintype.card α ^ (k - 2) := Finset.sum_le_sum hcodegree
    _ = P.card * Fintype.card α ^ (k - 2) := by simp
    _ ≤ (m * Fintype.card α) * Fintype.card α ^ (k - 2) := Nat.mul_le_mul_right _ hPcard
    _ = Fintype.card α * m * Fintype.card α ^ (k - 2) := by ring

omit [DecidableEq α] [DecidableEq I] [Fintype α] in
theorem noncrossing_mono_refinement {J : Type*} {c : α → I} {c' : α → J} (g : J → I)
    (hrefine : ∀ v, g (c' v) = c v) (H : Finset (Finset α)) :
    (noncrossingFamily c' H).card ≤ (noncrossingFamily c H).card := by
  classical
  apply Finset.card_le_card
  intro e he
  obtain ⟨heH, hnot⟩ := Finset.mem_filter.mp he
  refine Finset.mem_filter.mpr ⟨heH, ?_⟩
  intro hcross
  apply hnot
  intro v hv w hw hcolor
  apply hcross hv hw
  rw [← hrefine v, ← hrefine w, hcolor]

theorem exists_initial_coloring_noncrossing_bound {k t : ℕ} {H : Finset (Finset α)}
    (hk : 2 ≤ k) (ht : 0 < t) (htn : t ≤ Fintype.card α) (hu : IsUniform k H) :
    ∃ c : α → Fin t,
      t * (noncrossingFamily c H).card ≤ 2 * Fintype.card α ^ k := by
  obtain ⟨c, hc⟩ := exists_initial_coloring (α := α) ht
  refine ⟨c, ?_⟩
  have hcount := noncrossing_edges_bound hu hc
  have hmt : (Fintype.card α / t + 1) * t ≤ 2 * Fintype.card α := by
    have hdiv := Nat.div_mul_le_self (Fintype.card α) t
    nlinarith only [hdiv, htn]
  have hpow : Fintype.card α ^ k = Fintype.card α ^ 2 * Fintype.card α ^ (k - 2) := by
    rw [← pow_add, show 2 + (k - 2) = k by omega]
  calc
    t * (noncrossingFamily c H).card ≤
        t * (Fintype.card α * (Fintype.card α / t + 1) * Fintype.card α ^ (k - 2)) :=
      Nat.mul_le_mul_left t hcount
    _ = ((Fintype.card α / t + 1) * t) * (Fintype.card α * Fintype.card α ^ (k - 2)) := by ring
    _ ≤ (2 * Fintype.card α) * (Fintype.card α * Fintype.card α ^ (k - 2)) :=
      Nat.mul_le_mul_right _ hmt
    _ = 2 * Fintype.card α ^ k := by rw [hpow]; ring

end SharpTailMatching.Matching
