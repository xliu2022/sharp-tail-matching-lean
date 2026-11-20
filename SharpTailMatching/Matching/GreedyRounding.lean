/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Realize a prescribed multiset of reduced edges inside robust crossing cells.
The proof keeps the exact number of used vertices in each cluster and hence
does not assume an unproved hypergraph matching or rounding theorem.
-/
module

public import SharpTailMatching.Matching.HypergraphTuples
public import SharpTailMatching.Matching.Sparse
public import SharpTailMatching.Matching.CapacityZero

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I] [Fintype α]

def clusterLoad (P : Multiset (Finset I)) (i : I) : ℕ := (P.filter fun e ↦ i ∈ e).card

theorem clusterLoad_cons (e : Finset I) (P : Multiset (Finset I)) (i : I) :
    clusterLoad (e ::ₘ P) i = clusterLoad P i + if i ∈ e then 1 else 0 := by
  by_cases hi : i ∈ e <;> simp [clusterLoad, hi]

theorem card_inter_labelFiber (c : α → I) (E : Finset α) (i : I) :
    (E ∩ labelFiber c i).card = (E.filter fun v ↦ c v = i).card := by
  congr 1
  ext v
  simp only [Finset.mem_inter, labelFiber, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A finite integer plan can be realized if every required cell remains
nonempty whenever the available cluster portions have relative size `ε`. -/
theorem realize_robust_plan {k : ℕ} {c : α → I} {H : Finset (Finset α)}
    (hk : 0 < k) (hu : IsUniform k H) (ε : ℝ) (P : Multiset (Finset I))
    (hrobust : ∀ e ∈ P, ∀ U : Finset α,
      (∀ i ∈ e, ε * (labelFiber c i).card ≤ (U ∩ labelFiber c i).card) →
      ∃ E ∈ H, E ⊆ U ∧ IsCrossing c E ∧ E.image c = e)
    (hloads : ∀ i, (clusterLoad P i : ℝ) ≤ (1 - ε) * (labelFiber c i).card) :
    ∃ M : Finset (Finset α), M ⊆ H ∧ IsMatching M ∧ M.card = P.card ∧
      ∀ i, ((M.biUnion id) ∩ labelFiber c i).card = clusterLoad P i := by
  revert hrobust hloads
  induction P using Multiset.induction_on with
  | empty =>
    intro _ _
    exact ⟨∅, Finset.empty_subset _, by simp [IsMatching, Set.Pairwise], by simp, by simp [clusterLoad]⟩
  | @cons e P ih =>
    intro hrobust hloads
    have hloadsP : ∀ i, (clusterLoad P i : ℝ) ≤ (1 - ε) * (labelFiber c i).card := by
      intro i
      have h := hloads i
      rw [clusterLoad_cons, Nat.cast_add] at h
      have hnonneg : (0 : ℝ) ≤ (if i ∈ e then 1 else 0 : ℕ) := Nat.cast_nonneg _
      linarith only [h, hnonneg]
    obtain ⟨M, hMH, hM, hMcard, hused⟩ := ih
      (fun f hf ↦ hrobust f (Multiset.mem_cons_of_mem hf)) hloadsP
    let Vused := M.biUnion id
    let U := Finset.univ \ Vused
    have hsize : ∀ i ∈ e, ε * (labelFiber c i).card ≤ (U ∩ labelFiber c i).card := by
      intro i _
      have hset : U ∩ labelFiber c i = labelFiber c i \ Vused := by
        ext v
        simp only [U, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        tauto
      have hsubset : Vused ∩ labelFiber c i ⊆ labelFiber c i := Finset.inter_subset_right
      have hcardle := Finset.card_le_card hsubset
      have hcard : ((U ∩ labelFiber c i).card : ℝ) =
          (labelFiber c i).card - (clusterLoad P i : ℝ) := by
        rw [hset, Finset.card_sdiff, Nat.cast_sub hcardle, hused]
      rw [hcard]
      have h := hloadsP i
      linarith only [h]
    obtain ⟨E, hEH, hEU, hcross, hEimage⟩ := hrobust e (Multiset.mem_cons_self _ _) U hsize
    have hEused : Disjoint E Vused := by
      apply Finset.disjoint_left.mpr
      intro v hvE hvused
      exact (Finset.mem_sdiff.mp (hEU hvE)).2 hvused
    have hEM : E ∉ M := by
      intro hEM
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hu E hEH]; exact hk)
      exact Finset.disjoint_left.mp hEused hv (Finset.mem_biUnion.mpr ⟨E, hEM, hv⟩)
    have hdisjoint : ∀ F ∈ M, Disjoint E F := by
      intro F hFM
      exact hEused.mono_right (Finset.subset_biUnion_of_mem id hFM)
    refine ⟨insert E M, Finset.insert_subset hEH hMH, hM.insert hdisjoint, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hEM, hMcard, Multiset.card_cons]
    · intro i
      have hinter : Disjoint (E ∩ labelFiber c i) (Vused ∩ labelFiber c i) :=
        hEused.mono Finset.inter_subset_left Finset.inter_subset_left
      have hEcount : (E ∩ labelFiber c i).card = if i ∈ e then 1 else 0 := by
        rw [card_inter_labelFiber, crossing_filter_card hcross, hEimage]
      rw [Finset.biUnion_insert, id_eq, Finset.union_inter_distrib_right,
        Finset.card_union_of_disjoint hinter, hEcount, hused, clusterLoad_cons]
      omega

end SharpTailMatching.Matching
