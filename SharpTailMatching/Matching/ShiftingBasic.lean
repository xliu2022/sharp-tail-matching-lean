/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Elementary vertex shifts preserve uniformity, size, and the actual matching
bound. A matching containing a new edge is pulled back by the global vertex
transposition, which performs both possible edge repairs simultaneously.
-/
module

public import SharpTailMatching.Matching.Relabel
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

def shiftFamily (i j : α) (H : Finset (Finset α)) : Finset (Finset α) :=
  UV.compression {i} {j} H

@[simp] theorem card_shiftFamily (i j : α) (H : Finset (Finset α)) :
    (shiftFamily i j H).card = H.card := UV.card_compression _ _ _

theorem IsUniform.shiftFamily {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) (i j : α) : IsUniform k (shiftFamily i j H) := by
  exact Set.Sized.uvCompression (by simp) hu

theorem map_swap_of_mem_of_notMem {i j : α} {e : Finset α} (hi : i ∈ e) (hj : j ∉ e) :
    e.map (Equiv.swap i j).toEmbedding = (e ∪ {j}) \ {i} := by
  apply Finset.coe_injective
  simpa only [Finset.coe_map, Equiv.coe_toEmbedding, Finset.coe_sdiff, Finset.coe_union,
    Finset.coe_singleton, Set.union_singleton] using
    Equiv.image_swap_of_mem_of_notMem (s := (e : Set α)) hi hj

theorem map_swap_of_notMem_of_notMem {i j : α} {e : Finset α} (hi : i ∉ e) (hj : j ∉ e) :
    e.map (Equiv.swap i j).toEmbedding = e := by
  ext x
  rw [Finset.mem_map_equiv]
  by_cases hxi : x = i
  · subst x
    simp [hi, hj]
  by_cases hxj : x = j
  · subst x
    simp [hi, hj]
  simp [Equiv.swap_apply_of_ne_of_ne hxi hxj]

/-- A genuinely new shifted edge contains the receiving vertex and avoids the
donating vertex; reversing that exchange gives an original edge. -/
theorem new_shift_edge {i j : α} {H : Finset (Finset α)} {e : Finset α}
    (he : e ∈ shiftFamily i j H) (heH : e ∉ H) :
    i ∈ e ∧ j ∉ e ∧ e.map (Equiv.swap i j).toEmbedding ∈ H := by
  have hi : i ∈ e := Finset.singleton_subset_iff.mp
    (UV.le_of_mem_compression_of_notMem he heH)
  have hj : j ∉ e := Finset.disjoint_singleton_left.mp
    (UV.disjoint_of_mem_compression_of_notMem he heH)
  refine ⟨hi, hj, ?_⟩
  rw [map_swap_of_mem_of_notMem hi hj]
  exact UV.sup_sdiff_mem_of_mem_compression_of_notMem he heH

theorem exists_matching_before_shift {i j : α} {H M : Finset (Finset α)}
    (hMH : M ⊆ shiftFamily i j H) (hM : IsMatching M) :
    ∃ N : Finset (Finset α), N ⊆ H ∧ IsMatching N ∧ N.card = M.card := by
  by_cases hsub : M ⊆ H
  · exact ⟨M, hsub, hM, rfl⟩
  obtain ⟨e, heM, heH⟩ := Finset.not_subset.mp hsub
  obtain ⟨hie, hje, heold⟩ := new_shift_edge (hMH heM) heH
  refine ⟨mapFamily (Equiv.swap i j).toEmbedding M, ?_, hM.relabel _, card_mapFamily _ _⟩
  intro f hf
  obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_map.mp hf
  change f₀.map (Equiv.swap i j).toEmbedding ∈ H
  by_cases hfe : f₀ = e
  · exact hfe ▸ heold
  have hif : i ∉ f₀ := fun hi ↦ Finset.disjoint_left.mp (hM heM hf₀ (Ne.symm hfe)) hie hi
  by_cases hjf : j ∈ f₀
  · have h := UV.sup_sdiff_mem_of_mem_compression (hMH hf₀)
      (Finset.singleton_subset_iff.mpr hjf) (Finset.disjoint_singleton_left.mpr hif)
    have heq : f₀.map (Equiv.swap i j).toEmbedding = (f₀ ∪ {i}) \ {j} := by
      rw [Equiv.swap_comm i j]
      exact map_swap_of_mem_of_notMem hjf hif
    rwa [heq]
  · rw [map_swap_of_notMem_of_notMem hif hjf]
    by_contra hfH
    exact hif (new_shift_edge (hMH hf₀) hfH).1

theorem MatchingNumberAtMost.shiftFamily {s : ℕ} {H : Finset (Finset α)}
    (hν : MatchingNumberAtMost s H) (i j : α) :
    MatchingNumberAtMost s (shiftFamily i j H) := by
  intro M hMH hM
  obtain ⟨N, hNH, hN, hcard⟩ := exists_matching_before_shift hMH hM
  rw [← hcard]
  exact hν N hNH hN

def shiftMove (i j : α) (H : Finset (Finset α)) (e : Finset α) : Finset α :=
  if UV.compress {i} {j} e ∈ H then e else UV.compress {i} {j} e

theorem shiftFamily_eq_image (i j : α) (H : Finset (Finset α)) :
    shiftFamily i j H = H.image (shiftMove i j H) := by
  ext e
  rw [shiftFamily, UV.mem_compression, Finset.mem_image]
  constructor
  · rintro (⟨he, hc⟩ | ⟨he, f, hf, hfe⟩)
    · exact ⟨e, he, by simp only [shiftMove, ite_eq_left hc]⟩
    · refine ⟨f, hf, ?_⟩
      have hc : UV.compress {i} {j} f ∉ H := hfe ▸ he
      simpa only [shiftMove, ite_eq_right hc] using hfe
  · rintro ⟨f, hf, hfe⟩
    by_cases hc : UV.compress {i} {j} f ∈ H
    · simp only [shiftMove, ite_eq_left hc] at hfe
      subst e
      exact Or.inl ⟨hf, hc⟩
    · simp only [shiftMove, ite_eq_right hc] at hfe
      exact Or.inr ⟨hfe ▸ hc, f, hf, hfe⟩

theorem shiftMove_injOn (i j : α) (H : Finset (Finset α)) :
    Set.InjOn (shiftMove i j H) H := by
  apply Finset.card_image_iff.mp
  rw [← shiftFamily_eq_image, card_shiftFamily]

theorem sum_shiftFamily (i j : α) (H : Finset (Finset α)) (f : Finset α → ℕ) :
    ∑ e ∈ shiftFamily i j H, f e = ∑ e ∈ H, f (shiftMove i j H e) := by
  rw [shiftFamily_eq_image, Finset.sum_image (shiftMove_injOn i j H)]

theorem compress_subset_iff {i j : α} {Q e : Finset α} (hi : i ∈ Q) (hj : j ∈ Q) :
    UV.compress {i} {j} e ⊆ Q ↔ e ⊆ Q := by
  unfold UV.compress
  split_ifs with h
  · constructor
    · intro hsub x hx
      by_cases hxj : x = j
      · exact hxj ▸ hj
      · exact hsub (Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ hx, by simpa only [Finset.mem_singleton] using hxj⟩)
    · intro hsub
      exact Finset.sdiff_subset.trans (Finset.union_subset hsub (Finset.singleton_subset_iff.mpr hi))
  · rfl

theorem shiftMove_subset_iff {i j : α} {Q e : Finset α} (H : Finset (Finset α))
    (hi : i ∈ Q) (hj : j ∈ Q) : shiftMove i j H e ⊆ Q ↔ e ⊆ Q := by
  unfold shiftMove
  split_ifs
  · rfl
  · exact compress_subset_iff hi hj

theorem card_inside_shiftFamily {i j : α} {Q : Finset α} (H : Finset (Finset α))
    (hi : i ∈ Q) (hj : j ∈ Q) :
    ((shiftFamily i j H).filter fun e ↦ e ⊆ Q).card = (H.filter fun e ↦ e ⊆ Q).card := by
  have h := sum_shiftFamily i j H (fun e ↦ if e ⊆ Q then 1 else 0)
  simpa only [shiftMove_subset_iff H hi hj, Finset.sum_boole, Nat.cast_id] using h

theorem card_missing_clique {k : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H) (Q : Finset α) :
    (cliqueFamily k Q \ H).card = Q.card.choose k - (H.filter fun e ↦ e ⊆ Q).card := by
  have heq : H ∩ cliqueFamily k Q = H.filter fun e ↦ e ⊆ Q := by
    ext e
    simp only [Finset.mem_inter, mem_cliqueFamily, Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1, h.2.1⟩
    · exact fun h ↦ ⟨h.1, h.2, hu e h.1⟩
  rw [Finset.card_sdiff, heq, card_cliqueFamily]

theorem card_missing_clique_shiftFamily {k : ℕ} {i j : α} {Q : Finset α}
    {H : Finset (Finset α)} (hu : IsUniform k H) (hi : i ∈ Q) (hj : j ∈ Q) :
    (cliqueFamily k Q \ shiftFamily i j H).card = (cliqueFamily k Q \ H).card := by
  rw [card_missing_clique (hu.shiftFamily i j), card_missing_clique hu,
    card_inside_shiftFamily H hi hj]

def shiftEnergy (U : Finset α) (H : Finset (Finset α)) : ℕ :=
  ∑ e ∈ H, (e \ U).card

theorem shiftMove_outside_card_lt {i j : α} {U e : Finset α} {H : Finset (Finset α)}
    (hi : i ∈ U) (hj : j ∉ U) (he : e ∈ H) (hc : UV.compress {i} {j} e ∉ H) :
    (shiftMove i j H e \ U).card < (e \ U).card := by
  have hmove : Disjoint {i} e ∧ {j} ⊆ e := by
    by_contra hn
    have heq : UV.compress {i} {j} e = e := by simp only [UV.compress, ite_eq_right hn]
    rw [heq] at hc
    exact hc he
  have hje : j ∈ e := Finset.singleton_subset_iff.mp hmove.2
  have hset : shiftMove i j H e \ U = (e \ U).erase j := by
    rw [shiftMove, ite_eq_right hc, UV.compress_of_disjoint_of_le hmove.1 hmove.2]
    ext x
    by_cases hxi : x = i
    · subst x
      simp [hi]
    · simp only [Finset.sup_eq_union, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_singleton, Finset.mem_erase, hxi, or_false]
      tauto
  rw [hset, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hje, hj⟩)]
  have hpos := Finset.card_pos.mpr ⟨j, Finset.mem_sdiff.mpr ⟨hje, hj⟩⟩
  omega

theorem shiftEnergy_lt {i j : α} {U : Finset α} {H : Finset (Finset α)}
    (hi : i ∈ U) (hj : j ∉ U) (hchange : shiftFamily i j H ≠ H) :
    shiftEnergy U (shiftFamily i j H) < shiftEnergy U H := by
  have hle : ∀ e ∈ H, (shiftMove i j H e \ U).card ≤ (e \ U).card := by
    intro e he
    by_cases hc : UV.compress {i} {j} e ∈ H
    · simp only [shiftMove, ite_eq_left hc, le_refl]
    · exact (shiftMove_outside_card_lt hi hj he hc).le
  have hex : ∃ e ∈ H, UV.compress {i} {j} e ∉ H := by
    by_contra! h
    apply hchange
    rw [shiftFamily_eq_image]
    have himage : H.image (shiftMove i j H) = H.image id := by
      apply Finset.image_congr
      intro e he
      simp only [shiftMove, ite_eq_left (h e he), id_eq]
    simpa only [Finset.image_id] using himage
  obtain ⟨e, he, hc⟩ := hex
  unfold shiftEnergy
  rw [sum_shiftFamily]
  exact Finset.sum_lt_sum hle ⟨e, he, shiftMove_outside_card_lt hi hj he hc⟩

end SharpTailMatching.Matching
