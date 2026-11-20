/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Transport finite uniform hypergraphs, matchings, and cliques under vertex
embeddings. These lemmas keep the local theorems independent of a labelling.
-/
module

public import SharpTailMatching.Matching.Basic

@[expose] public section

namespace SharpTailMatching.Matching

variable {α β : Type*}

def mapFamily (f : α ↪ β) (H : Finset (Finset α)) : Finset (Finset β) :=
  H.map (Finset.mapEmbedding f).toEmbedding

@[simp] theorem card_mapFamily (f : α ↪ β) (H : Finset (Finset α)) :
    (mapFamily f H).card = H.card := Finset.card_map _

theorem mapFamily_subset_mapFamily (f : α ↪ β) {H J : Finset (Finset α)} :
    mapFamily f H ⊆ mapFamily f J ↔ H ⊆ J := Finset.map_subset_map

theorem mapFamily_clique (f : α ↪ β) (k : ℕ) (Q : Finset α) :
    mapFamily f (cliqueFamily k Q) = cliqueFamily k (Q.map f) :=
  (Finset.powersetCard_map f k Q).symm

theorem IsUniform.relabel {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) (f : α ↪ β) : IsUniform k (mapFamily f H) := by
  intro e he
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
  change (e₀.map f).card = k
  simpa only [Finset.card_map] using hu e₀ he₀

theorem IsMatching.relabel {M : Finset (Finset α)} (hM : IsMatching M)
    (f : α ↪ β) : IsMatching (mapFamily f M) := by
  intro e he e' he' hee'
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
  obtain ⟨e₁, he₁, rfl⟩ := Finset.mem_map.mp he'
  have hne : e₀ ≠ e₁ := fun h ↦ hee' (h ▸ rfl)
  exact (Finset.disjoint_map f).mpr (hM he₀ he₁ hne)

theorem isMatching_mapFamily_iff (f : α ↪ β) (M : Finset (Finset α)) :
    IsMatching (mapFamily f M) ↔ IsMatching M := by
  constructor
  · intro h e he e' he' hee'
    apply (Finset.disjoint_map f).mp
    exact h (Finset.mem_map.mpr ⟨e, he, rfl⟩) (Finset.mem_map.mpr ⟨e', he', rfl⟩)
      (fun heq ↦ hee' (Finset.map_injective f heq))
  · exact fun h ↦ h.relabel f

theorem MatchingNumberAtMost.relabel {s : ℕ} {H : Finset (Finset α)}
    (hν : MatchingNumberAtMost s H) (f : α ↪ β) :
    MatchingNumberAtMost s (mapFamily f H) := by
  classical
  intro M hMH hM
  let N := H.filter fun e ↦ e.map f ∈ M
  have hN : N ⊆ H := Finset.filter_subset _ _
  have heq : mapFamily f N = M := by
    apply Finset.Subset.antisymm
    · intro e he
      obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_map.mp he
      exact (Finset.mem_filter.mp he₀).2
    · intro e he
      obtain ⟨e₀, he₀, heq⟩ := Finset.mem_map.mp (hMH he)
      refine Finset.mem_map.mpr ⟨e₀, Finset.mem_filter.mpr ⟨he₀, ?_⟩, heq⟩
      change e₀.map f = e at heq
      rwa [heq]
  have hNm : IsMatching N := (isMatching_mapFamily_iff f N).mp (heq ▸ hM)
  have hcard := hν N hN hNm
  rw [← card_mapFamily f N, heq] at hcard
  exact hcard

@[simp] theorem mapFamily_equiv_symm (e : α ≃ β) (H : Finset (Finset α)) :
    mapFamily e.symm.toEmbedding (mapFamily e.toEmbedding H) = H := by
  exact (e.finsetCongr.finsetCongr).symm_apply_apply H

end SharpTailMatching.Matching
