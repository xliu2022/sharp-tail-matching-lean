/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Only cross-shifts from a reservoir into the desired clique are needed. Once
all such shifts fix the family, a single reservoir edge forces every desired
edge of the same size. This avoids a separate componentwise-order theory.
-/
module

public import SharpTailMatching.Matching.ShiftingBasic

@[expose] public section

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

def IsCrossShifted (U V : Finset α) (H : Finset (Finset α)) : Prop :=
  ∀ i ∈ U, ∀ j ∈ V, shiftFamily i j H = H

theorem mem_of_crossShifted {U V E F : Finset α} {H : Finset (Finset α)}
    (hshift : IsCrossShifted U V H) (hEU : E ⊆ U) (hFV : F \ E ⊆ V)
    (hcard : E.card = F.card) (hF : F ∈ H) : E ∈ H := by
  generalize hn : (E \ F).card = n
  induction n using Nat.strong_induction_on generalizing F with
  | h n ih =>
    by_cases hsub : E ⊆ F
    · have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
      exact heq ▸ hF
    obtain ⟨i, hiE, hiF⟩ := Finset.not_subset.mp hsub
    have hreverse : ¬ F ⊆ E := by
      intro hFE
      have heq := Finset.eq_of_subset_of_card_le hFE hcard.le
      exact hsub heq.symm.subset
    obtain ⟨j, hjF, hjE⟩ := Finset.not_subset.mp hreverse
    have hij : i ≠ j := fun h ↦ hjE (h ▸ hiE)
    let F' := insert i (F.erase j)
    have hcomp : UV.compress {i} {j} F = F' := by
      rw [UV.compress_of_disjoint_of_le (Finset.disjoint_singleton_left.mpr hiF)
        (Finset.singleton_subset_iff.mpr hjF)]
      ext x
      by_cases hxi : x = i
      · subst x
        simp [F', hij]
      · simp only [Finset.sup_eq_union, Finset.mem_sdiff, Finset.mem_union,
          Finset.mem_singleton, F', Finset.mem_insert, Finset.mem_erase, hxi, or_false, false_or]
        tauto
    have hF'H : F' ∈ H := by
      have h := UV.compress_mem_compression (u := ({i} : Finset α)) (v := {j}) hF
      change UV.compress {i} {j} F ∈ shiftFamily i j H at h
      rw [hcomp, hshift i (hEU hiE) j (hFV (Finset.mem_sdiff.mpr ⟨hjF, hjE⟩))] at h
      exact h
    have hF'card : F'.card = F.card := by
      change (insert i (F.erase j)).card = F.card
      rw [Finset.card_insert_of_notMem (fun h ↦ hiF (Finset.mem_of_mem_erase h))]
      exact Finset.card_erase_add_one hjF
    have hF'V : F' \ E ⊆ V := by
      intro x hx
      obtain ⟨hxF', hxE⟩ := Finset.mem_sdiff.mp hx
      rcases Finset.mem_insert.mp hxF' with rfl | hxF
      · exact (hxE hiE).elim
      · exact hFV (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hxF, hxE⟩)
    have hdiff : E \ F' = (E \ F).erase i := by
      ext x
      by_cases hxj : x = j
      · subst x
        simp [hjE]
      · simp only [Finset.mem_sdiff, F', Finset.mem_insert, Finset.mem_erase]
        tauto
    have hsmall : (E \ F').card < n := by
      rw [hdiff, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hiE, hiF⟩), hn]
      have hpos : 0 < n := by
        rw [← hn]
        exact Finset.card_pos.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hiE, hiF⟩⟩
      omega
    exact ih (E \ F').card hsmall hF'V (hcard.trans hF'card.symm) hF'H rfl

/-- Fewer missing edges than the number of reservoir `k`-sets forces a
genuine clique after the cross-shifts stabilize. -/
theorem crossShifted_contains_clique {k : ℕ} {Q U V : Finset α} {H : Finset (Finset α)}
    (hVQ : V ⊆ Q) (hshift : IsCrossShifted U V H)
    (hmissing : (cliqueFamily k Q \ H).card < V.card.choose k) :
    cliqueFamily k U ⊆ H := by
  intro E hE
  obtain ⟨hEU, hEcard⟩ := mem_cliqueFamily.mp hE
  by_contra hEH
  have hsub : cliqueFamily k V ⊆ cliqueFamily k Q \ H := by
    intro F hF
    obtain ⟨hFV, hFcard⟩ := mem_cliqueFamily.mp hF
    refine Finset.mem_sdiff.mpr ⟨mem_cliqueFamily.mpr ⟨hFV.trans hVQ, hFcard⟩, ?_⟩
    intro hFH
    exact hEH (mem_of_crossShifted hshift hEU (Finset.sdiff_subset.trans hFV)
      (hEcard.trans hFcard.symm) hFH)
  have hcount := Finset.card_le_card hsub
  rw [card_cliqueFamily] at hcount
  omega

end SharpTailMatching.Matching
