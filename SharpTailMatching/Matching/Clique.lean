/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite clique extension tools for the local clique argument in Section 8.
-/
module

public import SharpTailMatching.Matching.CoverExact

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

theorem IsMatching.union {M N : Finset (Finset α)} (hM : IsMatching M)
    (hN : IsMatching N) (hcross : ∀ e ∈ M, ∀ f ∈ N, Disjoint e f) :
    IsMatching (M ∪ N) := by
  intro e he f hf hef
  rcases Finset.mem_union.mp he with he | he
  · rcases Finset.mem_union.mp hf with hf | hf
    · exact hM he hf hef
    · exact hcross e he f hf
  · rcases Finset.mem_union.mp hf with hf | hf
    · exact (hcross f hf e he).symm
    · exact hN he hf hef

/-- A clique contains a matching of every size permitted by its vertex count. -/
theorem exists_matching_in_clique {k t : ℕ} {Q : Finset α}
    (hk : 0 < k) (hsize : k * t ≤ Q.card) :
    ∃ M : Finset (Finset α), M ⊆ cliqueFamily k Q ∧ IsMatching M ∧ M.card = t := by
  induction t generalizing Q with
  | zero =>
    exact ⟨∅, Finset.empty_subset _, by simp [IsMatching, Set.Pairwise], by simp⟩
  | succ t ih =>
    obtain ⟨e, heQ, hecard⟩ := Finset.exists_subset_card_eq
      (show k ≤ Q.card by nlinarith)
    have hleft : k * t ≤ (Q \ e).card := by
      rw [Finset.card_sdiff_of_subset heQ, hecard]
      rw [Nat.mul_succ] at hsize
      omega
    obtain ⟨M, hMQ, hM, hMcard⟩ := ih hleft
    have heM : e ∉ M := by
      intro he
      have hesub := (mem_cliqueFamily.mp (hMQ he)).1
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < e.card)
      exact (Finset.mem_sdiff.mp (hesub hv)).2 hv
    have hcross : ∀ f ∈ M, Disjoint e f := by
      intro f hf
      apply Finset.disjoint_left.mpr
      intro v hve hvf
      exact (Finset.mem_sdiff.mp ((mem_cliqueFamily.mp (hMQ hf)).1 hvf)).2 hve
    refine ⟨insert e M, ?_, hM.insert hcross, ?_⟩
    · apply Finset.insert_subset (mem_cliqueFamily.mpr ⟨heQ, hecard⟩)
      intro f hf
      obtain ⟨hfQ, hfcard⟩ := mem_cliqueFamily.mp (hMQ hf)
      exact mem_cliqueFamily.mpr ⟨hfQ.trans Finset.sdiff_subset, hfcard⟩
    · rw [Finset.card_insert_of_notMem heM, hMcard]

/-- A prescribed matching can be completed inside a clique whenever the
available vertices meet the exact divisibility-free capacity inequality. -/
theorem extend_matching_inside_clique {k s : ℕ} {Q : Finset α}
    {H M : Finset (Finset α)} (hk : 0 < k) (hu : IsUniform k H)
    (hQ : cliqueFamily k Q ⊆ H) (hMH : M ⊆ H) (hM : IsMatching M)
    (hMs : M.card ≤ s)
    (hcapacity : k * (s + 1) ≤ Q.card + ((M.biUnion id) \ Q).card) :
    ∃ N : Finset (Finset α), N ⊆ H ∧ IsMatching N ∧ N.card = s + 1 := by
  let U := M.biUnion id
  have hUcard : U.card = k * M.card := hM.card_biUnion (hu.mono hMH)
  have hQsplit := Finset.card_inter_add_card_sdiff Q U
  have hUsplit := Finset.card_inter_add_card_sdiff U Q
  rw [Finset.inter_comm Q U] at hQsplit
  have hfree : k * (s + 1 - M.card) ≤ (Q \ U).card := by
    have hsub : s + 1 - M.card + M.card = s + 1 := Nat.sub_add_cancel (by omega)
    change k * (s + 1) ≤ Q.card + (U \ Q).card at hcapacity
    nlinarith
  obtain ⟨P, hPQ, hP, hPcard⟩ := exists_matching_in_clique hk hfree
  have hPH : P ⊆ H := by
    intro e he
    obtain ⟨heQ, hecard⟩ := mem_cliqueFamily.mp (hPQ he)
    exact hQ (mem_cliqueFamily.mpr ⟨heQ.trans Finset.sdiff_subset, hecard⟩)
  have hcross : ∀ e ∈ M, ∀ f ∈ P, Disjoint e f := by
    intro e he f hf
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    have hvU : v ∈ U := Finset.mem_biUnion.mpr ⟨e, he, hve⟩
    exact (Finset.mem_sdiff.mp ((mem_cliqueFamily.mp (hPQ hf)).1 hvf)).2 hvU
  have hMP : Disjoint M P := by
    apply Finset.disjoint_left.mpr
    intro e heM heP
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by rw [hu e (hMH heM)]; exact hk)
    exact Finset.disjoint_left.mp (hcross e heM e heP) hv hv
  refine ⟨M ∪ P, Finset.union_subset hMH hPH, hM.union hP hcross, ?_⟩
  rw [Finset.card_union_of_disjoint hMP, hPcard]
  omega

/-- The outside-vertex restriction at the start of the local clique proof.
It holds for every matching, whether or not all its edges meet the outside. -/
theorem matching_outside_clique_bound {k s : ℕ} {Q : Finset α}
    {H M : Finset (Finset α)} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H) (hQ : cliqueFamily k Q ⊆ H)
    (hMH : M ⊆ H) (hM : IsMatching M) :
    Q.card + ((M.biUnion id) \ Q).card < k * (s + 1) := by
  by_contra hnot
  obtain ⟨N, hNH, hN, hNcard⟩ := extend_matching_inside_clique hk hu hQ hMH hM
    (hν M hMH hM) (le_of_not_gt hnot)
  have hNs := hν N hNH hN
  omega

theorem matching_outside_clique_le {k s : ℕ} {Q : Finset α}
    {H M : Finset (Finset α)} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H) (hQ : cliqueFamily k Q ⊆ H)
    (hMH : M ⊆ H) (hM : IsMatching M) :
    ((M.biUnion id) \ Q).card ≤ k * (s + 1) - 1 - Q.card := by
  have h := matching_outside_clique_bound hk hu hν hQ hMH hM
  omega

end SharpTailMatching.Matching
