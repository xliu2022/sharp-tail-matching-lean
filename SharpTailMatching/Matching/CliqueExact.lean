/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The genuine local clique lemma on an arbitrary finite vertex set, with all
numerical estimates and the full equality statement proved. The clique size
`((6*k-1)*s)/6` is the integer form of `floor((k-1/6)*s)`.
-/
module

public import SharpTailMatching.Matching.CliqueExactNumeric
public import SharpTailMatching.Matching.Relabel
public import Mathlib.Logic.Equiv.Sum

@[expose] public section

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Manuscript Lemma 8.3. The sufficient threshold is explicitly `120*k`;
the matching number hypothesis is the original, unconditional one. -/
theorem local_clique_exact {k s : ℕ} {H : Finset (Finset α)} {Q : Finset α}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ Fintype.card α)
    (hupper : 2 * Fintype.card α ≤ (2 * k + 1) * s)
    (hQcard : Q.card = ((6 * k - 1) * s) / 6)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k Q ⊆ H) :
    H.card ≤ (k * (s + 1) - 1).choose k ∧
      (H.card = (k * (s + 1) - 1).choose k ↔
        ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧ H = cliqueFamily k R) := by
  classical
  let A := ↥Q
  let W := {x : α // x ∉ Q}
  let e : A ⊕ W ≃ α := Equiv.sumCompl (fun x : α ↦ x ∈ Q)
  let J := mapFamily e.symm.toEmbedding H
  let Qleft : Finset (A ⊕ W) := (Finset.univ : Finset A).map Function.Embedding.inl
  have hsum : Fintype.card A + Fintype.card W = Fintype.card α := by
    simpa only [Fintype.card_sum] using Fintype.card_congr e
  have hA : Fintype.card A = Q.card := Fintype.card_coe Q
  have hQimage : Qleft.map e.toEmbedding = Q := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hy
      exact a.property
    · intro hx
      refine Finset.mem_map.mpr ⟨Sum.inl ⟨x, hx⟩, ?_, rfl⟩
      exact Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
  have hQback : Q.map e.symm.toEmbedding = Qleft := by
    calc
      Q.map e.symm.toEmbedding = (Qleft.map e.toEmbedding).map e.symm.toEmbedding :=
        congrArg (fun S : Finset α ↦ S.map e.symm.toEmbedding) hQimage.symm
      _ = Qleft := e.finsetCongr.symm_apply_apply Qleft
  have hQJ : cliqueFamily k Qleft ⊆ J := by
    have h := (mapFamily_subset_mapFamily e.symm.toEmbedding).mpr hQ
    rw [mapFamily_clique, hQback] at h
    exact h
  have hAcard : Fintype.card A = ((6 * k - 1) * s) / 6 := hA.trans hQcard
  have hlower' : k * (s + 1) ≤ Fintype.card A + Fintype.card W := by simpa only [hsum] using hlower
  have hupper' : 2 * (Fintype.card A + Fintype.card W) ≤ (2 * k + 1) * s := by
    simpa only [hsum] using hupper
  obtain ⟨_, _, hd, _⟩ := local_clique_range_capacities hk hs hlower' hupper' hAcard
  have hsize : Fintype.card A + (k * (s + 1) - 1 - Fintype.card A) = k * (s + 1) - 1 := by
    omega
  obtain ⟨hbound, heq⟩ := local_clique_exact_sum hk hs hlower' hupper' hAcard
    (hu.relabel e.symm.toEmbedding) (hν.relabel e.symm.toEmbedding) hQJ
  have hJcard : J.card = H.card := card_mapFamily _ _
  refine ⟨by simpa only [card_mapFamily] using hbound, ?_⟩
  constructor
  · intro hHcard
    obtain ⟨T, hT, hJ⟩ := heq.mp (hJcard.trans hHcard)
    refine ⟨((Finset.univ : Finset A).disjSum T).map e.toEmbedding, ?_, ?_⟩
    · rw [Finset.card_map, Finset.card_disjSum, Finset.card_univ, hT, hsize]
    · have hback : mapFamily e.toEmbedding J = H := mapFamily_equiv_symm e.symm H
      have h := congrArg (mapFamily e.toEmbedding) hJ
      rw [hback, mapFamily_clique] at h
      exact h
  · rintro ⟨R, hR, rfl⟩
    rw [card_cliqueFamily, hR]

end SharpTailMatching.Matching
