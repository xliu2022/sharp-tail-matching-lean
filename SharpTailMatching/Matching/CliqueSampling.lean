/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite combinatorial content of the local clique sampling proof.
-/
module

public import SharpTailMatching.Matching.Clique
public import SharpTailMatching.Matching.FiniteSampling

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I J : Type*} [DecidableEq α]

def singletonLinkEdge (v : I → α) (B : J → Finset α) (p : I × J) : Finset α :=
  insert (v p.1) (B p.2)

theorem singletonLinkEdge_image_isMatching {Q : Finset α} {v : I → α}
    {B : J → Finset α} {M : Finset (I × J)}
    (hv : Function.Injective v) (hvQ : ∀ i, v i ∉ Q) (hBQ : ∀ j, B j ⊆ Q)
    (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j)) (hM : IsBipartiteMatching M) :
    IsMatching (M.image (singletonLinkEdge v B)) := by
  intro e he f hf hef
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
  have hpq : p ≠ q := fun h ↦ hef (h ▸ rfl)
  obtain ⟨hrows, hcols⟩ := hM hp hq hpq
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  rcases Finset.mem_insert.mp hxp with rfl | hxB
  · rcases Finset.mem_insert.mp hxq with heq | hxB'
    · exact hrows (hv heq)
    · exact hvQ p.1 (hBQ q.2 hxB')
  · rcases Finset.mem_insert.mp hxq with rfl | hxB'
    · exact hvQ q.1 (hBQ p.2 hxB)
    · exact Finset.disjoint_left.mp (hB p.2 q.2 hcols) hxB hxB'

theorem singletonLinkEdge_outside_union {Q : Finset α} {v : I → α}
    {B : J → Finset α} (M : Finset (I × J))
    (hvQ : ∀ i, v i ∉ Q) (hBQ : ∀ j, B j ⊆ Q) :
    ((M.image (singletonLinkEdge v B)).biUnion id) \ Q = M.image (fun p ↦ v p.1) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxU, hxQ⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hxU
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_insert.mp hxe with rfl | hxB
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · exact False.elim (hxQ (hBQ p.2 hxB))
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_sdiff.mpr ⟨?_, hvQ p.1⟩
    exact Finset.mem_biUnion.mpr ⟨singletonLinkEdge v B p,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_insert_self _ _⟩

theorem singletonLinkEdge_outside_card {Q : Finset α} {v : I → α}
    {B : J → Finset α} {M : Finset (I × J)}
    (hv : Function.Injective v) (hvQ : ∀ i, v i ∉ Q) (hBQ : ∀ j, B j ⊆ Q)
    (hM : IsBipartiteMatching M) :
    (((M.image (singletonLinkEdge v B)).biUnion id) \ Q).card = M.card := by
  rw [singletonLinkEdge_outside_union M hvQ hBQ]
  apply Finset.card_image_of_injOn
  intro p hp q hq heq
  by_contra hne
  exact (hM hp hq hne).1 (hv heq)

/-- Every matching in the sampled bipartite graph embeds into a hypergraph
matching covering precisely one outside vertex per bipartite edge. -/
theorem sampled_bipartite_matching_bound {k s : ℕ} {Q : Finset α}
    {H : Finset (Finset α)} {v : I → α} {B : J → Finset α} {E : Finset (I × J)}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k Q ⊆ H) (hv : Function.Injective v) (hvQ : ∀ i, v i ∉ Q)
    (hBQ : ∀ j, B j ⊆ Q) (hB : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (hE : ∀ p ∈ E, singletonLinkEdge v B p ∈ H) :
    BipartiteMatchingNumberAtMost (k * (s + 1) - 1 - Q.card) E := by
  intro M hME hM
  have hMH : M.image (singletonLinkEdge v B) ⊆ H := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact hE p (hME hp)
  have hhyper := singletonLinkEdge_image_isMatching hv hvQ hBQ hB hM
  have hbound := matching_outside_clique_le hk hu hν hQ hMH hhyper
  rwa [singletonLinkEdge_outside_card hv hvQ hBQ hM] at hbound

theorem IsMatching.card_biUnion_sdiff {P : Finset (Finset α)} (hP : IsMatching P)
    (Q : Finset α) : ((P.biUnion id) \ Q).card = ∑ e ∈ P, (e \ Q).card := by
  have hset : P.biUnion (fun e ↦ e \ Q) = (P.biUnion id) \ Q := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_sdiff, id_eq]
    aesop
  rw [← hset]
  apply Finset.card_biUnion
  intro e he f hf hef
  exact (hP he hf hef).mono Finset.sdiff_subset Finset.sdiff_subset

/-- Replacement inequality for the clique proof. Starting with singleton-
outside matching edges, insert a second matching whose inside vertices avoid
the first. Delete only first-matching edges whose outside vertex is used by
the new matching. The number of newly covered outside vertices is bounded by
the original outside deficit. -/
theorem matching_replacement_outside_gain {k s : ℕ} {Q : Finset α}
    {H M P : Finset (Finset α)} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H) (hQ : cliqueFamily k Q ⊆ H)
    (hMH : M ⊆ H) (hM : IsMatching M) (hPH : P ⊆ H) (hP : IsMatching P)
    (hMsingle : ∀ e ∈ M, (e \ Q).card = 1)
    (hinside : Disjoint ((M.biUnion id) ∩ Q) ((P.biUnion id) ∩ Q)) :
    (((P.biUnion id) \ Q) \ ((M.biUnion id) \ Q)).card ≤
      (k * (s + 1) - 1 - Q.card) - ((M.biUnion id) \ Q).card := by
  let T := (M.biUnion id) \ Q
  let U := (P.biUnion id) \ Q
  let R := M.filter fun e ↦ Disjoint (e \ Q) U
  have hRM : R ⊆ M := Finset.filter_subset _ _
  have hcross : ∀ e ∈ R, ∀ f ∈ P, Disjoint e f := by
    intro e he f hf
    obtain ⟨heM, heU⟩ := Finset.mem_filter.mp he
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    by_cases hvQ : v ∈ Q
    · apply Finset.disjoint_left.mp hinside
      · exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨e, heM, hve⟩, hvQ⟩
      · exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨f, hf, hvf⟩, hvQ⟩
    · apply Finset.disjoint_left.mp heU (Finset.mem_sdiff.mpr ⟨hve, hvQ⟩)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨f, hf, hvf⟩, hvQ⟩
  have hN : IsMatching (R ∪ P) := (hM.mono hRM).union hP hcross
  have hNH : R ∪ P ⊆ H := Finset.union_subset (hRM.trans hMH) hPH
  have hvertices : ((R ∪ P).biUnion id) \ Q = T ∪ U := by
    ext v
    constructor
    · intro hv
      obtain ⟨hvN, hvQ⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hvN
      rcases Finset.mem_union.mp he with heR | heP
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨e, hRM heR, hve⟩, hvQ⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨e, heP, hve⟩, hvQ⟩)
    · intro hv
      have hfromU : v ∈ U → v ∈ ((R ∪ P).biUnion id) \ Q := by
        intro hvU
        obtain ⟨hvP, hvQ⟩ := Finset.mem_sdiff.mp hvU
        obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvP
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
          ⟨f, Finset.mem_union_right _ hf, hvf⟩, hvQ⟩
      rcases Finset.mem_union.mp hv with hvT | hvU
      · by_cases hvU : v ∈ U
        · exact hfromU hvU
        obtain ⟨hvM, hvQ⟩ := Finset.mem_sdiff.mp hvT
        obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hvM
        obtain ⟨w, hew⟩ := Finset.card_eq_one.mp (hMsingle e heM)
        have hvw : v = w := by
          have hvout : v ∈ e \ Q := Finset.mem_sdiff.mpr ⟨hve, hvQ⟩
          rw [hew] at hvout
          exact Finset.mem_singleton.mp hvout
        have heR : e ∈ R := by
          apply Finset.mem_filter.mpr ⟨heM, ?_⟩
          rw [hew, ← hvw]
          exact Finset.disjoint_singleton_left.mpr hvU
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
          ⟨e, Finset.mem_union_left _ heR, hve⟩, hvQ⟩
      · exact hfromU hvU
  have hbound := matching_outside_clique_le hk hu hν hQ hNH hN
  rw [hvertices] at hbound
  have hcard := Finset.card_sdiff_add_card U T
  rw [Finset.union_comm U T] at hcard
  change (U \ T).card ≤ (k * (s + 1) - 1 - Q.card) - T.card
  omega

theorem matching_replacement_outside_gain_sum {k s : ℕ} {Q : Finset α}
    {H M P : Finset (Finset α)} (hk : 0 < k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H) (hQ : cliqueFamily k Q ⊆ H)
    (hMH : M ⊆ H) (hM : IsMatching M) (hPH : P ⊆ H) (hP : IsMatching P)
    (hMsingle : ∀ e ∈ M, (e \ Q).card = 1)
    (hinside : Disjoint ((M.biUnion id) ∩ Q) ((P.biUnion id) ∩ Q)) :
    (∑ e ∈ P, ((e \ Q) \ ((M.biUnion id) \ Q)).card) ≤
      (k * (s + 1) - 1 - Q.card) - ((M.biUnion id) \ Q).card := by
  have hgain := matching_replacement_outside_gain hk hu hν hQ hMH hM hPH hP hMsingle hinside
  have hsum := hP.card_biUnion_sdiff (Q ∪ ((M.biUnion id) \ Q))
  simp only [sdiff_sdiff_left, Finset.sup_eq_union] at hgain ⊢
  rwa [hsum] at hgain

/-- Count successful disjoint tests by those contained in the already matched
outside set, plus the available outside deficit. All hypergraph hypotheses
are the actual uniformity, matching, and contained-clique hypotheses. -/
theorem successful_tests_le_contained_add_deficit {ι : Type*} [Fintype ι]
    {k s : ℕ} {Q : Finset α} {H M : Finset (Finset α)}
    (hk : 0 < k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k Q ⊆ H) (hMH : M ⊆ H) (hM : IsMatching M)
    (hMsingle : ∀ e ∈ M, (e \ Q).card = 1)
    (F : ι → Finset α) (hF : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hinside : ∀ i, Disjoint ((M.biUnion id) ∩ Q) (F i ∩ Q)) :
    (Finset.univ.filter fun i ↦ F i ∈ H).card ≤
      (Finset.univ.filter fun i ↦ F i \ Q ⊆ (M.biUnion id) \ Q).card +
        ((k * (s + 1) - 1 - Q.card) - ((M.biUnion id) \ Q).card) := by
  classical
  let S := Finset.univ.filter fun i ↦ F i ∈ H
  let T := (M.biUnion id) \ Q
  let P := S.image F
  have hPH : P ⊆ H := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hi).2
  have hP : IsMatching P := by
    intro e he f hf hef
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hf
    exact hF i j (fun hij ↦ hef (hij ▸ rfl))
  have hinj : Set.InjOn F S := by
    intro i hi j hj heq
    by_contra hne
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (by rw [hu (F i) (Finset.mem_filter.mp hi).2]; exact hk)
    exact Finset.disjoint_left.mp (hF i j hne) hv (heq ▸ hv)
  have hdis : Disjoint ((M.biUnion id) ∩ Q) ((P.biUnion id) ∩ Q) := by
    apply Finset.disjoint_left.mpr
    intro v hvM hvP
    obtain ⟨hvP, hvQ⟩ := Finset.mem_inter.mp hvP
    obtain ⟨e, heP, hve⟩ := Finset.mem_biUnion.mp hvP
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp heP
    exact Finset.disjoint_left.mp (hinside i) hvM (Finset.mem_inter.mpr ⟨hve, hvQ⟩)
  have hgain := matching_replacement_outside_gain_sum hk hu hν hQ hMH hM hPH hP hMsingle hdis
  change (∑ e ∈ S.image F, ((e \ Q) \ T).card) ≤
    (k * (s + 1) - 1 - Q.card) - T.card at hgain
  rw [Finset.sum_image hinj] at hgain
  have hpoint : ∀ i ∈ S, 1 ≤ (if F i \ Q ⊆ T then 1 else 0) + ((F i \ Q) \ T).card := by
    intro i hi
    by_cases hsub : F i \ Q ⊆ T
    · simp [hsub]
    · obtain ⟨v, hv, hvT⟩ := Finset.not_subset.mp hsub
      have hpos : 0 < ((F i \ Q) \ T).card :=
        Finset.card_pos.mpr ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvT⟩⟩
      simp only [ite_eq_right hsub, Nat.zero_add]
      exact hpos
  have hcount : (∑ i ∈ S, if F i \ Q ⊆ T then 1 else 0) ≤
      (Finset.univ.filter fun i ↦ F i \ Q ⊆ T).card := by
    rw [Finset.sum_boole]
    apply Finset.card_le_card
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_one] at hsum
  exact hsum.trans (Nat.add_le_add hcount hgain)

end SharpTailMatching.Matching
