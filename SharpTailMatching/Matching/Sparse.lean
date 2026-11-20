/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite matching and degree tools for the sparse range.
-/
module

public import SharpTailMatching.Matching.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

def IsOn (V : Finset α) (H : Finset (Finset α)) : Prop :=
  ∀ e ∈ H, e ⊆ V

def degree (H : Finset (Finset α)) (v : α) : ℕ :=
  (H.filter fun e ↦ v ∈ e).card

def deleteVertex (H : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  H.filter fun e ↦ v ∉ e

theorem IsMatching.insert {M : Finset (Finset α)} {e : Finset α}
    (hM : IsMatching M) (hd : ∀ f ∈ M, Disjoint e f) :
    IsMatching (insert e M) := by
  change ((Insert.insert e M : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint
  rw [Finset.coe_insert]
  exact Set.Pairwise.insert hM (fun f hf _ ↦ ⟨hd f hf, (hd f hf).symm⟩)

omit [DecidableEq α] in
theorem exists_maximum_matching (H : Finset (Finset α)) :
    ∃ M : Finset (Finset α), M ⊆ H ∧ IsMatching M ∧
      ∀ N : Finset (Finset α), N ⊆ H → IsMatching N → N.card ≤ M.card := by
  classical
  let F := H.powerset.filter IsMatching
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [F, IsMatching, Set.Pairwise]
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image F Finset.card hF
  have hM' : M ⊆ H ∧ IsMatching M := by
    simpa [F] using hM
  refine ⟨M, hM'.1, hM'.2, ?_⟩
  intro N hNH hN
  exact hmax N (by simp [F, hNH, hN])

/-- The vertices of a maximum matching meet every nonempty edge. -/
theorem maximum_matching_hits {H M : Finset (Finset α)}
    (hMH : M ⊆ H) (hM : IsMatching M)
    (hmax : ∀ N : Finset (Finset α), N ⊆ H → IsMatching N → N.card ≤ M.card)
    (hne : ∀ e ∈ H, e.Nonempty) :
    ∀ e ∈ H, ∃ v ∈ e, v ∈ M.biUnion id := by
  intro e he
  by_contra hnot
  have hd : ∀ f ∈ M, Disjoint e f := by
    intro f hf
    apply Finset.disjoint_left.mpr
    intro v hve hvf
    exact hnot ⟨v, hve, Finset.mem_biUnion.mpr ⟨f, hf, hvf⟩⟩
  have heM : e ∉ M := by
    intro hem
    obtain ⟨v, hv⟩ := hne e he
    exact Finset.disjoint_left.mp (hd e hem) hv hv
  have hcard := hmax (insert e M) (Finset.insert_subset he hMH) (hM.insert hd)
  rw [Finset.card_insert_of_notMem heM] at hcard
  exact Nat.not_succ_le_self _ hcard

/-- A matching bound gives a transversal with at most `k * b` vertices. -/
theorem exists_small_transversal {k b : ℕ} {V : Finset α} {H : Finset (Finset α)}
    (hk : 0 < k) (hV : IsOn V H) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost b H) :
    ∃ T : Finset α, T ⊆ V ∧ T.card ≤ k * b ∧
      ∀ e ∈ H, ∃ v ∈ e, v ∈ T := by
  obtain ⟨M, hMH, hM, hmax⟩ := exists_maximum_matching H
  refine ⟨M.biUnion id, ?_, ?_, ?_⟩
  · exact Finset.biUnion_subset.mpr (fun e he ↦ hV e (hMH he))
  · rw [hM.card_biUnion (hu.mono hMH)]
    exact Nat.mul_le_mul_left k (hν M hMH hM)
  · apply maximum_matching_hits hMH hM hmax
    intro e he
    apply Finset.card_pos.mp
    rw [hu e he]
    exact hk

theorem card_le_sum_degrees_of_hitting_set {H : Finset (Finset α)} {T : Finset α}
    (hT : ∀ e ∈ H, ∃ v ∈ e, v ∈ T) : H.card ≤ ∑ v ∈ T, degree H v := by
  have hUnion : H = T.biUnion (fun v ↦ H.filter fun e ↦ v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨v, hve, hvT⟩ := hT e he
      exact Finset.mem_biUnion.mpr ⟨v, hvT, Finset.mem_filter.mpr ⟨he, hve⟩⟩
    · intro he
      obtain ⟨v, _, hv⟩ := Finset.mem_biUnion.mp he
      exact (Finset.mem_filter.mp hv).1
  calc
    H.card = (T.biUnion (fun v ↦ H.filter fun e ↦ v ∈ e)).card :=
      congrArg Finset.card hUnion
    _ ≤ ∑ v ∈ T, (H.filter fun e ↦ v ∈ e).card := Finset.card_biUnion_le
    _ = ∑ v ∈ T, degree H v := rfl

theorem exists_degree_gt_of_card_gt {k b D : ℕ} {V : Finset α}
    {H : Finset (Finset α)} (hk : 0 < k) (hV : IsOn V H)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost b H)
    (hcard : k * b * D < H.card) : ∃ v ∈ V, D < degree H v := by
  obtain ⟨T, hTV, hTcard, hT⟩ := exists_small_transversal hk hV hu hν
  by_contra hnot
  have hdegree : ∀ v ∈ T, degree H v ≤ D := by
    intro v hv
    by_contra h
    exact hnot ⟨v, hTV hv, lt_of_not_ge h⟩
  have hsum : (∑ v ∈ T, degree H v) ≤ T.card * D := by
    calc
      (∑ v ∈ T, degree H v) ≤ ∑ _v ∈ T, D := Finset.sum_le_sum hdegree
      _ = T.card * D := by simp
  have hbound := (card_le_sum_degrees_of_hitting_set hT).trans hsum
  exact (not_lt_of_ge (hbound.trans (Nat.mul_le_mul_right D hTcard))) hcard

theorem degree_add_card_deleteVertex (H : Finset (Finset α)) (v : α) :
    degree H v + (deleteVertex H v).card = H.card := by
  exact Finset.card_filter_add_card_filter_not (s := H) (fun e ↦ v ∈ e)

theorem deleteVertex_on {V : Finset α} {H : Finset (Finset α)}
    (hV : IsOn V H) (v : α) : IsOn (V.erase v) (deleteVertex H v) := by
  intro e he w hw
  obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
  apply Finset.mem_erase.mpr
  refine ⟨?_, hV e heH hw⟩
  intro hwv
  apply hve
  simpa [hwv] using hw

theorem deleteVertex_uniform {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) (v : α) : IsUniform k (deleteVertex H v) := by
  exact hu.mono (Finset.filter_subset _ _)

/-- Erasing prescribed vertices injects the edges containing them into a smaller powerset. -/
theorem card_edges_containing_le {k : ℕ} {V A : Finset α} {H : Finset (Finset α)}
    (hV : IsOn V H) (hu : IsUniform k H) (hAV : A ⊆ V) :
    (H.filter fun e ↦ A ⊆ e).card ≤ (V.card - A.card).choose (k - A.card) := by
  have hle : (H.filter fun e ↦ A ⊆ e).card ≤
      ((V \ A).powersetCard (k - A.card)).card := by
    apply Finset.card_le_card_of_injOn (fun e ↦ e \ A)
    · intro e he
      obtain ⟨heH, hAe⟩ := Finset.mem_filter.mp he
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.sdiff_subset_sdiff_left A (hV e heH), ?_⟩
      rw [Finset.card_sdiff_of_subset hAe, hu e heH]
    · intro e he f hf hef
      have hAe := (Finset.mem_filter.mp he).2
      have hAf := (Finset.mem_filter.mp hf).2
      change e \ A = f \ A at hef
      calc
        e = (e \ A) ∪ A := (Finset.sdiff_union_of_subset hAe).symm
        _ = (f \ A) ∪ A := by rw [hef]
        _ = f := Finset.sdiff_union_of_subset hAf
  simpa only [Finset.card_powersetCard, Finset.card_sdiff_of_subset hAV] using hle

theorem degree_le_choose {k : ℕ} {V : Finset α} {H : Finset (Finset α)}
    (hV : IsOn V H) (hu : IsUniform k H) {v : α} (hv : v ∈ V) :
    degree H v ≤ (V.card - 1).choose (k - 1) := by
  simpa only [degree, Finset.singleton_subset_iff, Finset.card_singleton] using
    card_edges_containing_le hV hu (Finset.singleton_subset_iff.mpr hv)

theorem codegree_le_choose {k : ℕ} {V : Finset α} {H : Finset (Finset α)}
    (hV : IsOn V H) (hu : IsUniform k H) {v w : α}
    (hv : v ∈ V) (hw : w ∈ V) (hvw : v ≠ w) :
    (H.filter fun e ↦ v ∈ e ∧ w ∈ e).card ≤
      (V.card - 2).choose (k - 2) := by
  have hp : ({v, w} : Finset α) ⊆ V := by
    simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hv, hw]
  simpa [Finset.insert_subset_iff, hvw] using card_edges_containing_le hV hu hp

/-- A high-degree vertex has an incident edge avoiding a prescribed vertex set. -/
theorem exists_edge_through_disjoint {k : ℕ} {V T : Finset α}
    {H : Finset (Finset α)} (hV : IsOn V H) (hu : IsUniform k H)
    {v : α} (hv : v ∈ V) (hTV : T ⊆ V) (hvT : v ∉ T)
    (hdegree : T.card * (V.card - 2).choose (k - 2) < degree H v) :
    ∃ e ∈ H, v ∈ e ∧ Disjoint e T := by
  by_contra! hnot
  have hhit : ∀ e ∈ H.filter (fun e ↦ v ∈ e), ∃ w ∈ e, w ∈ T := by
    intro e he
    obtain ⟨heH, hve⟩ := Finset.mem_filter.mp he
    exact Finset.not_disjoint_iff.mp (hnot e heH hve)
  have hsum := card_le_sum_degrees_of_hitting_set hhit
  have hbound : (∑ w ∈ T, degree (H.filter fun e ↦ v ∈ e) w) ≤
      T.card * (V.card - 2).choose (k - 2) := by
    calc
      (∑ w ∈ T, degree (H.filter fun e ↦ v ∈ e) w) ≤
          ∑ _w ∈ T, (V.card - 2).choose (k - 2) := by
        apply Finset.sum_le_sum
        intro w hw
        have hvw : v ≠ w := by
          intro h
          exact hvT (h ▸ hw)
        simpa only [degree, Finset.filter_filter] using
          codegree_le_choose hV hu hv (hTV hw) hvw
      _ = T.card * (V.card - 2).choose (k - 2) := by simp
  exact (not_lt_of_ge (hsum.trans hbound)) hdegree

/-- Deleting a sufficiently high-degree vertex lowers the matching bound by one. -/
theorem deleteVertex_matchingNumberAtMost {k b : ℕ} {V : Finset α}
    {H : Finset (Finset α)} (hV : IsOn V H) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost (b + 1) H) {v : α} (hv : v ∈ V)
    (hdegree : k * (b + 1) * (V.card - 2).choose (k - 2) < degree H v) :
    MatchingNumberAtMost b (deleteVertex H v) := by
  intro M hsub hM
  have hMH : M ⊆ H := hsub.trans (Finset.filter_subset _ _)
  have hcard := hν M hMH hM
  by_contra hnot
  have hMcard : M.card = b + 1 := by omega
  let T := M.biUnion id
  have hTcard : T.card = k * (b + 1) := by
    rw [hM.card_biUnion (hu.mono hMH), hMcard]
  have hTV : T ⊆ V := Finset.biUnion_subset.mpr (fun e he ↦ hV e (hMH he))
  have hvT : v ∉ T := by
    intro hvT
    obtain ⟨e, heM, hve⟩ := Finset.mem_biUnion.mp hvT
    exact (Finset.mem_filter.mp (hsub heM)).2 hve
  obtain ⟨e, heH, hve, hed⟩ := exists_edge_through_disjoint hV hu hv hTV hvT
    (by simpa only [hTcard] using hdegree)
  have heM : e ∉ M := by
    intro hem
    exact (Finset.mem_filter.mp (hsub hem)).2 hve
  have hdis : ∀ f ∈ M, Disjoint e f := by
    intro f hf
    apply Finset.disjoint_left.mpr
    intro w hwe hwf
    exact Finset.disjoint_left.mp hed hwe (Finset.mem_biUnion.mpr ⟨f, hf, hwf⟩)
  have hbound := hν (insert e M) (Finset.insert_subset heH hMH) (hM.insert hdis)
  rw [Finset.card_insert_of_notMem heM, hMcard] at hbound
  omega

/-- A lower estimate for a binomial difference, obtained by Pascal telescoping. -/
theorem choose_difference_lower (m b r : ℕ) :
    b * m.choose r ≤ (m + b).choose (r + 1) - m.choose (r + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hmono := Nat.choose_le_choose r (Nat.le_add_right m b)
    have hbase := Nat.choose_le_choose (r + 1) (Nat.le_add_right m b)
    have hpascal := Nat.choose_succ_succ (m + b) r
    have hadd : m + (b + 1) = m + b + 1 := by omega
    rw [hadd]
    have ih' := (Nat.le_sub_iff_add_le hbase).mp ih
    apply (Nat.le_sub_iff_add_le
      (Nat.choose_le_choose (r + 1) (by omega : m ≤ m + b + 1))).mpr
    simp only [Nat.succ_eq_add_one] at hpascal
    nlinarith

/-- An upper estimate for a binomial difference with its last increment. -/
theorem choose_difference_upper (m b r : ℕ) :
    (m + b).choose (r + 1) ≤
      m.choose (r + 1) + b * (m + b - 1).choose r := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hmono := Nat.choose_le_choose r (Nat.sub_le (m + b) 1)
    have hpascal := Nat.choose_succ_succ (m + b) r
    have hadd : m + (b + 1) = m + b + 1 := by omega
    rw [hadd, Nat.add_sub_cancel]
    have hmul := Nat.mul_le_mul_left b hmono
    nlinarith

theorem sparse_binomial_comparison {k b n : ℕ} (hk : 2 ≤ k) (hb : 0 < b)
    (hn : 4 * k ^ 3 * b ≤ n) :
    k ^ 2 * b * (n - 2).choose (k - 2) < (n - b).choose (k - 1) := by
  have hkpow : k ≤ k ^ 3 := le_self_pow₀ (by omega) (by decide)
  have hpowb : k ^ 3 ≤ k ^ 3 * b := by
    simpa using Nat.mul_le_mul_left (k ^ 3) (Nat.succ_le_of_lt hb)
  have hkn : k ≤ n := by nlinarith
  have hbn : b ≤ n := by
    have hkp : 1 ≤ k ^ 3 := (by omega : 1 ≤ k).trans hkpow
    have hmul := Nat.mul_le_mul_right b hkp
    nlinarith
  have hn2 : 2 ≤ n := hk.trans hkn
  have hCpos : 0 < (n - 2).choose (k - 2) := Nat.choose_pos (by omega)
  have hupper := choose_difference_upper (n - b) (b - 1) (k - 2)
  have he1 : n - b + (b - 1) = n - 1 := by omega
  have he2 : k - 2 + 1 = k - 1 := by omega
  have he3 : n - 1 - 1 = n - 2 := by omega
  rw [he1, he2, he3] at hupper
  have hupper' : (n - 1).choose (k - 1) ≤
      (n - b).choose (k - 1) + b * (n - 2).choose (k - 2) := by
    exact hupper.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (Nat.sub_le b 1)) _)
  have hratio := Nat.add_one_mul_choose_eq (n - 2) (k - 2)
  have hn1 : n - 2 + 1 = n - 1 := by omega
  rw [hn1, he2] at hratio
  have hcoeff : (k ^ 2 * b + b) * (k - 1) ≤ 2 * (k ^ 3 * b) := by
    calc
      (k ^ 2 * b + b) * (k - 1) ≤ (k ^ 2 * b + b) * k :=
        Nat.mul_le_mul_left _ (Nat.sub_le k 1)
      _ = k ^ 3 * b + k * b := by ring
      _ ≤ k ^ 3 * b + k ^ 3 * b :=
        Nat.add_le_add_left (Nat.mul_le_mul_right b hkpow) _
      _ = 2 * (k ^ 3 * b) := by omega
  have hp : 0 < k ^ 3 * b := by positivity
  have hsize : 4 * (k ^ 3 * b) ≤ n := by nlinarith
  have hcoefflt : (k ^ 2 * b + b) * (k - 1) < n - 1 := by omega
  by_contra hnot
  have hsmall : (n - b).choose (k - 1) ≤
      k ^ 2 * b * (n - 2).choose (k - 2) := le_of_not_gt hnot
  have hbig : (n - 1).choose (k - 1) ≤
      (k ^ 2 * b + b) * (n - 2).choose (k - 2) := by
    nlinarith
  have hmul := Nat.mul_le_mul_right (k - 1) hbig
  have hstrict := Nat.mul_lt_mul_of_pos_right hcoefflt hCpos
  nlinarith [hratio]

theorem sparse_cover_size_gt {k b n : ℕ} (hk : 2 ≤ k) (hb : 0 < b)
    (hn : 4 * k ^ 3 * b ≤ n) :
    k * b * (k * b * (n - 2).choose (k - 2)) <
      n.choose k - (n - b).choose k := by
  have hkpow : 1 ≤ k ^ 3 :=
    (by omega : 1 ≤ k).trans (le_self_pow₀ (by omega) (by decide))
  have hbn : b ≤ n := by
    have hmul := Nat.mul_le_mul_right b hkpow
    nlinarith
  have hlow := choose_difference_lower (n - b) b (k - 1)
  have hsum : n - b + b = n := Nat.sub_add_cancel hbn
  have hk1 : k - 1 + 1 = k := by omega
  rw [hsum, hk1] at hlow
  have hbin := sparse_binomial_comparison hk hb hn
  calc
    k * b * (k * b * (n - 2).choose (k - 2)) =
        b * (k ^ 2 * b * (n - 2).choose (k - 2)) := by ring
    _ < b * (n - b).choose (k - 1) := Nat.mul_lt_mul_of_pos_left hbin hb
    _ ≤ n.choose k - (n - b).choose k := hlow

/-- The exact sparse-range matching bound, including the unique extremal family.

This is Lemma 8.1 of the readable manuscript. The proof is induction on the
matching bound, with the numerical step supplied by Pascal telescoping.
-/
theorem sparse_matching_bound_and_equality {k b : ℕ} {V : Finset α}
    {H : Finset (Finset α)} (hk : 2 ≤ k) (hV : IsOn V H)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost b H)
    (hn : 4 * k ^ 3 * b ≤ V.card) :
    H.card ≤ V.card.choose k - (V.card - b).choose k ∧
      (H.card = V.card.choose k - (V.card - b).choose k →
        ∃ S : Finset α, S ⊆ V ∧ S.card = b ∧ H = coverFamily k V S) := by
  induction b generalizing V H with
  | zero =>
    have hH : H = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      have hm : IsMatching ({e} : Finset (Finset α)) := by
        simp [IsMatching, Set.Pairwise]
      have hc := hν {e} (Finset.singleton_subset_iff.mpr he) hm
      simp at hc
    subst H
    constructor
    · simp
    · intro _
      refine ⟨∅, by simp, rfl, ?_⟩
      simp [coverFamily]
  | succ b ih =>
    by_cases hsmall : H.card < V.card.choose k - (V.card - (b + 1)).choose k
    · refine ⟨hsmall.le, ?_⟩
      intro heq
      exact (hsmall.ne heq).elim
    have hlarge : V.card.choose k - (V.card - (b + 1)).choose k ≤ H.card :=
      le_of_not_gt hsmall
    have hcard := (sparse_cover_size_gt hk (Nat.succ_pos b) hn).trans_le hlarge
    obtain ⟨v, hv, hdegree⟩ := exists_degree_gt_of_card_gt
      (k := k) (b := b + 1) (D := k * (b + 1) * (V.card - 2).choose (k - 2))
      (by omega) hV hu hν hcard
    have hn' : 4 * k ^ 3 * b ≤ (V.erase v).card := by
      rw [Finset.card_erase_of_mem hv]
      have hp : 0 < 4 * k ^ 3 := by positivity
      have hexp : 4 * k ^ 3 * (b + 1) = 4 * k ^ 3 * b + 4 * k ^ 3 := by ring
      rw [hexp] at hn
      omega
    have hrec := ih (deleteVertex_on hV v) (deleteVertex_uniform hu v)
      (deleteVertex_matchingNumberAtMost hV hu hν hv hdegree) hn'
    have hdelete := hrec.1
    have hsub : V.card - 1 - b = V.card - (b + 1) := by omega
    rw [Finset.card_erase_of_mem hv, hsub] at hdelete
    have hdeg := degree_le_choose hV hu hv
    have htotal := degree_add_card_deleteVertex H v
    have hn1 : V.card - 1 + 1 = V.card :=
      Nat.sub_add_cancel (Finset.card_pos.mpr ⟨v, hv⟩)
    have hk1 : k - 1 + 1 = k := by omega
    have hpascal := Nat.choose_succ_succ (V.card - 1) (k - 1)
    simp only [Nat.succ_eq_add_one, hn1, hk1] at hpascal
    have hchoose := Nat.choose_le_choose k (Nat.sub_le (V.card - 1) b)
    rw [hsub] at hchoose
    constructor
    · calc
        H.card = degree H v + (deleteVertex H v).card := htotal.symm
        _ ≤ (V.card - 1).choose (k - 1) +
            ((V.card - 1).choose k - (V.card - (b + 1)).choose k) :=
          Nat.add_le_add hdeg hdelete
        _ = V.card.choose k - (V.card - (b + 1)).choose k := by
          rw [← Nat.add_sub_assoc hchoose, ← hpascal]
    · intro heq
      have htotal' : degree H v + (deleteVertex H v).card =
          (V.card - 1).choose (k - 1) +
            ((V.card - 1).choose k - (V.card - (b + 1)).choose k) := by
        rw [htotal, heq, hpascal, Nat.add_sub_assoc hchoose]
      have hdeleteEq : (deleteVertex H v).card =
          (V.erase v).card.choose k - ((V.erase v).card - b).choose k := by
        rw [Finset.card_erase_of_mem hv, hsub]
        linarith only [hdeg, hdelete, htotal']
      obtain ⟨S, hSV, hScard, hfamily⟩ := hrec.2 hdeleteEq
      have hvS : v ∉ S := by
        intro hvs
        exact (Finset.mem_erase.mp (hSV hvs)).1 rfl
      have hSV' : insert v S ⊆ V :=
        Finset.insert_subset hv (hSV.trans (Finset.erase_subset v V))
      have hScard' : (insert v S).card = b + 1 := by
        rw [Finset.card_insert_of_notMem hvS, hScard]
      refine ⟨insert v S, hSV', hScard', ?_⟩
      have hcontained : H ⊆ coverFamily k V (insert v S) := by
        intro e he
        apply mem_coverFamily_iff.mpr
        refine ⟨hV e he, hu e he, ?_⟩
        by_cases hve : v ∈ e
        · exact ⟨v, hve, Finset.mem_insert_self v S⟩
        · have heDel : e ∈ deleteVertex H v := Finset.mem_filter.mpr ⟨he, hve⟩
          rw [hfamily] at heDel
          obtain ⟨w, hwe, hwS⟩ := (mem_coverFamily_iff.mp heDel).2.2
          exact ⟨w, hwe, Finset.mem_insert_of_mem hwS⟩
      apply Finset.eq_of_subset_of_card_le hcontained
      rw [card_coverFamily k hSV', hScard', heq]

theorem sparse_matching_bound {k b : ℕ} {V : Finset α} {H : Finset (Finset α)}
    (hk : 2 ≤ k) (hV : IsOn V H) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost b H) (hn : 4 * k ^ 3 * b ≤ V.card) :
    H.card ≤ V.card.choose k - (V.card - b).choose k :=
  (sparse_matching_bound_and_equality hk hV hu hν hn).1

theorem sparse_matching_equality_iff {k b : ℕ} {V : Finset α}
    {H : Finset (Finset α)} (hk : 2 ≤ k) (hV : IsOn V H)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost b H)
    (hn : 4 * k ^ 3 * b ≤ V.card) :
    H.card = V.card.choose k - (V.card - b).choose k ↔
      ∃ S : Finset α, S ⊆ V ∧ S.card = b ∧ H = coverFamily k V S := by
  constructor
  · exact (sparse_matching_bound_and_equality hk hV hu hν hn).2
  · rintro ⟨S, hSV, hScard, rfl⟩
    rw [card_coverFamily k hSV, hScard]

end SharpTailMatching.Matching
