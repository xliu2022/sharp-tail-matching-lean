/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Translate a finite uniform hypergraph to its bounded k-ary indicator, and
extract robust crossing edges from regular dense cells.
-/
module

public import SharpTailMatching.Matching.WeakRegularity
public import SharpTailMatching.Matching.Basic

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I]

def tupleEdge {k : ℕ} (x : Fin k → α) : Finset α := Finset.univ.image x

noncomputable def tupleIndicator {k : ℕ} (H : Finset (Finset α)) (x : Fin k → α) : ℝ :=
  if tupleEdge x ∈ H then 1 else 0

theorem tupleIndicator_bounds {k : ℕ} (H : Finset (Finset α)) (x : Fin k → α) :
    0 ≤ tupleIndicator H x ∧ tupleIndicator H x ≤ 1 := by
  unfold tupleIndicator
  split_ifs <;> norm_num

theorem exists_tuple_of_card {k : ℕ} {e : Finset α} (he : e.card = k) :
    ∃ x : Fin k → α, Function.Injective x ∧ tupleEdge x = e := by
  classical
  let E : Fin k ≃ e := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe, he])
  let x : Fin k → α := fun r ↦ (E r).val
  refine ⟨x, ?_, ?_⟩
  · intro r s hrs
    exact E.injective (Subtype.ext hrs)
  · ext v
    constructor
    · intro hv
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
      exact (E r).property
    · intro hv
      refine Finset.mem_image.mpr ⟨E.symm ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
      simp only [x, Equiv.apply_symm_apply]

theorem tupleEdge_image {k : ℕ} (c : α → I) (x : Fin k → α) :
    (tupleEdge x).image c = tupleEdge (tupleLabel c x) := by
  simp only [tupleEdge, Finset.image_image, Function.comp_def]
  rfl

def IsCrossing (c : α → I) (e : Finset α) : Prop := Set.InjOn c e

omit [DecidableEq I] in
theorem tupleEdge_isCrossing {k : ℕ} {c : α → I} {a : Fin k → I} {x : Fin k → α}
    (ha : Function.Injective a) (hx : tupleLabel c x = a) : IsCrossing c (tupleEdge x) := by
  intro v hv w hw hvw
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hw
  have hrs : r = s := ha (by
    have hr := congrFun hx r
    have hs := congrFun hx s
    change c (x r) = a r at hr
    change c (x s) = a s at hs
    exact hr.symm.trans (hvw.trans hs))
  exact hrs ▸ rfl

omit [DecidableEq α] in
theorem crossing_filter_card {c : α → I} {e : Finset α} (he : IsCrossing c e) (i : I) :
    (e.filter fun v ↦ c v = i).card = if i ∈ e.image c then 1 else 0 := by
  by_cases hi : i ∈ e.image c
  · rw [ite_eq_left hi]
    obtain ⟨v, hv, hvi⟩ := Finset.mem_image.mp hi
    apply Finset.card_eq_one.mpr
    refine ⟨v, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hw
      exact he hw.1 hv (hw.2.trans hvi.symm)
    · rintro rfl
      exact ⟨hv, hvi⟩
  · rw [ite_eq_right hi, Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro v hv
    obtain ⟨hve, hvi⟩ := Finset.mem_filter.mp hv
    exact hi (Finset.mem_image.mpr ⟨v, hve, hvi⟩)

variable [Fintype α] [Fintype I]

theorem labelMean_pos_nonempty {Ω J : Type*} [Fintype Ω] [DecidableEq J]
    {c : Ω → J} {f : Ω → ℝ} {j : J} (h : 0 < labelMean c f j) :
    (labelFiber c j).Nonempty := by
  by_contra hn
  have heq := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [labelMean, finiteSetMean, heq, Finset.sum_empty, Finset.card_empty,
    Nat.cast_zero, div_zero, lt_self_iff_false] at h

omit [Fintype I] in
/-- Positive density in every sufficiently large subrectangle supplies the
next crossing edge for greedy matching rounding. -/
theorem exists_edge_of_regular_cell {k : ℕ} {c : α → I} {H : Finset (Finset α)}
    {a : Fin k → I} {ε d : ℝ} (ha : Function.Injective a)
    (hregular : IsRectRegular c (tupleIndicator H) ε a)
    (hdensity : d ≤ labelMean (tupleLabel c) (tupleIndicator H) a) (hd : ε < d)
    (U : Finset α) (hsize : ∀ r,
      ε * (labelFiber c (a r)).card ≤ (U ∩ labelFiber c (a r)).card) :
    ∃ e ∈ H, e ⊆ U ∧ IsCrossing c e ∧ e.image c = tupleEdge a := by
  let W := fun r ↦ U ∩ labelFiber c (a r)
  have hdev := hregular W (fun _ ↦ Finset.inter_subset_right) hsize
  have hmean : 0 < finiteSetMean (tupleIndicator H) (Fintype.piFinset W) := by
    have hlow := (abs_lt.mp hdev).1
    linarith only [hlow, hdensity, hd]
  have hex : ∃ x ∈ Fintype.piFinset W, tupleEdge x ∈ H := by
    by_contra! hn
    have hzero : (∑ x ∈ Fintype.piFinset W, tupleIndicator H x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      exact ite_eq_right (hn x hx)
    have hzero' : finiteSetMean (tupleIndicator H) (Fintype.piFinset W) = 0 := by
      simp only [finiteSetMean, hzero, zero_div]
    linarith only [hmean, hzero']
  obtain ⟨x, hx, hxH⟩ := hex
  have hx' := Fintype.mem_piFinset.mp hx
  have hlabel : tupleLabel c x = a := by
    funext r
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp (hx' r)).2).2
  refine ⟨tupleEdge x, hxH, ?_, tupleEdge_isCrossing ha hlabel, ?_⟩
  · intro v hv
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_inter.mp (hx' r)).1
  · rw [tupleEdge_image, hlabel]

noncomputable def reducedFamily (k : ℕ) (c : α → I) (H : Finset (Finset α)) (ε d : ℝ) :
    Finset (Finset I) := by
  classical
  exact (Finset.univ.powersetCard k).filter fun e ↦ ∃ a : Fin k → I,
    Function.Injective a ∧ tupleEdge a = e ∧ IsRectRegular c (tupleIndicator H) ε a ∧
      d ≤ labelMean (tupleLabel c) (tupleIndicator H) a

theorem reducedFamily_uniform (k : ℕ) (c : α → I) (H : Finset (Finset α)) (ε d : ℝ) :
    IsUniform k (reducedFamily k c H ε d) := by
  classical
  intro e he
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

theorem reduced_edge_witness {k : ℕ} {c : α → I} {H : Finset (Finset α)} {ε d : ℝ}
    {e : Finset I} (he : e ∈ reducedFamily k c H ε d) :
    ∃ a : Fin k → I, Function.Injective a ∧ tupleEdge a = e ∧
      IsRectRegular c (tupleIndicator H) ε a ∧ d ≤ labelMean (tupleLabel c) (tupleIndicator H) a := by
  classical
  exact (Finset.mem_filter.mp he).2

theorem reduced_edge_robust {k : ℕ} {c : α → I} {H : Finset (Finset α)} {ε d : ℝ}
    (hd : ε < d) {e : Finset I} (he : e ∈ reducedFamily k c H ε d)
    (U : Finset α) (hsize : ∀ i ∈ e,
      ε * (labelFiber c i).card ≤ (U ∩ labelFiber c i).card) :
    ∃ E ∈ H, E ⊆ U ∧ IsCrossing c E ∧ E.image c = e := by
  obtain ⟨a, ha, heq, hregular, hdensity⟩ := reduced_edge_witness he
  have hsize' : ∀ r, ε * (labelFiber c (a r)).card ≤ (U ∩ labelFiber c (a r)).card := by
    intro r
    apply hsize
    rw [← heq]
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩
  simpa only [heq] using exists_edge_of_regular_cell ha hregular hdensity hd U hsize'

theorem reduced_edge_positive_classes {k : ℕ} {c : α → I} {H : Finset (Finset α)} {ε d : ℝ}
    (hd : 0 < d) {e : Finset I} (he : e ∈ reducedFamily k c H ε d) :
    ∀ i ∈ e, 0 < (labelFiber c i).card := by
  obtain ⟨a, _, heq, _, hdensity⟩ := reduced_edge_witness he
  obtain ⟨x, hx⟩ := labelMean_pos_nonempty (hd.trans_le hdensity)
  intro i hi
  rw [← heq] at hi
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hi
  apply Finset.card_pos.mpr
  refine ⟨x r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact congrFun (Finset.mem_filter.mp hx).2 r

end SharpTailMatching.Matching
