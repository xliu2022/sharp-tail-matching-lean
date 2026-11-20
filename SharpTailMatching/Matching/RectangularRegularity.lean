/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Weak regularity for k-ary functions: rectangular witnesses and their common
vertex refinement. The weighted energy increment uses no equipartition or
unformalized graph-regularity theorem.
-/
module

public import SharpTailMatching.Matching.RegularityEnergy
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [Fintype α] [Fintype I] [DecidableEq α] [DecidableEq I]

def tupleLabel {k : ℕ} (c : α → I) (x : Fin k → α) : Fin k → I := fun r ↦ c (x r)

omit [Fintype I] [DecidableEq α] in
theorem tuple_labelFiber {k : ℕ} (c : α → I) (a : Fin k → I) :
    labelFiber (tupleLabel c) a = Fintype.piFinset (fun r ↦ labelFiber c (a r)) := by
  ext x
  simp only [labelFiber, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    funext_iff, tupleLabel]

def IsRectRegular {k : ℕ} (c : α → I) (f : (Fin k → α) → ℝ) (ε : ℝ) (a : Fin k → I) : Prop :=
  ∀ W : Fin k → Finset α,
    (∀ r, W r ⊆ labelFiber c (a r)) →
    (∀ r, ε * (labelFiber c (a r)).card ≤ (W r).card) →
    |finiteSetMean f (Fintype.piFinset W) - labelMean (tupleLabel c) f a| < ε

noncomputable def irregularCells {k : ℕ} (c : α → I) (f : (Fin k → α) → ℝ) (ε : ℝ) :
    Finset (Fin k → I) := by
  classical
  exact Finset.univ.filter fun a ↦ ¬IsRectRegular c f ε a

noncomputable def irregularMass {k : ℕ} (c : α → I) (f : (Fin k → α) → ℝ) (ε : ℝ) : ℝ :=
  ∑ a ∈ irregularCells c f ε, ((labelFiber (tupleLabel c) a).card : ℝ)

omit [DecidableEq α] in
theorem exists_rectangular_witness {k : ℕ} {c : α → I} {f : (Fin k → α) → ℝ}
    {ε : ℝ} {a : Fin k → I} (ha : a ∈ irregularCells c f ε) :
    ∃ W : Fin k → Finset α,
      (∀ r, W r ⊆ labelFiber c (a r)) ∧
      (∀ r, ε * (labelFiber c (a r)).card ≤ (W r).card) ∧
      ε ≤ |finiteSetMean f (Fintype.piFinset W) - labelMean (tupleLabel c) f a| := by
  classical
  have hnot := (Finset.mem_filter.mp ha).2
  obtain ⟨W, hW⟩ := not_forall.mp hnot
  obtain ⟨hsub, hrest⟩ := not_imp.mp hW
  obtain ⟨hsize, hdev⟩ := not_imp.mp hrest
  exact ⟨W, hsub, hsize, le_of_not_gt hdev⟩

omit [Fintype I] [DecidableEq α] in
theorem rectangle_relative_card {k : ℕ} (c : α → I) (a : Fin k → I)
    (W : Fin k → Finset α) {ε : ℝ} (hε : 0 ≤ ε)
    (hsize : ∀ r, ε * (labelFiber c (a r)).card ≤ (W r).card) :
    ε ^ k * (labelFiber (tupleLabel c) a).card ≤ (Fintype.piFinset W).card := by
  have hprod := Finset.prod_le_prod₀
    (fun r (_ : r ∈ (Finset.univ : Finset (Fin k))) ↦
      mul_nonneg hε (Nat.cast_nonneg (labelFiber c (a r)).card))
    (fun r _ ↦ hsize r)
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    tuple_labelFiber, Fintype.card_piFinset, Nat.cast_prod] using hprod

def witnessRefinement {k : ℕ} (c : α → I) (W : (Fin k → I) → Fin k → Finset α) (x : α) :
    I × ((Fin k → I) × Fin k → Bool) :=
  (c x, fun p ↦ decide (x ∈ W p.1 p.2))

omit [Fintype α] [Fintype I] [DecidableEq I] in
theorem witness_rectangle_saturated {k : ℕ} (c : α → I)
    (W : (Fin k → I) → Fin k → Finset α) (a : Fin k → I) :
    ∀ x ∈ Fintype.piFinset (W a), ∀ y,
      tupleLabel (witnessRefinement c W) x = tupleLabel (witnessRefinement c W) y →
        y ∈ Fintype.piFinset (W a) := by
  intro x hx y hxy
  apply Fintype.mem_piFinset.mpr
  intro r
  have hxr := Fintype.mem_piFinset.mp hx r
  have hlabel := congrFun hxy r
  have hbit := congrFun (congrArg Prod.snd hlabel) (a, r)
  change decide (x r ∈ W a r) = decide (y r ∈ W a r) at hbit
  apply of_decide_eq_true
  rw [← hbit]
  exact decide_eq_true hxr

/-- Simultaneously refine by every bad-cell rectangle. The energy gain is
bounded below by `ε^(k+2)` times the total mass of irregular cells. -/
theorem exists_witness_refinement {k : ℕ} (c : α → I) (f : (Fin k → α) → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ W : (Fin k → I) → Fin k → Finset α,
      ε ^ (k + 2) * irregularMass c f ε ≤
        partitionEnergy (tupleLabel (witnessRefinement c W)) f - partitionEnergy (tupleLabel c) f := by
  classical
  let B := irregularCells c f ε
  have hw : ∀ a ∈ B, ∃ W : Fin k → Finset α,
      (∀ r, W r ⊆ labelFiber c (a r)) ∧
      (∀ r, ε * (labelFiber c (a r)).card ≤ (W r).card) ∧
      ε ≤ |finiteSetMean f (Fintype.piFinset W) - labelMean (tupleLabel c) f a| := by
    intro a ha
    exact exists_rectangular_witness ha
  let W (a : Fin k → I) : Fin k → Finset α :=
    if ha : a ∈ B then (hw a ha).choose else fun r ↦ labelFiber c (a r)
  have hW : ∀ a ∈ B,
      (∀ r, W a r ⊆ labelFiber c (a r)) ∧
      (∀ r, ε * (labelFiber c (a r)).card ≤ (W a r).card) ∧
      ε ≤ |finiteSetMean f (Fintype.piFinset (W a)) - labelMean (tupleLabel c) f a| := by
    intro a ha
    simpa only [W, dite_eq_left ha] using (hw a ha).choose_spec
  let g (a : Fin k → I × ((Fin k → I) × Fin k → Bool)) : Fin k → I := fun r ↦ (a r).1
  have hrefine : ∀ x : Fin k → α, g (tupleLabel (witnessRefinement c W) x) = tupleLabel c x :=
    fun _ ↦ rfl
  have hsub : ∀ a ∈ B, Fintype.piFinset (W a) ⊆ labelFiber (tupleLabel c) a := by
    intro a ha
    rw [tuple_labelFiber]
    exact Fintype.piFinset_subset _ _ (hW a ha).1
  have hsize : ∀ a ∈ B, ε ^ k * (labelFiber (tupleLabel c) a).card ≤
      (Fintype.piFinset (W a)).card := by
    intro a ha
    exact rectangle_relative_card c a (W a) hε (hW a ha).2.1
  have h := partitionEnergy_increment_of_witnesses (tupleLabel c)
    (tupleLabel (witnessRefinement c W)) g hrefine f B (fun a ↦ Fintype.piFinset (W a))
    hε hsub (fun a _ ↦ witness_rectangle_saturated c W a) (fun a ha ↦ (hW a ha).2.2) hsize
  refine ⟨W, ?_⟩
  simpa only [pow_add, irregularMass, B] using h

end SharpTailMatching.Matching
