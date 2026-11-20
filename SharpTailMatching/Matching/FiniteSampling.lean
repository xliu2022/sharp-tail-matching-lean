/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Exact finite averages for the clique sampling argument. Uniform marginals are
proved by transitive finite group actions; no independence between blocks of
one sampled disjoint collection is assumed.
-/
module

public import SharpTailMatching.Matching.Bipartite
public import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

noncomputable def finiteAverage {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

theorem finiteAverage_congr {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a = g a) : finiteAverage f = finiteAverage g := by
  unfold finiteAverage
  congr 1
  exact Finset.sum_congr rfl (fun a _ ↦ h a)

theorem finiteAverage_le {A : Type*} [Fintype A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ ↦ h a)) (Nat.cast_nonneg _)

theorem finiteAverage_const {A : Type*} [Fintype A] [Nonempty A] (c : ℝ) :
    finiteAverage (fun _a : A ↦ c) = c := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hcard]

theorem eq_const_of_finiteAverage_eq {A : Type*} [Fintype A] [Nonempty A]
    {f : A → ℝ} {c : ℝ} (hle : ∀ a, f a ≤ c) (heq : finiteAverage f = c) :
    ∀ a, f a = c := by
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, f a) = ∑ _a : A, c := by
    have h := (div_eq_iff hcard).mp heq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    nlinarith only [h]
  exact fun a ↦ (Finset.sum_eq_sum_iff_of_le (fun b _ ↦ hle b)).mp hsum a (Finset.mem_univ a)

theorem finiteAverage_sum {A I : Type*} [Fintype A] [Fintype I] (f : A → I → ℝ) :
    finiteAverage (fun a ↦ ∑ i, f a i) = ∑ i, finiteAverage (fun a ↦ f a i) := by
  simp only [finiteAverage]
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_add {A : Type*} [Fintype A] (f g : A → ℝ) :
    finiteAverage (fun a ↦ f a + g a) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_sub {A : Type*} [Fintype A] (f g : A → ℝ) :
    finiteAverage (fun a ↦ f a - g a) = finiteAverage f - finiteAverage g := by
  simp only [finiteAverage, Finset.sum_sub_distrib, sub_div]

theorem finiteAverage_mul_const {A : Type*} [Fintype A] (f : A → ℝ) (c : ℝ) :
    finiteAverage (fun a ↦ f a * c) = finiteAverage f * c := by
  simp only [finiteAverage, ← Finset.sum_mul]
  ring

theorem finiteAverage_product {A B : Type*} [Fintype A] [Fintype B]
    (f : A × B → ℝ) :
    finiteAverage f = finiteAverage (fun a ↦ finiteAverage (fun b ↦ f (a, b))) := by
  simp only [finiteAverage, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type,
    ← Finset.sum_div]
  ring

theorem finiteAverage_comm {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℝ) :
    finiteAverage (fun a ↦ finiteAverage (f a)) =
      finiteAverage (fun b ↦ finiteAverage (fun a ↦ f a b)) := by
  simp only [finiteAverage, ← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

theorem finiteAverage_indicator {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    finiteAverage (fun a ↦ if p a then (1 : ℝ) else 0) =
      ((Finset.univ.filter p).card : ℝ) / Fintype.card A := by
  simp only [finiteAverage, Finset.sum_boole]

/-- Averaging over a transitive finite group action gives the uniform average
over the orbit. This proves exact marginal distributions for sampled blocks. -/
theorem finiteAverage_transitive_action {G A : Type*} [Fintype G] [Group G]
    [Fintype A] [MulAction G A] [MulAction.IsPretransitive G A]
    (f : A → ℝ) (x : A) : finiteAverage (fun g : G ↦ f (g • x)) = finiteAverage f := by
  classical
  have hconst : ∀ y : A, (∑ g : G, f (g • y)) = ∑ g : G, f (g • x) := by
    intro y
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G x y
    have heq := Equiv.sum_comp (Equiv.mulRight h) (fun g : G ↦ f (g • x))
    change (∑ g : G, f ((g * h) • x)) = _ at heq
    simpa only [mul_smul] using heq
  have hinner : ∀ g : G, (∑ y : A, f (g • y)) = ∑ y : A, f y := by
    intro g
    exact Equiv.sum_comp (MulAction.toPerm g) f
  have hsum : (Fintype.card A : ℝ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℝ) * ∑ y : A, f y := by
    calc
      (Fintype.card A : ℝ) * (∑ g : G, f (g • x)) = ∑ _y : A, ∑ g : G, f (g • x) := by simp
      _ = ∑ y : A, ∑ g : G, f (g • y) := by
        apply Finset.sum_congr rfl
        intro y _
        exact (hconst y).symm
      _ = ∑ g : G, ∑ y : A, f (g • y) := Finset.sum_comm
      _ = (Fintype.card G : ℝ) * ∑ y : A, f y := by simp only [hinner]; simp
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    have : Nonempty A := ⟨x⟩
    exact_mod_cast Fintype.card_ne_zero
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  apply (div_eq_div_iff hG hA).mpr
  nlinarith only [hsum]

theorem finiteAverage_two_transitive_actions {G K A B : Type*}
    [Fintype G] [Group G] [Fintype K] [Group K]
    [Fintype A] [Fintype B] [MulAction G A] [MulAction K B]
    [MulAction.IsPretransitive G A] [MulAction.IsPretransitive K B]
    (f : A → B → ℝ) (x : A) (y : B) :
    finiteAverage (fun p : G × K ↦ f (p.1 • x) (p.2 • y)) =
      finiteAverage (fun p : A × B ↦ f p.1 p.2) := by
  rw [finiteAverage_product]
  calc
    finiteAverage (fun g : G ↦ finiteAverage (fun h : K ↦ f (g • x) (h • y))) =
        finiteAverage (fun g : G ↦ finiteAverage (fun b : B ↦ f (g • x) b)) := by
      apply finiteAverage_congr
      intro g
      exact finiteAverage_transitive_action (f (g • x)) y
    _ = finiteAverage (fun b : B ↦ finiteAverage (fun g : G ↦ f (g • x) b)) :=
      finiteAverage_comm (fun g : G ↦ fun b : B ↦ f (g • x) b)
    _ = finiteAverage (fun b : B ↦ finiteAverage (fun a : A ↦ f a b)) := by
      apply finiteAverage_congr
      intro b
      exact finiteAverage_transitive_action (fun a ↦ f a b) x
    _ = finiteAverage (fun a : A ↦ finiteAverage (fun b : B ↦ f a b)) :=
      (finiteAverage_comm f).symm
    _ = finiteAverage (fun p : A × B ↦ f p.1 p.2) :=
      (finiteAverage_product (fun p : A × B ↦ f p.1 p.2)).symm

/-- A fixed-size block moved by a uniform permutation is a uniform fixed-size
subset. The formula is an identity of finite sums. -/
theorem finiteAverage_permuted_subset {A : Type*} [Fintype A] [DecidableEq A]
    {r : ℕ} (B : Set.powersetCard A r) (f : Finset A → ℝ) :
    finiteAverage (fun π : Equiv.Perm A ↦ f ((π • B : Set.powersetCard A r) : Finset A)) =
      (∑ C ∈ (Finset.univ : Finset A).powersetCard r, f C) /
        ((Fintype.card A).choose r : ℝ) := by
  classical
  have := Set.powersetCard.isPretransitive (α := A) (n := r)
  have h := finiteAverage_transitive_action (G := Equiv.Perm A)
    (fun C : Set.powersetCard A r ↦ f C) B
  have hcard : Fintype.card (Set.powersetCard A r) = (Fintype.card A).choose r := by
    simpa only [Nat.card_eq_fintype_card] using (Set.powersetCard.card A r)
  have hsum : (∑ C ∈ (Finset.univ : Finset A).powersetCard r, f C) =
      ∑ C : Set.powersetCard A r, f C := by
    exact Finset.sum_subtype _ (fun C ↦ by simp) f
  simpa only [finiteAverage, hcard, hsum] using h

end SharpTailMatching.Matching
