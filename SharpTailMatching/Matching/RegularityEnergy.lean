/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite conditional averages and the exact energy increment identity. These
lemmas are independent of graph arity and form the core of weak hypergraph
regularity on arbitrary vertex partitions.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

noncomputable def finiteSetMean (f : Ω → ℝ) (S : Finset Ω) : ℝ :=
  (∑ x ∈ S, f x) / S.card

omit [Fintype Ω] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem card_mul_finiteSetMean (f : Ω → ℝ) (S : Finset Ω) :
    (S.card : ℝ) * finiteSetMean f S = ∑ x ∈ S, f x := by
  by_cases hS : S.Nonempty
  · have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
    exact mul_div_cancel₀ _ hcard
  · have heq := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [heq, finiteSetMean]

def labelFiber (c : Ω → I) (i : I) : Finset Ω :=
  Finset.univ.filter fun x ↦ c x = i

noncomputable def labelMean (c : Ω → I) (f : Ω → ℝ) (i : I) : ℝ :=
  finiteSetMean f (labelFiber c i)

noncomputable def conditionalAverage (c : Ω → I) (f : Ω → ℝ) (x : Ω) : ℝ :=
  labelMean c f (c x)

noncomputable def partitionEnergy (c : Ω → I) (f : Ω → ℝ) : ℝ :=
  ∑ x, conditionalAverage c f x ^ 2

omit [Fintype J] [DecidableEq J] in
theorem sum_labelFiber (c : Ω → I) (f : Ω → ℝ) :
    (∑ i, ∑ x ∈ labelFiber c i, f x) = ∑ x, f x := by
  simp only [labelFiber, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Fintype J] [DecidableEq J] in
theorem sum_mul_conditionalAverage (c : Ω → I) (f : Ω → ℝ) (g : I → ℝ) :
    (∑ x, f x * g (c x)) = ∑ x, conditionalAverage c f x * g (c x) := by
  rw [← sum_labelFiber c (fun x ↦ f x * g (c x)),
    ← sum_labelFiber c (fun x ↦ conditionalAverage c f x * g (c x))]
  apply Finset.sum_congr rfl
  intro i _
  have hf : (∑ x ∈ labelFiber c i, f x * g (c x)) =
      (∑ x ∈ labelFiber c i, f x) * g i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hg : (∑ x ∈ labelFiber c i, conditionalAverage c f x * g (c x)) =
      (labelFiber c i).card * labelMean c f i * g i := by
    have hconst : ∀ x ∈ labelFiber c i, conditionalAverage c f x * g (c x) =
        labelMean c f i * g i := by
      intro x hx
      simp only [conditionalAverage, (Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hf, hg, labelMean, card_mul_finiteSetMean]

omit [Fintype J] [DecidableEq J] in
theorem sum_mul_average_eq_energy (c : Ω → I) (f : Ω → ℝ) :
    (∑ x, f x * conditionalAverage c f x) = partitionEnergy c f := by
  have h := sum_mul_conditionalAverage c f (labelMean c f)
  simpa only [conditionalAverage, partitionEnergy, pow_two] using h

theorem average_cross_refinement (c : Ω → I) (c' : Ω → J) (g : J → I)
    (hrefine : ∀ x, g (c' x) = c x) (f : Ω → ℝ) :
    (∑ x, conditionalAverage c' f x * conditionalAverage c f x) = partitionEnergy c f := by
  have h := sum_mul_conditionalAverage c' f (fun j ↦ labelMean c f (g j))
  simp only [hrefine] at h
  exact h.symm.trans (sum_mul_average_eq_energy c f)

/-- The energy increment is exactly a sum of squares, including empty cells. -/
theorem partitionEnergy_refinement_identity (c : Ω → I) (c' : Ω → J) (g : J → I)
    (hrefine : ∀ x, g (c' x) = c x) (f : Ω → ℝ) :
    (∑ x, (conditionalAverage c' f x - conditionalAverage c f x) ^ 2) =
      partitionEnergy c' f - partitionEnergy c f := by
  have hcross := average_cross_refinement c c' g hrefine f
  have hexpand : (∑ x, (conditionalAverage c' f x - conditionalAverage c f x) ^ 2) =
      partitionEnergy c' f - 2 * (∑ x, conditionalAverage c' f x * conditionalAverage c f x) +
        partitionEnergy c f := by
    simp only [partitionEnergy, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hexpand, hcross]
  ring

theorem partitionEnergy_mono (c : Ω → I) (c' : Ω → J) (g : J → I)
    (hrefine : ∀ x, g (c' x) = c x) (f : Ω → ℝ) :
    partitionEnergy c f ≤ partitionEnergy c' f := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset Ω))
    (fun x _ ↦ sq_nonneg (conditionalAverage c' f x - conditionalAverage c f x))
  rw [partitionEnergy_refinement_identity c c' g hrefine] at h
  exact sub_nonneg.mp h

omit [Fintype J] [DecidableEq J] in
theorem partitionEnergy_le_sum_sq (c : Ω → I) (f : Ω → ℝ) :
    partitionEnergy c f ≤ ∑ x, f x ^ 2 := by
  have hcross := sum_mul_average_eq_energy c f
  have hnonneg := Finset.sum_nonneg (s := (Finset.univ : Finset Ω))
    (fun x _ ↦ sq_nonneg (f x - conditionalAverage c f x))
  have hexpand : (∑ x, (f x - conditionalAverage c f x) ^ 2) =
      (∑ x, f x ^ 2) - 2 * (∑ x, f x * conditionalAverage c f x) + partitionEnergy c f := by
    simp only [partitionEnergy, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hexpand, hcross] at hnonneg
  linarith only [hnonneg]

omit [Fintype J] [DecidableEq J] in
theorem partitionEnergy_le_card (c : Ω → I) (f : Ω → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : partitionEnergy c f ≤ Fintype.card Ω := by
  calc
    partitionEnergy c f ≤ ∑ x, f x ^ 2 := partitionEnergy_le_sum_sq c f
    _ ≤ ∑ _x : Ω, (1 : ℝ) := Finset.sum_le_sum (fun x _ ↦ by nlinarith only [hf x])
    _ = Fintype.card Ω := by simp

variable [DecidableEq Ω]

omit [Fintype J] [DecidableEq J] [DecidableEq Ω] in
/-- A union of label classes has the same sum before and after averaging. -/
theorem sum_conditionalAverage_of_saturated (c : Ω → I) (f : Ω → ℝ) (R : Finset Ω)
    (hsaturated : ∀ x ∈ R, ∀ y, c x = c y → y ∈ R) :
    (∑ x ∈ R, conditionalAverage c f x) = ∑ x ∈ R, f x := by
  let S := R.image c
  have hR : Finset.univ.filter (fun x ↦ c x ∈ S) = R := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hx
      exact hsaturated y hy x heq
    · intro hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have h := sum_mul_conditionalAverage c f (fun i ↦ if i ∈ S then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter, hR] at h
  exact h.symm

omit [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq Ω] in
theorem sum_conditionalAverage_on_cell (c : Ω → I) (f : Ω → ℝ) (i : I) (R : Finset Ω)
    (hsub : R ⊆ labelFiber c i) :
    (∑ x ∈ R, conditionalAverage c f x) = (R.card : ℝ) * labelMean c f i := by
  have hconst : ∀ x ∈ R, conditionalAverage c f x = labelMean c f i := by
    intro x hx
    simp only [conditionalAverage, (Finset.mem_filter.mp (hsub hx)).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

omit [Fintype I] [DecidableEq Ω] in
/-- A measurable witness whose mean changes by at least `ε` contributes at
least `|R| ε²` to the squared error on its original cell. -/
theorem cell_error_lower_of_witness (c : Ω → I) (c' : Ω → J) (f : Ω → ℝ)
    (i : I) (R : Finset Ω) {ε : ℝ} (hε : 0 ≤ ε)
    (hsub : R ⊆ labelFiber c i)
    (hsaturated : ∀ x ∈ R, ∀ y, c' x = c' y → y ∈ R)
    (hdeviation : ε ≤ |finiteSetMean f R - labelMean c f i|) :
    (R.card : ℝ) * ε ^ 2 ≤
      ∑ x ∈ labelFiber c i, (conditionalAverage c' f x - conditionalAverage c f x) ^ 2 := by
  by_cases hR : R.Nonempty
  · have hcard : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
    let δ := fun x ↦ conditionalAverage c' f x - conditionalAverage c f x
    have hsum : (∑ x ∈ R, δ x) = (R.card : ℝ) * (finiteSetMean f R - labelMean c f i) := by
      simp only [δ, Finset.sum_sub_distrib]
      rw [sum_conditionalAverage_of_saturated c' f R hsaturated,
        sum_conditionalAverage_on_cell c f i R hsub, mul_sub, card_mul_finiteSetMean]
    have hCS : (∑ x ∈ R, δ x) ^ 2 ≤ (R.card : ℝ) * ∑ x ∈ R, δ x ^ 2 := by
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq R (fun _ ↦ (1 : ℝ)) δ)
    have hsubset : (∑ x ∈ R, δ x ^ 2) ≤ ∑ x ∈ labelFiber c i, δ x ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ ↦ sq_nonneg (δ x))
    have hsq : ε ^ 2 ≤ (finiteSetMean f R - labelMean c f i) ^ 2 := by
      have h := mul_self_le_mul_self hε hdeviation
      simpa only [← pow_two, sq_abs] using h
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (R.card : ℝ))
    have hCS' := hCS.trans (mul_le_mul_of_nonneg_left hsubset hcard.le)
    rw [hsum, mul_pow] at hCS'
    have hfinal : (R.card : ℝ) * ((R.card : ℝ) * ε ^ 2) ≤
        (R.card : ℝ) * ∑ x ∈ labelFiber c i, δ x ^ 2 := by
      nlinarith only [hmul, hCS']
    exact (mul_le_mul_iff_right₀ hcard).mp hfinal
  · have heq : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    rw [heq, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun x _ ↦ sq_nonneg _)

omit [DecidableEq Ω] in
/-- Summing local witness contributions yields the quantitative global
increment, while every other cell contributes a nonnegative square. -/
theorem partitionEnergy_increment_of_witnesses (c : Ω → I) (c' : Ω → J) (g : J → I)
    (hrefine : ∀ x, g (c' x) = c x) (f : Ω → ℝ) (B : Finset I)
    (R : I → Finset Ω) {ε a : ℝ} (hε : 0 ≤ ε)
    (hsub : ∀ i ∈ B, R i ⊆ labelFiber c i)
    (hsaturated : ∀ i ∈ B, ∀ x ∈ R i, ∀ y, c' x = c' y → y ∈ R i)
    (hdeviation : ∀ i ∈ B, ε ≤ |finiteSetMean f (R i) - labelMean c f i|)
    (hsize : ∀ i ∈ B, a * (labelFiber c i).card ≤ (R i).card) :
    a * ε ^ 2 * (∑ i ∈ B, ((labelFiber c i).card : ℝ)) ≤
      partitionEnergy c' f - partitionEnergy c f := by
  let δ := fun x ↦ conditionalAverage c' f x - conditionalAverage c f x
  have hpoint : ∀ i ∈ B, a * ε ^ 2 * (labelFiber c i).card ≤ ∑ x ∈ labelFiber c i, δ x ^ 2 := by
    intro i hi
    have hlocal := cell_error_lower_of_witness c c' f i (R i) hε
      (hsub i hi) (hsaturated i hi) (hdeviation i hi)
    have hscale := mul_le_mul_of_nonneg_right (hsize i hi) (sq_nonneg ε)
    nlinarith only [hlocal, hscale]
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum] at hsum
  have hglobal : (∑ i ∈ B, ∑ x ∈ labelFiber c i, δ x ^ 2) ≤
      ∑ i : I, ∑ x ∈ labelFiber c i, δ x ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
    intro i _ _
    exact Finset.sum_nonneg (fun x _ ↦ sq_nonneg (δ x))
  have h := hsum.trans hglobal
  rw [sum_labelFiber c, partitionEnergy_refinement_identity c c' g hrefine] at h
  exact h

end SharpTailMatching.Matching
