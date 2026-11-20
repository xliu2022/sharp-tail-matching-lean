/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Fractional matching-cover duality for a finite hypergraph. This specializes
the proved finite minimax theorem; no linear programming duality axiom or
assumed optimizer is used.
-/
module

public import SharpTailMatching.Matching.FiniteMinimax
public import SharpTailMatching.Matching.Basic
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

noncomputable def fractionalDegree (H : Finset (Finset α)) (φ : H → ℝ) (v : α) : ℝ :=
  ∑ e : H, if v ∈ (e : Finset α) then φ e else 0

def IsFractionalMatching (H : Finset (Finset α)) (φ : H → ℝ) : Prop :=
  (∀ e, 0 ≤ φ e) ∧ ∀ v, fractionalDegree H φ v ≤ 1

def IsFractionalCover (H : Finset (Finset α)) (z : α → ℝ) : Prop :=
  (∀ v, 0 ≤ z v) ∧ ∀ e ∈ H, 1 ≤ ∑ v ∈ e, z v

theorem fractional_incidence_sum (H : Finset (Finset α)) (φ : H → ℝ) (z : α → ℝ) :
    (∑ e : H, φ e * ∑ v ∈ (e : Finset α), z v) =
      ∑ v, z v * fractionalDegree H φ v := by
  simp only [fractionalDegree, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, mul_comm]

theorem fractional_weak_duality {H : Finset (Finset α)} {φ : H → ℝ} {z : α → ℝ}
    (hφ : IsFractionalMatching H φ) (hz : IsFractionalCover H z) :
    (∑ e : H, φ e) ≤ ∑ v, z v := by
  calc
    (∑ e : H, φ e) ≤ ∑ e : H, φ e * ∑ v ∈ (e : Finset α), z v := by
      apply Finset.sum_le_sum
      intro e _
      exact le_mul_of_one_le_right (hφ.1 e) (hz.2 e e.property)
    _ = ∑ v, z v * fractionalDegree H φ v := fractional_incidence_sum H φ z
    _ ≤ ∑ v, z v := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_of_le_one_right (hz.1 v) (hφ.2 v)

omit [Fintype α] in
theorem fractionalDegree_div (H : Finset (Finset α)) (p : H → ℝ) (c : ℝ) (v : α) :
    fractionalDegree H (fun e ↦ p e / c) v = fractionalDegree H p v / c := by
  unfold fractionalDegree
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hv : v ∈ (e : Finset α) <;> simp [hv]

noncomputable def incidenceMatrix (H : Finset (Finset α)) (e : H) (v : α) : ℝ :=
  if v ∈ (e : Finset α) then 1 else 0

theorem incidence_row (H : Finset (Finset α)) (q : α → ℝ) (e : H) :
    (∑ v, incidenceMatrix H e v * q v) = ∑ v ∈ (e : Finset α), q v := by
  simp [incidenceMatrix, ite_mul]

omit [Fintype α] in
theorem incidence_column (H : Finset (Finset α)) (p : H → ℝ) (v : α) :
    (∑ e : H, p e * incidenceMatrix H e v) = fractionalDegree H p v := by
  simp only [incidenceMatrix, fractionalDegree, mul_ite, mul_one, mul_zero]

theorem exists_fractional_matching_cover_raw {H : Finset (Finset α)}
    (hH : H.Nonempty) (hedges : ∀ e ∈ H, e.Nonempty) :
    ∃ φ : H → ℝ, ∃ z : α → ℝ, IsFractionalMatching H φ ∧ IsFractionalCover H z ∧
      (∑ e : H, φ e) = ∑ v, z v := by
  classical
  obtain ⟨e₀, he₀⟩ := hH
  obtain ⟨v₀, hv₀⟩ := hedges e₀ he₀
  have : Nonempty H := ⟨⟨e₀, he₀⟩⟩
  have : Nonempty α := ⟨v₀⟩
  obtain ⟨p, hp, q, hq, hcolumns, hrows⟩ := exists_matrix_minimax (incidenceMatrix H)
  let τ := matrixPayoff (incidenceMatrix H) p q
  have hcol : ∀ v, fractionalDegree H p v ≤ τ := by
    intro v
    simpa only [incidence_column] using hcolumns v
  have hrow : ∀ e : H, τ ≤ ∑ v ∈ (e : Finset α), q v := by
    intro e
    simpa only [incidence_row] using hrows e
  have hpPos : ∃ e : H, 0 < p e := by
    by_contra! h
    have hsum := Finset.sum_nonpos (s := (Finset.univ : Finset H)) (fun e _ ↦ h e)
    rw [hp.2] at hsum
    norm_num at hsum
  obtain ⟨e, hpe⟩ := hpPos
  obtain ⟨v, hv⟩ := hedges e e.property
  have hpdeg : p e ≤ fractionalDegree H p v := by
    have h := Finset.single_le_sum (f := fun e' : H ↦ if v ∈ (e' : Finset α) then p e' else 0)
      (fun e' _ ↦ by split_ifs; exact hp.1 e'; exact le_rfl) (Finset.mem_univ e)
    simpa only [fractionalDegree, ite_eq_left hv] using h
  have hτ : 0 < τ := hpe.trans_le (hpdeg.trans (hcol v))
  let φ : H → ℝ := fun e ↦ p e / τ
  let z : α → ℝ := fun v ↦ q v / τ
  have hφ : IsFractionalMatching H φ := by
    refine ⟨fun e ↦ div_nonneg (hp.1 e) hτ.le, ?_⟩
    intro v
    rw [fractionalDegree_div]
    exact (div_le_one hτ).mpr (hcol v)
  have hz : IsFractionalCover H z := by
    refine ⟨fun v ↦ div_nonneg (hq.1 v) hτ.le, ?_⟩
    intro e he
    change 1 ≤ ∑ v ∈ e, q v / τ
    rw [← Finset.sum_div]
    exact (one_le_div hτ).mpr (hrow ⟨e, he⟩)
  refine ⟨φ, z, hφ, hz, ?_⟩
  simp only [φ, z, ← Finset.sum_div, hp.2, hq.2]

omit [DecidableEq α] [Fintype α] in
theorem IsFractionalCover.min_one {H : Finset (Finset α)} {z : α → ℝ}
    (hz : IsFractionalCover H z) : IsFractionalCover H (fun v ↦ min (z v) 1) := by
  refine ⟨fun v ↦ le_min (hz.1 v) (by norm_num), ?_⟩
  intro e he
  by_cases hex : ∃ v ∈ e, 1 ≤ z v
  · obtain ⟨v, hv, hzv⟩ := hex
    have h := Finset.single_le_sum (f := fun v ↦ min (z v) 1)
      (fun v _ ↦ le_min (hz.1 v) (by norm_num)) hv
    simpa only [min_eq_right hzv] using h
  · have hsmall : ∀ v ∈ e, z v ≤ 1 := by
      intro v hv
      exact (lt_of_not_ge (fun h ↦ hex ⟨v, hv, h⟩)).le
    have heq : (∑ v ∈ e, min (z v) 1) = ∑ v ∈ e, z v :=
      Finset.sum_congr rfl (fun v hv ↦ min_eq_left (hsmall v hv))
    rw [heq]
    exact hz.2 e he

/-- Strong finite hypergraph duality, including an actual primal optimizer
and a dual optimizer with every vertex coordinate in `[0,1]`. -/
theorem exists_fractional_matching_cover {H : Finset (Finset α)}
    (hedges : ∀ e ∈ H, e.Nonempty) :
    ∃ φ : H → ℝ, ∃ z : α → ℝ, IsFractionalMatching H φ ∧ IsFractionalCover H z ∧
      (∀ v, z v ≤ 1) ∧ (∑ e : H, φ e) = ∑ v, z v := by
  by_cases hH : H.Nonempty
  · obtain ⟨φ, z, hφ, hz, htotal⟩ := exists_fractional_matching_cover_raw hH hedges
    let z' := fun v ↦ min (z v) 1
    have hz' : IsFractionalCover H z' := hz.min_one
    refine ⟨φ, z', hφ, hz', fun v ↦ min_le_right _ _, le_antisymm (fractional_weak_duality hφ hz') ?_⟩
    rw [htotal]
    exact Finset.sum_le_sum (fun v _ ↦ min_le_left (z v) 1)
  · have heq : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    subst H
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, by simp, by simp⟩
    · simp [IsFractionalMatching, fractionalDegree]
    · simp [IsFractionalCover]

theorem exists_fractional_cover_of_matching_bound {H : Finset (Finset α)} {b : ℝ}
    (hedges : ∀ e ∈ H, e.Nonempty)
    (hbound : ∀ φ : H → ℝ, IsFractionalMatching H φ → (∑ e : H, φ e) ≤ b) :
    ∃ z : α → ℝ, IsFractionalCover H z ∧ (∀ v, z v ≤ 1) ∧ (∑ v, z v) ≤ b := by
  obtain ⟨φ, z, hφ, hz, hz₁, htotal⟩ := exists_fractional_matching_cover hedges
  exact ⟨z, hz, hz₁, htotal ▸ hbound φ hφ⟩

end SharpTailMatching.Matching
