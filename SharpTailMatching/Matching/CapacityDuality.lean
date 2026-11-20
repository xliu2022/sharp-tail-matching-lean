/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The capacity form of fractional hypergraph duality. Cluster sizes can serve
as capacities, allowing regularity partitions with unequal part sizes.
-/
module

public import SharpTailMatching.Matching.FractionalDuality

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

def IsCapacityMatching (H : Finset (Finset α)) (c : α → ℝ) (φ : H → ℝ) : Prop :=
  (∀ e, 0 ≤ φ e) ∧ ∀ v, fractionalDegree H φ v ≤ c v

theorem capacity_weak_duality {H : Finset (Finset α)} {c z : α → ℝ} {φ : H → ℝ}
    (hφ : IsCapacityMatching H c φ) (hz : IsFractionalCover H z) :
    (∑ e : H, φ e) ≤ ∑ v, c v * z v := by
  calc
    (∑ e : H, φ e) ≤ ∑ e : H, φ e * ∑ v ∈ (e : Finset α), z v := by
      apply Finset.sum_le_sum
      intro e _
      exact le_mul_of_one_le_right (hφ.1 e) (hz.2 e e.property)
    _ = ∑ v, z v * fractionalDegree H φ v := fractional_incidence_sum H φ z
    _ ≤ ∑ v, c v * z v := Finset.sum_le_sum (fun v _ ↦ by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hφ.2 v) (hz.1 v))

noncomputable def capacityMatrix (H : Finset (Finset α)) (c : α → ℝ) (e : H) (v : α) : ℝ :=
  incidenceMatrix H e v / c v

theorem capacity_row (H : Finset (Finset α)) (c q : α → ℝ) (e : H) :
    (∑ v, capacityMatrix H c e v * q v) = ∑ v ∈ (e : Finset α), q v / c v := by
  simp [capacityMatrix, incidenceMatrix, div_eq_mul_inv, mul_comm]

omit [Fintype α] in
theorem capacity_column (H : Finset (Finset α)) (c : α → ℝ) (p : H → ℝ) (v : α) :
    (∑ e : H, p e * capacityMatrix H c e v) = fractionalDegree H p v / c v := by
  simp only [capacityMatrix, ← mul_div_assoc, ← Finset.sum_div, incidence_column]

theorem exists_capacity_matching_cover_raw {H : Finset (Finset α)} {c : α → ℝ}
    (hc : ∀ v, 0 < c v) (hH : H.Nonempty) (hedges : ∀ e ∈ H, e.Nonempty) :
    ∃ φ : H → ℝ, ∃ z : α → ℝ, IsCapacityMatching H c φ ∧ IsFractionalCover H z ∧
      (∑ e : H, φ e) = ∑ v, c v * z v := by
  classical
  obtain ⟨e₀, he₀⟩ := hH
  obtain ⟨v₀, _⟩ := hedges e₀ he₀
  have : Nonempty H := ⟨⟨e₀, he₀⟩⟩
  have : Nonempty α := ⟨v₀⟩
  obtain ⟨p, hp, q, hq, hcolumns, hrows⟩ := exists_matrix_minimax (capacityMatrix H c)
  let τ := matrixPayoff (capacityMatrix H c) p q
  have hcol : ∀ v, fractionalDegree H p v / c v ≤ τ := by
    intro v
    simpa only [capacity_column] using hcolumns v
  have hrow : ∀ e : H, τ ≤ ∑ v ∈ (e : Finset α), q v / c v := by
    intro e
    simpa only [capacity_row] using hrows e
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
  have hτ : 0 < τ := (div_pos (hpe.trans_le hpdeg) (hc v)).trans_le (hcol v)
  let φ : H → ℝ := fun e ↦ p e / τ
  let z : α → ℝ := fun v ↦ (q v / c v) / τ
  have hφ : IsCapacityMatching H c φ := by
    refine ⟨fun e ↦ div_nonneg (hp.1 e) hτ.le, ?_⟩
    intro v
    rw [fractionalDegree_div]
    apply (div_le_iff₀ hτ).mpr
    simpa only [mul_comm] using (div_le_iff₀ (hc v)).mp (hcol v)
  have hz : IsFractionalCover H z := by
    refine ⟨fun v ↦ div_nonneg (div_nonneg (hq.1 v) (hc v).le) hτ.le, ?_⟩
    intro e he
    change 1 ≤ ∑ v ∈ e, (q v / c v) / τ
    rw [← Finset.sum_div]
    exact (one_le_div hτ).mpr (hrow ⟨e, he⟩)
  refine ⟨φ, z, hφ, hz, ?_⟩
  have hpoint : ∀ v, c v * z v = q v / τ := by
    intro v
    dsimp only [z]
    rw [← mul_div_assoc, mul_div_cancel₀ _ (hc v).ne']
  simp only [φ, hpoint, ← Finset.sum_div, hp.2, hq.2]

theorem exists_capacity_matching_cover {H : Finset (Finset α)} {c : α → ℝ}
    (hc : ∀ v, 0 < c v) (hedges : ∀ e ∈ H, e.Nonempty) :
    ∃ φ : H → ℝ, ∃ z : α → ℝ, IsCapacityMatching H c φ ∧ IsFractionalCover H z ∧
      (∀ v, z v ≤ 1) ∧ (∑ e : H, φ e) = ∑ v, c v * z v := by
  by_cases hH : H.Nonempty
  · obtain ⟨φ, z, hφ, hz, htotal⟩ := exists_capacity_matching_cover_raw hc hH hedges
    let z' := fun v ↦ min (z v) 1
    have hz' : IsFractionalCover H z' := hz.min_one
    refine ⟨φ, z', hφ, hz', fun v ↦ min_le_right _ _, le_antisymm (capacity_weak_duality hφ hz') ?_⟩
    rw [htotal]
    exact Finset.sum_le_sum (fun v _ ↦ mul_le_mul_of_nonneg_left (min_le_left (z v) 1) (hc v).le)
  · have heq : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    subst H
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, by simp, by simp⟩
    · exact ⟨by simp, fun v ↦ by simpa [fractionalDegree] using (hc v).le⟩
    · simp [IsFractionalCover]

theorem exists_fractional_cover_of_capacity_bound {H : Finset (Finset α)} {c : α → ℝ} {b : ℝ}
    (hc : ∀ v, 0 < c v) (hedges : ∀ e ∈ H, e.Nonempty)
    (hbound : ∀ φ : H → ℝ, IsCapacityMatching H c φ → (∑ e : H, φ e) ≤ b) :
    ∃ z : α → ℝ, IsFractionalCover H z ∧ (∀ v, z v ≤ 1) ∧ (∑ v, c v * z v) ≤ b := by
  obtain ⟨φ, z, hφ, hz, hz₁, htotal⟩ := exists_capacity_matching_cover hc hedges
  exact ⟨z, hz, hz₁, htotal ▸ hbound φ hφ⟩

end SharpTailMatching.Matching
