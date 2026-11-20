/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Allow zero-capacity isolated vertices in the reduced hypergraph. Empty color
classes can therefore remain in a regularity partition without relabelling.
-/
module

public import SharpTailMatching.Matching.CapacityDuality

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem exists_fractional_cover_of_nonnegative_capacity_bound
    {H : Finset (Finset α)} {c : α → ℝ} {b : ℝ}
    (hc : ∀ v, 0 ≤ c v) (hedges : ∀ e ∈ H, e.Nonempty)
    (hpositive : ∀ e ∈ H, ∀ v ∈ e, 0 < c v)
    (hbound : ∀ φ : H → ℝ, IsCapacityMatching H c φ → (∑ e : H, φ e) ≤ b) :
    ∃ z : α → ℝ, IsFractionalCover H z ∧ (∀ v, z v ≤ 1) ∧ (∑ v, c v * z v) ≤ b := by
  classical
  let c' := fun v ↦ if 0 < c v then c v else 1
  have hc' : ∀ v, 0 < c' v := by
    intro v
    dsimp only [c']
    split_ifs with h
    · exact h
    · norm_num
  have hbound' : ∀ φ : H → ℝ, IsCapacityMatching H c' φ → (∑ e : H, φ e) ≤ b := by
    intro φ hφ
    apply hbound φ
    refine ⟨hφ.1, ?_⟩
    intro v
    by_cases hv : 0 < c v
    · simpa only [c', ite_eq_left hv] using hφ.2 v
    · have hnot : ∀ e : H, v ∉ (e : Finset α) := by
        intro e hve
        exact hv (hpositive e e.property v hve)
      simpa [fractionalDegree, hnot] using hc v
  obtain ⟨z, hz, hz₁, htotal⟩ := exists_fractional_cover_of_capacity_bound hc' hedges hbound'
  refine ⟨z, hz, hz₁, le_trans ?_ htotal⟩
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hz.1 v)
  dsimp only [c']
  split_ifs with hv
  · exact le_refl _
  · have hzero : c v = 0 := le_antisymm (le_of_not_gt hv) (hc v)
    rw [hzero]
    norm_num

end SharpTailMatching.Matching
