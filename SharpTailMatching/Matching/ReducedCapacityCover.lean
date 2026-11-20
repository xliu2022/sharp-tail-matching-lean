/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A genuine integral matching bound on the original hypergraph bounds every
capacity matching of the reduced hypergraph. Finite duality then supplies
the reduced cover; no fractional matching hypothesis is imposed on the
original hypergraph.
-/
module

public import SharpTailMatching.Matching.ReducedCover
public import SharpTailMatching.Matching.CapacityZero

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I] [Fintype α] [Fintype I]

theorem IsUniform.card_le_pow {k : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H) :
    H.card ≤ Fintype.card α ^ k := by
  classical
  have h := family_card_le_tuple_count hu
  have hle := h.trans (Finset.card_le_card (Finset.filter_subset _ _))
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin] using hle

theorem exists_reduced_cover_of_matching_bound {k : ℕ} {c : α → I}
    {H : Finset (Finset α)} {ε d γ b x : ℝ}
    (hk : 0 < k) (hu : IsUniform k H) (hγ : γ < 1) (hεγ : ε ≤ γ)
    (hd : ε < d) (hdpos : 0 < d)
    (hν : ∀ M : Finset (Finset α), M ⊆ H → IsMatching M →
      (M.card : ℝ) ≤ x * Fintype.card α)
    (hslack : ((reducedFamily k c H ε d).card : ℝ) ≤
      ((1 - γ) * b - x) * Fintype.card α) :
    ∃ z : I → ℝ, IsFractionalCover (reducedFamily k c H ε d) z ∧
      (∀ i, z i ≤ 1) ∧ (∑ i, ((labelFiber c i).card : ℝ) * z i) ≤ b * Fintype.card α := by
  classical
  apply exists_fractional_cover_of_nonnegative_capacity_bound
  · intro i
    exact Nat.cast_nonneg _
  · intro e he
    apply Finset.card_pos.mp
    rw [reducedFamily_uniform k c H ε d e he]
    exact hk
  · intro e he i hi
    exact_mod_cast reduced_edge_positive_classes hdpos he i hi
  · intro φ hφ
    obtain ⟨M, hMH, hM, hround⟩ := exists_matching_of_reduced_capacity hk hu hγ hεγ hd φ hφ
    have hMbound := hν M hMH hM
    apply (mul_le_mul_iff_right₀ (sub_pos.mpr hγ)).mp
    nlinarith only [hround, hMbound, hslack]

end SharpTailMatching.Matching
