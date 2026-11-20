/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A bounded weak regularity lemma for arbitrary finite k-ary functions. The
partition may have unequal classes, and irregularity is measured by the
total number of tuples in bad cells. This weighted version is sufficient
for the approximate fractional-cover argument.
-/
module

public import SharpTailMatching.Matching.RectangularRegularity

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

def regularityStepBound (k t : ℕ) : ℕ := t * 2 ^ (t ^ k * k)

def regularityColorBound (k t : ℕ) : ℕ → ℕ
  | 0 => t
  | r + 1 => regularityStepBound k (regularityColorBound k t r)

theorem le_regularityStepBound (k t : ℕ) : t ≤ regularityStepBound k t := by
  exact Nat.le_mul_of_pos_right t (Nat.pow_pos (by omega))

theorem regularityStepBound_mono (k : ℕ) : Monotone (regularityStepBound k) := by
  intro a b hab
  exact Nat.mul_le_mul hab (Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_right k (Nat.pow_le_pow_left hab k)))

universe u v

variable {α : Type u} {I : Type v} [Fintype α] [Fintype I] [DecidableEq α] [DecidableEq I]

/-- At each bounded step either regularity has already been reached or the
energy has grown by a fixed positive amount per step. -/
theorem exists_regularity_iteration {k : ℕ} (c : α → I) (f : (Fin k → α) → ℝ)
    {ε : ℝ} (hε : 0 < ε) (r : ℕ) :
    ∃ (J : Type v) (_ : Fintype J) (_ : DecidableEq J) (c' : α → J) (g : J → I),
      (∀ x, g (c' x) = c x) ∧ Fintype.card J ≤ regularityColorBound k (Fintype.card I) r ∧
      (irregularMass c' f ε ≤ ε * Fintype.card (Fin k → α) ∨
        (r : ℝ) * ε ^ (k + 3) * Fintype.card (Fin k → α) ≤ partitionEnergy (tupleLabel c') f) := by
  induction r with
  | zero =>
    refine ⟨I, inferInstance, inferInstance, c, id, fun _ ↦ rfl, le_refl _, Or.inr ?_⟩
    simp only [Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg (fun x _ ↦ sq_nonneg _)
  | succ r ih =>
    obtain ⟨J, hfinJ, hdecJ, c', g, hrefine, hcard, hstate⟩ := ih
    let : Fintype J := hfinJ
    let : DecidableEq J := hdecJ
    by_cases hregular : irregularMass c' f ε ≤ ε * Fintype.card (Fin k → α)
    · refine ⟨J, hfinJ, hdecJ, c', g, hrefine, ?_, Or.inl hregular⟩
      exact hcard.trans (le_regularityStepBound _ _)
    · have henergy := hstate.resolve_left hregular
      obtain ⟨W, hW⟩ := exists_witness_refinement c' f hε.le
      let K := J × ((Fin k → J) × Fin k → Bool)
      let c'' : α → K := witnessRefinement c' W
      let g' : K → I := fun p ↦ g p.1
      have hK : Fintype.card K = regularityStepBound k (Fintype.card J) := by
        simp only [K, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_bool, regularityStepBound]
      have hcard' : Fintype.card K ≤ regularityColorBound k (Fintype.card I) (r + 1) := by
        rw [hK]
        exact regularityStepBound_mono k hcard
      have hinc : ε ^ (k + 3) * Fintype.card (Fin k → α) <
          partitionEnergy (tupleLabel c'') f - partitionEnergy (tupleLabel c') f := by
        have hp : 0 < ε ^ (k + 2) := pow_pos hε _
        have h := mul_lt_mul_of_pos_left (lt_of_not_ge hregular) hp
        have heq : ε ^ (k + 2) * (ε * (Fintype.card (Fin k → α) : ℝ)) =
            ε ^ (k + 3) * Fintype.card (Fin k → α) := by
          rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
          ring
        rw [heq] at h
        exact h.trans_le hW
      refine ⟨K, inferInstance, inferInstance, c'', g', hrefine, hcard', Or.inr ?_⟩
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith only [henergy, hinc]

/-- A finite weighted regularity lemma with a bound chosen before the vertex
set and the k-ary function. Refinement preserves every initial class. -/
theorem weighted_rectangular_regularity (k t : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, ∀ {β : Type u} [Fintype β] [DecidableEq β] [Nonempty β]
      (c : β → Fin t) (f : (Fin k → β) → ℝ),
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (c' : β → J) (g : J → Fin t),
        (∀ x, g (c' x) = c x) ∧ Fintype.card J ≤ T ∧
          irregularMass c' f ε ≤ ε * Fintype.card (Fin k → β) := by
  have hδ : 0 < ε ^ (k + 3) := pow_pos hε _
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε ^ (k + 3))
  have hrδ : 1 < (r : ℝ) * ε ^ (k + 3) := (div_lt_iff₀ hδ).mp hr
  refine ⟨regularityColorBound k t r, ?_⟩
  intro β _ _ _ c f hf
  obtain ⟨J, hfinJ, hdecJ, c', g, hrefine, hcard, hstate⟩ := exists_regularity_iteration c f hε r
  let : Fintype J := hfinJ
  let : DecidableEq J := hdecJ
  refine ⟨J, hfinJ, hdecJ, c', g, hrefine, by simpa only [Fintype.card_fin] using hcard, ?_⟩
  rcases hstate with hregular | henergy
  · exact hregular
  · have hupper := partitionEnergy_le_card (tupleLabel c') f hf
    have hn : (0 : ℝ) < Fintype.card (Fin k → β) := by exact_mod_cast Fintype.card_pos
    nlinarith only [henergy, hupper, mul_lt_mul_of_pos_right hrδ hn]

end SharpTailMatching.Matching
