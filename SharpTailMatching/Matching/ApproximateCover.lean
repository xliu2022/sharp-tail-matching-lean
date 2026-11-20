/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The approximate fractional-cover lemma used in the manuscript. Its
hypothesis is an ordinary integral matching bound. Weighted weak vertex
regularity, greedy rounding, and finite capacity duality are all proved
in the imported modules. The size threshold is chosen uniformly over all
finite vertex sets, all hypergraphs, and all matching densities x ≤ ξ.
-/
module

public import SharpTailMatching.Matching.ReducedCapacityCover
public import SharpTailMatching.Matching.WeakRegularity

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

universe u

/-- Every sufficiently large uniform hypergraph with matching number at
most `x * n` admits vertex weights in `[0,1]` of total at most `(x + ρ) * n`
which cover all but at most `ρ * n^k` edges. The threshold is uniform for
`x ≤ ξ`; the matching hypothesis is integral and unconditional. -/
theorem approximate_fractional_cover {k : ℕ} (hk : 2 ≤ k) {ξ ρ : ℝ}
    (hξ : 0 ≤ ξ) (hρ : 0 < ρ) :
    ∃ n₀ : ℕ, ∀ {α : Type u} [Fintype α] [DecidableEq α], n₀ ≤ Fintype.card α →
      ∀ {x : ℝ}, x ≤ ξ → ∀ H : Finset (Finset α), IsUniform k H →
        (∀ M : Finset (Finset α), M ⊆ H → IsMatching M →
          (M.card : ℝ) ≤ x * Fintype.card α) →
      ∃ w : α → ℝ, (∀ v, 0 ≤ w v ∧ w v ≤ 1) ∧
        (∑ v, w v) ≤ (x + ρ) * Fintype.card α ∧
        ((uncoveredFamily H w).card : ℝ) ≤ ρ * (Fintype.card α : ℝ) ^ k := by
  classical
  let a : ℝ := ρ / 4
  have ha : 0 < a := div_pos hρ (by norm_num)
  have hden : 0 < 2 * (ξ + a) := by positivity
  let γ : ℝ := a / (2 * (ξ + a))
  have hγpos : 0 < γ := div_pos ha hden
  have hγhalf : γ ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith only [hξ]
  have hγ : γ < 1 := lt_of_le_of_lt hγhalf (by norm_num)
  have hγeq : γ * (ξ + a) = a / 2 := by
    dsimp only [γ]
    field_simp
  let ε : ℝ := min (γ / 2) (ρ / 8)
  let d : ℝ := ρ / 4
  have hε : 0 < ε := lt_min (div_pos hγpos (by norm_num)) (div_pos hρ (by norm_num))
  have hεγ : ε ≤ γ := (min_le_left _ _).trans (by linarith only [hγpos])
  have hερ : ε ≤ ρ / 8 := min_le_right _ _
  have hd : ε < d := by dsimp only [d]; linarith only [hερ, hρ]
  have hdpos : 0 < d := ha
  obtain ⟨t, ht⟩ := exists_nat_gt (max (8 / ρ) 0)
  have htpos : 0 < t := by
    have ht' : (0 : ℝ) < t := (le_max_right _ _).trans_lt ht
    exact_mod_cast ht'
  have htcoef : (2 : ℝ) ≤ (ρ / 4) * t := by
    have ht' : 8 / ρ < (t : ℝ) := (le_max_left _ _).trans_lt ht
    have ht'' := (div_lt_iff₀ hρ).mp ht'
    linarith only [ht'']
  obtain ⟨T, hT⟩ := weighted_rectangular_regularity.{u} k t hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (T : ℝ) ^ k / a)
  have hNbound : (T : ℝ) ^ k ≤ (a / 2) * N := by
    have h := (div_lt_iff₀ ha).mp hN
    linarith only [h]
  refine ⟨max t N, ?_⟩
  intro α _ _ hn x hx H hu hν
  have htn : t ≤ Fintype.card α := (le_max_left _ _).trans hn
  have hNn : N ≤ Fintype.card α := (le_max_right _ _).trans hn
  have hnpos : 0 < Fintype.card α := htpos.trans_le htn
  let : Nonempty α := Fintype.card_pos_iff.mp hnpos
  obtain ⟨c, hc⟩ := exists_initial_coloring_noncrossing_bound hk htpos htn hu
  obtain ⟨J, hfinJ, hdecJ, c', g, hrefine, hcardJ, hregular⟩ := hT c (tupleIndicator H)
    (tupleIndicator_bounds H)
  let : Fintype J := hfinJ
  let : DecidableEq J := hdecJ
  have hnoncross : ((noncrossingFamily c' H).card : ℝ) ≤
      (ρ / 4) * (Fintype.card α : ℝ) ^ k := by
    have hmono := noncrossing_mono_refinement g hrefine H
    have hcount : t * (noncrossingFamily c' H).card ≤ 2 * Fintype.card α ^ k :=
      (Nat.mul_le_mul_left t hmono).trans hc
    have hcount' : (t : ℝ) * (noncrossingFamily c' H).card ≤ 2 * (Fintype.card α : ℝ) ^ k := by
      exact_mod_cast hcount
    have hpow : 0 ≤ (Fintype.card α : ℝ) ^ k := pow_nonneg (Nat.cast_nonneg _) _
    have hcoef := mul_le_mul_of_nonneg_right htcoef hpow
    have htpos' : (0 : ℝ) < t := by exact_mod_cast htpos
    apply (mul_le_mul_iff_right₀ htpos').mp
    nlinarith only [hcount', hcoef]
  have hRcard : ((reducedFamily k c' H ε d).card : ℝ) ≤ (T : ℝ) ^ k := by
    have h := (reducedFamily_uniform k c' H ε d).card_le_pow
    have h' := h.trans (Nat.pow_le_pow_left hcardJ k)
    exact_mod_cast h'
  have hslackcoef : a / 2 ≤ (1 - γ) * (x + a) - x := by
    have hprod := mul_le_mul_of_nonneg_left hx hγpos.le
    nlinarith only [hprod, hγeq]
  have hslack : ((reducedFamily k c' H ε d).card : ℝ) ≤
      ((1 - γ) * (x + a) - x) * Fintype.card α := by
    have hNn' : (N : ℝ) ≤ Fintype.card α := by exact_mod_cast hNn
    calc
      ((reducedFamily k c' H ε d).card : ℝ) ≤ (T : ℝ) ^ k := hRcard
      _ ≤ (a / 2) * N := hNbound
      _ ≤ (a / 2) * Fintype.card α := mul_le_mul_of_nonneg_left hNn' (by positivity)
      _ ≤ ((1 - γ) * (x + a) - x) * Fintype.card α :=
        mul_le_mul_of_nonneg_right hslackcoef (Nat.cast_nonneg _)
  obtain ⟨z, hz, hz₁, hweight⟩ := exists_reduced_cover_of_matching_bound
    (by omega : 0 < k) hu hγ hεγ hd hdpos hν hslack
  refine ⟨fun v ↦ z (c' v), fun v ↦ ⟨hz.1 _, hz₁ _⟩, ?_, ?_⟩
  · rw [sum_lifted_weights]
    apply hweight.trans
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    dsimp only [a]
    linarith only [hρ]
  · have h := uncovered_lift_bound hu hdpos.le hz
    have htuples : (Fintype.card (Fin k → α) : ℝ) = (Fintype.card α : ℝ) ^ k := by
      simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    rw [htuples] at h hregular
    have hsmall := mul_le_mul_of_nonneg_right hερ
      (pow_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card α)) k)
    dsimp only [d] at h
    nlinarith only [h, hnoncross, hregular, hsmall,
      mul_nonneg hρ.le (pow_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card α)) k)]

end SharpTailMatching.Matching
