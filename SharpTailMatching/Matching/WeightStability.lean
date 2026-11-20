/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Near-extremal hypergraphs have approximately covering vertex weights whose
mean and distance to one of the two atomic supports are uniformly small.
This is the empirical-law and compactness step of Section 7. All analytic
and approximate-cover inputs are theorems, not additional hypotheses.
-/
module

public import SharpTailMatching.Matching.EmpiricalSampling
public import SharpTailMatching.Matching.ProbabilityStability
public import SharpTailMatching.Matching.BinomialApproximation

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Matching

universe u

theorem near_extremal_weights {k : ℕ} (hk : 2 ≤ k) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {α : Type u} [Fintype α] [DecidableEq α], n₀ ≤ Fintype.card α →
      ∀ {s : ℕ}, 1 ≤ s → k * (s + 1) ≤ Fintype.card α →
      ∀ H : Finset (Finset α), IsUniform k H → MatchingNumberAtMost s H →
        (max (coverSize k (Fintype.card α) s) (cliqueSize k s) : ℝ) -
          δ * (Fintype.card α : ℝ) ^ k ≤ H.card →
      ∃ w : α → ℝ, (∀ v, 0 ≤ w v ∧ w v ≤ 1) ∧
        |(∑ v, w v) - s| ≤ η * Fintype.card α ∧
        ((uncoveredFamily H w).card : ℝ) ≤ η * (Fintype.card α : ℝ) ^ k ∧
        ((∑ v, twoAtomCost 1 (w v)) ≤ η * Fintype.card α ∨
          (∑ v, twoAtomCost (k : ℝ)⁻¹ (w v)) ≤ η * Fintype.card α) := by
  classical
  obtain ⟨δ, hδ, hlaw⟩ := law_stability k (by omega) hη
  have hFpos : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hFone : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  let θ : ℝ := δ / (4 * k.factorial)
  have hθ : 0 < θ := div_pos hδ (by positivity)
  have hθδ : θ ≤ δ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * k.factorial)).mpr
    nlinarith only [hδ, hFone]
  have hFθ : (k.factorial : ℝ) * θ = δ / 4 := by
    dsimp only [θ]
    field_simp
  let ρ : ℝ := min η θ
  have hρ : 0 < ρ := lt_min hη hθ
  have hρη : ρ ≤ η := min_le_left _ _
  have hρθ : ρ ≤ θ := min_le_right _ _
  have hρδ : ρ ≤ δ := hρθ.trans hθδ
  have hkRpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨n₀, hcover⟩ := approximate_fractional_cover.{u} hk (inv_nonneg.mpr hkRpos.le) hρ
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * (k : ℝ) ^ 2 / δ)
  refine ⟨θ, hθ, max n₀ N, ?_⟩
  intro α _ _ hn s hs hnks H hu hν hH
  let n := Fintype.card α
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < k * (s + 1)) hnks
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn0 : (n : ℝ) ≠ 0 := hnRpos.ne'
  have hpowpos : (0 : ℝ) < (n : ℝ) ^ k := pow_pos hnRpos _
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hfinite : (k : ℝ) ^ 2 / n ≤ δ / 4 := by
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have h := (div_lt_iff₀ hδ).mp hN
    have hNmul := mul_le_mul_of_nonneg_left hnN' hδ.le
    apply (div_le_iff₀ hnRpos).mpr
    nlinarith only [h, hNmul]
  let x : ℝ := (s : ℝ) / n
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hnRpos.le
  have hxmul : x * n = s := div_mul_cancel₀ _ hn0
  have hxle : x ≤ (k : ℝ)⁻¹ := by
    have hkn : k * s ≤ n := (Nat.mul_le_mul_left k (Nat.le_succ s)).trans hnks
    have hkn' : (k : ℝ) * s ≤ n := by exact_mod_cast hkn
    dsimp only [x]
    apply (div_le_iff₀ hnRpos).mpr
    apply (mul_le_mul_iff_right₀ hkRpos).mp
    rw [← mul_assoc, mul_inv_cancel₀ hkRpos.ne', one_mul]
    exact hkn'
  have hνreal : ∀ M : Finset (Finset α), M ⊆ H → IsMatching M → (M.card : ℝ) ≤ x * Fintype.card α := by
    intro M hMH hM
    change (M.card : ℝ) ≤ x * n
    rw [hxmul]
    exact_mod_cast hν M hMH hM
  obtain ⟨w, hw, hweight, huncovered⟩ := hcover ((le_max_left _ _).trans hn) hxle H hu hνreal
  let wU : α → Probability.UnitInterval := fun v ↦
    ⟨⟨w v, (hw v).1⟩, by exact ⟨zero_le, by exact_mod_cast (hw v).2⟩⟩
  let : MeasurableSpace α := ⊤
  let : Nonempty α := Fintype.card_pos_iff.mp hnpos
  let μ := empiricalUnitLaw wU
  have hmeanEq : realUnitMean μ = (∑ v, w v) / n := realUnitMean_empiricalUnitLaw wU
  have hmeanmul : realUnitMean μ * n = ∑ v, w v := by rw [hmeanEq, div_mul_cancel₀ _ hn0]
  have hmean : realUnitMean μ ≤ x + δ := by
    rw [hmeanEq]
    apply (div_le_iff₀ hnRpos).mpr
    have hchange := mul_le_mul_of_nonneg_right hρδ hnRpos.le
    change (∑ v, w v) ≤ (x + ρ) * n at hweight
    nlinarith only [hweight, hchange]
  have htail : max (1 - (1 - x) ^ k) (((k : ℝ) * x) ^ k) - δ ≤
      (Probability.unitTail k μ).toReal := by
    let D : ℝ := max (coverSize k n s) (cliqueSize k s)
    have hsample := factorial_covered_card_le_unitTail hu wU
    change (k.factorial : ℝ) * ((H.card : ℝ) - (uncoveredFamily H w).card) ≤
      (Probability.unitTail k μ).toReal * (n : ℝ) ^ k at hsample
    have hH' : D - θ * (n : ℝ) ^ k ≤ H.card := hH
    have hHm := mul_le_mul_of_nonneg_left hH' hFpos.le
    have hUm := mul_le_mul_of_nonneg_left huncovered hFpos.le
    have hdivide : (k.factorial : ℝ) * D / (n : ℝ) ^ k ≤
        (Probability.unitTail k μ).toReal + k.factorial * (θ + ρ) := by
      apply (div_le_iff₀ hpowpos).mpr
      nlinarith only [hsample, hHm, hUm]
    have hbin := candidate_density_le_binomial_max hk hs hnks
    change max (1 - (1 - x) ^ k) (((k : ℝ) * x) ^ k) ≤
      (k.factorial : ℝ) * D / (n : ℝ) ^ k + (k : ℝ) ^ 2 / n at hbin
    have hρm := mul_le_mul_of_nonneg_left hρθ hFpos.le
    linarith only [hbin, hdivide, hfinite, hFθ, hρm, hδ]
  obtain ⟨hmclose, hcost⟩ := hlaw x hx0 hxle μ hmean htail
  refine ⟨w, hw, ?_, huncovered.trans (mul_le_mul_of_nonneg_right hρη hpowpos.le), ?_⟩
  · have h := mul_le_mul_of_nonneg_right hmclose.le hnRpos.le
    have heq : |(∑ v, w v) - s| = |realUnitMean μ - x| * n := by
      calc
        |(∑ v, w v) - s| = |(realUnitMean μ - x) * n| := by rw [sub_mul, hmeanmul, hxmul]
        _ = |realUnitMean μ - x| * n := by rw [abs_mul, abs_of_pos hnRpos]
    rwa [heq]
  · have hscale : ∀ a : ℝ, unitAtomCost a μ < η → (∑ v, twoAtomCost a (w v)) ≤ η * Fintype.card α := by
      intro a ha
      have heq : unitAtomCost a μ = (∑ v, twoAtomCost a (w v)) / n := unitAtomCost_empiricalUnitLaw a wU
      rw [heq] at ha
      exact ((div_lt_iff₀ hnRpos).mp ha).le
    exact hcost.elim (fun h ↦ Or.inl (hscale 1 h)) (fun h ↦ Or.inr (hscale _ h))

end SharpTailMatching.Matching
