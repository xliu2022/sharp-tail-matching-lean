/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The full hypergraph stability proposition, uniformly for every
n ≥ k(s+1). Approximate covers, empirical sampling, compact law stability,
and finite editing are all discharged in the imported development.
-/
module

public import SharpTailMatching.Matching.WeightStability
public import SharpTailMatching.Matching.WeightEditing

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Matching

universe u

/-- Every near-extremal large matching problem is close in symmetric
difference to a standard complete cover or a standard complete clique. -/
theorem matching_stability {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ {α : Type u} [Fintype α] [DecidableEq α], k * (s + 1) ≤ Fintype.card α →
      ∀ H : Finset (Finset α), IsUniform k H → MatchingNumberAtMost s H →
        (max (coverSize k (Fintype.card α) s) (cliqueSize k s) : ℝ) -
          δ * (Fintype.card α : ℝ) ^ k ≤ H.card →
      (∃ S : Finset α, S.card = s ∧
        ((H \ coverFamily k Finset.univ S).card : ℝ) + (coverFamily k Finset.univ S \ H).card ≤
          ε * (Fintype.card α : ℝ) ^ k) ∨
      (∃ Q : Finset α, Q.card = k * (s + 1) - 1 ∧
        ((H \ cliqueFamily k Q).card : ℝ) + (cliqueFamily k Q \ H).card ≤
          ε * (Fintype.card α : ℝ) ^ k) := by
  classical
  let η : ℝ := ε / (16 * ((k : ℝ) + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : ((k : ℝ) + 1) * η = ε / 16 := by dsimp only [η]; field_simp
  obtain ⟨δ, hδ, n₀, hweights⟩ := near_extremal_weights.{u} (by omega : 2 ≤ k) hη
  let δ' : ℝ := min δ (ε / 4)
  have hδ' : 0 < δ' := lt_min hδ (div_pos hε (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_gt (16 * (k : ℝ) / ε)
  refine ⟨δ', hδ', max n₀ (max N 1), ?_⟩
  intro s hs α _ _ hnks H hu hν hH
  let n := Fintype.card α
  have hsone : 1 ≤ s := (le_max_right N 1).trans ((le_max_right n₀ _).trans hs)
  have hsn : s ≤ n := (Nat.le_mul_of_pos_left s (by omega : 0 < k)).trans
    ((Nat.mul_le_mul_left k (Nat.le_succ s)).trans hnks)
  have hnpos : 0 < n := lt_of_lt_of_le (by omega : 0 < s) hsn
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn0 : n₀ ≤ n := ((le_max_left _ _).trans hs).trans hsn
  have hnN : N ≤ n := ((le_max_left N 1).trans ((le_max_right n₀ _).trans hs)).trans hsn
  have hpow : 0 ≤ (n : ℝ) ^ k := pow_nonneg hnRpos.le _
  have hpow' : 0 ≤ (n : ℝ) ^ (k - 1) := pow_nonneg hnRpos.le _
  have hpoweq : (n : ℝ) * (n : ℝ) ^ (k - 1) = (n : ℝ) ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ k)]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkfinite : (k : ℝ) ≤ (ε / 16) * n := by
    have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
    have h := (div_lt_iff₀ hε).mp hN
    have hmul := mul_le_mul_of_nonneg_left hnN' hε.le
    nlinarith only [h, hmul]
  have hHweights : (max (coverSize k n s) (cliqueSize k s) : ℝ) - δ * (n : ℝ) ^ k ≤ H.card := by
    have hle := mul_le_mul_of_nonneg_right (min_le_left δ (ε / 4)) hpow
    change (max (coverSize k n s) (cliqueSize k s) : ℝ) - δ' * (n : ℝ) ^ k ≤ H.card at hH
    linarith only [hH, hle]
  obtain ⟨w, hw, hm, hU, hcost⟩ := hweights hn0 hsone hnks H hu hν hHweights
  have herror : η * (n : ℝ) ^ k +
      (3 * k * η * n + k) * (n : ℝ) ^ (k - 1) ≤ (ε / 4) * (n : ℝ) ^ k := by
    have hsmall := mul_le_mul_of_nonneg_right hkfinite hpow'
    have hsmall' : (k : ℝ) * (n : ℝ) ^ (k - 1) ≤ (ε / 16) * (n : ℝ) ^ k := by
      calc
        _ ≤ ((ε / 16) * n) * (n : ℝ) ^ (k - 1) := hsmall
        _ = _ := by rw [mul_assoc, hpoweq]
    have hcoef : (1 + 3 * (k : ℝ)) * η ≤ 3 * ε / 16 := by
      nlinarith only [hηeq, hη]
    have hcoef' := mul_le_mul_of_nonneg_right hcoef hpow
    have heq : η * (n : ℝ) ^ k + (3 * k * η * n + k) * (n : ℝ) ^ (k - 1) =
        (1 + 3 * (k : ℝ)) * η * (n : ℝ) ^ k + k * (n : ℝ) ^ (k - 1) := by
      rw [← hpoweq]
      ring
    rw [heq]
    linarith only [hsmall', hcoef']
  have hfinish : ∀ A : Finset (Finset α), (A.card : ℝ) ≤
      max (coverSize k n s : ℝ) (cliqueSize k s : ℝ) →
      ((H \ A).card : ℝ) ≤ (ε / 4) * (n : ℝ) ^ k →
      ((H \ A).card : ℝ) + (A \ H).card ≤ ε * (n : ℝ) ^ k := by
    intro A hA hbad
    have h := symmetric_difference_bound_of_one_sided H A hH hA hbad
    have hδsmall := mul_le_mul_of_nonneg_right (min_le_right δ (ε / 4)) hpow
    have hεnonneg := mul_nonneg hε.le hpow
    nlinarith only [h, hδsmall, hεnonneg]
  rcases hcost with hcover | hclique
  · obtain ⟨S, hS, hbad⟩ := weight_edit_cover hu (fun v ↦ (hw v).1) hsn
    refine Or.inl ⟨S, hS, hfinish _ ?_ ?_⟩
    · rw [card_coverFamily k (Finset.subset_univ S), Finset.card_univ, hS]
      change (coverSize k n s : ℝ) ≤ max (coverSize k n s : ℝ) (cliqueSize k s : ℝ)
      exact le_max_left _ _
    · have hcostbound : (2 * ∑ v, twoAtomCost 1 (w v)) + |(∑ v, w v) - s| ≤ 3 * η * n := by
        linarith only [hcover, hm]
      have hcostbound' := mul_le_mul_of_nonneg_right hcostbound hpow'
      have hraise : 3 * η * n * (n : ℝ) ^ (k - 1) ≤
          (3 * k * η * n + k) * (n : ℝ) ^ (k - 1) := by
        apply mul_le_mul_of_nonneg_right _ hpow'
        have hηn := mul_nonneg hη.le hnRpos.le
        nlinarith only [hkR, hηn]
      nlinarith only [hbad, hU, hcostbound', hraise, herror]
  · have hQsize : k * (s + 1) - 1 ≤ n := (Nat.sub_le _ _).trans hnks
    obtain ⟨Q, hQ, hbad⟩ := weight_edit_clique (by omega : 1 ≤ k) hu (fun v ↦ (hw v).1) hQsize
    refine Or.inr ⟨Q, hQ, hfinish _ ?_ ?_⟩
    · rw [card_cliqueFamily, hQ]
      change (cliqueSize k s : ℝ) ≤ max (coverSize k n s : ℝ) (cliqueSize k s : ℝ)
      exact le_max_right _ _
    · have hcostbound : (2 * k * ∑ v, twoAtomCost (k : ℝ)⁻¹ (w v)) +
          k * |(∑ v, w v) - s| + k ≤ 3 * k * η * n + k := by
        have h1 := mul_le_mul_of_nonneg_left hclique (by positivity : (0 : ℝ) ≤ 2 * k)
        have h2 := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (α := ℝ) k)
        linarith only [h1, h2]
      have hcostbound' := mul_le_mul_of_nonneg_right hcostbound hpow'
      nlinarith only [hbad, hU, hcostbound', herror]

end SharpTailMatching.Matching
