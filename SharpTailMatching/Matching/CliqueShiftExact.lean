/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Exactification near a clique by cross-shifts. All bounds are proved for the
original matching number, and equality is pulled backwards one shift at a
time using the already established genuine-clique theorem.
-/
module

public import SharpTailMatching.Matching.CliqueExact
public import SharpTailMatching.Matching.ShiftingClosure

@[expose] public section

namespace SharpTailMatching.Matching

theorem local_clique_size_le {k s : ℕ} : ((6 * k - 1) * s) / 6 ≤ k * s := by
  have hfloor := Nat.mul_div_le ((6 * k - 1) * s) 6
  have hnum := Nat.mul_le_mul_right s (Nat.sub_le (6 * k) 1)
  nlinarith only [hfloor, hnum]

theorem clique_reservoir_choose_lower {k s : ℕ} (hk : 3 ≤ k) (hs : 120 * k ≤ s) :
    s ^ k ≤ (12 ^ k * k.factorial) *
      (k * (s + 1) - 1 - ((6 * k - 1) * s) / 6).choose k := by
  have hk₆ : 6 * k - 1 + 1 = 6 * k := by omega
  have hfloor₁ := Nat.mul_div_le ((6 * k - 1) * s) 6
  have hfloor₂ := Nat.mul_div_le s 6
  have hsmall : ((6 * k - 1) * s) / 6 + s / 6 ≤ k * s := by
    nlinarith only [hfloor₁, hfloor₂, hk₆]
  have hm : k * s ≤ k * (s + 1) - 1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hreservoir : s / 6 ≤ k * (s + 1) - 1 - ((6 * k - 1) * s) / 6 := by omega
  have hs' : 2 * 6 * (k + 1) ≤ s := by omega
  have hlow : s ^ k ≤ (12 ^ k * k.factorial) * (s / 6).choose k := by
    simpa only [Nat.add_sub_cancel, show 2 * 6 = 12 from rfl] using
      (division_choose_lower (k := k + 1) (L := 6) (s := s) (by omega) hs')
  exact hlow.trans (Nat.mul_le_mul_left _ (Nat.choose_le_choose k hreservoir))

theorem clique_missing_lt_choose_of_small {k s b : ℕ} (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hmissing : (b : ℝ) ≤ (1 / (2 * (12 : ℝ) ^ k * (k.factorial : ℝ))) * (s : ℝ) ^ k) :
    b < (k * (s + 1) - 1 - ((6 * k - 1) * s) / 6).choose k := by
  let C : ℝ := (12 : ℝ) ^ k * (k.factorial : ℝ)
  let B := (k * (s + 1) - 1 - ((6 * k - 1) * s) / 6).choose k
  have hC : 0 < C := by dsimp only [C]; positivity
  have hden : 0 < 2 * C := by positivity
  have hspos : 0 < s := by omega
  have hspow : 0 < (s : ℝ) ^ k := by positivity
  have hlow : (s : ℝ) ^ k ≤ C * (B : ℝ) := by
    dsimp only [C, B]
    exact_mod_cast clique_reservoir_choose_lower hk hs
  have hmiss : (b : ℝ) ≤ (s : ℝ) ^ k / (2 * C) := by
    simpa only [C, mul_assoc, one_div_mul_eq_div] using hmissing
  have hprod := (le_div_iff₀ hden).mp hmiss
  have hB : 0 < (B : ℝ) := by nlinarith only [hlow, hspow, hC]
  have hlt : (b : ℝ) < B := by nlinarith only [hprod, hlow, hC, hB]
  exact_mod_cast hlt

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
/-- Every edge of a shifted clique avoiding the receiving vertex was already
present before the shift. One deleted vertex is enough for the pullback. -/
theorem clique_before_shift_erase {k : ℕ} {i j : α} {H : Finset (Finset α)}
    {R : Finset α} (hR : shiftFamily i j H = cliqueFamily k R) :
    cliqueFamily k (R.erase i) ⊆ H := by
  intro e he
  obtain ⟨hesub, hecard⟩ := mem_cliqueFamily.mp he
  have heShift : e ∈ shiftFamily i j H := by
    rw [hR]
    exact mem_cliqueFamily.mpr ⟨hesub.trans (Finset.erase_subset _ _), hecard⟩
  by_contra heH
  have hie := (new_shift_edge heShift heH).1
  exact (Finset.mem_erase.mp (hesub hie)).1 rfl

theorem clique_of_shift_clique {k s : ℕ} {i j : α} {H : Finset (Finset α)}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ Fintype.card α)
    (hupper : 2 * Fintype.card α ≤ (2 * k + 1) * s)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hcard : H.card = (k * (s + 1) - 1).choose k)
    (hshift : ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧
      shiftFamily i j H = cliqueFamily k R) :
    ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧ H = cliqueFamily k R := by
  obtain ⟨R, hRcard, hR⟩ := hshift
  have hsize : ((6 * k - 1) * s) / 6 ≤ (R.erase i).card := by
    have hu₀ : ((6 * k - 1) * s) / 6 ≤ k * s := local_clique_size_le
    have hm : k * s + 2 ≤ k * (s + 1) - 1 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    by_cases hi : i ∈ R
    · rw [Finset.card_erase_of_mem hi, hRcard]
      omega
    · rw [Finset.erase_eq_of_notMem hi, hRcard]
      omega
  obtain ⟨Q, hQR, hQcard⟩ := Finset.exists_subset_card_eq hsize
  have hQH : cliqueFamily k Q ⊆ H := by
    intro e he
    obtain ⟨heQ, hecard⟩ := mem_cliqueFamily.mp he
    exact clique_before_shift_erase hR (mem_cliqueFamily.mpr ⟨heQ.trans hQR, hecard⟩)
  exact (local_clique_exact hk hs hlower hupper hQcard hu hν hQH).2.mp hcard

/-- Finite shifting transfer with the exact missing-edge threshold. -/
theorem clique_exact_of_missing_lt_choose {k s : ℕ} {H : Finset (Finset α)}
    {Q₀ : Finset α}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ Fintype.card α)
    (hupper : 2 * Fintype.card α ≤ (2 * k + 1) * s)
    (hQ₀ : Q₀.card = k * (s + 1) - 1)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hmissing : (cliqueFamily k Q₀ \ H).card <
      (k * (s + 1) - 1 - ((6 * k - 1) * s) / 6).choose k) :
    H.card ≤ (k * (s + 1) - 1).choose k ∧
      (H.card = (k * (s + 1) - 1).choose k ↔
        ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧ H = cliqueFamily k R) := by
  have hsize : ((6 * k - 1) * s) / 6 ≤ Q₀.card := by
    have hu₀ : ((6 * k - 1) * s) / 6 ≤ k * s := local_clique_size_le
    rw [hQ₀]
    have hm : k * s ≤ k * (s + 1) - 1 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    exact hu₀.trans hm
  obtain ⟨U, hUQ, hUcard⟩ := Finset.exists_subset_card_eq hsize
  let V := Q₀ \ U
  have hVcard : V.card = k * (s + 1) - 1 - ((6 * k - 1) * s) / 6 := by
    change (Q₀ \ U).card = _
    rw [Finset.card_sdiff_of_subset hUQ, hQ₀, hUcard]
  generalize hn : shiftEnergy U H = n
  induction n using Nat.strong_induction_on generalizing H with
  | h n ih =>
    by_cases hshift : IsCrossShifted U V H
    · have hmissV : (cliqueFamily k Q₀ \ H).card < V.card.choose k := by
        rw [hVcard]
        exact hmissing
      have hclique := crossShifted_contains_clique (k := k) (Finset.sdiff_subset : V ⊆ Q₀)
        hshift hmissV
      exact local_clique_exact hk hs hlower hupper hUcard hu hν hclique
    · obtain ⟨i, hi, j, hj, hchange⟩ :
          ∃ i ∈ U, ∃ j ∈ V, shiftFamily i j H ≠ H := by
        by_contra hnot
        apply hshift
        intro i hi j hj
        by_contra hne
        exact hnot ⟨i, hi, j, hj, hne⟩
      have hsmall : shiftEnergy U (shiftFamily i j H) < n := by
        rw [← hn]
        exact shiftEnergy_lt hi (Finset.mem_sdiff.mp hj).2 hchange
      have hmissing' : (cliqueFamily k Q₀ \ shiftFamily i j H).card <
          (k * (s + 1) - 1 - ((6 * k - 1) * s) / 6).choose k := by
        rw [card_missing_clique_shiftFamily hu (hUQ hi) (Finset.mem_sdiff.mp hj).1]
        exact hmissing
      obtain ⟨hbound, heq⟩ := ih (shiftEnergy U (shiftFamily i j H)) hsmall
        (hu.shiftFamily i j) (hν.shiftFamily i j) hmissing' rfl
      rw [card_shiftFamily] at hbound heq
      refine ⟨hbound, ?_⟩
      constructor
      · intro hcard
        exact clique_of_shift_clique hk hs hlower hupper hu hν hcard (heq.mp hcard)
      · rintro ⟨R, hR, rfl⟩
        rw [card_cliqueFamily, hR]

/-- Manuscript Lemma 8.4 with explicit constants. The admissible error is
`η = 1 / (2 * 12^k * k!)` and the threshold is `s₀ = 120k`. -/
theorem local_near_clique_exact {k s : ℕ} {H : Finset (Finset α)} {Q₀ : Finset α}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ Fintype.card α)
    (hupper : 2 * Fintype.card α ≤ (2 * k + 1) * s)
    (hQ₀ : Q₀.card = k * (s + 1) - 1)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hmissing : ((cliqueFamily k Q₀ \ H).card : ℝ) ≤
      (1 / (2 * (12 : ℝ) ^ k * (k.factorial : ℝ))) * (s : ℝ) ^ k) :
    H.card ≤ (k * (s + 1) - 1).choose k ∧
      (H.card = (k * (s + 1) - 1).choose k ↔
        ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧ H = cliqueFamily k R) := by
  exact clique_exact_of_missing_lt_choose hk hs hlower hupper hQ₀ hu hν
    (clique_missing_lt_choose_of_small hk hs hmissing)

theorem local_near_clique_exact_eventually (k : ℕ) (hk : 3 ≤ k) :
    ∃ η : ℝ, 0 < η ∧ ∃ s₀ : ℕ,
      ∀ (s : ℕ) (H : Finset (Finset α)) (Q₀ : Finset α),
        s₀ ≤ s → k * (s + 1) ≤ Fintype.card α →
        2 * Fintype.card α ≤ (2 * k + 1) * s → Q₀.card = k * (s + 1) - 1 →
        IsUniform k H → MatchingNumberAtMost s H →
        ((cliqueFamily k Q₀ \ H).card : ℝ) ≤ η * (s : ℝ) ^ k →
        H.card ≤ (k * (s + 1) - 1).choose k ∧
          (H.card = (k * (s + 1) - 1).choose k ↔
            ∃ R : Finset α, R.card = k * (s + 1) - 1 ∧ H = cliqueFamily k R) := by
  refine ⟨1 / (2 * (12 : ℝ) ^ k * (k.factorial : ℝ)), by positivity, 120 * k, ?_⟩
  intro s H Q₀ hs hlower hupper hQ₀ hu hν hmissing
  exact local_near_clique_exact hk hs hlower hupper hQ₀ hu hν hmissing

end SharpTailMatching.Matching
