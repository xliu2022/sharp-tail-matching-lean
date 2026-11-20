module

public import SharpTailMatching.Matching.CoverExact
public import SharpTailMatching.Matching.CliqueShiftExact
public import SharpTailMatching.Matching.EditDistance
public import SharpTailMatching.Matching.HeadlineBridge

/-! # From uniform edit stability to the exact matching theorem

The tolerance is chosen once for each fixed uniformity. The sparse theorem
handles every larger ambient vertex set, while the two local exactification
theorems handle the remaining compact ratio range.
-/

@[expose] public section

noncomputable section

namespace SharpTailMatching.Matching

/-- The exact-extremal specialization of uniform edit stability. -/
def GlobalExtremalEditStability (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℕ, ∀ s n : ℕ, s₀ ≤ s → k*(s+1) ≤ n →
    ∀ H : Finset (Finset (Fin n)), IsUniform k H → MatchingNumberAtMost s H →
      max (coverSize k n s) (cliqueSize k s) ≤ H.card →
      (∃ S : Finset (Fin n),S.card = s ∧
        ((H \ coverFamily k Finset.univ S).card : ℝ)+(coverFamily k Finset.univ S \ H).card ≤ ε*(n : ℝ)^k) ∨
      (∃ Q : Finset (Fin n),Q.card = k*(s+1)-1 ∧
        ((H \ cliqueFamily k Q).card : ℝ)+(cliqueFamily k Q \ H).card ≤ ε*(n : ℝ)^k)

/-- Uniform separation of the two local exactification ranges. This is a
finite numerical property of the two binomial candidate sizes. -/
def FiniteBranchSeparation (k : ℕ) : Prop :=
  ∃ ε : ℝ,0 < ε ∧ ∃ s₁ : ℕ,∀ s n : ℕ,∀ h : ℝ,
    s₁ ≤ s → k*(s+1) ≤ n → n ≤ 4*k^3*s →
    (max (coverSize k n s) (cliqueSize k s) : ℝ) ≤ h →
    (h ≤ (coverSize k n s : ℝ)+ε*(n : ℝ)^k → ((k : ℝ)+1/4)*(s : ℝ) ≤ n) ∧
    (h ≤ (cliqueSize k s : ℝ)+ε*(n : ℝ)^k → 2*n ≤ (2*k+1)*s)

theorem cardinal_upper_of_edit_close {α : Type*} [DecidableEq α]
    (H A : Finset α) {e : ℝ}
    (hclose : ((H \ A).card : ℝ)+(A \ H).card ≤ e) :
    (H.card : ℝ) ≤ A.card+e ∧ ((A \ H).card : ℝ) ≤ e := by
  have hid := sdiff_real_card_identity H A
  have hHA : (0 : ℝ) ≤ (H \ A).card := Nat.cast_nonneg _
  have hAH : (0 : ℝ) ≤ (A \ H).card := Nat.cast_nonneg _
  constructor <;> linarith

theorem uniform_exactification_of_stability (k : ℕ) (hk : 3 ≤ k)
    (hstable : GlobalExtremalEditStability k) (hseparate : FiniteBranchSeparation k) :
    ∃ s₀ : ℕ,∀ s n : ℕ,s₀ ≤ s → k*(s+1) ≤ n →
      ∀ H : Finset (Finset (Fin n)),IsUniform k H → MatchingNumberAtMost s H →
        max (coverSize k n s) (cliqueSize k s) ≤ H.card →
        H.card = max (coverSize k n s) (cliqueSize k s) ∧
          (IsCompleteCover k s H ∨ IsStandardClique k s H) := by
  let K : ℝ := (4*k^3 : ℕ)
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hK : (k : ℝ)+1/4 ≤ K := by
    have hsquare : 1 ≤ (k : ℝ)^2 := by nlinarith
    have hcube : (k : ℝ) ≤ (k : ℝ)^3 := by
      have h := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith only [h]
    dsimp [K]
    push_cast
    nlinarith
  obtain ⟨ηC,hηC,sC,hcover⟩ := local_cover_exact hk (by norm_num : (0 : ℝ) < 1/4) hK
  obtain ⟨εS,hεS,sS,hsep⟩ := hseparate
  let ηQ : ℝ := 1/(2*(12 : ℝ)^k*(k.factorial : ℝ))
  have hηQ : 0 < ηQ := by dsimp [ηQ]; positivity
  let ε : ℝ := min εS (min ηC (ηQ/K^k))
  have hε : 0 < ε := lt_min hεS (lt_min hηC (div_pos hηQ (pow_pos hKpos k)))
  have hεS' : ε ≤ εS := min_le_left _ _
  have hεC : ε ≤ ηC := (min_le_right _ _).trans (min_le_left _ _)
  have hεQ : ε ≤ ηQ/K^k := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨sE,hstab⟩ := hstable ε hε
  refine ⟨max sS (max sC (max (120*k) sE)),?_⟩
  intro s n hs hn H hu hν hlarge
  have hsS : sS ≤ s := (le_max_left _ _).trans hs
  have hsC : sC ≤ s := (le_max_left _ _).trans ((le_max_right _ _).trans hs)
  have hsQ : 120*k ≤ s := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
  have hsE : sE ≤ s := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
  have hV : IsOn (Finset.univ : Finset (Fin n)) H := fun e _ => Finset.subset_univ e
  by_cases hsparse : 4*k^3*s ≤ n
  · have hsp := sparse_matching_bound_and_equality (by omega : 2 ≤ k) hV hu hν
      (by simpa only [Finset.card_univ,Fintype.card_fin] using hsparse)
    simp only [Finset.card_univ,Fintype.card_fin] at hsp
    change H.card ≤ coverSize k n s ∧
      (H.card = coverSize k n s → ∃ S : Finset (Fin n),S ⊆ Finset.univ ∧
        S.card = s ∧ H = coverFamily k Finset.univ S) at hsp
    have heqC : H.card = coverSize k n s := le_antisymm hsp.1 ((le_max_left _ _).trans hlarge)
    refine ⟨le_antisymm (hsp.1.trans (le_max_left _ _)) hlarge,Or.inl ?_⟩
    obtain ⟨S,_,hScard,hH⟩ := hsp.2 heqC
    exact headline_cover_iff.mpr ⟨S,hScard,hH⟩
  · have hnK : n ≤ 4*k^3*s := le_of_not_ge hsparse
    have hnKR : (n : ℝ) ≤ K*(s : ℝ) := by
      dsimp [K]
      exact_mod_cast hnK
    have hsepH := hsep s n (H.card : ℝ) hsS hn hnK (by exact_mod_cast hlarge)
    rcases hstab s n hsE hn H hu hν hlarge with ⟨S,hScard,hclose⟩ | ⟨Q,hQcard,hclose⟩
    · have hcardS : (coverFamily k Finset.univ S).card = coverSize k n s := by
        rw [card_coverFamily k (Finset.subset_univ S),hScard]
        simp only [Finset.card_univ,Fintype.card_fin,coverSize]
      have hclose' := cardinal_upper_of_edit_close H (coverFamily k Finset.univ S) hclose
      rw [hcardS] at hclose'
      have hnear : (H.card : ℝ) ≤ (coverSize k n s : ℝ)+εS*(n : ℝ)^k :=
        hclose'.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hεS' (pow_nonneg (Nat.cast_nonneg n) _)))
      have hnlo := hsepH.1 hnear
      have hmiss : ((coverFamily k Finset.univ S \ H).card : ℝ) ≤ ηC*(n : ℝ)^k :=
        hclose'.2.trans (mul_le_mul_of_nonneg_right hεC (pow_nonneg (Nat.cast_nonneg n) _))
      have hloc := hcover Finset.univ S H
        (by simpa only [hScard] using hsC)
        (by simpa only [hScard,Finset.card_univ,Fintype.card_fin] using hnlo)
        (by simpa only [hScard,Finset.card_univ,Fintype.card_fin] using hnKR)
        hV hu (by simpa only [hScard] using hν) (Finset.subset_univ S)
        (by simpa only [Finset.card_univ,Fintype.card_fin] using hmiss)
      simp only [Finset.card_univ,Fintype.card_fin,hScard] at hloc
      change H.card ≤ coverSize k n s ∧ (H.card = coverSize k n s ↔
        ∃ T : Finset (Fin n),T ⊆ Finset.univ ∧ T.card = s ∧ H = coverFamily k Finset.univ T) at hloc
      have heqC : H.card = coverSize k n s := le_antisymm hloc.1 ((le_max_left _ _).trans hlarge)
      refine ⟨le_antisymm (hloc.1.trans (le_max_left _ _)) hlarge,Or.inl ?_⟩
      obtain ⟨T,_,hTcard,hH⟩ := hloc.2.mp heqC
      exact headline_cover_iff.mpr ⟨T,hTcard,hH⟩
    · have hcardQ : (cliqueFamily k Q).card = cliqueSize k s := by rw [card_cliqueFamily,hQcard]; rfl
      have hclose' := cardinal_upper_of_edit_close H (cliqueFamily k Q) hclose
      rw [hcardQ] at hclose'
      have hnear : (H.card : ℝ) ≤ (cliqueSize k s : ℝ)+εS*(n : ℝ)^k :=
        hclose'.1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hεS' (pow_nonneg (Nat.cast_nonneg n) _)))
      have hnhi := hsepH.2 hnear
      have hscaled : ε*K^k ≤ ηQ := (le_div_iff₀ (pow_pos hKpos k)).mp hεQ
      have hmiss : ((cliqueFamily k Q \ H).card : ℝ) ≤ ηQ*(s : ℝ)^k := by
        calc
          _ ≤ ε*(n : ℝ)^k := hclose'.2
          _ ≤ ε*(K*(s : ℝ))^k := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (Nat.cast_nonneg n) hnKR k) hε.le
          _ = (ε*K^k)*(s : ℝ)^k := by rw [mul_pow]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hscaled (pow_nonneg (Nat.cast_nonneg s) _)
      have hloc := local_near_clique_exact hk hsQ
        (by simpa only [Fintype.card_fin] using hn)
        (by simpa only [Fintype.card_fin] using hnhi) hQcard hu hν hmiss
      change H.card ≤ cliqueSize k s ∧ (H.card = cliqueSize k s ↔
        ∃ R : Finset (Fin n),R.card = k*(s+1)-1 ∧ H = cliqueFamily k R) at hloc
      have heqQ : H.card = cliqueSize k s := le_antisymm hloc.1 ((le_max_right _ _).trans hlarge)
      refine ⟨le_antisymm (hloc.1.trans (le_max_right _ _)) hlarge,Or.inr ?_⟩
      exact headline_clique_iff.mpr (hloc.2.mp heqQ)

/-- Exact upper bound and both directions of the equality classification,
with one threshold that is uniform in the ambient number of vertices. -/
theorem exact_matching_of_stability (k : ℕ) (hk : 3 ≤ k)
    (hstable : GlobalExtremalEditStability k) (hseparate : FiniteBranchSeparation k) :
    ∃ s₀ : ℕ,∀ s n : ℕ,s₀ ≤ s → k*(s+1) ≤ n →
      ∀ H : Finset (Finset (Fin n)),SharpTailMatching.IsUniform k H →
        SharpTailMatching.MatchingNumberAtMost s H →
        H.card ≤ max (coverSize k n s) (cliqueSize k s) ∧
        (H.card = max (coverSize k n s) (cliqueSize k s) ↔
          (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
          (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) := by
  obtain ⟨s₀,hs₀⟩ := uniform_exactification_of_stability k hk hstable hseparate
  refine ⟨s₀,?_⟩
  intro s n hs hn H hu hν
  have hclass := hs₀ s n hs hn H (headline_uniform_iff.mp hu) (headline_matching_iff.mp hν)
  constructor
  · by_cases hlarge : max (coverSize k n s) (cliqueSize k s) ≤ H.card
    · exact (hclass hlarge).1.le
    · exact le_of_lt (lt_of_not_ge hlarge)
  · exact headline_equality_of_classification (fun heq => (hclass heq.ge).2)

end SharpTailMatching.Matching
