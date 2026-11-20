/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Local exactification near a complete cover (manuscript Lemma 8.2).
The finite greedy extension and counting arguments are explicit; the sparse
range theorem is imported as a proved theorem, not as an additional assumption.
-/
module

public import SharpTailMatching.Matching.Sparse
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α]

/-- Missing `(k-1)`-sets in the link of `v` on `W`. -/
def missingLinks (k : ℕ) (H : Finset (Finset α)) (W : Finset α) (v : α) :
    Finset (Finset α) :=
  (W.powersetCard (k - 1)).filter fun A ↦ insert v A ∉ H

theorem exists_link_on_remaining {k r : ℕ} {H : Finset (Finset α)}
    {W U : Finset α} {v : α} (hUW : U ⊆ W) (hr : r ≤ U.card)
    (hmiss : (missingLinks k H W v).card < r.choose (k - 1)) :
    ∃ A ⊆ U, A.card = k - 1 ∧ insert v A ∈ H := by
  by_contra! hnot
  have hsub : U.powersetCard (k - 1) ⊆ missingLinks k H W v := by
    intro A hA
    obtain ⟨hAU, hcard⟩ := Finset.mem_powersetCard.mp hA
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powersetCard.mpr ⟨hAU.trans hUW, hcard⟩, hnot A hAU hcard⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_powersetCard] at hle
  exact (not_lt_of_ge ((Nat.choose_le_choose (k - 1) hr).trans hle)) hmiss

/-- A matching can be extended through every good center if each link has fewer
missing sets than the number of available choices. The capacity bound counts
`k` vertices for each initial edge and only `k-1` for each added edge. -/
theorem extend_matching_through_centers {k s r : ℕ}
    {H M₀ : Finset (Finset α)} {W G : Finset α}
    (hk : 1 ≤ k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost s H) (hM₀H : M₀ ⊆ H) (hM₀ : IsMatching M₀)
    (hWG : Disjoint W G) (hM₀G : Disjoint (M₀.biUnion id) G)
    (hcapacity : r + (k - 1) * s + M₀.card ≤ W.card)
    (hgood : ∀ v ∈ G, (missingLinks k H W v).card < r.choose (k - 1)) :
    M₀.card + G.card ≤ s := by
  have hex : ∀ T : Finset α, T ⊆ G →
      ∃ M : Finset (Finset α), M ⊆ H ∧ IsMatching M ∧
        M.card = M₀.card + T.card ∧ (M.biUnion id) ∩ G = T ∧
        ((M.biUnion id) ∩ W).card ≤ k * M₀.card + (k - 1) * T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨M₀, hM₀H, hM₀, by simp, ?_, ?_⟩
      · exact Finset.disjoint_iff_inter_eq_empty.mp hM₀G
      · simpa only [Finset.card_empty, Nat.mul_zero, Nat.add_zero] using
          (Finset.card_le_card (Finset.inter_subset_left :
            (M₀.biUnion id) ∩ W ⊆ M₀.biUnion id)).trans_eq
              (hM₀.card_biUnion (hu.mono hM₀H))
    | @insert v T hvT ih =>
      intro hTG
      have hvG : v ∈ G := hTG (Finset.mem_insert_self _ _)
      have hTG' : T ⊆ G := (Finset.subset_insert _ _).trans hTG
      obtain ⟨M, hMH, hM, hMcard, hMG, hMW⟩ := ih hTG'
      have hMs : M.card ≤ s := hν M hMH hM
      have hvM : v ∉ M.biUnion id := by
        intro hv
        have : v ∈ (M.biUnion id) ∩ G := Finset.mem_inter.mpr ⟨hv, hvG⟩
        exact hvT (hMG ▸ this)
      have hvW : v ∉ W := fun hv ↦ Finset.disjoint_left.mp hWG hv hvG
      have hused : ((M.biUnion id) ∩ W).card ≤ (k - 1) * s + M₀.card := by
        have hk' : k = (k - 1) + 1 := by omega
        have hmul := Nat.mul_le_mul_left (k - 1) hMs
        rw [hMcard] at hmul
        nlinarith
      have havail : r ≤ (W \ M.biUnion id).card := by
        have hsplit := Finset.card_inter_add_card_sdiff W (M.biUnion id)
        rw [Finset.inter_comm W (M.biUnion id)] at hsplit
        omega
      obtain ⟨A, hA, hAcard, hAH⟩ := exists_link_on_remaining
        (Finset.sdiff_subset : W \ M.biUnion id ⊆ W) havail (hgood v hvG)
      have hAW : A ⊆ W := hA.trans Finset.sdiff_subset
      have hvA : v ∉ A := fun hv ↦ hvW (hAW hv)
      have hAd : Disjoint A (M.biUnion id) := by
        apply Finset.disjoint_left.mpr
        intro w hw hwM
        exact (Finset.mem_sdiff.mp (hA hw)).2 hwM
      have hAG : Disjoint A G := hWG.mono_left hAW
      have heM : insert v A ∉ M := by
        intro he
        exact hvM (Finset.mem_biUnion.mpr ⟨insert v A, he, Finset.mem_insert_self _ _⟩)
      have hd : ∀ e ∈ M, Disjoint (insert v A) e := by
        intro e he
        apply Finset.disjoint_left.mpr
        intro w hw hwe
        have hwM : w ∈ M.biUnion id := Finset.mem_biUnion.mpr ⟨e, he, hwe⟩
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hvM hwM
        · exact Finset.disjoint_left.mp hAd hw hwM
      refine ⟨insert (insert v A) M, Finset.insert_subset hAH hMH, hM.insert hd,
        ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem heM, Finset.card_insert_of_notMem hvT, hMcard]
        omega
      · rw [Finset.biUnion_insert, id_eq, Finset.union_inter_distrib_right, hMG]
        have heG : insert v A ∩ G = {v} := by
          ext w
          simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ⟨rfl | hwA, hwG⟩
            · rfl
            · exact False.elim (Finset.disjoint_left.mp hAG hwA hwG)
          · rintro rfl
            exact ⟨Or.inl rfl, hvG⟩
        rw [heG, Finset.singleton_union]
      · rw [Finset.biUnion_insert, id_eq, Finset.union_inter_distrib_right]
        have heW : insert v A ∩ W = A := by
          ext w
          simp only [Finset.mem_inter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hwA, hwW⟩
            · exact False.elim (hvW hwW)
            · exact hwA
          · intro hwA
            exact ⟨Or.inr hwA, hAW hwA⟩
        rw [heW]
        have hcard := Finset.card_union_le A ((M.biUnion id) ∩ W)
        rw [hAcard] at hcard
        rw [Finset.card_insert_of_notMem hvT]
        nlinarith
  obtain ⟨M, hMH, hM, hcard, _, _⟩ := hex G Finset.Subset.rfl
  simpa only [hcard] using hν M hMH hM

/-- The induced subfamily on a prescribed vertex set. -/
def induce (H : Finset (Finset α)) (U : Finset α) : Finset (Finset α) :=
  H.filter fun e ↦ e ⊆ U

theorem induce_subset (H : Finset (Finset α)) (U : Finset α) : induce H U ⊆ H :=
  Finset.filter_subset _ _

theorem induce_on (H : Finset (Finset α)) (U : Finset α) : IsOn U (induce H U) :=
  fun _ he ↦ (Finset.mem_filter.mp he).2

theorem induce_uniform {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) (U : Finset α) : IsUniform k (induce H U) :=
  hu.mono (induce_subset H U)

/-- Removing all good centers leaves matching number at most the number of bad centers. -/
theorem residual_matching_bound {k r : ℕ} {V S B : Finset α}
    {H : Finset (Finset α)} (hk : 1 ≤ k) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost S.card H) (hBS : B ⊆ S)
    (hcapacity : r + (k - 1) * S.card + (B.card + 1) ≤ (V \ S).card)
    (hgood : ∀ v ∈ S \ B,
      (missingLinks k H (V \ S) v).card < r.choose (k - 1)) :
    MatchingNumberAtMost B.card (induce H (V \ (S \ B))) := by
  intro M hMR hM
  by_contra hnot
  obtain ⟨M₀, hM₀M, hcard⟩ := Finset.exists_subset_card_eq
    (show B.card + 1 ≤ M.card by omega)
  have hM₀H : M₀ ⊆ H := hM₀M.trans (hMR.trans (induce_subset _ _))
  have hM₀G : Disjoint (M₀.biUnion id) (S \ B) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvG
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact (Finset.mem_sdiff.mp ((induce_on H (V \ (S \ B))) e (hMR (hM₀M he)) hve)).2 hvG
  have hWG : Disjoint (V \ S) (S \ B) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvG
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hvG).1
  have hext := extend_matching_through_centers hk hu hν hM₀H (hM.mono hM₀M)
    hWG hM₀G (by simpa only [hcard] using hcapacity) hgood
  rw [hcard, Finset.card_sdiff_of_subset hBS] at hext
  have hBcard := Finset.card_le_card hBS
  omega

theorem card_outside_induce_le {k : ℕ} {V U : Finset α}
    {H : Finset (Finset α)} (hV : IsOn V H) (hu : IsUniform k H) (hUV : U ⊆ V) :
    (H \ induce H U).card ≤ V.card.choose k - U.card.choose k := by
  have hsub : H \ induce H U ⊆ V.powersetCard k \ U.powersetCard k := by
    intro e he
    obtain ⟨heH, heR⟩ := Finset.mem_sdiff.mp he
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨hV e heH, hu e heH⟩, ?_⟩
    intro heU
    exact heR (Finset.mem_filter.mpr ⟨heH, (Finset.mem_powersetCard.mp heU).1⟩)
  have hle := Finset.card_le_card hsub
  simpa only [Finset.card_sdiff_of_subset (Finset.powersetCard_mono hUV),
    Finset.card_powersetCard] using hle

/-- Exact finite form of the local cover argument. The two explicit capacity
conditions are later supplied by the quantitative small-error hypothesis. -/
theorem cover_exact_of_good_centers {k r : ℕ} {V S B : Finset α}
    {H : Finset (Finset α)} (hk : 2 ≤ k) (hV : IsOn V H) (hu : IsUniform k H)
    (hν : MatchingNumberAtMost S.card H) (hSV : S ⊆ V) (hBS : B ⊆ S)
    (hcapacity : r + (k - 1) * S.card + (B.card + 1) ≤ (V \ S).card)
    (hsparse : 4 * k ^ 3 * B.card ≤ (V \ (S \ B)).card)
    (hgood : ∀ v ∈ S \ B,
      (missingLinks k H (V \ S) v).card < r.choose (k - 1)) :
    H.card ≤ V.card.choose k - (V.card - S.card).choose k ∧
      (H.card = V.card.choose k - (V.card - S.card).choose k →
        ∃ T, T ⊆ V ∧ T.card = S.card ∧ H = coverFamily k V T) := by
  let G := S \ B
  let U := V \ G
  let R := induce H U
  have hGV : G ⊆ V := Finset.sdiff_subset.trans hSV
  have hUV : U ⊆ V := Finset.sdiff_subset
  have hGcard : G.card = S.card - B.card := Finset.card_sdiff_of_subset hBS
  have hUcard : U.card = V.card - G.card := Finset.card_sdiff_of_subset hGV
  have hBcard : B.card ≤ S.card := Finset.card_le_card hBS
  have hScard : S.card ≤ V.card := Finset.card_le_card hSV
  have hdiff : U.card - B.card = V.card - S.card := by omega
  have hRU : IsOn U R := induce_on H U
  have hRu : IsUniform k R := induce_uniform hu U
  have hRν : MatchingNumberAtMost B.card R :=
    residual_matching_bound (by omega) hu hν hBS hcapacity hgood
  obtain ⟨hRbound, hReq⟩ := sparse_matching_bound_and_equality hk hRU hRu hRν hsparse
  have hout : (H \ R).card ≤ V.card.choose k - U.card.choose k :=
    card_outside_induce_le hV hu hUV
  have hsplit : R.card + (H \ R).card = H.card := by
    rw [Finset.card_sdiff_of_subset (induce_subset H U)]
    exact Nat.add_sub_of_le (Finset.card_le_card (induce_subset H U))
  have hcu : U.card.choose k ≤ V.card.choose k :=
    Nat.choose_le_choose k (Finset.card_le_card hUV)
  have hcw : (U.card - B.card).choose k ≤ U.card.choose k :=
    Nat.choose_le_choose k (Nat.sub_le _ _)
  have hbound : H.card ≤ V.card.choose k - (V.card - S.card).choose k := by
    rw [← hdiff]
    clear hReq
    omega
  refine ⟨hbound, ?_⟩
  intro heq
  have hRequal : R.card = U.card.choose k - (U.card - B.card).choose k := by
    rw [← hdiff] at heq
    clear hReq
    omega
  obtain ⟨T, hTU, hTcard, hRT⟩ := hReq hRequal
  have hGT : Disjoint G T := by
    apply Finset.disjoint_left.mpr
    intro v hvG hvT
    exact (Finset.mem_sdiff.mp (hTU hvT)).2 hvG
  have hcenters : (G ∪ T).card = S.card := by
    rw [Finset.card_union_of_disjoint hGT, hTcard, hGcard]
    exact Nat.sub_add_cancel hBcard
  have hcentersV : G ∪ T ⊆ V := Finset.union_subset hGV (hTU.trans hUV)
  have hHsub : H ⊆ coverFamily k V (G ∪ T) := by
    intro e he
    refine mem_coverFamily_iff.mpr ⟨hV e he, hu e he, ?_⟩
    by_cases hd : Disjoint e G
    · have heU : e ⊆ U := by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨hV e he hv,
          fun hvG ↦ Finset.disjoint_left.mp hd hv hvG⟩
      have heR : e ∈ R := Finset.mem_filter.mpr ⟨he, heU⟩
      rw [hRT] at heR
      obtain ⟨v, hve, hvT⟩ := (mem_coverFamily_iff.mp heR).2.2
      exact ⟨v, hve, Finset.mem_union_right _ hvT⟩
    · obtain ⟨v, hve, hvG⟩ := Finset.not_disjoint_iff.mp hd
      exact ⟨v, hve, Finset.mem_union_left _ hvG⟩
  refine ⟨G ∪ T, hcentersV, hcenters, Finset.eq_of_subset_of_card_le hHsub ?_⟩
  rw [card_coverFamily k hcentersV, hcenters, heq]

/-- Missing links at different centers give different missing cover edges:
each of the resulting edges contains exactly one center. -/
theorem sum_missing_links_le {k : ℕ} {V S B : Finset α}
    {H : Finset (Finset α)} (hk : 1 ≤ k) (hSV : S ⊆ V) (hBS : B ⊆ S) :
    (∑ v ∈ B, (missingLinks k H (V \ S) v).card) ≤
      (coverFamily k V S \ H).card := by
  let F := B.sigma fun v ↦ missingLinks k H (V \ S) v
  have hle : F.card ≤ (coverFamily k V S \ H).card := by
    apply Finset.card_le_card_of_injOn (fun p : (Σ _v : α, Finset α) ↦ insert p.1 p.2)
    · rintro ⟨v, A⟩ hp
      obtain ⟨hvB, hA⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hAW, hnot⟩ := Finset.mem_filter.mp hA
      obtain ⟨hAW, hAcard⟩ := Finset.mem_powersetCard.mp hAW
      have hvS := hBS hvB
      have hvA : v ∉ A := fun hv ↦ (Finset.mem_sdiff.mp (hAW hv)).2 hvS
      refine Finset.mem_sdiff.mpr ⟨mem_coverFamily_iff.mpr ⟨?_, ?_, ?_⟩, hnot⟩
      · exact Finset.insert_subset (hSV hvS) (hAW.trans Finset.sdiff_subset)
      · rw [Finset.card_insert_of_notMem hvA, hAcard]
        omega
      · exact ⟨v, Finset.mem_insert_self _ _, hvS⟩
    · rintro ⟨v, A⟩ hp ⟨w, C⟩ hq heq
      obtain ⟨hvB, hA⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hwB, hC⟩ := Finset.mem_sigma.mp hq
      have hAW := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).1
      have hCW := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).1
      change insert v A = insert w C at heq
      have hvw : v = w := by
        have hv : v ∈ insert w C := heq ▸ Finset.mem_insert_self v A
        rcases Finset.mem_insert.mp hv with hvw | hvC
        · exact hvw
        · exact False.elim ((Finset.mem_sdiff.mp (hCW hvC)).2 (hBS hvB))
      subst w
      have hvA : v ∉ A := fun hv ↦ (Finset.mem_sdiff.mp (hAW hv)).2 (hBS hvB)
      have hvC : v ∉ C := fun hv ↦ (Finset.mem_sdiff.mp (hCW hv)).2 (hBS hvB)
      have hAC : A = C := by
        have herase := congrArg (fun e : Finset α ↦ e.erase v) heq
        simpa only [Finset.erase_insert hvA, Finset.erase_insert hvC] using herase
      subst C
      rfl
  simpa only [F, Finset.card_sigma] using hle

theorem bad_centers_card_mul_le {k D : ℕ} {V S B : Finset α}
    {H : Finset (Finset α)} (hk : 1 ≤ k) (hSV : S ⊆ V) (hBS : B ⊆ S)
    (hbad : ∀ v ∈ B, D ≤ (missingLinks k H (V \ S) v).card) :
    B.card * D ≤ (coverFamily k V S \ H).card := by
  calc
    B.card * D = ∑ _v ∈ B, D := by simp
    _ ≤ ∑ v ∈ B, (missingLinks k H (V \ S) v).card := Finset.sum_le_sum hbad
    _ ≤ (coverFamily k V S \ H).card := sum_missing_links_le hk hSV hBS

/-- An explicit binomial lower bound, with no asymptotic or floor-limit argument. -/
theorem division_choose_lower {k L s : ℕ} (hL : 0 < L) (hs : 2 * L * k ≤ s) :
    s ^ (k - 1) ≤ ((2 * L) ^ (k - 1) * (k - 1).factorial) *
      (s / L).choose (k - 1) := by
  have hr : 2 * k ≤ s / L := (Nat.le_div_iff_mul_le hL).mpr (by nlinarith)
  have ht : s / L + 1 ≤ 2 * (s / L + 1 - (k - 1)) := by omega
  have hsbound : s ≤ (2 * L) * (s / L + 1 - (k - 1)) := by
    have hdiv := Nat.lt_mul_div_succ s hL
    have hmul := Nat.mul_le_mul_left L ht
    nlinarith
  calc
    s ^ (k - 1) ≤ ((2 * L) * (s / L + 1 - (k - 1))) ^ (k - 1) :=
      Nat.pow_le_pow_left hsbound (k - 1)
    _ = (2 * L) ^ (k - 1) * (s / L + 1 - (k - 1)) ^ (k - 1) := mul_pow _ _ _
    _ ≤ (2 * L) ^ (k - 1) * (s / L).descFactorial (k - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial _ _)
    _ = ((2 * L) ^ (k - 1) * (k - 1).factorial) *
        (s / L).choose (k - 1) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring

/-- The explicit error constant forces at most `s/L` bad centers. -/
theorem bad_count_of_small_missing {k L s n b m : ℕ} {K : ℝ}
    (hk : 1 ≤ k) (hL : 0 < L) (hK : 0 < K) (hs : 2 * L * k ≤ s)
    (hn : (n : ℝ) ≤ K * s)
    (hbad : b * (s / L).choose (k - 1) ≤ m)
    (hmissing : (m : ℝ) ≤
      (1 / ((L : ℝ) * (((2 * L) ^ (k - 1) * (k - 1).factorial : ℕ) : ℝ) * K ^ k)) *
        (n : ℝ) ^ k) : L * b ≤ s := by
  let C : ℕ := (2 * L) ^ (k - 1) * (k - 1).factorial
  have hC : 0 < C := by dsimp [C]; positivity
  have hCr : 0 < (C : ℝ) := by exact_mod_cast hC
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hspos : 0 < s := by nlinarith
  have hsr : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hlower : (s : ℝ) ^ (k - 1) ≤ (C : ℝ) * ((s / L).choose (k - 1) : ℝ) := by
    exact_mod_cast division_choose_lower hL hs
  have hbad' : (b : ℝ) * ((s / L).choose (k - 1) : ℝ) ≤ m := by exact_mod_cast hbad
  have hnpow : (n : ℝ) ^ k ≤ (K * s) ^ k := by gcongr
  have hmupper : (m : ℝ) ≤ (s : ℝ) ^ k / ((L : ℝ) * C) := by
    calc
      (m : ℝ) ≤ (1 / ((L : ℝ) * C * K ^ k)) * (n : ℝ) ^ k := hmissing
      _ ≤ (1 / ((L : ℝ) * C * K ^ k)) * (K * s) ^ k := by gcongr
      _ = (s : ℝ) ^ k / ((L : ℝ) * C) := by
        rw [mul_pow]
        field_simp
  have hstep : (L : ℝ) * b * (s : ℝ) ^ (k - 1) ≤ (s : ℝ) ^ k := by
    calc
      (L : ℝ) * b * (s : ℝ) ^ (k - 1) ≤
          (L : ℝ) * b * ((C : ℝ) * ((s / L).choose (k - 1) : ℝ)) := by gcongr
      _ = (L : ℝ) * C * ((b : ℝ) * ((s / L).choose (k - 1) : ℝ)) := by ring
      _ ≤ (L : ℝ) * C * m := by gcongr
      _ ≤ (s : ℝ) ^ k := by
        have h := (le_div_iff₀ (mul_pos hLr hCr)).mp hmupper
        nlinarith only [h]
  have hpow : (s : ℝ) ^ k = (s : ℝ) * (s : ℝ) ^ (k - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    ring
  rw [hpow] at hstep
  have hLb : (L : ℝ) * b ≤ s :=
    (mul_le_mul_iff_left₀ (pow_pos hsr (k - 1))).mp hstep
  exact_mod_cast hLb

/-- Quantitative choices that simultaneously leave room for the greedy
extensions and put the residual family in the proved sparse range. -/
theorem local_cover_capacities {k L s n b : ℕ} {γ : ℝ}
    (hk : 2 ≤ k) (hL : 0 < L) (hLlarge : 4 * k ^ 3 ≤ L)
    (hγL : 4 ≤ γ * L) (hs : L ≤ s) (hLb : L * b ≤ s)
    (hn : ((k : ℝ) + γ) * s ≤ n) :
    s / L + (k - 1) * s + (b + 1) ≤ n - s ∧
      4 * k ^ 3 * b ≤ n - s := by
  have hLr : 0 < (L : ℝ) := by exact_mod_cast hL
  have hr : (L : ℝ) * ((s / L : ℕ) : ℝ) ≤ s := by
    exact_mod_cast (show L * (s / L) ≤ s by simpa [Nat.mul_comm] using Nat.div_mul_le_self s L)
  have hb : (L : ℝ) * b ≤ s := by exact_mod_cast hLb
  have hLs : (L : ℝ) ≤ s := by exact_mod_cast hs
  have hbudget : ((s / L : ℕ) : ℝ) + b + 1 ≤ γ * s := by
    apply (mul_le_mul_iff_right₀ hLr).mp
    have hscale := mul_le_mul_of_nonneg_right hγL (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    nlinarith
  have hns : k * s + s / L + b + 1 ≤ n := by
    have hreal : (k : ℝ) * s + ((s / L : ℕ) : ℝ) + b + 1 ≤ n := by nlinarith
    exact_mod_cast hreal
  have h2s : 2 * s ≤ n := by
    have hks := Nat.mul_le_mul_right s hk
    exact hks.trans ((Nat.le_add_right (k * s) (s / L + b + 1)).trans
      (by simpa only [Nat.add_assoc] using hns))
  have hsub : n - s + s = n := Nat.sub_add_cancel (by omega)
  have hk' : k = (k - 1) + 1 := by omega
  constructor
  · nlinarith
  · calc
      4 * k ^ 3 * b ≤ L * b := Nat.mul_le_mul_right b hLlarge
      _ ≤ s := hLb
      _ ≤ n - s := by omega

/-- Manuscript Lemma 8.2, including the equality characterization. The constants
are uniform over every finite vertex set and every family on that set. A valid
choice is `s₀ = 2*L*k` and
`η = 1 / (L * (2*L)^(k-1) * (k-1)! * K^k)`, where
`L > max (4/γ) (4*k^3) + 1`. -/
theorem local_cover_exact {k : ℕ} (hk : 3 ≤ k) {γ K : ℝ}
    (hγ : 0 < γ) (hK : (k : ℝ) + γ ≤ K) :
    ∃ η : ℝ, 0 < η ∧ ∃ s₀ : ℕ,
      ∀ {β : Type*} [DecidableEq β] (V S : Finset β) (H : Finset (Finset β)),
        s₀ ≤ S.card →
        ((k : ℝ) + γ) * S.card ≤ V.card → (V.card : ℝ) ≤ K * S.card →
        IsOn V H → IsUniform k H → MatchingNumberAtMost S.card H → S ⊆ V →
        ((coverFamily k V S \ H).card : ℝ) ≤ η * (V.card : ℝ) ^ k →
        H.card ≤ V.card.choose k - (V.card - S.card).choose k ∧
          (H.card = V.card.choose k - (V.card - S.card).choose k ↔
            ∃ T, T ⊆ V ∧ T.card = S.card ∧ H = coverFamily k V T) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (4 / γ) (((4 * k ^ 3 : ℕ) : ℝ)) + 1)
  have hmaxnonneg : 0 ≤ max (4 / γ) (((4 * k ^ 3 : ℕ) : ℝ)) :=
    (Nat.cast_nonneg _).trans (le_max_right _ _)
  have hLr : 0 < (L : ℝ) := by linarith
  have hLnat : 0 < L := by exact_mod_cast hLr
  have hLlarge : 4 * k ^ 3 ≤ L := by
    have h := le_max_right (4 / γ) (((4 * k ^ 3 : ℕ) : ℝ))
    exact_mod_cast (show (((4 * k ^ 3 : ℕ) : ℝ)) ≤ L by linarith)
  have hγL : 4 ≤ γ * L := by
    have h := le_max_left (4 / γ) (((4 * k ^ 3 : ℕ) : ℝ))
    have hdiv : 4 / γ ≤ (L : ℝ) := by linarith
    have hmul := (div_le_iff₀ hγ).mp hdiv
    nlinarith
  have hKpos : 0 < K := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  let C : ℕ := (2 * L) ^ (k - 1) * (k - 1).factorial
  let η : ℝ := 1 / ((L : ℝ) * C * K ^ k)
  have hCpos : 0 < (C : ℝ) := by dsimp [C]; positivity
  refine ⟨η, by dsimp [η]; positivity, 2 * L * k, ?_⟩
  intro β inst V S H hs hnlo hnhi hV hu hν hSV hmissing
  let B := S.filter fun v ↦ (S.card / L).choose (k - 1) ≤
    (missingLinks k H (V \ S) v).card
  have hBS : B ⊆ S := Finset.filter_subset _ _
  have hbad : B.card * (S.card / L).choose (k - 1) ≤
      (coverFamily k V S \ H).card := by
    apply bad_centers_card_mul_le (by omega) hSV hBS
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hLb : L * B.card ≤ S.card :=
    bad_count_of_small_missing (by omega) hLnat hKpos hs hnhi hbad hmissing
  have hsL : L ≤ S.card := by nlinarith
  obtain ⟨hcapacity, hsparse⟩ := local_cover_capacities (by omega) hLnat hLlarge hγL hsL hLb hnlo
  have hWU : V \ S ⊆ V \ (S \ B) := by
    intro v hv
    obtain ⟨hvV, hvS⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvV, fun hvG ↦ hvS (Finset.mem_sdiff.mp hvG).1⟩
  have hgood : ∀ v ∈ S \ B,
      (missingLinks k H (V \ S) v).card < (S.card / L).choose (k - 1) := by
    intro v hv
    obtain ⟨hvS, hvB⟩ := Finset.mem_sdiff.mp hv
    apply lt_of_not_ge
    intro hbad
    exact hvB (Finset.mem_filter.mpr ⟨hvS, hbad⟩)
  obtain ⟨hbound, heq⟩ := cover_exact_of_good_centers (by omega) hV hu hν hSV hBS
    (by simpa only [Finset.card_sdiff_of_subset hSV] using hcapacity)
    (hsparse.trans (by simpa only [Finset.card_sdiff_of_subset hSV] using Finset.card_le_card hWU))
    hgood
  refine ⟨hbound, heq, ?_⟩
  rintro ⟨T, hTV, hTcard, rfl⟩
  rw [card_coverFamily k hTV, hTcard]

end SharpTailMatching.Matching
