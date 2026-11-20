module

public import SharpTailMatching.Matching.EditDistance
public import SharpTailMatching.Matching.AtomCosts

/-! # Editing estimates from distances to two-point weight sets -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α : Type*} [DecidableEq α] [Fintype α]

def roundedSet (a : ℝ) (w : α → ℝ) : Finset α :=
  Finset.univ.filter (fun v => a/2 ≤ w v)

def roundedWeight (a : ℝ) (w : α → ℝ) (v : α) : ℝ :=
  if v ∈ roundedSet a w then a else 0

theorem roundedWeight_error {a : ℝ} (ha : 0 ≤ a) {w : α → ℝ} (hw : ∀ v,0 ≤ w v) (v : α) :
    |w v-roundedWeight a w v| = twoAtomCost a (w v) := by
  rw [twoAtomCost_eq_rounding_error ha (hw v)]
  simp only [roundedWeight,roundedSet,Finset.mem_filter,Finset.mem_univ,true_and]

theorem sum_roundedWeight (a : ℝ) (w : α → ℝ) :
    (∑v,roundedWeight a w v) = a*((roundedSet a w).card : ℝ) := by
  dsimp only [roundedWeight]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  ring

theorem rounded_card_mean_bound {a : ℝ} (ha : 0 ≤ a) {w : α → ℝ} (hw : ∀ v,0 ≤ w v) :
    |a*((roundedSet a w).card : ℝ)-∑v,w v| ≤ ∑v,twoAtomCost a (w v) := by
  have h := Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun v => roundedWeight a w v-w v)
  rw [Finset.sum_sub_distrib,sum_roundedWeight] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro v _
  rw [abs_sub_comm,roundedWeight_error ha hw]

theorem sum_weights_le_rounding {a : ℝ} (ha : 0 ≤ a) {w : α → ℝ} (hw : ∀ v,0 ≤ w v)
    (e : Finset α) : (∑v ∈ e,w v) ≤ (∑v ∈ e,roundedWeight a w v)+∑v ∈ e,twoAtomCost a (w v) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have h := le_abs_self (w v-roundedWeight a w v)
  rw [roundedWeight_error ha hw] at h
  linarith

theorem weighted_incidence_sum (H : Finset (Finset α)) (f : α → ℝ) :
    (∑e ∈ H,∑v ∈ e,f v) = ∑v,(degree H v : ℝ)*f v := by
  calc
    _ = ∑e ∈ H,∑v,if v ∈ e then f v else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]
    _ = ∑v,∑e ∈ H,if v ∈ e then f v else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,degree]

theorem weighted_incidence_le {k : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H)
    {f : α → ℝ} (hf : ∀ v,0 ≤ f v) :
    (∑e ∈ H,∑v ∈ e,f v) ≤ (Fintype.card α : ℝ)^(k-1)*(∑v,f v) := by
  rw [weighted_incidence_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hf v)
  exact_mod_cast degree_le_pow hu v

theorem card_cost_bound {k : ℕ} {G : Finset (Finset α)} (hu : IsUniform k G)
    {f : α → ℝ} (hf : ∀ v,0 ≤ f v) {a : ℝ}
    (hcost : ∀ e ∈ G,a ≤ ∑v ∈ e,f v) :
    a*(G.card : ℝ) ≤ (Fintype.card α : ℝ)^(k-1)*(∑v,f v) := by
  have h := (Finset.sum_le_sum hcost).trans (weighted_incidence_le hu hf)
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm a] using h

theorem card_outside_le_uncovered (H U F : Finset (Finset α)) :
    (H \ F).card ≤ U.card+((H \ U) \ F).card := by
  have hsub : H \ F ⊆ U ∪ ((H \ U) \ F) := by
    intro e he
    obtain ⟨heH,heF⟩ := Finset.mem_sdiff.mp he
    by_cases heU : e ∈ U
    · exact Finset.mem_union_left _ heU
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heH,heU⟩,heF⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem rounded_cover_bound {k : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H)
    {w : α → ℝ} (hw : ∀ v,0 ≤ w v) :
    ((H \ coverFamily k Finset.univ (roundedSet 1 w)).card : ℝ) ≤
      (uncoveredFamily H w).card+(∑v,twoAtomCost 1 (w v))*(Fintype.card α : ℝ)^(k-1) := by
  let G := (H \ uncoveredFamily H w) \ coverFamily k Finset.univ (roundedSet 1 w)
  have hGsub : G ⊆ H := fun _ he => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hcost : ∀ e ∈ G,(1:ℝ) ≤ ∑v ∈ e,twoAtomCost 1 (w v) := by
    intro e he
    obtain ⟨heHU,heS⟩ := Finset.mem_sdiff.mp he
    obtain ⟨heH,heU⟩ := Finset.mem_sdiff.mp heHU
    have hcovered : 1 ≤ ∑v ∈ e,w v := by
      by_contra h
      exact heU (Finset.mem_filter.mpr ⟨heH,lt_of_not_ge h⟩)
    have hround : (∑v ∈ e,roundedWeight 1 w v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hve
      have hv : v ∉ roundedSet 1 w := by
        intro hv
        exact heS (mem_coverFamily_iff.mpr ⟨Finset.subset_univ e,hu e heH,v,hve,hv⟩)
      simp [roundedWeight,hv]
    have h := sum_weights_le_rounding (a := 1) (by norm_num) hw e
    rw [hround,zero_add] at h
    exact hcovered.trans h
  have hG := card_cost_bound (hu.mono hGsub) (fun v => twoAtomCost_nonneg 1 (w v)) hcost
  have hc := card_outside_le_uncovered H (uncoveredFamily H w)
    (coverFamily k Finset.univ (roundedSet 1 w))
  have hcR : ((H \ coverFamily k Finset.univ (roundedSet 1 w)).card : ℝ) ≤
      (uncoveredFamily H w).card+G.card := by exact_mod_cast hc
  nlinarith only [hG,hcR]

theorem rounded_clique_bound {k : ℕ} (hk : 1 ≤ k) {H : Finset (Finset α)} (hu : IsUniform k H)
    {w : α → ℝ} (hw : ∀ v,0 ≤ w v) :
    ((H \ cliqueFamily k (roundedSet (k : ℝ)⁻¹ w)).card : ℝ) ≤
      (uncoveredFamily H w).card+(k : ℝ)*(∑v,twoAtomCost (k : ℝ)⁻¹ (w v))*
        (Fintype.card α : ℝ)^(k-1) := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  let a : ℝ := (k : ℝ)⁻¹
  have ha : 0 ≤ a := (inv_pos.mpr hkpos).le
  let G := (H \ uncoveredFamily H w) \ cliqueFamily k (roundedSet a w)
  have hGsub : G ⊆ H := fun _ he => (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).1
  have hcost : ∀ e ∈ G,a ≤ ∑v ∈ e,twoAtomCost a (w v) := by
    intro e he
    obtain ⟨heHU,heS⟩ := Finset.mem_sdiff.mp he
    obtain ⟨heH,heU⟩ := Finset.mem_sdiff.mp heHU
    have hcovered : 1 ≤ ∑v ∈ e,w v := by
      by_contra h
      exact heU (Finset.mem_filter.mpr ⟨heH,lt_of_not_ge h⟩)
    have hnsub : ¬ e ⊆ roundedSet a w := fun h => heS (mem_cliqueFamily.mpr ⟨h,hu e heH⟩)
    obtain ⟨v,hve,hv⟩ := Finset.not_subset.mp hnsub
    have hroundv : roundedWeight a w v = 0 := by simp [roundedWeight,hv]
    have hround : (∑u ∈ e,roundedWeight a w u) ≤ 1-a := by
      have hle : (∑u ∈ e.erase v,roundedWeight a w u) ≤ ((e.erase v).card : ℝ)*a := by
        calc
          _ ≤ ∑_u ∈ e.erase v,a := by
            apply Finset.sum_le_sum
            intro u _
            dsimp only [roundedWeight]
            split_ifs <;> simp_all
          _ = _ := by simp [nsmul_eq_mul]
      have hs := Finset.sum_erase_add (f := roundedWeight a w) e hve
      rw [hroundv,add_zero] at hs
      rw [← hs]
      have hcard : (e.erase v).card = k-1 := by rw [Finset.card_erase_of_mem hve,hu e heH]
      rw [hcard] at hle
      have heq : ((k-1 : ℕ) : ℝ)*a = 1-a := by
        rw [Nat.cast_sub hk,Nat.cast_one]
        dsimp only [a]
        field_simp [hkpos.ne']
      exact hle.trans_eq heq
    have h := sum_weights_le_rounding ha hw e
    linarith
  have hG := card_cost_bound (hu.mono hGsub) (fun v => twoAtomCost_nonneg a (w v)) hcost
  have hscaled := mul_le_mul_of_nonneg_left hG hkpos.le
  have hka : (k:ℝ)*a = 1 := mul_inv_cancel₀ hkpos.ne'
  have hc := card_outside_le_uncovered H (uncoveredFamily H w) (cliqueFamily k (roundedSet a w))
  have hcR : ((H \ cliqueFamily k (roundedSet a w)).card : ℝ) ≤
      (uncoveredFamily H w).card+G.card := by exact_mod_cast hc
  have hgcard : (G.card : ℝ) ≤ (k:ℝ)*(∑v,twoAtomCost a (w v))*(Fintype.card α : ℝ)^(k-1) := by
    calc
      _ = (k:ℝ)*(a*(G.card : ℝ)) := by rw [← mul_assoc,hka,one_mul]
      _ ≤ _ := by convert hscaled using 1 <;> ring
  dsimp only [a] at hgcard hcR
  linarith

/-- Round to a cover and adjust to exactly `s` vertices. -/
theorem weight_edit_cover {k s : ℕ} {H : Finset (Finset α)} (hu : IsUniform k H)
    {w : α → ℝ} (hw : ∀ v,0 ≤ w v) (hs : s ≤ Fintype.card α) :
    ∃ S : Finset α, S.card = s ∧
      ((H \ coverFamily k Finset.univ S).card : ℝ) ≤
        (uncoveredFamily H w).card+(2*(∑v,twoAtomCost 1 (w v))+|(∑v,w v)-(s:ℝ)|)*
          (Fintype.card α : ℝ)^(k-1) := by
  let R := roundedSet 1 w
  obtain ⟨S,hScard,hchange⟩ := exists_adjusted_set R hs
  refine ⟨S,hScard,?_⟩
  have herr := rounded_card_mean_bound (a := 1) (by norm_num) hw
  simp only [one_mul] at herr
  have hsize : |(R.card : ℝ)-s| ≤ (∑v,twoAtomCost 1 (w v))+|(∑v,w v)-(s:ℝ)| := by
    have h := abs_sub_le (R.card : ℝ) (∑v,w v) (s:ℝ)
    change |(R.card : ℝ)-∑v,w v| ≤ _ at herr
    linarith
  have hchangele : ((R \ S).card : ℝ) ≤ (∑v,twoAtomCost 1 (w v))+|(∑v,w v)-(s:ℝ)| := by
    have hle : ((R \ S).card : ℝ) ≤ |(R.card : ℝ)-s| := by
      rw [← hchange,Nat.cast_add]
      linarith [Nat.cast_nonneg (α := ℝ) ((S \ R).card)]
    exact hle.trans hsize
  have hround := rounded_cover_bound hu hw
  have hsplit := sdiff_card_le_sum H (coverFamily k Finset.univ R) (coverFamily k Finset.univ S)
  have hfamily := coverFamily_sdiff_card_le k R S
  have hsplitR : ((H \ coverFamily k Finset.univ S).card : ℝ) ≤
      (H \ coverFamily k Finset.univ R).card+
        ((R \ S).card : ℝ)*(Fintype.card α : ℝ)^(k-1) := by
    exact_mod_cast hsplit.trans (Nat.add_le_add_left hfamily _)
  have hmul := mul_le_mul_of_nonneg_right hchangele (pow_nonneg (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _) (k-1))
  change ((H \ coverFamily k Finset.univ R).card : ℝ) ≤ _ at hround
  nlinarith only [hround,hsplitR,hmul]

/-- Round to a clique and adjust to exactly `k(s+1)-1` vertices. -/
theorem weight_edit_clique {k s : ℕ} (hk : 1 ≤ k) {H : Finset (Finset α)} (hu : IsUniform k H)
    {w : α → ℝ} (hw : ∀ v,0 ≤ w v) (hQ : k*(s+1)-1 ≤ Fintype.card α) :
    ∃ Q : Finset α, Q.card = k*(s+1)-1 ∧
      ((H \ cliqueFamily k Q).card : ℝ) ≤
        (uncoveredFamily H w).card+
          (2*(k:ℝ)*(∑v,twoAtomCost (k:ℝ)⁻¹ (w v))+(k:ℝ)*|(∑v,w v)-(s:ℝ)|+(k:ℝ))*
            (Fintype.card α : ℝ)^(k-1) := by
  let R := roundedSet (k:ℝ)⁻¹ w
  obtain ⟨Q,hQcard,hchange⟩ := exists_adjusted_set R hQ
  refine ⟨Q,hQcard,?_⟩
  have hkpos : (0:ℝ) < k := by exact_mod_cast hk
  have herr := rounded_card_mean_bound (a := (k:ℝ)⁻¹) (inv_pos.mpr hkpos).le hw
  have hscaled := mul_le_mul_of_nonneg_left herr hkpos.le
  have hsize1 : |(R.card : ℝ)-(k:ℝ)*(∑v,w v)| ≤ (k:ℝ)*(∑v,twoAtomCost (k:ℝ)⁻¹ (w v)) := by
    have heq : (k:ℝ)*|((k:ℝ)⁻¹)*((R.card : ℝ))-(∑v,w v)| =
        |(R.card : ℝ)-(k:ℝ)*(∑v,w v)| := by
      calc
        _ = |(k:ℝ)*(((k:ℝ)⁻¹)*((R.card : ℝ))-(∑v,w v))| := by
          rw [abs_mul,abs_of_pos hkpos]
        _ = _ := by congr 1; field_simp [hkpos.ne']
    rwa [heq] at hscaled
  have hkcard : ((k*(s+1)-1 : ℕ) : ℝ) = (k:ℝ)*((s:ℝ)+1)-1 := by
    have hpos : 1 ≤ k*(s+1) := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [Nat.cast_sub hpos]
    push_cast
    ring
  have hsize2 : |(k:ℝ)*(s:ℝ)-((k*(s+1)-1 : ℕ):ℝ)| ≤ (k:ℝ) := by
    have hk1real : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hneg : (k:ℝ)*(s:ℝ)-((k:ℝ)*((s:ℝ)+1)-1) ≤ 0 := by nlinarith
    rw [hkcard,abs_of_nonpos hneg]
    linarith
  have hsize3 : |(k:ℝ)*(∑v,w v)-(k:ℝ)*(s:ℝ)| = (k:ℝ)*|(∑v,w v)-(s:ℝ)| := by
    rw [← mul_sub,abs_mul,abs_of_pos hkpos]
  have hsize : |(R.card : ℝ)-((k*(s+1)-1 : ℕ):ℝ)| ≤
      (k:ℝ)*(∑v,twoAtomCost (k:ℝ)⁻¹ (w v))+(k:ℝ)*|(∑v,w v)-(s:ℝ)|+(k:ℝ) := by
    have h₁ := abs_sub_le (R.card : ℝ) ((k:ℝ)*(∑v,w v)) (((k*(s+1)-1 : ℕ):ℝ))
    have h₂ := abs_sub_le ((k:ℝ)*(∑v,w v)) ((k:ℝ)*(s:ℝ)) (((k*(s+1)-1 : ℕ):ℝ))
    rw [hsize3] at h₂
    linarith
  have hchangele : ((R \ Q).card : ℝ) ≤
      (k:ℝ)*(∑v,twoAtomCost (k:ℝ)⁻¹ (w v))+(k:ℝ)*|(∑v,w v)-(s:ℝ)|+(k:ℝ) := by
    have hle : ((R \ Q).card : ℝ) ≤ |(R.card : ℝ)-((k*(s+1)-1 : ℕ):ℝ)| := by
      rw [← hchange,Nat.cast_add]
      linarith [Nat.cast_nonneg (α := ℝ) ((Q \ R).card)]
    exact hle.trans hsize
  have hround := rounded_clique_bound hk hu hw
  have hsplit := sdiff_card_le_sum H (cliqueFamily k R) (cliqueFamily k Q)
  have hfamily := cliqueFamily_sdiff_card_le k R Q
  have hsplitR : ((H \ cliqueFamily k Q).card : ℝ) ≤
      (H \ cliqueFamily k R).card+((R \ Q).card : ℝ)*(Fintype.card α : ℝ)^(k-1) := by
    exact_mod_cast hsplit.trans (Nat.add_le_add_left hfamily _)
  have hmul := mul_le_mul_of_nonneg_right hchangele (pow_nonneg (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _) (k-1))
  change ((H \ cliqueFamily k R).card : ℝ) ≤ _ at hround
  nlinarith only [hround,hsplitR,hmul]

end SharpTailMatching.Matching
