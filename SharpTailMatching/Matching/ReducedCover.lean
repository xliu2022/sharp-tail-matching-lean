/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Lift a fractional cover of regular dense cells and count the uncovered
hyperedges. The three error terms are repeated colors, irregular-cell mass,
and sparse-cell density.
-/
module

public import SharpTailMatching.Matching.InitialPartition
public import SharpTailMatching.Matching.ReducedRounding

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I] [Fintype α] [Fintype I]

noncomputable def uncoveredFamily (H : Finset (Finset α)) (w : α → ℝ) : Finset (Finset α) :=
  H.filter fun e ↦ (∑ v ∈ e, w v) < 1

omit [DecidableEq α] in
theorem sum_lifted_weights (c : α → I) (z : I → ℝ) :
    (∑ v, z (c v)) = ∑ i, ((labelFiber c i).card : ℝ) * z i := by
  rw [← sum_labelFiber c (fun v ↦ z (c v))]
  apply Finset.sum_congr rfl
  intro i _
  have hconst : ∀ v ∈ labelFiber c i, z (c v) = z i := by
    intro v hv
    rw [(Finset.mem_filter.mp hv).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

omit [DecidableEq α] [Fintype α] [Fintype I] in
theorem crossing_edge_covered {c : α → I} {R : Finset (Finset I)} {z : I → ℝ}
    (hz : IsFractionalCover R z) {E : Finset α} (hcross : IsCrossing c E)
    (hER : E.image c ∈ R) : 1 ≤ ∑ v ∈ E, z (c v) := by
  have h := hz.2 (E.image c) hER
  rwa [Finset.sum_image hcross] at h

omit [Fintype α] in
theorem tuple_injective_of_uniform_member {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) {x : Fin k → α} (hx : tupleEdge x ∈ H) : Function.Injective x := by
  have hcard : (Finset.univ.image x).card = (Finset.univ : Finset (Fin k)).card := by
    simpa only [tupleEdge, Finset.card_univ, Fintype.card_fin] using hu (tupleEdge x) hx
  have hinj := Finset.card_image_iff.mp hcard
  exact fun r s hrs ↦ hinj (Finset.mem_univ _) (Finset.mem_univ _) hrs

theorem family_card_le_tuple_count {k : ℕ} {K : Finset (Finset α)} (hu : IsUniform k K) :
    K.card ≤ (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K).card := by
  classical
  have hex : ∀ e : K, ∃ x : Fin k → α, Function.Injective x ∧ tupleEdge x = e.val :=
    fun e ↦ exists_tuple_of_card (hu e e.property)
  let x := fun e : K ↦ (hex e).choose
  have hcard : K.attach.card ≤ (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K).card := by
    apply Finset.card_le_card_of_injOn x
    · intro e _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hex e).choose_spec.2 ▸ e.property⟩
    · intro e _ f _ hef
      apply Subtype.ext
      exact (hex e).choose_spec.2.symm.trans ((congrArg tupleEdge hef).trans (hex f).choose_spec.2)
  simpa only [Finset.card_attach] using hcard

theorem mem_reducedFamily_of_cell {k : ℕ} {c : α → I} {H : Finset (Finset α)} {ε d : ℝ}
    {a : Fin k → I} (ha : Function.Injective a)
    (hregular : IsRectRegular c (tupleIndicator H) ε a)
    (hdensity : d ≤ labelMean (tupleLabel c) (tupleIndicator H) a) :
    tupleEdge a ∈ reducedFamily k c H ε d := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, a, ha, rfl, hregular, hdensity⟩
  rw [tupleEdge, Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]

theorem uncovered_lift_bound {k : ℕ} {c : α → I} {H : Finset (Finset α)} {ε d : ℝ}
    (hu : IsUniform k H) (hd : 0 ≤ d) {z : I → ℝ}
    (hz : IsFractionalCover (reducedFamily k c H ε d) z) :
    ((uncoveredFamily H (fun v ↦ z (c v))).card : ℝ) ≤
      (noncrossingFamily c H).card + irregularMass c (tupleIndicator (k := k) H) ε +
        d * Fintype.card (Fin k → α) := by
  classical
  let U := uncoveredFamily H (fun v ↦ z (c v))
  let K := U.filter fun e ↦ IsCrossing c e
  let G : (Fin k → α) → ℝ := fun x ↦ if tupleEdge x ∈ K then 1 else 0
  have hKsub : K ⊆ H := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hKcard : (K.card : ℝ) ≤ ∑ x, G x := by
    have h := family_card_le_tuple_count (hu.mono hKsub)
    have h' : (K.card : ℝ) ≤ (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K).card := by
      exact_mod_cast h
    simpa only [G, Finset.sum_boole] using h'
  have hGle : ∀ x, G x ≤ tupleIndicator H x := by
    intro x
    by_cases hx : tupleEdge x ∈ K
    · simp only [G, ite_eq_left hx, tupleIndicator, ite_eq_left (hKsub hx), le_refl]
    · simp only [G, ite_eq_right hx]
      exact (tupleIndicator_bounds H x).1
  have hG₁ : ∀ x, G x ≤ 1 := by
    intro x
    dsimp only [G]
    split_ifs <;> norm_num
  have hcell : ∀ a : Fin k → I,
      (∑ x ∈ labelFiber (tupleLabel c) a, G x) ≤
        (if a ∈ irregularCells c (tupleIndicator H) ε then
          ((labelFiber (tupleLabel c) a).card : ℝ) else 0) +
          d * (labelFiber (tupleLabel c) a).card := by
    intro a
    by_cases hbad : a ∈ irregularCells c (tupleIndicator H) ε
    · rw [ite_eq_left hbad]
      have hsum := Finset.sum_le_sum (fun x (_ : x ∈ labelFiber (tupleLabel c) a) ↦ hG₁ x)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
      exact hsum.trans (le_add_of_nonneg_right (mul_nonneg hd (Nat.cast_nonneg _)))
    · rw [ite_eq_right hbad, zero_add]
      have hregular : IsRectRegular c (tupleIndicator H) ε a := by
        by_contra hn
        exact hbad (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩)
      by_cases hdensity : d ≤ labelMean (tupleLabel c) (tupleIndicator H) a
      · have hzero : (∑ x ∈ labelFiber (tupleLabel c) a, G x) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          apply ite_eq_right
          intro hxK
          obtain ⟨hxU, hcross⟩ := Finset.mem_filter.mp hxK
          obtain ⟨hxH, hxsum⟩ := Finset.mem_filter.mp hxU
          have hlabel : tupleLabel c x = a := (Finset.mem_filter.mp hx).2
          have hxinj := tuple_injective_of_uniform_member hu hxH
          have hainj : Function.Injective a := by
            intro r s hrs
            apply hxinj
            apply hcross (Finset.mem_image.mpr ⟨r, Finset.mem_univ _, rfl⟩)
              (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)
            exact (congrFun hlabel r).trans (hrs.trans (congrFun hlabel s).symm)
          have hR : (tupleEdge x).image c ∈ reducedFamily k c H ε d := by
            rw [tupleEdge_image, hlabel]
            exact mem_reducedFamily_of_cell hainj hregular hdensity
          exact not_lt_of_ge (crossing_edge_covered hz hcross hR) hxsum
        rw [hzero]
        exact mul_nonneg hd (Nat.cast_nonneg _)
      · have hsum := Finset.sum_le_sum (fun x (_ : x ∈ labelFiber (tupleLabel c) a) ↦ hGle x)
        have hmean := card_mul_finiteSetMean (tupleIndicator H) (labelFiber (tupleLabel c) a)
        have hsmall := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hdensity))
          (Nat.cast_nonneg (α := ℝ) (labelFiber (tupleLabel c) a).card)
        change (labelFiber (tupleLabel c) a).card * labelMean (tupleLabel c) (tupleIndicator H) a = _ at hmean
        nlinarith only [hsum, hmean, hsmall]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin k → I))) ↦ hcell a)
  rw [sum_labelFiber] at hsum
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter] at hsum
  have hmass : (∑ a : Fin k → I, ((labelFiber (tupleLabel c) a).card : ℝ)) =
      Fintype.card (Fin k → α) := by
    have h := sum_labelFiber (tupleLabel (k := k) c) (fun _ ↦ (1 : ℝ))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h
  rw [hmass] at hsum
  have hsplit : U.card ≤ (noncrossingFamily c H).card + K.card := by
    have h := Finset.card_filter_add_card_filter_not (s := U) (fun e ↦ IsCrossing c e)
    have hsub : (U.filter fun e ↦ ¬IsCrossing c e) ⊆ noncrossingFamily c H := by
      intro e he
      obtain ⟨heU, hnot⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp heU).1, hnot⟩
    have hle := Finset.card_le_card hsub
    change K.card + _ = U.card at h
    omega
  have hsplit' : (U.card : ℝ) ≤ (noncrossingFamily c H).card + (K.card : ℝ) := by
    exact_mod_cast hsplit
  change (U.card : ℝ) ≤ _
  change (∑ x, G x) ≤ irregularMass c (tupleIndicator H) ε + _ at hsum
  linarith only [hsplit', hKcard, hsum]

end SharpTailMatching.Matching
