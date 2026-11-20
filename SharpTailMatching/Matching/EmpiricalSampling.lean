/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Empirical vertex-weight laws and their exact finite sampling formulas.
Every covered k-edge supplies k! distinct successful ordered samples;
samples with repeated vertices can only increase the tail probability.
-/
module

public import SharpTailMatching.Matching.AtomCosts
public import SharpTailMatching.Matching.CompactStability
public import SharpTailMatching.Matching.ApproximateCover
public import Mathlib.Probability.UniformOn
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Matching

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem tupleEdge_comp_perm {k : ℕ} (x : Fin k → α) (σ : Equiv.Perm (Fin k)) :
    tupleEdge (x ∘ σ) = tupleEdge x := by
  ext v
  constructor
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨σ i, Finset.mem_univ _, rfl⟩
  · intro h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨σ.symm i, Finset.mem_univ _, by simp⟩

theorem factorial_card_le_tuple_count {k : ℕ} {K : Finset (Finset α)} (hu : IsUniform k K) :
    k.factorial * K.card ≤ (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K).card := by
  classical
  have hex : ∀ e : K, ∃ x : Fin k → α, Function.Injective x ∧ tupleEdge x = e.val :=
    fun e ↦ exists_tuple_of_card (hu e e.property)
  let f : K × Equiv.Perm (Fin k) → (Fin k → α) := fun p ↦ (hex p.1).choose ∘ p.2
  have hfedge : ∀ p, tupleEdge (f p) = p.1.val := by
    intro p
    exact (tupleEdge_comp_perm _ p.2).trans (hex p.1).choose_spec.2
  have hcard : (Finset.univ : Finset (K × Equiv.Perm (Fin k))).card ≤
      (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K).card := by
    apply Finset.card_le_card_of_injOn f
    · intro p _
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hfedge]
      exact p.1.property
    · intro p _ q _ hpq
      have hpq₁ : p.1 = q.1 := Subtype.ext ((hfedge p).symm.trans ((congrArg tupleEdge hpq).trans (hfedge q)))
      apply Prod.ext hpq₁
      apply Equiv.ext
      intro r
      have h := congrFun hpq r
      change (hex p.1).choose (p.2 r) = (hex q.1).choose (q.2 r) at h
      rw [← hpq₁] at h
      exact (hex p.1).choose_spec.1 h
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_perm, Fintype.card_fin, Nat.mul_comm] using hcard

section Measure

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Nonempty α]

omit [DecidableEq α] [MeasurableSingletonClass α] [Nonempty α] in
theorem uniformOn_univ_eq_smul_count :
    uniformOn (Set.univ : Set α) = (Fintype.card α : ℝ≥0∞)⁻¹ • Measure.count := by
  ext S hS
  rw [uniformOn_univ, Measure.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

omit [DecidableEq α] [Nonempty α] in
theorem integral_uniformOn_univ (f : α → ℝ) :
    (∫ v, f v ∂uniformOn (Set.univ : Set α)) = (∑ v, f v) / Fintype.card α := by
  rw [uniformOn_univ_eq_smul_count, integral_smul_measure, integral_count,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]
  ring

omit [DecidableEq α] [Nonempty α] in
theorem pi_uniformOn_univ (k : ℕ) :
    Measure.pi (fun _ : Fin k ↦ uniformOn (Set.univ : Set α)) =
      uniformOn (Set.univ : Set (Fin k → α)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton, uniformOn_univ]
  simp only [uniformOn_univ, Measure.count_singleton, one_div, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

def empiricalUnitLaw (w : α → Probability.UnitInterval) : ProbabilityMeasure Probability.UnitInterval :=
  (uniformOn (Set.univ : Set α)).toProbabilityMeasure.map w

omit [DecidableEq α] in
theorem integral_empiricalUnitLaw (w : α → Probability.UnitInterval)
    (f : Probability.UnitInterval → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(empiricalUnitLaw w : Measure Probability.UnitInterval)) =
      (∑ v, f (w v)) / Fintype.card α := by
  rw [empiricalUnitLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (measurable_of_countable w).aemeasurable hf.aestronglyMeasurable]
  exact integral_uniformOn_univ _

omit [DecidableEq α] in
theorem realUnitMean_empiricalUnitLaw (w : α → Probability.UnitInterval) :
    realUnitMean (empiricalUnitLaw w) = (∑ v, ((w v : ℝ≥0) : ℝ)) / Fintype.card α := by
  exact integral_empiricalUnitLaw w _ (by fun_prop)

omit [DecidableEq α] in
theorem unitAtomCost_empiricalUnitLaw (a : ℝ) (w : α → Probability.UnitInterval) :
    unitAtomCost a (empiricalUnitLaw w) =
      (∑ v, twoAtomCost a ((w v : ℝ≥0) : ℝ)) / Fintype.card α := by
  exact integral_empiricalUnitLaw w _ ((continuous_twoAtomCost a).comp (by fun_prop)).measurable

omit [DecidableEq α] in
theorem unitTail_empiricalUnitLaw (k : ℕ) (w : α → Probability.UnitInterval) :
    (Probability.unitTail k (empiricalUnitLaw w)).toReal =
      ((Finset.univ.filter fun x : Fin k → α ↦ 1 ≤ ∑ i, (w (x i) : ℝ≥0)).card : ℝ) /
        (Fintype.card α : ℝ) ^ k := by
  classical
  unfold Probability.unitTail empiricalUnitLaw
  simp only [ProbabilityMeasure.toMeasure_map, Measure.coe_toProbabilityMeasure]
  rw [← Measure.pi_map_pi (fun _ : Fin k ↦ (measurable_of_countable w).aemeasurable)]
  rw [Measure.map_apply (by fun_prop) (by measurability), pi_uniformOn_univ, uniformOn_univ]
  have hset : (fun x : Fin k → α ↦ fun i ↦ w (x i)) ⁻¹'
      {z : Fin k → Probability.UnitInterval | 1 ≤ ∑ i, (z i : ℝ≥0)} =
      ((Finset.univ.filter fun x : Fin k → α ↦ 1 ≤ ∑ i, (w (x i) : ℝ≥0)) : Set (Fin k → α)) := by
    ext x
    simp
  rw [hset, Measure.count_apply_finset, ENNReal.toReal_div, ENNReal.toReal_natCast]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]

theorem factorial_covered_card_le_unitTail {k : ℕ} {H : Finset (Finset α)}
    (hu : IsUniform k H) (w : α → Probability.UnitInterval) :
    (k.factorial : ℝ) * ((H.card : ℝ) - (uncoveredFamily H (fun v ↦ ((w v : ℝ≥0) : ℝ))).card) ≤
      (Probability.unitTail k (empiricalUnitLaw w)).toReal * (Fintype.card α : ℝ) ^ k := by
  classical
  let K := H \ uncoveredFamily H (fun v ↦ ((w v : ℝ≥0) : ℝ))
  have hcount := factorial_card_le_tuple_count (K := K) (hu.mono Finset.sdiff_subset)
  have hsub : (Finset.univ.filter fun x : Fin k → α ↦ tupleEdge x ∈ K) ⊆
      (Finset.univ.filter fun x : Fin k → α ↦ 1 ≤ ∑ i, (w (x i) : ℝ≥0)) := by
    intro x hx
    obtain ⟨hxH, hxnot⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).2
    have hxsum : 1 ≤ ∑ v ∈ tupleEdge x, ((w v : ℝ≥0) : ℝ) := by
      by_contra! h
      exact hxnot (Finset.mem_filter.mpr ⟨hxH, h⟩)
    have hxinj := tuple_injective_of_uniform_member hu hxH
    have heq : (∑ v ∈ tupleEdge x, ((w v : ℝ≥0) : ℝ)) = ∑ i, ((w (x i) : ℝ≥0) : ℝ) := by
      exact Finset.sum_image (fun i _ j _ h ↦ hxinj h)
    rw [heq] at hxsum
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by exact_mod_cast hxsum⟩
  have hcount' : (k.factorial : ℝ) * (K.card : ℝ) ≤
      ((Finset.univ.filter fun x : Fin k → α ↦ 1 ≤ ∑ i, (w (x i) : ℝ≥0)).card : ℝ) := by
    exact_mod_cast hcount.trans (Finset.card_le_card hsub)
  have hK : (K.card : ℝ) = (H.card : ℝ) - (uncoveredFamily H (fun v ↦ ((w v : ℝ≥0) : ℝ))).card := by
    dsimp only [K]
    have hU : uncoveredFamily H (fun v ↦ ((w v : ℝ≥0) : ℝ)) ⊆ H := Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset hU, Nat.cast_sub (Finset.card_le_card hU)]
  rw [unitTail_empiricalUnitLaw, div_mul_cancel₀]
  · rwa [hK] at hcount'
  · exact pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)

end Measure

end SharpTailMatching.Matching
