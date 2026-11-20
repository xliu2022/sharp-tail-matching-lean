/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Round a reduced capacity matching by floor quotas and realize the resulting
integer plan inside regular dense cells. The additive loss is at most the
number of reduced edges.
-/
module

public import SharpTailMatching.Matching.GreedyRounding

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

variable {α I : Type*} [DecidableEq α] [DecidableEq I] [Fintype α]

def quotaPlan (R : Finset (Finset I)) (q : R → ℕ) : Multiset (Finset I) :=
  ∑ e : R, Multiset.replicate (q e) e.val

omit [DecidableEq I] in
theorem quotaPlan_card (R : Finset (Finset I)) (q : R → ℕ) :
    (quotaPlan R q).card = ∑ e : R, q e := by
  simp only [quotaPlan, Multiset.card_sum, Multiset.card_replicate]

omit [DecidableEq I] in
theorem quotaPlan_mem {R : Finset (Finset I)} {q : R → ℕ} {e : Finset I}
    (he : e ∈ quotaPlan R q) : e ∈ R := by
  obtain ⟨f, _, hf⟩ := Multiset.mem_sum.mp he
  have heq := (Multiset.mem_replicate.mp hf).2
  exact heq ▸ f.property

theorem clusterLoad_add (P Q : Multiset (Finset I)) (i : I) :
    clusterLoad (P + Q) i = clusterLoad P i + clusterLoad Q i := by
  simp only [clusterLoad, Multiset.filter_add, Multiset.card_add]

theorem clusterLoad_replicate (e : Finset I) (n : ℕ) (i : I) :
    clusterLoad (Multiset.replicate n e) i = if i ∈ e then n else 0 := by
  induction n with
  | zero => simp [clusterLoad]
  | succ n ih =>
    rw [Multiset.replicate_succ, clusterLoad_cons, ih]
    by_cases hi : i ∈ e <;> simp [hi]

theorem clusterLoad_sum {J : Type*} (S : Finset J) (P : J → Multiset (Finset I)) (i : I) :
    clusterLoad (∑ j ∈ S, P j) i = ∑ j ∈ S, clusterLoad (P j) i := by
  classical
  induction S using Finset.induction with
  | empty => simp [clusterLoad]
  | @insert j S hj ih => rw [Finset.sum_insert hj, clusterLoad_add, ih, Finset.sum_insert hj]

theorem quotaPlan_load (R : Finset (Finset I)) (q : R → ℕ) (i : I) :
    clusterLoad (quotaPlan R q) i = ∑ e : R, if i ∈ (e : Finset I) then q e else 0 := by
  simp only [quotaPlan, clusterLoad_sum, clusterLoad_replicate]

variable [Fintype I]

theorem exists_matching_of_reduced_capacity {k : ℕ} {c : α → I} {H : Finset (Finset α)}
    {ε d γ : ℝ} (hk : 0 < k) (hu : IsUniform k H) (hγ : γ < 1) (hεγ : ε ≤ γ)
    (hd : ε < d) (φ : reducedFamily k c H ε d → ℝ)
    (hφ : IsCapacityMatching (reducedFamily k c H ε d) (fun i ↦ (labelFiber c i).card) φ) :
    ∃ M : Finset (Finset α), M ⊆ H ∧ IsMatching M ∧
      (1 - γ) * (∑ e : reducedFamily k c H ε d, φ e) - (reducedFamily k c H ε d).card ≤
        (M.card : ℝ) := by
  classical
  let R := reducedFamily k c H ε d
  let q : R → ℕ := fun e ↦ ⌊(1 - γ) * φ e⌋₊
  let P := quotaPlan R q
  have hscale : 0 ≤ 1 - γ := sub_nonneg.mpr hγ.le
  have hfloor : ∀ e : R, (q e : ℝ) ≤ (1 - γ) * φ e :=
    fun e ↦ Nat.floor_le (mul_nonneg hscale (hφ.1 e))
  have hloads : ∀ i, (clusterLoad P i : ℝ) ≤ (1 - ε) * (labelFiber c i).card := by
    intro i
    have hpoint : ∀ e : R,
        ((if i ∈ (e : Finset I) then q e else 0 : ℕ) : ℝ) ≤
          (1 - γ) * (if i ∈ (e : Finset I) then φ e else 0) := by
      intro e
      by_cases hi : i ∈ (e : Finset I)
      · simpa only [ite_eq_left hi] using hfloor e
      · simp only [ite_eq_right hi, Nat.cast_zero, mul_zero, le_refl]
    have hsum := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset R)) ↦ hpoint e)
    rw [← Nat.cast_sum, ← Finset.mul_sum, ← quotaPlan_load] at hsum
    have hdegree := mul_le_mul_of_nonneg_left (hφ.2 i) hscale
    have hchange : (1 - γ) * (labelFiber c i).card ≤ (1 - ε) * (labelFiber c i).card := by
      have hnonneg := Nat.cast_nonneg (α := ℝ) (labelFiber c i).card
      nlinarith only [hεγ, hnonneg]
    exact hsum.trans (hdegree.trans hchange)
  have hrobust : ∀ e ∈ P, ∀ U : Finset α,
      (∀ i ∈ e, ε * (labelFiber c i).card ≤ (U ∩ labelFiber c i).card) →
      ∃ E ∈ H, E ⊆ U ∧ IsCrossing c E ∧ E.image c = e := by
    intro e he U hsize
    exact reduced_edge_robust hd (quotaPlan_mem he) U hsize
  obtain ⟨M, hMH, hM, hMcard, _⟩ := realize_robust_plan hk hu ε P hrobust hloads
  have hlower : ∀ e : R, (1 - γ) * φ e - 1 ≤ (q e : ℝ) := by
    intro e
    have h := Nat.lt_floor_add_one ((1 - γ) * φ e)
    linarith only [h]
  have hsum := Finset.sum_le_sum (fun e (_ : e ∈ (Finset.univ : Finset R)) ↦ hlower e)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one, ← Nat.cast_sum] at hsum
  refine ⟨M, hMH, hM, ?_⟩
  rw [hMcard, quotaPlan_card]
  exact hsum

end SharpTailMatching.Matching
