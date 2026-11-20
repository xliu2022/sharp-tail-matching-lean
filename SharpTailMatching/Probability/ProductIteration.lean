module

public import SharpTailMatching.Probability.Capping
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Iterating capping inequalities

This file proves the numerical induction that turns selected caps into a
failure-probability product. The cap-selection hypothesis is explicit; its
probabilistic construction is a separate step.
-/

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Probability

/-- Adding a nonnegative loss to one coordinate can be paid for by one
additional multiplicative factor. -/
theorem product_loss_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (i : ι) (r ζ : ℝ) (hr : 0 < r) (hζ : 0 ≤ ζ)
    (hz : ∀ j, 0 ≤ z j ∧ z j ≤ r) :
    (∏ j, (1 - Function.update z i (z i + ζ) j / r)) ≤
      (1 - ζ / r) * ∏ j, (1 - z j / r) := by
  have hrest : 0 ≤ ∏ j ∈ Finset.univ.erase i, (1 - z j / r) := by
    apply Finset.prod_nonneg
    intro j _
    exact sub_nonneg.mpr ((div_le_one hr).mpr (hz j).2)
  have hfactor : 1 - (z i + ζ) / r ≤ (1 - ζ / r) * (1 - z i / r) := by
    have hprod := mul_nonneg (div_nonneg hζ hr.le) (div_nonneg (hz i).1 hr.le)
    rw [add_div]
    nlinarith
  have hupdate :
      (fun j => 1 - Function.update z i (z i + ζ) j / r) =
        Function.update (fun j => 1 - z j / r) i (1 - (z i + ζ) / r) := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  rw [hupdate, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ (fun j => 1 - z j / r) (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  nlinarith [mul_le_mul_of_nonneg_right hfactor hrest]

/-- A product of these factors increases when the positive denominator increases. -/
theorem product_loss_mono_denominator {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (r r' : ℝ) (hr : 0 < r) (hrr : r ≤ r')
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ r) :
    (∏ i, (1 - z i / r)) ≤ ∏ i, (1 - z i / r') := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact sub_nonneg.mpr ((div_le_one hr).mpr (hz i).2)
  · intro i _
    have hdiv : z i / r' ≤ z i / r :=
      div_le_div_of_nonneg_left (hz i).1 hr hrr
    linarith

/-- One cap extends the next state's loss vector to the preceding state. -/
theorem extend_product_bound_across_cap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p p' r r' ζ B B' : ℝ) (m m' z' : ι → ℝ) (i : ι)
    (hr : 0 < r) (hrr : r ≤ r') (hζ : 0 ≤ ζ)
    (hm : ∀ j, m j < r)
    (hmean : ∀ j, m' j + (if j = i then ζ else 0) ≤ m j)
    (hz' : ∀ j, 0 ≤ z' j ∧ z' j ≤ m' j)
    (hsum : ∑ j, z' j = B') (hB : B = B' + ζ)
    (hprod : (∏ j, (1 - z' j / r')) ≤ p')
    (hstep : p' * (1 - ζ / r) ≤ p) :
    ∃ z : ι → ℝ, (∀ j, 0 ≤ z j ∧ z j ≤ m j) ∧
      (∑ j, z j = B) ∧ (∏ j, (1 - z j / r)) ≤ p := by
  classical
  let z := Function.update z' i (z' i + ζ)
  have hpoint (j : ι) : z j = z' j + (if j = i then ζ else 0) := by
    by_cases hji : j = i <;> simp [z, hji]
  have hz (j : ι) : 0 ≤ z j ∧ z j ≤ m j := by
    rw [hpoint]
    constructor
    · split_ifs <;> linarith [(hz' j).1]
    · linarith [(hz' j).2, hmean j]
  have hz'r (j : ι) : 0 ≤ z' j ∧ z' j ≤ r := by
    refine ⟨(hz' j).1, ?_⟩
    have hinc : z' j ≤ z j := by
      rw [hpoint]
      split_ifs <;> linarith
    exact (hinc.trans (hz j).2).trans (hm j).le
  have hζr : ζ ≤ r := by
    have := hz i
    simp only [z, Function.update_self] at this
    linarith [(hz' i).1, hm i]
  have hfactor : 0 ≤ 1 - ζ / r :=
    sub_nonneg.mpr ((div_le_one hr).mpr hζr)
  refine ⟨z, hz, ?_, ?_⟩
  · simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linarith
  · calc
      (∏ j, (1 - z j / r)) ≤ (1 - ζ / r) * ∏ j, (1 - z' j / r) :=
        product_loss_update z' i r ζ hr hζ hz'r
      _ ≤ (1 - ζ / r) * ∏ j, (1 - z' j / r') := by
        exact mul_le_mul_of_nonneg_left
          (product_loss_mono_denominator z' r r' hr hrr hz'r) hfactor
      _ ≤ (1 - ζ / r) * p' := mul_le_mul_of_nonneg_left hprod hfactor
      _ ≤ p := by simpa [mul_comm] using hstep

/-- Well-founded capping induction. `rank` measures the remaining support
complexity. The step hypothesis records precisely the facts needed of an
actual selected cap; all accumulation and product grouping are proved here. -/
theorem product_bound_of_terminating_caps {σ ι : Type*} [Fintype ι]
    [DecidableEq ι] (rank : σ → ℕ) (p r B : σ → ℝ) (m : σ → ι → ℝ)
    (hcap : ∀ s, 0 < p s → 0 < r s → (∀ i, 0 ≤ m s i ∧ m s i < r s) →
      (p s = 1 ∧ B s = 0) ∨
      ∃ t i ζ, rank t < rank s ∧ p s ≤ p t ∧ r s ≤ r t ∧ 0 ≤ ζ ∧
        (∀ j, 0 ≤ m t j) ∧
        (∀ j, m t j + (if j = i then ζ else 0) ≤ m s j) ∧
        B s = B t + ζ ∧ p t * (1 - ζ / r s) ≤ p s)
    (s : σ) (hp : 0 < p s) (hr : 0 < r s)
    (hm : ∀ i, 0 ≤ m s i ∧ m s i < r s) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ m s i) ∧
      (∑ i, z i = B s) ∧ (∏ i, (1 - z i / r s)) ≤ p s := by
  have hall : ∀ n, ∀ s, rank s = n → 0 < p s → 0 < r s →
      (∀ i, 0 ≤ m s i ∧ m s i < r s) →
      ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ m s i) ∧
        (∑ i, z i = B s) ∧ (∏ i, (1 - z i / r s)) ≤ p s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs hp hr hm
      rcases hcap s hp hr hm with hterminal | hnext
      · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
        · intro i
          exact ⟨le_rfl, (hm i).1⟩
        · simp [hterminal.2]
        · simp [hterminal.1]
      · obtain ⟨t, i, ζ, hrank, hpp, hrr, hζ, hmt, hmean, hB, hstep⟩ := hnext
        have hmt_lt (j) : m t j < r t := by
          have hmts : m t j ≤ m s j := by
            have h := hmean j
            split_ifs at h <;> linarith
          exact (hmts.trans_lt (hm j).2).trans_le hrr
        obtain ⟨z', hz', hsum, hprod⟩ := ih (rank t) (by omega) t rfl
          (hp.trans_le hpp) (hr.trans_le hrr) (fun j => ⟨hmt j, hmt_lt j⟩)
        exact extend_product_bound_across_cap (p s) (p t) (r s) (r t) ζ
          (B s) (B t) (m s) (m t) z' i hr hrr hζ (fun j => (hm j).2)
          hmean hz' hsum hB hprod hstep
  exact hall (rank s) s rfl hp hr hm

end SharpTailMatching.Probability
