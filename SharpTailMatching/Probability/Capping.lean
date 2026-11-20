module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

/-!
# Finite capping certificates

These lemmas prove the ordered finite-support selection and the numerical
one-step estimate used in the failure-probability product argument. They
do not assume or assert the full probabilistic product bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

namespace SharpTailMatching.Probability

/-- The covariance identity that selects a coordinate to cap. It applies to
the failure-conditioned probability measure as well as to any other finite measure. -/
theorem sum_covariance_with_sum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (∑ i, cov[fun ω => ∑ j, X j ω, X i; μ]) =
      Var[fun ω => ∑ i, X i ω; μ] := by
  have hsum : MemLp (fun ω => ∑ i, X i ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => hX i)
  rw [← covariance_fun_sum_right hX hsum, covariance_self hsum.aemeasurable]

/-- If some coordinate is nonconstant, one can select a nonconstant coordinate
whose covariance with the total sum is nonnegative. Constant coordinates cannot
be selected merely because their covariance vanishes. -/
theorem exists_nonconstant_coordinate_nonneg_covariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hnonconstant : ∃ i, ¬ ∃ c : ℝ, X i = fun _ => c) :
    ∃ i, (¬ ∃ c : ℝ, X i = fun _ => c) ∧
      0 ≤ cov[fun ω => ∑ j, X j ω, X i; μ] := by
  classical
  by_contra h
  have hneg (i) (hi : ¬ ∃ c : ℝ, X i = fun _ => c) :
      cov[fun ω => ∑ j, X j ω, X i; μ] < 0 := by
    apply lt_of_not_ge
    intro hc
    exact h ⟨i, hi, hc⟩
  have hnonpos (i) : cov[fun ω => ∑ j, X j ω, X i; μ] ≤ 0 := by
    by_cases hi : ∃ c : ℝ, X i = fun _ => c
    · obtain ⟨c, hc⟩ := hi
      rw [hc, covariance_const_right]
    · exact (hneg i hi).le
  obtain ⟨i, hi⟩ := hnonconstant
  have hsum := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hnonpos j)
    ⟨i, Finset.mem_univ i, hneg i hi⟩
  simp only [Finset.sum_const_zero, sum_covariance_with_sum μ X hX] at hsum
  exact (variance_nonneg _ μ).not_gt hsum

/-- If a zero-total signed mass has nonpositive first moment along strictly
increasing support points, a proper initial segment has nonnegative mass. -/
theorem exists_nonnegative_proper_prefix (n : ℕ) (hn : 0 < n)
    (x v : ℕ → ℝ) (hx : ∀ i < n, x i < x (i+1))
    (htotal : ∑ i ∈ Finset.range (n+1), v i = 0)
    (hmoment : ∑ i ∈ Finset.range (n+1), x i * v i ≤ 0) :
    ∃ q < n, 0 ≤ ∑ i ∈ Finset.range (q+1), v i := by
  by_contra h
  push Not at h
  have hnegative : ∀ q ∈ Finset.range n,
      (x (q+1)-x q) * (∑ i ∈ Finset.range (q+1), v i) < 0 := by
    intro q hq
    exact mul_neg_of_pos_of_neg (sub_pos.mpr (hx q (Finset.mem_range.mp hq)))
      (h q (Finset.mem_range.mp hq))
  have hsum := Finset.sum_lt_sum
    (fun q hq => (hnegative q hq).le)
    ⟨0, Finset.mem_range.mpr hn, hnegative 0 (Finset.mem_range.mpr hn)⟩
  simp only [Finset.sum_const_zero] at hsum
  have hab := Finset.sum_range_by_parts x v (n+1)
  simp only [smul_eq_mul, Nat.add_sub_cancel, htotal, mul_zero, zero_sub] at hab
  linarith

/-- The first nonnegative proper prefix also has a nonnegative last summand.
This is the precise support-index choice used by the capping operation. -/
theorem exists_first_nonnegative_proper_prefix (n : ℕ) (hn : 0 < n)
    (x v : ℕ → ℝ) (hx : ∀ i < n, x i < x (i+1))
    (htotal : ∑ i ∈ Finset.range (n+1), v i = 0)
    (hmoment : ∑ i ∈ Finset.range (n+1), x i * v i ≤ 0) :
    ∃ q < n,
      0 ≤ (∑ i ∈ Finset.range (q+1), v i) ∧
      (∑ i ∈ Finset.range q, v i) ≤ 0 ∧ 0 ≤ v q := by
  classical
  have hex := exists_nonnegative_proper_prefix n hn x v hx htotal hmoment
  let q := Nat.find hex
  have hq : q < n ∧ 0 ≤ ∑ i ∈ Finset.range (q+1), v i := Nat.find_spec hex
  have hprev : (∑ i ∈ Finset.range q, v i) ≤ 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hmin := Nat.find_min hex (show q-1 < q by omega)
      have hindex : q-1 < n := by omega
      have hid : q-1+1 = q := by omega
      have hnot : ¬ 0 ≤ ∑ i ∈ Finset.range q, v i := by
        intro hpos
        apply hmin
        exact ⟨hindex, by simpa [hid] using hpos⟩
      exact (lt_of_not_ge hnot).le
  refine ⟨q, hq.1, hq.2, hprev, ?_⟩
  have hnext := hq.2
  rw [Finset.sum_range_succ] at hnext
  linarith

/-- Weighted form of the cap-selection lemma. Positive atom weights allow
the sign of the last weighted summand to determine the sign of `K` at the cap. -/
theorem exists_finite_cap_index (n : ℕ) (hn : 0 < n) (x w K : ℕ → ℝ)
    (hx : ∀ i < n, x i < x (i+1)) (hw : ∀ i ≤ n, 0 < w i)
    (htotal : ∑ i ∈ Finset.range (n+1), w i * K i = 0)
    (hmoment : ∑ i ∈ Finset.range (n+1), x i * (w i * K i) ≤ 0) :
    ∃ q < n,
      0 ≤ (∑ i ∈ Finset.range (q+1), w i * K i) ∧
      (∑ i ∈ Finset.range q, w i * K i) ≤ 0 ∧ 0 ≤ K q := by
  obtain ⟨q, hqn, hprefix, hprev, hterm⟩ :=
    exists_first_nonnegative_proper_prefix n hn x (fun i => w i * K i)
      hx htotal hmoment
  exact ⟨q, hqn, hprefix, hprev,
    nonneg_of_mul_nonneg_right hterm (hw q hqn.le)⟩

/-- The support selection also permits repeated ordered values. This form is
preserved by capping: the atom weights stay fixed and positive, while several
upper atoms may acquire the same value. The selected value is strictly below
the largest value, so the support complexity decreases. -/
theorem exists_cap_index_of_monotone (n : ℕ) (x w K : ℕ → ℝ)
    (hx : Monotone x) (hxstrict : x 0 < x n) (hw : ∀ i ≤ n, 0 < w i)
    (htotal : ∑ i ∈ Finset.range (n+1), w i * K i = 0)
    (hmoment : ∑ i ∈ Finset.range (n+1), x i * (w i * K i) ≤ 0) :
    ∃ q < n, x q < x n ∧
      0 ≤ (∑ i ∈ Finset.range (q+1), w i * K i) ∧
      (∑ i ∈ Finset.range q, w i * K i) ≤ 0 ∧ 0 ≤ K q := by
  classical
  let v := fun i => w i * K i
  have hgap : ∃ q < n, x q < x (q+1) := by
    by_contra h
    push Not at h
    have hz : (∑ q ∈ Finset.range n, (x (q+1)-x q)) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      exact sub_eq_zero.mpr (le_antisymm (h q (Finset.mem_range.mp hq))
        (hx (Nat.le_succ q)))
    rw [Finset.sum_range_sub] at hz
    linarith
  have hgood : ∃ q < n, x q < x (q+1) ∧ 0 ≤ ∑ i ∈ Finset.range (q+1), v i := by
    by_contra h
    have hneg (q) (hqn : q < n) (hgapq : x q < x (q+1)) :
        (∑ i ∈ Finset.range (q+1), v i) < 0 := by
      apply lt_of_not_ge
      intro hq
      exact h ⟨q, hqn, hgapq, hq⟩
    have hnonpos (q) (hqn : q < n) :
        (x (q+1)-x q) * (∑ i ∈ Finset.range (q+1), v i) ≤ 0 := by
      rcases (hx (Nat.le_succ q)).eq_or_lt with heq | hlt
      · simp [heq]
      · exact (mul_neg_of_pos_of_neg (sub_pos.mpr hlt) (hneg q hqn hlt)).le
    obtain ⟨q, hqn, hgapq⟩ := hgap
    have hsum := Finset.sum_lt_sum
      (fun j hj => hnonpos j (Finset.mem_range.mp hj))
      ⟨q, Finset.mem_range.mpr hqn,
        mul_neg_of_pos_of_neg (sub_pos.mpr hgapq) (hneg q hqn hgapq)⟩
    simp only [Finset.sum_const_zero] at hsum
    have hab := Finset.sum_range_by_parts x v (n+1)
    simp only [smul_eq_mul, Nat.add_sub_cancel, v, htotal, mul_zero, zero_sub] at hab
    dsimp [v] at hsum
    linarith
  obtain ⟨q₀, hq₀n, hq₀gap, hq₀prefix⟩ := hgood
  have hex : ∃ q ≤ q₀, 0 ≤ ∑ i ∈ Finset.range (q+1), v i :=
    ⟨q₀, le_rfl, hq₀prefix⟩
  let q := Nat.find hex
  have hq : q ≤ q₀ ∧ 0 ≤ ∑ i ∈ Finset.range (q+1), v i := Nat.find_spec hex
  have hprev : (∑ i ∈ Finset.range q, v i) ≤ 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hmin := Nat.find_min hex (show q-1 < q by omega)
      have hid : q-1+1 = q := by omega
      have hnot : ¬ 0 ≤ ∑ i ∈ Finset.range q, v i := by
        intro hpos
        apply hmin
        exact ⟨by omega, by simpa [hid] using hpos⟩
      exact (lt_of_not_ge hnot).le
  have hterm : 0 ≤ v q := by
    have hnext := hq.2
    rw [Finset.sum_range_succ] at hnext
    linarith
  refine ⟨q, by omega, (hx hq.1).trans_lt (hq₀gap.trans_le (hx (by omega))),
    hq.2, hprev, ?_⟩
  exact nonneg_of_mul_nonneg_right hterm (hw q (by omega))

/-- Pointwise control of the change in positive deficit after capping one
coordinate. The indicator depends only on the other coordinates and the cap. -/
theorem cap_positive_deficit_difference (T X τ : ℝ) :
    max (1-T-min X τ) 0 - max (1-T-X) 0 ≤
      if T+τ < 1 then max (X-τ) 0 else 0 := by
  by_cases hXτ : X ≤ τ
  · rw [min_eq_left hXτ, sub_self]
    split_ifs <;> positivity
  · have hτX : τ ≤ X := le_of_not_ge hXτ
    rw [min_eq_right hτX]
    by_cases hT : T+τ < 1
    · rw [ite_eq_left hT, max_eq_left (by linarith : 0 ≤ 1-T-τ),
        max_eq_left (sub_nonneg.mpr hτX)]
      linarith [le_max_left (1-T-X) 0]
    · rw [ite_eq_right hT, max_eq_right (by linarith : 1-T-τ ≤ 0)]
      linarith [le_max_right (1-T-X) 0]

/-- Exact arithmetic of one selected cap. The assumptions express increasing
failure probability and deficit and the pointwise capped-excess estimate. -/
theorem cap_step_estimate (p p' r r' d : ℝ)
    (hp : 0 < p) (hpp : p ≤ p') (hr : 0 < r) (hrr : r ≤ r')
    (hexcess : p'*r' - p*r ≤ p'*d) :
    let ζ := d-(r'-r)
    0 ≤ ζ ∧ ζ ≤ d ∧ p'*(r-ζ) ≤ p*r ∧ p'*(1-ζ/r) ≤ p := by
  dsimp
  have hp' : 0 < p' := hp.trans_le hpp
  have hstep : p'*(r-(d-(r'-r))) ≤ p*r := by nlinarith only [hexcess]
  have hnonneg : 0 ≤ d-(r'-r) := by
    have hmul : 0 ≤ p'*(d-(r'-r)) := by
      nlinarith only [hstep, mul_nonneg (sub_nonneg.mpr hpp) hr.le]
    exact nonneg_of_mul_nonneg_right hmul hp'
  refine ⟨hnonneg, by linarith, hstep, ?_⟩
  apply (mul_le_mul_iff_left₀ hr).mp
  calc
    (p'*(1-(d-(r'-r))/r))*r = p'*(r-(d-(r'-r))) := by field_simp
    _ ≤ p*r := hstep

end SharpTailMatching.Probability
