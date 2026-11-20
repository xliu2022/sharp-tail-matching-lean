module

public import SharpTailMatching.Probability.ProductIteration
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Logic.Equiv.Prod

/-!
# Finite independent distributions

Finite expectations are represented by exact real weighted sums. A family of
nonnegative weights with unit total on each coordinate defines the independent
product distribution, with no probabilistic identities postulated.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability.FiniteProduct

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

def weight (w : ι → α → ℝ) (ω : ι → α) : ℝ := ∏ i, w i (ω i)

def expect (w : ι → α → ℝ) (f : (ι → α) → ℝ) : ℝ :=
  ∑ ω, weight w ω * f ω

omit [Fintype α] [DecidableEq ι] in
theorem weight_nonneg (w : ι → α → ℝ) (hw : ∀ i a, 0 ≤ w i a) (ω) :
    0 ≤ weight w ω := Finset.prod_nonneg (fun i _ => hw i (ω i))

theorem weight_total (w : ι → α → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    ∑ ω, weight w ω = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [hw]

@[simp] theorem expect_zero (w : ι → α → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

theorem expect_const (w : ι → α → ℝ) (hw : ∀ i, ∑ a, w i a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, weight_total w hw, one_mul]

theorem expect_add (w : ι → α → ℝ) (f g : (ι → α) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (w : ι → α → ℝ) (f g : (ι → α) → ℝ) :
    expect w (fun ω => f ω - g ω) = expect w f - expect w g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul_const (w : ι → α → ℝ) (f : (ι → α) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  simp only [expect, mul_assoc, Finset.sum_mul]

theorem expect_const_mul (w : ι → α → ℝ) (c : ℝ) (f : (ι → α) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c, expect_mul_const]

theorem expect_sum {κ : Type*} [Fintype κ] (w : ι → α → ℝ)
    (f : κ → (ι → α) → ℝ) :
    expect w (fun ω => ∑ i, f i ω) = ∑ i, expect w (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg (w : ι → α → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (f : (ι → α) → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (weight_nonneg w hw ω) (hf ω))

theorem expect_mono (w : ι → α → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (f g : (ι → α) → ℝ) (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (weight_nonneg w hw ω))

/-- Fubini's identity for a distinguished coordinate of a finite independent
product. The other coordinates carry their own product of the original weights. -/
theorem expect_split (w : ι → α → ℝ) (f : (ι → α) → ℝ) (i : ι) :
    expect w f = ∑ a, w i a *
      expect (fun j : {j // j ≠ i} => w j)
        (fun ω => f ((Equiv.funSplitAt i α).symm (a, ω))) := by
  classical
  unfold expect weight
  rw [← (Equiv.funSplitAt i α).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have hweight :
      (∏ j, w j ((Equiv.funSplitAt i α).symm (a, ω) j)) =
        w i a * ∏ j : {j // j ≠ i}, w j (ω j) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => w j ((Equiv.funSplitAt i α).symm (a, ω) j)) (Finset.mem_univ i)]
    simp only [Equiv.funSplitAt_symm_apply, dite_true]
    congr 1
    rw [Finset.prod_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp)]
    apply Finset.prod_congr rfl
    intro j _
    simp [j.property]
  rw [hweight]
  ring

theorem expect_coordinate (w : ι → α → ℝ) (hw : ∀ i, ∑ a, w i a = 1)
    (i : ι) (f : α → ℝ) :
    expect w (fun ω => f (ω i)) = ∑ a, w i a * f a := by
  rw [expect_split w _ i]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  rw [expect_const (ι := {j // j ≠ i}) (fun j => w j) (fun j => hw j) (f a)]

def total (X : ι → α → ℝ) (ω : ι → α) : ℝ := ∑ i, X i (ω i)

def failureIndicator (t : ℝ) : ℝ := if t < 1 then 1 else 0

def failure (w X : ι → α → ℝ) : ℝ :=
  expect w (fun ω => failureIndicator (total X ω))

def positiveDeficit (w X : ι → α → ℝ) : ℝ :=
  expect w (fun ω => max (1 - total X ω) 0)

def conditionalDeficit (w X : ι → α → ℝ) : ℝ :=
  positiveDeficit w X / failure w X

def mean (w X : ι → α → ℝ) (i : ι) : ℝ := ∑ a, w i a * X i a

def centeredFailure (r t : ℝ) : ℝ := if t < 1 then 1 - r - t else 0

theorem centeredFailure_eq (r t : ℝ) :
    centeredFailure r t = max (1 - t) 0 - r * failureIndicator t := by
  unfold centeredFailure failureIndicator
  split_ifs with h
  · rw [max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith)]
    ring

theorem expect_centeredFailure_eq (w X : ι → α → ℝ) (r : ℝ) :
    expect w (fun ω => centeredFailure r (total X ω)) =
      positiveDeficit w X - r * failure w X := by
  simp_rw [centeredFailure_eq]
  rw [expect_sub, expect_const_mul]
  rfl

theorem expect_centeredFailure (w X : ι → α → ℝ) (r : ℝ)
    (hr : positiveDeficit w X = failure w X * r) :
    expect w (fun ω => centeredFailure r (total X ω)) = 0 := by
  simp_rw [centeredFailure_eq]
  rw [expect_sub, expect_const_mul]
  change positiveDeficit w X - r * failure w X = 0
  rw [hr]
  ring

omit [Fintype α] in
theorem total_split (X : ι → α → ℝ) (i : ι) (a : α)
    (ω : {j // j ≠ i} → α) :
    total X ((Equiv.funSplitAt i α).symm (a, ω)) =
      X i a + total (fun j : {j // j ≠ i} => X j) ω := by
  unfold total
  rw [← Finset.add_sum_erase Finset.univ
    (fun j => X j ((Equiv.funSplitAt i α).symm (a, ω) j)) (Finset.mem_univ i)]
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  congr 1
  rw [Finset.sum_subtype (p := fun j => j ≠ i) (Finset.univ.erase i) (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  simp [j.property]

/-- Finite-sum version of the conditional covariance identity. Its left side
is the sum of the signed first moments used to choose a coordinate. -/
theorem sum_centered_moments_nonpos (w X : ι → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (r : ℝ)
    (hr : positiveDeficit w X = failure w X * r) :
    (∑ i, expect w (fun ω => X i (ω i) * centeredFailure r (total X ω))) ≤ 0 := by
  have hcenter := expect_centeredFailure w X r hr
  have hidentity (t : ℝ) :
      t * centeredFailure r t =
        (1-r) * centeredFailure r t - (t-(1-r))^2 * failureIndicator t := by
    unfold centeredFailure failureIndicator
    split_ifs <;> ring
  have hsum :
      (∑ i, expect w (fun ω => X i (ω i) * centeredFailure r (total X ω))) =
        expect w (fun ω => total X ω * centeredFailure r (total X ω)) := by
    rw [← expect_sum]
    simp only [total, Finset.sum_mul]
  rw [hsum]
  simp_rw [hidentity]
  rw [expect_sub, expect_const_mul, hcenter, mul_zero, zero_sub]
  apply neg_nonpos.mpr
  apply expect_nonneg w hw
  intro ω
  apply mul_nonneg (sq_nonneg _)
  unfold failureIndicator
  split_ifs <;> norm_num

/-- A nonconstant coordinate has nonpositive centered first moment. Constant
coordinates have zero contribution and cannot be used to mask this choice. -/
theorem exists_nonconstant_coordinate_nonpos_moment (w X : ι → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (r : ℝ)
    (hr : positiveDeficit w X = failure w X * r)
    (hnonconstant : ∃ i, ¬ ∃ c : ℝ, X i = fun _ => c) :
    ∃ i, (¬ ∃ c : ℝ, X i = fun _ => c) ∧
      expect w (fun ω => X i (ω i) * centeredFailure r (total X ω)) ≤ 0 := by
  by_contra h
  have hpos (i) (hi : ¬ ∃ c : ℝ, X i = fun _ => c) :
      0 < expect w (fun ω => X i (ω i) * centeredFailure r (total X ω)) := by
    apply lt_of_not_ge
    intro hm
    exact h ⟨i, hi, hm⟩
  have hnonneg (i) :
      0 ≤ expect w (fun ω => X i (ω i) * centeredFailure r (total X ω)) := by
    by_cases hi : ∃ c : ℝ, X i = fun _ => c
    · obtain ⟨c, hc⟩ := hi
      simp only [hc]
      rw [expect_const_mul, expect_centeredFailure w X r hr, mul_zero]
    · exact (hpos i hi).le
  obtain ⟨i, hi⟩ := hnonconstant
  have hstrict := Finset.sum_lt_sum
    (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hnonneg j)
    ⟨i, Finset.mem_univ i, hpos i hi⟩
  simp only [Finset.sum_const_zero] at hstrict
  exact (sum_centered_moments_nonpos w X hw r hr).not_gt hstrict

def coordinateKernel (w X : ι → α → ℝ) (r : ℝ) (i : ι) (t : ℝ) : ℝ :=
  expect (fun j : {j // j ≠ i} => w j)
    (fun ω => centeredFailure r (t + total (fun j : {j // j ≠ i} => X j) ω))

theorem centeredFailure_split (w X : ι → α → ℝ) (r : ℝ) (i : ι) :
    expect w (fun ω => centeredFailure r (total X ω)) =
      ∑ a, w i a * coordinateKernel w X r i (X i a) := by
  rw [expect_split w _ i]
  simp only [total_split, coordinateKernel]

theorem centered_moment_split (w X : ι → α → ℝ) (r : ℝ) (i : ι) :
    expect w (fun ω => X i (ω i) * centeredFailure r (total X ω)) =
      ∑ a, X i a * (w i a * coordinateKernel w X r i (X i a)) := by
  rw [expect_split w _ i]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Equiv.funSplitAt_symm_apply, dite_true, total_split]
  rw [expect_const_mul]
  unfold coordinateKernel
  ring

omit [Fintype α] in
theorem total_eq_coordinate_add_rest (X : ι → α → ℝ) (i : ι) (ω : ι → α) :
    total X ω = X i (ω i) +
      total (fun j : {j // j ≠ i} => X j) (fun j => ω j) := by
  convert total_split X i (ω i) (fun j => ω j) using 1
  exact congrArg (total X) ((Equiv.funSplitAt i α).symm_apply_apply ω).symm

/-- Factorization of an arbitrary one-coordinate statistic and an arbitrary
statistic of the remaining coordinates. -/
theorem expect_coordinate_mul_rest (w : ι → α → ℝ) (i : ι)
    (f : α → ℝ) (g : ({j // j ≠ i} → α) → ℝ) :
    expect w (fun ω => f (ω i) * g (fun j => ω j)) =
      (∑ a, w i a * f a) * expect (fun j : {j // j ≠ i} => w j) g := by
  rw [expect_split w _ i, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  have hrest (ω : {j // j ≠ i} → α) :
      (fun j : {j // j ≠ i} => (Equiv.funSplitAt i α).symm (a, ω) j) = ω := by
    funext j
    simp [Equiv.funSplitAt_symm_apply, j.property]
  simp_rw [hrest]
  simp only [Equiv.funSplitAt_symm_apply, dite_true]
  rw [expect_const_mul]
  ring

def cap (X : ι → α → ℝ) (i : ι) (τ : ℝ) : ι → α → ℝ :=
  Function.update X i (fun a => min (X i a) τ)

omit [Fintype ι] [Fintype α] in
@[simp] theorem cap_same (X : ι → α → ℝ) (i : ι) (τ : ℝ) (a : α) :
    cap X i τ i a = min (X i a) τ := by simp [cap]

omit [Fintype ι] [Fintype α] in
@[simp] theorem cap_ne (X : ι → α → ℝ) (i : ι) (τ : ℝ) (j : ι) (hji : j ≠ i) :
    cap X i τ j = X j := by simp [cap, hji]

omit [Fintype α] in
theorem total_cap (X : ι → α → ℝ) (i : ι) (τ : ℝ) (ω : ι → α) :
    total (cap X i τ) ω = min (X i (ω i)) τ +
      total (fun j : {j // j ≠ i} => X j) (fun j => ω j) := by
  rw [total_eq_coordinate_add_rest _ i]
  have hother : (fun j : {j // j ≠ i} => cap X i τ j) =
      (fun j : {j // j ≠ i} => X j) := by
    funext j
    exact cap_ne X i τ j j.property
  rw [hother, cap_same]

theorem cap_centeredFailure_split (w X : ι → α → ℝ) (r : ℝ) (i : ι) (τ : ℝ) :
    expect w (fun ω => centeredFailure r (total (cap X i τ) ω)) =
      ∑ a, w i a * coordinateKernel w X r i (min (X i a) τ) := by
  rw [centeredFailure_split w (cap X i τ) r i]
  have hother : (fun j : {j // j ≠ i} => cap X i τ j) =
      (fun j : {j // j ≠ i} => X j) := by
    funext j
    exact cap_ne X i τ j j.property
  simp only [cap_same, coordinateKernel, hother]

theorem failure_mono_cap (w X : ι → α → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (i : ι) (τ : ℝ) : failure w X ≤ failure w (cap X i τ) := by
  apply expect_mono w hw
  intro ω
  have hsum : total (cap X i τ) ω ≤ total X ω := by
    rw [total_cap, total_eq_coordinate_add_rest X i]
    linarith [min_le_left (X i (ω i)) τ]
  unfold failureIndicator
  split_ifs <;> norm_num
  linarith

def meanLoss (w X : ι → α → ℝ) (i : ι) (τ : ℝ) : ℝ :=
  ∑ a, w i a * max (X i a - τ) 0

omit [Fintype ι] [DecidableEq ι] in
theorem meanLoss_nonneg (w X : ι → α → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (i : ι) (τ : ℝ) : 0 ≤ meanLoss w X i τ := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (hw i a) (le_max_right _ _)

omit [Fintype ι] in
theorem mean_cap (w X : ι → α → ℝ) (i : ι) (τ : ℝ) :
    mean w (cap X i τ) i = mean w X i - meanLoss w X i τ := by
  unfold mean meanLoss
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [cap_same]
  by_cases h : X i a ≤ τ
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

/-- The expected positive deficit gained by an arbitrary cap is bounded by
the lost mean times the new failure probability. Independence is derived
from the finite product weights by `expect_coordinate_mul_rest`. -/
theorem positiveDeficit_cap_sub_le (w X : ι → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (i : ι) (τ : ℝ) :
    positiveDeficit w (cap X i τ) - positiveDeficit w X ≤
      failure w (cap X i τ) * meanLoss w X i τ := by
  let T : (ι → α) → ℝ := fun ω =>
    total (fun j : {j // j ≠ i} => X j) (fun j => ω j)
  let q : ℝ := expect (fun j : {j // j ≠ i} => w j)
    (fun ω => failureIndicator (τ + total (fun j : {j // j ≠ i} => X j) ω))
  have hpoint (ω : ι → α) :
      max (1 - total (cap X i τ) ω) 0 - max (1 - total X ω) 0 ≤
        max (X i (ω i) - τ) 0 * failureIndicator (τ + T ω) := by
    rw [total_cap, total_eq_coordinate_add_rest X i]
    change max (1 - (min (X i (ω i)) τ + T ω)) 0 -
      max (1 - (X i (ω i) + T ω)) 0 ≤ _
    have hfirst : 1 - (min (X i (ω i)) τ + T ω) = 1 - T ω - min (X i (ω i)) τ := by ring
    have hsecond : 1 - (X i (ω i) + T ω) = 1 - T ω - X i (ω i) := by ring
    rw [hfirst, hsecond]
    simpa only [failureIndicator, mul_ite, mul_one, mul_zero, add_comm (T ω) τ] using
      cap_positive_deficit_difference (T ω) (X i (ω i)) τ
  have hexcess : positiveDeficit w (cap X i τ) - positiveDeficit w X ≤
      meanLoss w X i τ * q := by
    rw [positiveDeficit, positiveDeficit, ← expect_sub]
    calc
      _ ≤ expect w (fun ω => max (X i (ω i) - τ) 0 * failureIndicator (τ + T ω)) :=
        expect_mono w hw _ _ hpoint
      _ = meanLoss w X i τ * q := by
        exact expect_coordinate_mul_rest w i (fun a => max (X i a - τ) 0)
          (fun ω => failureIndicator (τ + total (fun j : {j // j ≠ i} => X j) ω))
  have hq : q ≤ failure w (cap X i τ) := by
    have hf (ω : ι → α) : failureIndicator (τ + T ω) ≤
        failureIndicator (total (cap X i τ) ω) := by
      have hle : total (cap X i τ) ω ≤ τ + T ω := by
        rw [total_cap]
        dsimp [T]
        linarith [min_le_right (X i (ω i)) τ]
      unfold failureIndicator
      split_ifs <;> norm_num
      linarith
    have h := expect_mono w hw _ _ hf
    have hleft : expect w (fun ω => failureIndicator (τ + T ω)) = q := by
      have hfactor := expect_coordinate_mul_rest w i (fun _ => 1)
        (fun ω => failureIndicator (τ + total (fun j : {j // j ≠ i} => X j) ω))
      simpa only [one_mul, mul_one, hw1 i, T, q] using hfactor
    rwa [hleft] at h
  exact hexcess.trans (by nlinarith [mul_le_mul_of_nonneg_left hq (meanLoss_nonneg w X hw i τ)])

end SharpTailMatching.Probability.FiniteProduct
