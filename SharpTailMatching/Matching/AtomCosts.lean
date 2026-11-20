/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The continuous distance to a two-point support, used to turn weak
probabilistic stability into finite hypergraph editing estimates.
-/
module

public import SharpTailMatching.Probability.Normalization

@[expose] public section

namespace SharpTailMatching.Matching

def twoAtomCost (a t : ℝ) : ℝ := min |t| |t - a|

theorem twoAtomCost_nonneg (a t : ℝ) : 0 ≤ twoAtomCost a t :=
  le_min (abs_nonneg _) (abs_nonneg _)

theorem twoAtomCost_le_abs (a t : ℝ) : twoAtomCost a t ≤ |t| := min_le_left _ _

theorem twoAtomCost_le_one (a : ℝ) {t : ℝ} (ht : 0 ≤ t) (ht₁ : t ≤ 1) :
    twoAtomCost a t ≤ 1 := by
  exact (twoAtomCost_le_abs a t).trans (by rwa [abs_of_nonneg ht])

theorem continuous_twoAtomCost (a : ℝ) : Continuous (twoAtomCost a) := by
  unfold twoAtomCost
  fun_prop

@[simp] theorem twoAtomCost_zero (a : ℝ) : twoAtomCost a 0 = 0 := by
  simp [twoAtomCost]

@[simp] theorem twoAtomCost_self (a : ℝ) : twoAtomCost a a = 0 := by
  simp [twoAtomCost]

theorem twoAtomCost_eq_rounding_error {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    twoAtomCost a t = |t - if a / 2 ≤ t then a else 0| := by
  by_cases h : a / 2 ≤ t
  · rw [ite_eq_left h, twoAtomCost, abs_of_nonneg ht, min_eq_right]
    apply abs_le.mpr
    constructor <;> linarith
  · have hta : t ≤ a := by linarith [lt_of_not_ge h]
    rw [ite_eq_right h, sub_zero, twoAtomCost, abs_of_nonneg ht,
      abs_of_nonpos (sub_nonpos.mpr hta), min_eq_left]
    linarith [lt_of_not_ge h]

end SharpTailMatching.Matching
