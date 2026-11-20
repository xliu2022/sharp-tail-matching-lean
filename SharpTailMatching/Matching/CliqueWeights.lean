/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Explicit numerical estimates for the local clique argument. In particular,
the weight gap is proved from integer capacity inequalities; it is not assumed
as a replacement for the manuscript's numerical endgame.
-/
module

public import SharpTailMatching.Matching.CliqueLayerBounds
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Factorial.BigOperators

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

theorem exp_two_thirds_lt : Real.exp (2 / 3 : ℝ) < 39 / 20 := by
  have h := Real.exp_bound' (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num)
    (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

/-- A uniform denominator estimate for the ratio of two binomial coefficients. -/
theorem choose_add_le_exp {u r : ℕ} (t : ℕ) (hru : r ≤ u) :
    ((u + t).choose r : ℝ) ≤
      Real.exp ((r : ℝ) * t / (u - r + 1 : ℕ)) * (u.choose r : ℝ) := by
  let D : ℝ := (u - r + 1 : ℕ)
  let x : ℝ := (t : ℝ) / D
  have hD : 0 < D := by dsimp only [D]; positivity
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg t) hD.le
  have hpoint : ∀ i ∈ Finset.range r, ((u + t - i : ℕ) : ℝ) ≤
      (1 + x) * ((u - i : ℕ) : ℝ) := by
    intro i hi
    have hir : i < r := Finset.mem_range.mp hi
    have hbi : u - r + 1 ≤ u - i := by omega
    have hbi' : D ≤ ((u - i : ℕ) : ℝ) := by dsimp only [D]; exact_mod_cast hbi
    have hsplit : u + t - i = u - i + t := by omega
    rw [hsplit, Nat.cast_add]
    have hxD : x * D = t := div_mul_cancel₀ _ hD.ne'
    nlinarith only [mul_le_mul_of_nonneg_left hbi' hx, hxD]
  have hprod := Finset.prod_le_prod₀
    (fun i (_ : i ∈ Finset.range r) ↦ Nat.cast_nonneg (u + t - i)) hpoint
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hprod
  have hprod₁ : (∏ i ∈ Finset.range r, ((u + t - i : ℕ) : ℝ)) =
      (r.factorial : ℝ) * ((u + t).choose r : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_prod_range (u + t) r).symm.trans
      (Nat.descFactorial_eq_factorial_mul_choose (u + t) r)
  have hprod₂ : (∏ i ∈ Finset.range r, ((u - i : ℕ) : ℝ)) =
      (r.factorial : ℝ) * (u.choose r : ℝ) := by
    exact_mod_cast (Nat.descFactorial_eq_prod_range u r).symm.trans
      (Nat.descFactorial_eq_factorial_mul_choose u r)
  rw [hprod₁, hprod₂] at hprod
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hchoose : ((u + t).choose r : ℝ) ≤ (1 + x) ^ r * (u.choose r : ℝ) := by
    nlinarith only [hprod, hfac]
  have hpower : (1 + x) ^ r ≤ Real.exp ((r : ℝ) * x) := by
    calc
      (1 + x) ^ r ≤ (Real.exp x) ^ r :=
        pow_le_pow_left₀ (by linarith only [hx]) (by simpa [add_comm] using Real.add_one_le_exp x) r
      _ = Real.exp ((r : ℝ) * x) := (Real.exp_nat_mul x r).symm
  have hfinal := hchoose.trans (mul_le_mul_of_nonneg_right hpower (Nat.cast_nonneg _))
  simpa only [x, D, mul_div_assoc] using hfinal

/-- The coarse `3rN ≤ 2u` capacity gives a strict, rationally certified
binomial ratio bound. -/
theorem choose_add_pred_lt {u r N : ℕ} (hru : r ≤ u) (hN : 0 < N)
    (hcapacity : 3 * r * N ≤ 2 * u) :
    20 * ((u + N - 1).choose r : ℝ) < 39 * (u.choose r : ℝ) := by
  have hD : (0 : ℝ) < (u - r + 1 : ℕ) := by positivity
  have hDsum : u - r + 1 + r = u + 1 := by omega
  have hNsum : N - 1 + 1 = N := by omega
  have hnum : 3 * r * (N - 1) < 2 * (u - r + 1) := by
    nlinarith only [hcapacity, hDsum, hNsum]
  have hnum' : (3 : ℝ) * r * (N - 1 : ℕ) < 2 * (u - r + 1 : ℕ) := by
    exact_mod_cast hnum
  have hexponent : (r : ℝ) * (N - 1 : ℕ) / (u - r + 1 : ℕ) < 2 / 3 := by
    apply (div_lt_iff₀ hD).mpr
    linarith only [hnum']
  have hC : (0 : ℝ) < u.choose r := by exact_mod_cast Nat.choose_pos hru
  have hbound := choose_add_le_exp (N - 1) hru
  have heq : u + (N - 1) = u + N - 1 := by omega
  rw [heq] at hbound
  have h := hbound.trans_lt (mul_lt_mul_of_pos_right
    ((Real.exp_lt_exp.mpr hexponent).trans exp_two_thirds_lt) hC)
  linarith only [h]

theorem cliqueLayerWeight_mul_gap_le {k u N j : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (hkN : k ≤ N) :
    cliqueLayerWeight k u N j * (N - k + 1 : ℕ) ≤
      (N : ℝ) * (N - 1).choose (j - 1) * (u.choose (k - j) : ℝ) := by
  have hjN : j ≤ N := hjk.trans hkN
  have hN : 1 ≤ N := hj.trans_le hjN
  have hb : (0 : ℝ) < (N / j : ℕ) := by exact_mod_cast Nat.div_pos hjN hj
  have hmod := Nat.mod_lt N hj
  have hdiv := Nat.div_add_mod N j
  have hgap : N - k + 1 ≤ j * (N / j) := by omega
  have hgap' : ((N - k + 1 : ℕ) : ℝ) ≤ (j : ℝ) * (N / j : ℕ) := by
    exact_mod_cast hgap
  have hchoose : j * N.choose j = N * (N - 1).choose (j - 1) := by
    simpa only [Nat.sub_add_cancel hN, Nat.sub_add_cancel hj, Nat.mul_comm] using
      (Nat.add_one_mul_choose_eq (N - 1) (j - 1)).symm
  have hchoose' : (j : ℝ) * N.choose j = (N : ℝ) * (N - 1).choose (j - 1) := by
    exact_mod_cast hchoose
  have hbase : (N.choose j : ℝ) / (N / j : ℕ) * (N - k + 1 : ℕ) ≤
      (N : ℝ) * (N - 1).choose (j - 1) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hb).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hgap' (Nat.cast_nonneg (N.choose j)), hchoose']
  have h := mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg (u.choose (k - j)))
  simpa only [cliqueLayerWeight, mul_assoc, mul_left_comm, mul_comm] using h

theorem vandermonde_shifted_tail {k : ℕ} (hk : 1 ≤ k) (u N : ℕ) :
    (∑ j ∈ Finset.Icc 2 k, ((N - 1).choose (j - 1) : ℝ) * u.choose (k - j)) =
      ((u + (N - 1)).choose (k - 1) : ℝ) - (u.choose (k - 1) : ℝ) := by
  have htail :
      (∑ j ∈ Finset.Icc 2 k, ((N - 1).choose (j - 1) : ℝ) * u.choose (k - j)) =
      ∑ i ∈ Finset.range (k - 1), ((N - 1).choose (i + 1) : ℝ) *
        u.choose (k - 1 - (i + 1)) := by
    apply Finset.sum_bij (fun j _ ↦ j - 2)
    · intro j hj
      obtain ⟨h₂, hₖ⟩ := Finset.mem_Icc.mp hj
      exact Finset.mem_range.mpr (by omega)
    · intro j hj j' hj' heq
      obtain ⟨h₂, hₖ⟩ := Finset.mem_Icc.mp hj
      obtain ⟨h₂', hₖ'⟩ := Finset.mem_Icc.mp hj'
      omega
    · intro i hi
      have hi' := Finset.mem_range.mp hi
      refine ⟨i + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      obtain ⟨h₂, hₖ⟩ := Finset.mem_Icc.mp hj
      rw [show j - 2 + 1 = j - 1 by omega,
        show k - 1 - (j - 1) = k - j by omega]
  have hnat : (∑ i ∈ Finset.range ((k - 1) + 1),
      (N - 1).choose i * u.choose (k - 1 - i)) = (u + (N - 1)).choose (k - 1) := by
    simpa only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Nat.add_comm (N - 1) u] using (Nat.add_choose_eq (N - 1) u (k - 1)).symm
  have hreal : (∑ i ∈ Finset.range ((k - 1) + 1),
      ((N - 1).choose i : ℝ) * u.choose (k - 1 - i)) =
        ((u + (N - 1)).choose (k - 1) : ℝ) := by exact_mod_cast hnat
  rw [Finset.sum_range_succ'] at hreal
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at hreal
  linarith only [hreal, htail]

theorem cliqueWeightSum_mul_gap_le {k u N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    cliqueWeightSum k u N * (N - k + 1 : ℕ) ≤ (N : ℝ) *
      (((u + N - 1).choose (k - 1) : ℝ) - (u.choose (k - 1) : ℝ)) := by
  have hN : 1 ≤ N := hk.trans hkN
  have hpoint : ∀ j ∈ Finset.Icc 2 k,
      cliqueLayerWeight k u N j * (N - k + 1 : ℕ) ≤
        (N : ℝ) * ((N - 1).choose (j - 1) : ℝ) * u.choose (k - j) := by
    intro j hj
    obtain ⟨hj₂, hjk⟩ := Finset.mem_Icc.mp hj
    exact cliqueLayerWeight_mul_gap_le (by omega) hjk hkN
  have hsum := Finset.sum_le_sum hpoint
  rw [← Finset.sum_mul] at hsum
  simp only [mul_assoc] at hsum
  rw [← Finset.mul_sum, vandermonde_shifted_tail hk] at hsum
  simpa only [cliqueWeightSum, show u + (N - 1) = u + N - 1 by omega] using hsum

/-- A concrete strict weight gap, sufficient for the whole finite clique
argument. Both hypotheses involve only integer vertex counts. -/
theorem cliqueWeightSum_lt_choose {k u N : ℕ} (hk : 2 ≤ k)
    (hN : 20 * (k - 1) ≤ N) (hcapacity : 3 * (k - 1) * N ≤ 2 * u) :
    cliqueWeightSum k u N < (u.choose (k - 1) : ℝ) := by
  have hkN : k ≤ N := by omega
  have hNp : 0 < N := by omega
  have hru : k - 1 ≤ u := by nlinarith only [hk, hN, hcapacity]
  have hgap : 19 * N ≤ 20 * (N - k + 1) := by omega
  have hgap' : (19 : ℝ) * N ≤ 20 * (N - k + 1 : ℕ) := by exact_mod_cast hgap
  have hD : (0 : ℝ) < (N - k + 1 : ℕ) := by exact_mod_cast (by omega : 0 < N - k + 1)
  have hNp' : (0 : ℝ) < N := by exact_mod_cast hNp
  have hC : (0 : ℝ) < u.choose (k - 1) := by exact_mod_cast Nat.choose_pos hru
  have hratio := choose_add_pred_lt hru hNp hcapacity
  have hsum := cliqueWeightSum_mul_gap_le (by omega) hkN (u := u)
  have hstrict : (N : ℝ) *
      (((u + N - 1).choose (k - 1) : ℝ) - (u.choose (k - 1) : ℝ)) <
        (N - k + 1 : ℕ) * (u.choose (k - 1) : ℝ) := by
    have h₁ := mul_lt_mul_of_pos_left hratio hNp'
    have h₂ := mul_le_mul_of_nonneg_right hgap' hC.le
    nlinarith only [h₁, h₂]
  have h := hsum.trans_lt hstrict
  nlinarith only [h, hD]

end SharpTailMatching.Matching
