module

public import SharpTailMatching.CriticalLowerBound
public import SharpTailMatching.SmallDeviationAlgebra

/-! # Elementary probabilities at the critical mean -/

@[expose] public section

noncomputable section

open Set
open scoped BigOperators

namespace SharpTailMatching.CriticalEstimates

theorem exp_neg_one_lt_three_eighths : Real.exp (-1) < 3/8 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
  nlinarith

theorem failure_power_ge_six {k : ℕ} (hk : 6 ≤ k) :
    (5/6:ℝ)^6 ≤ (1-(k:ℝ)⁻¹)^k := by
  have hk6 : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hi : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by linarith)
  have hmono := SmallDeviationAlgebra.deficit_log_monotone (ε := 0) (by norm_num)
    (show (6:ℝ) ∈ Ioi 1 by norm_num) (show (k:ℝ) ∈ Ioi 1 by change 1 < (k:ℝ); linarith) hk6
  apply (Real.log_le_log_iff (by positivity : 0 < (5/6:ℝ)^6)
    (pow_pos (by linarith : 0 < 1-(k:ℝ)⁻¹) k)).mp
  rw [Real.log_pow, Real.log_pow]
  simpa only [sub_zero, one_div, show (1-(6:ℝ)⁻¹) = 5/6 by norm_num,
    Nat.cast_ofNat] using hmono

theorem failure_above_one_third {k : ℕ} (hk : 6 ≤ k) {x : ℝ}
    (hx : x < (k:ℝ)⁻¹) : 1/3 < (1-x)^k := by
  have hk6 : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hi : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by linarith)
  have hp := pow_lt_pow_left₀ (by linarith : 1-(k:ℝ)⁻¹ < 1-x)
    (by linarith : 0 ≤ 1-(k:ℝ)⁻¹) (by omega : k ≠ 0)
  have h6 := failure_power_ge_six hk
  norm_num at h6
  linarith

theorem half_shift_failure_lt_exp {k : ℕ} (hk : 1 ≤ k) :
    (1-1/((k:ℝ)+1/2))^k < Real.exp (-1) := by
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  let u : ℝ := 1/(2*(k:ℝ))
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hseries := Real.sum_range_le_log_div hu0.le hu1 2
  norm_num [Finset.sum_range_succ] at hseries
  have hlog : 2*u < Real.log ((1+u)/(1-u)) := by
    nlinarith [pow_pos hu0 3]
  have hratio : 1-1/((k:ℝ)+1/2) = ((1+u)/(1-u))⁻¹ := by
    dsimp [u]
    field_simp
    ring
  have hratio0 : 0 < 1-1/((k:ℝ)+1/2) := by
    have hdiv : 1/((k:ℝ)+1/2) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hlogratio : (k:ℝ)*Real.log (1-1/((k:ℝ)+1/2)) < -1 := by
    rw [hratio, Real.log_inv]
    have h := mul_lt_mul_of_pos_left hlog hkpos
    have hku : (k:ℝ)*(2*u) = 1 := by dsimp [u]; field_simp
    rw [hku] at h
    linarith
  have h := Real.exp_lt_exp.mpr hlogratio
  rw [Real.exp_nat_mul, Real.exp_log hratio0] at h
  exact h

theorem critical_elementary_bounds {k : ℕ} (hk : 6 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    let x := 1/((k:ℝ)+c)
    let a := (k:ℝ)*x
    12/13 < a ∧ a < 1 ∧ 5/12 < a*c ∧
      1/3 < (1-x)^k ∧ (1-x)^k < Real.exp (-1) ∧ Real.exp (-1) < 3/8 := by
  have hk6 : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hcHalf := critical_parameter_lt_half (by omega : 3 ≤ k) hc0 hcross
  have hcLower := critical_parameter_lower (by omega : 2 ≤ k) hc0 hcross
  have hcmore : 11/24 < c := by
    have hp : 0 < 2/(25*(k:ℝ)) := by positivity
    linarith
  have hcpos : 0 < c := by linarith
  have hden : 0 < (k:ℝ)+c := by linarith
  let x := 1/((k:ℝ)+c)
  let a := (k:ℝ)*x
  change 12/13 < a ∧ a < 1 ∧ 5/12 < a*c ∧
    1/3 < (1-x)^k ∧ (1-x)^k < Real.exp (-1) ∧ Real.exp (-1) < 3/8
  have ha : a = (k:ℝ)/((k:ℝ)+c) := by dsimp [a, x]; ring
  have haLower : 12/13 < a := by
    rw [ha]
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have haUpper : a < 1 := by
    rw [ha]
    exact (div_lt_one hden).mpr (by linarith)
  have hac : 5/12 < a*c := by
    nlinarith [mul_pos (by linarith : 0 < a) (by linarith : 0 < c-11/24)]
  have hxlt : x < (k:ℝ)⁻¹ := by
    dsimp [x]
    simpa only [one_div] using one_div_lt_one_div_of_lt hkpos (by linarith : (k:ℝ) < (k:ℝ)+c)
  have hxlower : 1/((k:ℝ)+1/2) ≤ x := by
    dsimp [x]
    exact one_div_le_one_div_of_le hden (by linarith)
  have hi : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by linarith)
  have hupper : (1-x)^k < Real.exp (-1) :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ 1-x) (by linarith : 1-x ≤ 1-1/((k:ℝ)+1/2)) k).trans_lt
      (half_shift_failure_lt_exp (by omega : 1 ≤ k))
  exact ⟨haLower, haUpper, hac, failure_above_one_third hk hxlt, hupper,
    exp_neg_one_lt_three_eighths⟩

end SharpTailMatching.CriticalEstimates
