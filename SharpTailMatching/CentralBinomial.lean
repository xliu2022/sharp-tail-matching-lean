module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic

/-! # A central binomial estimate with an exponential majorant -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.CentralBinomial

theorem paired_descFactorial_bound (n j : ℕ) :
    n.descFactorial (2*j) ≤ (n*(n-1))^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show 2*(j+1) = (2*j+1)+1 by omega,
        Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ]
      calc
        (n-(2*j+1)) * ((n-2*j) * n.descFactorial (2*j)) ≤
            (n-1) * (n * (n*(n-1))^j) := by
          exact Nat.mul_le_mul (Nat.sub_le_sub_left (by omega) n)
            (Nat.mul_le_mul (Nat.sub_le _ _) ih)
        _ = (n*(n-1))^j * (n*(n-1)) := by ring

theorem six_factorial_bound (j : ℕ) : 6^j * j.factorial ≤ (2*j+1).factorial := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      have hp : 6*(j+1) ≤ (2*j+3)*(2*j+2) := by nlinarith
      have h := Nat.mul_le_mul hp ih
      rw [pow_succ, Nat.factorial_succ,
        show 2*(j+1)+1 = (2*j+1+1)+1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      nlinarith only [h]

theorem paired_choose_bound (n j : ℕ) :
    (n.choose (2*j) : ℝ) / (2*j+1) ≤
      ((n*(n-1) : ℕ) : ℝ)^j / (6^j * (j.factorial : ℝ)) := by
  have hd : (n.descFactorial (2*j) : ℝ) ≤ ((n*(n-1) : ℕ) : ℝ)^j := by
    exact_mod_cast paired_descFactorial_bound n j
  have hf : (6:ℝ)^j * (j.factorial : ℝ) ≤ ((2*j+1).factorial : ℝ) := by
    exact_mod_cast six_factorial_bound j
  have hident : (n.choose (2*j) : ℝ) / (2*j+1) =
      (n.descFactorial (2*j) : ℝ) / ((2*j+1).factorial : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_one]
    have hf0 : ((2*j).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [hident]
  exact div_le_div₀ (by positivity) hd (by positivity) hf

theorem sum_range_double (m : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (2*m), f i) =
      ∑ j ∈ Finset.range m, (f (2*j) + f (2*j+1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2*(m+1) = (2*m+1)+1 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

theorem add_pow_extended (b h : ℝ) (k m : ℕ) (hkm : k < m) :
    (b+h)^k = ∑ i ∈ Finset.range m, (k.choose i : ℝ) * b^(k-i) * h^i := by
  rw [add_pow]
  calc
    (∑ i ∈ Finset.range (k+1), b^i * h^(k-i) * (k.choose i : ℝ)) =
        ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ) * b^(k-i) * h^i := by
      rw [← Finset.sum_range_reflect (fun i => (k.choose i : ℝ) * b^(k-i) * h^i) (k+1)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ k := by simpa using Finset.mem_range.mp hi
      have hsub : k+1-1-i = k-i := by omega
      rw [hsub, Nat.sub_sub_self hi', Nat.choose_symm hi']
      ring
    _ = ∑ i ∈ Finset.range m, (k.choose i : ℝ) * b^(k-i) * h^i := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hnot
      have hki : k < i := by simpa using hnot
      simp [Nat.choose_eq_zero_of_lt hki]

theorem central_binomial_identity (n : ℕ) {b : ℝ} (hb : b ≠ 0) (h : ℝ) :
    (b+h)^(n+1) - (b-h)^(n+1) =
      2*(n+1:ℕ)*h*b^n *
        ∑ j ∈ Finset.range (n+1), (n.choose (2*j) : ℝ)/(2*j+1) * (h/b)^(2*j) := by
  rw [add_pow_extended b h (n+1) (2*(n+1)) (by omega),
    show b-h = b+(-h) by ring,
    add_pow_extended b (-h) (n+1) (2*(n+1)) (by omega), ← Finset.sum_sub_distrib,
    sum_range_double]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have heven : (-h)^(2*j) = h^(2*j) := by simp [pow_mul]
  have hodd : (-h)^(2*j+1) = -(h^(2*j+1)) := by rw [pow_succ, heven, pow_succ]; ring
  rw [heven, hodd]
  by_cases hj : 2*j ≤ n
  · have hcoef : (n.choose (2*j) : ℝ) * (n+1) =
        ((n+1).choose (2*j+1) : ℝ) * (2*j+1) := by
      have hh := Nat.add_one_mul_choose_eq n (2*j)
      exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
    have hpow : b^n * (h/b)^(2*j) = b^(n-2*j) * h^(2*j) := by
      conv_lhs => rw [show n = (n-2*j)+2*j by omega, pow_add]
      rw [div_pow]
      field_simp
    have hsub : n+1-(2*j+1) = n-2*j := by omega
    rw [hsub]
    have hcoef' : ((n+1).choose (2*j+1) : ℝ) =
        (n.choose (2*j) : ℝ)*(n+1)/(2*j+1) := by
      apply (eq_div_iff (by positivity : (2*j+1:ℝ) ≠ 0)).mpr
      exact hcoef.symm
    rw [hcoef']
    calc
      _ = 2*(n+1:ℕ)*h*(b^(n-2*j)*h^(2*j)) * ((n.choose (2*j):ℝ)/(2*j+1)) := by
        rw [pow_succ]
        push_cast
        ring
      _ = _ := by rw [← hpow]; ring
  · have hn : n < 2*j := by omega
    have hn' : n+1 < 2*j+1 := by omega
    simp [Nat.choose_eq_zero_of_lt hn, Nat.choose_eq_zero_of_lt hn']

theorem central_binomial_exp_bound (n : ℕ) {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    (b+h)^(n+1) - (b-h)^(n+1) ≤
      2*(n+1:ℕ)*h*b^n * Real.exp (((n*(n-1):ℕ):ℝ) * (h/b)^2 / 6) := by
  rw [central_binomial_identity n hb.ne' h]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ j ∈ Finset.range (n+1), (n.choose (2*j):ℝ)/(2*j+1)*(h/b)^(2*j)) ≤
        ∑ j ∈ Finset.range (n+1),
          (((n*(n-1):ℕ):ℝ)*(h/b)^2/6)^j / (j.factorial:ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      have hv := mul_le_mul_of_nonneg_right (paired_choose_bound n j)
        (pow_nonneg (div_nonneg hh hb.le) (2*j))
      convert hv using 1
      rw [div_pow, mul_pow, ← pow_mul]
      ring
    _ ≤ _ := Real.sum_le_exp_of_nonneg (by positivity) (n+1)

end SharpTailMatching.CentralBinomial
