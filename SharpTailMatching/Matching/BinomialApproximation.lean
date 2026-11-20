module

public import SharpTailMatching.Matching.HeadlineBridge
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic

/-! # Explicit finite errors for the two extremal densities -/

@[expose] public section

namespace SharpTailMatching.Matching

theorem factorial_choose_le_power (a k : ℕ) :
    (k.factorial:ℝ)*(a.choose k:ℝ) ≤ (a:ℝ)^k := by
  exact_mod_cast (show k.factorial*a.choose k ≤ a^k by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow a k)

theorem factorial_choose_power_error {a n k : ℕ} (hk : 1 ≤ k) (han : a ≤ n) :
    (a:ℝ)^k-(k.factorial:ℝ)*(a.choose k:ℝ) ≤ (k:ℝ)^2*(n:ℝ)^(k-1) := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hanR : (a:ℝ) ≤ n := by exact_mod_cast han
  by_cases hka : k ≤ a
  · let b := a+1-k
    have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg b
    have hba : b ≤ a := by dsimp [b]; omega
    have hbaR : (b:ℝ) ≤ a := by exact_mod_cast hba
    have hbcast : (b:ℝ) = (a:ℝ)+1-k := by
      dsimp [b]
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hlower : (b:ℝ)^k ≤ (k.factorial:ℝ)*(a.choose k:ℝ) := by
      exact_mod_cast (show b^k ≤ k.factorial*a.choose k by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.pow_sub_le_descFactorial a k)
    have hab := abs_pow_sub_pow_le (a := (a:ℝ)) (b := (b:ℝ)) (n := k)
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0, max_eq_left hbaR,
      abs_of_nonneg (sub_nonneg.mpr hbaR)] at hab
    have hdiff := (le_abs_self ((a:ℝ)^k-(b:ℝ)^k)).trans hab
    have hcoef : ((a:ℝ)-b)*(k:ℝ) ≤ (k:ℝ)^2 := by nlinarith
    have hpower := pow_le_pow_left₀ ha0 hanR (k-1)
    have hright := mul_le_mul hcoef hpower (pow_nonneg ha0 _)
      (sq_nonneg (k:ℝ))
    nlinarith only [hlower, hdiff, hright]
  · have hak : a < k := lt_of_not_ge hka
    rw [Nat.choose_eq_zero_of_lt hak]
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    have hakR : (a:ℝ) < k := by exact_mod_cast hak
    have hak2 : (a:ℝ) ≤ (k:ℝ)^2 := by nlinarith
    calc
      (a:ℝ)^k = (a:ℝ)^(k-1)*(a:ℝ) := by
        rw [← pow_succ]
        congr 1
        omega
      _ ≤ (n:ℝ)^(k-1)*(k:ℝ)^2 :=
        mul_le_mul (pow_le_pow_left₀ ha0 hanR _) hak2 ha0
          (pow_nonneg (Nat.cast_nonneg n) _)
      _ = _ := by ring

theorem quotient_power_error {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    {u v C : ℝ} (h : u ≤ v+C*(n:ℝ)^(k-1)) :
    u/(n:ℝ)^k ≤ v/(n:ℝ)^k+C/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hpow : (n:ℝ)^k = (n:ℝ)^(k-1)*(n:ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hcancel : C*(n:ℝ)^(k-1)/(n:ℝ)^k = C/(n:ℝ) := by
    rw [hpow]
    field_simp
  calc
    u/(n:ℝ)^k ≤ (v+C*(n:ℝ)^(k-1))/(n:ℝ)^k :=
      div_le_div_of_nonneg_right h (pow_nonneg hnR.le _)
    _ = _ := by rw [add_div, hcancel]

theorem cover_density_lower {k s n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hsn : s ≤ n) :
    1-(1-(s:ℝ)/(n:ℝ))^k ≤
      (k.factorial:ℝ)*(coverSize k n s:ℝ)/(n:ℝ)^k+(k:ℝ)^2/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hden : (n:ℝ)^k ≠ 0 := pow_ne_zero _ hnR.ne'
  have hlower := factorial_choose_power_error hk (le_refl n)
  have hupper := factorial_choose_le_power (n-s) k
  have hcard : (k.factorial:ℝ)*(coverSize k n s:ℝ) =
      (k.factorial:ℝ)*(n.choose k:ℝ)-(k.factorial:ℝ)*((n-s).choose k:ℝ) := by
    unfold coverSize
    rw [Nat.cast_sub (Nat.choose_le_choose k (Nat.sub_le n s))]
    ring
  have hraw : (n:ℝ)^k-((n-s:ℕ):ℝ)^k ≤
      (k.factorial:ℝ)*(coverSize k n s:ℝ)+(k:ℝ)^2*(n:ℝ)^(k-1) := by
    rw [hcard]
    linarith
  have hsub : 1-(s:ℝ)/(n:ℝ) = ((n-s:ℕ):ℝ)/(n:ℝ) := by
    rw [Nat.cast_sub hsn]
    field_simp
  calc
    1-(1-(s:ℝ)/(n:ℝ))^k = ((n:ℝ)^k-((n-s:ℕ):ℝ)^k)/(n:ℝ)^k := by
      rw [hsub, div_pow, sub_div, div_self hden]
    _ ≤ _ := quotient_power_error hn hk hraw

theorem clique_density_lower {k s n : ℕ} (hk : 1 ≤ k)
    (hn : k*(s+1) ≤ n) :
    ((k:ℝ)*(s:ℝ)/(n:ℝ))^k ≤
      (k.factorial:ℝ)*(cliqueSize k s:ℝ)/(n:ℝ)^k+(k:ℝ)^2/(n:ℝ) := by
  have hkpos : 0 < k := by omega
  have hnpos : 0 < n := (Nat.mul_pos hkpos (Nat.succ_pos s)).trans_le hn
  have hqlo : k*s ≤ k*(s+1)-1 := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hqln : k*(s+1)-1 ≤ n := (Nat.sub_le _ _).trans hn
  have hqloR : ((k*s:ℕ):ℝ) ≤ ((k*(s+1)-1:ℕ):ℝ) := by exact_mod_cast hqlo
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (k*s)) hqloR k
  have hlower := factorial_choose_power_error hk hqln
  have hraw : ((k*s:ℕ):ℝ)^k ≤
      (k.factorial:ℝ)*(cliqueSize k s:ℝ)+(k:ℝ)^2*(n:ℝ)^(k-1) := by
    unfold cliqueSize
    linarith
  simpa only [div_pow, Nat.cast_mul] using quotient_power_error hnpos hk hraw

theorem cover_density_upper {k s n : ℕ} (hk : 1 ≤ k) (hn : 0 < n) (hsn : s ≤ n) :
    (k.factorial:ℝ)*(coverSize k n s:ℝ)/(n:ℝ)^k ≤
      1-(1-(s:ℝ)/(n:ℝ))^k+(k:ℝ)^2/(n:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hden : (n:ℝ)^k ≠ 0 := pow_ne_zero _ hnR.ne'
  have hlower := factorial_choose_power_error hk (Nat.sub_le n s)
  have hupper := factorial_choose_le_power n k
  have hcard : (k.factorial:ℝ)*(coverSize k n s:ℝ) =
      (k.factorial:ℝ)*(n.choose k:ℝ)-(k.factorial:ℝ)*((n-s).choose k:ℝ) := by
    unfold coverSize
    rw [Nat.cast_sub (Nat.choose_le_choose k (Nat.sub_le n s))]
    ring
  have hraw : (k.factorial:ℝ)*(coverSize k n s:ℝ) ≤
      ((n:ℝ)^k-((n-s:ℕ):ℝ)^k)+(k:ℝ)^2*(n:ℝ)^(k-1) := by
    rw [hcard]
    linarith
  have hsub : 1-(s:ℝ)/(n:ℝ) = ((n-s:ℕ):ℝ)/(n:ℝ) := by
    rw [Nat.cast_sub hsn]
    field_simp
  have heq : ((n:ℝ)^k-((n-s:ℕ):ℝ)^k)/(n:ℝ)^k = 1-(1-(s:ℝ)/(n:ℝ))^k := by
    rw [hsub, div_pow, sub_div, div_self hden]
  simpa only [heq] using quotient_power_error hn hk hraw

theorem clique_density_upper {k s n : ℕ} (hk : 1 ≤ k)
    (hn : k*(s+1) ≤ n) :
    (k.factorial:ℝ)*(cliqueSize k s:ℝ)/(n:ℝ)^k ≤
      ((k:ℝ)*(s:ℝ)/(n:ℝ))^k+(k:ℝ)^2/(n:ℝ) := by
  have hkpos : 0 < k := by omega
  have hnpos : 0 < n := (Nat.mul_pos hkpos (Nat.succ_pos s)).trans_le hn
  let q := k*(s+1)-1
  have hqlo : k*s ≤ q := by
    dsimp [q]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hqn : q ≤ n := (Nat.sub_le _ _).trans hn
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg q
  have hqloR : ((k*s:ℕ):ℝ) ≤ q := by exact_mod_cast hqlo
  have hqnR : (q:ℝ) ≤ n := by exact_mod_cast hqn
  have hks0 : (0:ℝ) ≤ ((k*s:ℕ):ℝ) := Nat.cast_nonneg (k*s)
  have hqcast : (q:ℝ) = (k:ℝ)*(s:ℝ)+(k:ℝ)-1 := by
    dsimp [q]
    rw [Nat.cast_sub (by nlinarith : 1 ≤ k*(s+1)), Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    ring
  have hab := abs_pow_sub_pow_le (a := (q:ℝ)) (b := ((k*s:ℕ):ℝ)) (n := k)
  rw [abs_of_nonneg hq0, abs_of_nonneg hks0, max_eq_left hqloR,
    abs_of_nonneg (sub_nonneg.mpr hqloR)] at hab
  have hdiff := (le_abs_self ((q:ℝ)^k-((k*s:ℕ):ℝ)^k)).trans hab
  have hcoef : ((q:ℝ)-((k*s:ℕ):ℝ))*(k:ℝ) ≤ (k:ℝ)^2 := by
    rw [Nat.cast_mul]
    nlinarith [show (0:ℝ) ≤ k from Nat.cast_nonneg k]
  have hright := mul_le_mul hcoef (pow_le_pow_left₀ hq0 hqnR (k-1))
    (pow_nonneg hq0 _) (sq_nonneg (k:ℝ))
  have hupper := factorial_choose_le_power q k
  have hraw : (k.factorial:ℝ)*(cliqueSize k s:ℝ) ≤
      ((k*s:ℕ):ℝ)^k+(k:ℝ)^2*(n:ℝ)^(k-1) := by
    change (k.factorial:ℝ)*(q.choose k:ℝ) ≤ _
    nlinarith only [hdiff, hright, hupper]
  simpa only [Nat.cast_mul, div_pow] using quotient_power_error hnpos hk hraw

/-- The finite two-construction maximum is within `k²/n` of the probability
candidate. The error is uniform over the full matching-parameter range. -/
theorem candidate_density_le_binomial_max {k s n : ℕ} (hk : 2 ≤ k)
    (hs : 1 ≤ s) (hn : k*(s+1) ≤ n) :
    max (1-(1-(s:ℝ)/(n:ℝ))^k) (((k:ℝ)*((s:ℝ)/(n:ℝ)))^k) ≤
      (k.factorial:ℝ)*(max (coverSize k n s) (cliqueSize k s):ℝ)/(n:ℝ)^k+
        (k:ℝ)^2/(n:ℝ) := by
  have hk1 : 1 ≤ k := by omega
  have hnpos : 0 < n := (Nat.mul_pos (by omega : 0 < k) (Nat.succ_pos s)).trans_le hn
  have hsn : s ≤ n := by nlinarith
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hcover := cover_density_lower hk1 hnpos hsn
  have hclique := clique_density_lower hk1 hn
  apply max_le
  · refine hcover.trans ?_
    gcongr
    exact_mod_cast le_max_left (coverSize k n s) (cliqueSize k s)
  · have hmul : (k:ℝ)*((s:ℝ)/(n:ℝ)) = (k:ℝ)*(s:ℝ)/(n:ℝ) := by ring
    rw [hmul]
    refine hclique.trans ?_
    gcongr
    exact_mod_cast le_max_right (coverSize k n s) (cliqueSize k s)

end SharpTailMatching.Matching
