module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Tactic

/-! # Finite binomial-tail bounds

The geometric majorant is proved for finite sums. No convergence assertion
or numerical approximation is used in the tail estimate.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace SharpTailMatching.TailEstimates

theorem factorial_growth (n j : ℕ) :
    (n+1).factorial * (n+2)^j ≤ (n+1+j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show n+1+(j+1) = (n+1+j)+1 by omega, Nat.factorial_succ, pow_succ]
      calc
        (n+1).factorial * ((n+2)^j * (n+2)) =
            (n+2) * ((n+1).factorial * (n+2)^j) := by ring
        _ ≤ (n+1+j+1) * (n+1+j).factorial := Nat.mul_le_mul (by omega) ih

theorem power_increment_bound (j : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    a^(j+1)-1 ≤ ((j+1:ℕ):ℝ)*(a-1)*a^j := by
  have ha0 : 0 ≤ a := by linarith
  induction j with
  | zero => simp
  | succ j ih =>
      have hp : 1 ≤ a^(j+1) := one_le_pow₀ ha
      have hh := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ a-1)
      have hm := mul_le_mul_of_nonneg_left ih ha0
      rw [pow_succ] at hm
      rw [pow_succ] at hh
      rw [pow_succ, pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one] at *
      nlinarith

theorem weighted_geometric_identity (m : ℕ) (r : ℝ) :
    (1-r)^2 * (∑ j ∈ Finset.range m, ((j+1:ℕ):ℝ)*r^j) =
      1-r^m*(1+(m:ℝ)*(1-r)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      push_cast
      ring

theorem weighted_geometric_bound (m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ j ∈ Finset.range m, ((j+1:ℕ):ℝ)*r^j) ≤ 1/(1-r)^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < 1-r))).mpr
  have h := weighted_geometric_identity m r
  have hp : 0 ≤ r^m*(1+(m:ℝ)*(1-r)) := by positivity
  nlinarith

theorem scaled_choose_bound {k : ℕ} (hk : 1 ≤ k) (h : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ((k-1).choose h : ℝ)*(c/(k:ℝ))^h ≤ c^h/(h.factorial:ℝ) := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hchoose := (Nat.choose_le_pow_div h (k-1) :
    ((k-1).choose h : ℝ) ≤ ((k-1:ℕ):ℝ)^h/(h.factorial:ℝ))
  have hpow : ((k-1:ℕ):ℝ)^h ≤ (k:ℝ)^h :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le k 1) h
  have hbound := hchoose.trans (div_le_div_of_nonneg_right hpow (by positivity))
  have hmul := mul_le_mul_of_nonneg_right hbound (pow_nonneg (div_nonneg hc hkpos.le) h)
  have hid : ((k:ℝ)^h/(h.factorial:ℝ))*(c/(k:ℝ))^h = c^h/(h.factorial:ℝ) := by
    rw [div_pow]
    field_simp
  rwa [hid] at hmul

def tailRatio (n : ℕ) (c : ℝ) : ℝ := c*((n:ℝ)+1)/((n:ℝ)*((n:ℝ)+2))

def tailPrefactor (n : ℕ) (c : ℝ) : ℝ := c^(n+1)/((n:ℝ)*((n+1).factorial:ℝ))

def tailTerm (n k j : ℕ) (c : ℝ) : ℝ :=
  ((k-1).choose (n+1+j):ℝ)*(c/(k:ℝ))^(n+1+j) *
    ((((n:ℝ)+1)/(n:ℝ))^(j+1)-1)

def tailSeries (n k : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, tailTerm n k j c

theorem tailRatio_bounds {n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    0 ≤ tailRatio n c ∧ tailRatio n c < 1 := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  constructor
  · unfold tailRatio; positivity
  · unfold tailRatio
    apply (div_lt_one (by positivity)).mpr
    have hp : c*((n:ℝ)+1) ≤ ((n:ℝ)+1)/2 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1/2-c) (by positivity : 0 ≤ (n:ℝ)+1)]
    nlinarith

theorem tailTerm_nonneg {n : ℕ} (hn : 1 ≤ n) (k j : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ tailTerm n k j c := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have ha : 1 ≤ ((n:ℝ)+1)/(n:ℝ) := (le_div_iff₀ hnpos).mpr (by linarith)
  unfold tailTerm
  exact mul_nonneg (by positivity) (sub_nonneg.mpr (one_le_pow₀ ha))

theorem tailTerm_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (j : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    tailTerm n k j c ≤ tailPrefactor n c * (((j+1:ℕ):ℝ)*(tailRatio n c)^j) := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let a := ((n:ℝ)+1)/(n:ℝ)
  have ha : 1 ≤ a := (le_div_iff₀ hnpos).mpr (by linarith)
  have hdif : 0 ≤ a^(j+1)-1 := sub_nonneg.mpr (one_le_pow₀ ha)
  have haid : a-1 = 1/(n:ℝ) := by dsimp [a]; field_simp; ring
  have hd := power_increment_bound j ha
  rw [haid] at hd
  have hfactor : ((n+1).factorial:ℝ)*((n:ℝ)+2)^j ≤ ((n+1+j).factorial:ℝ) := by
    exact_mod_cast factorial_growth n j
  have hcoef := scaled_choose_bound hk (n+1+j) hc
  have hfact := div_le_div_of_nonneg_left (pow_nonneg hc (n+1+j))
    (by positivity : 0 < ((n+1).factorial:ℝ)*((n:ℝ)+2)^j) hfactor
  change ((k-1).choose (n+1+j):ℝ)*(c/(k:ℝ))^(n+1+j) * (a^(j+1)-1) ≤ _
  calc
    _ ≤ (c^(n+1+j)/((n+1+j).factorial:ℝ)) * (a^(j+1)-1) :=
      mul_le_mul_of_nonneg_right hcoef hdif
    _ ≤ (c^(n+1+j)/((n+1+j).factorial:ℝ)) *
        (((j+1:ℕ):ℝ)*(1/(n:ℝ))*a^j) := mul_le_mul_of_nonneg_left hd (by positivity)
    _ ≤ (c^(n+1+j)/(((n+1).factorial:ℝ)*((n:ℝ)+2)^j)) *
        (((j+1:ℕ):ℝ)*(1/(n:ℝ))*a^j) :=
      mul_le_mul_of_nonneg_right hfact (by dsimp [a]; positivity)
    _ = _ := by
      unfold tailPrefactor tailRatio
      dsimp [a]
      simp only [pow_add, div_pow, mul_pow]
      field_simp

theorem tailSeries_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    tailSeries n k c ≤ tailPrefactor n c / (1-tailRatio n c)^2 := by
  obtain ⟨hr0, hr1⟩ := tailRatio_bounds hn hc0 hc1
  unfold tailSeries
  calc
    _ ≤ ∑ j ∈ Finset.range k, tailPrefactor n c * (((j+1:ℕ):ℝ)*(tailRatio n c)^j) :=
      Finset.sum_le_sum fun j _ => tailTerm_bound hn hk j hc0
    _ = tailPrefactor n c * ∑ j ∈ Finset.range k, ((j+1:ℕ):ℝ)*(tailRatio n c)^j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ tailPrefactor n c * (1/(1-tailRatio n c)^2) :=
      mul_le_mul_of_nonneg_left (weighted_geometric_bound k hr0 hr1)
        (by unfold tailPrefactor; positivity)
    _ = _ := by ring

theorem normalized_tail_bound {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {c R : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1/2) (hR0 : 0 ≤ R) (hR3 : R < 3) :
    R*tailSeries n k c < 3*tailPrefactor n c / (1-tailRatio n c)^2 := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hr1 := (tailRatio_bounds hn hc0.le hc1).2
  have hbound := mul_le_mul_of_nonneg_left (tailSeries_bound hn hk hc0.le hc1) hR0
  have hpos : 0 < tailPrefactor n c/(1-tailRatio n c)^2 := by
    unfold tailPrefactor
    exact div_pos (by positivity) (sq_pos_of_pos (by linarith))
  have hstrict := mul_lt_mul_of_pos_right hR3 hpos
  have hh := hbound.trans_lt hstrict
  simpa only [mul_div_assoc] using hh

end SharpTailMatching.TailEstimates
