module

public import SharpTailMatching.Probability.InterpolationSlopes
public import SharpTailMatching.CriticalProbabilityEstimates

/-! # Positivity of the normalized interpolation multipliers -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace SharpTailMatching.SlopeEstimates

theorem large_multiplier_step {k ℓ c a W α h hnext : ℝ}
    (hk : 0 < k) (hℓ : 3 ≤ ℓ) (hℓk : ℓ ≤ k)
    (hc0 : 0 ≤ c) (hc1 : c < 1/2) (ha : a ≤ 1)
    (hα : 0 ≤ α) (hnext0 : 0 ≤ hnext) (hslope : 5/4 < (W-1)*α)
    (hrec : (1+α)*h = c/ℓ*((1-ℓ/k)*hnext-a)+W*α) : 1 < h := by
  have hℓ0 : 0 < ℓ := by linarith
  have hcoef : 0 ≤ 1-ℓ/k := sub_nonneg.mpr ((div_le_one hk).mpr hℓk)
  have hprod := mul_nonneg hcoef hnext0
  have hterm : -(c/ℓ) ≤ c/ℓ*((1-ℓ/k)*hnext-a) := by
    have hh := mul_nonneg (div_nonneg hc0 hℓ0.le) (by linarith : 0 ≤ (1-ℓ/k)*hnext-a+1)
    rw [mul_add, mul_one] at hh
    linarith only [hh]
  have hfrac : c/ℓ < 1/6 := (div_lt_iff₀ hℓ0).mpr (by linarith)
  have hmul : (1+α)*1 < (1+α)*h := by nlinarith only [hrec, hterm, hfrac, hslope]
  exact lt_of_mul_lt_mul_left hmul (by linarith : 0 ≤ 1+α)

theorem second_multiplier_step {k c a W α h hnext : ℝ}
    (hk : 6 ≤ k) (hc0 : 0 ≤ c) (hc1 : c < 1/2) (ha : a ≤ 1)
    (hα : 0 ≤ α) (hnext1 : 1 < hnext) (hslope : 3/4 < (W-2/3)*α)
    (hrec : (1+α)*h = c/2*((1-2/k)*hnext-a)+W*α) : 2/3 < h := by
  have hk0 : 0 < k := by linarith
  have hcoef : 0 ≤ 1-2/k := sub_nonneg.mpr ((div_le_one hk0).mpr (by linarith))
  have hprod := mul_le_mul_of_nonneg_left hnext1.le hcoef
  have hterm : -(c/k) ≤ c/2*((1-2/k)*hnext-a) := by
    have hm := mul_nonneg (by positivity : 0 ≤ c/2) (by linarith : 0 ≤ (1-2/k)*hnext-a+2/k)
    have hid : c/2*((1-2/k)*hnext-a+2/k) = c/2*((1-2/k)*hnext-a)+c/k := by ring
    rw [hid] at hm
    linarith only [hm]
  have hfrac : c/k < 1/12 := (div_lt_iff₀ hk0).mpr (by linarith)
  have hmul : (1+α)*(2/3) < (1+α)*h := by nlinarith only [hrec, hterm, hfrac, hslope]
  exact lt_of_mul_lt_mul_left hmul (by linarith : 0 ≤ 1+α)

theorem first_multiplier_step {k c a W α h hnext : ℝ}
    (hk : 6 ≤ k) (hc0 : 0 < c) (hc1 : c < 1/2) (hac : 5/12 < a*c)
    (hrel : k*(1-a) = a*c) (hα : 0 ≤ α) (hnext1 : 2/3 < hnext)
    (hslope : 1/5 < W*α)
    (hrec : (1+α)*h = c*((1-1/k)*hnext-a)+W*α) : 0 < h := by
  have hk0 : 0 < k := by linarith
  have hcoef : 0 < 1-1/k := sub_pos.mpr ((div_lt_one hk0).mpr (by linarith))
  have hprod := mul_lt_mul_of_pos_left hnext1 hcoef
  have hterm := mul_lt_mul_of_pos_left (sub_lt_sub_right hprod a) hc0
  have hfrac : c/k < 1/12 := (div_lt_iff₀ hk0).mpr (by linarith)
  have hfrac0 : 0 < c/k := div_pos hc0 hk0
  have hlast := mul_pos hfrac0 (by linarith : 0 < a*c-5/12)
  have hid : 1/5+c*((1-1/k)*(2/3)-a) = 1/5-c/3+(c/k)*(a*c-2/3) := by
    have hm := congrArg (fun z : ℝ => c*z) hrel
    field_simp
    nlinarith only [hm]
  have hpos : 0 < 1/5+c*((1-1/k)*(2/3)-a) := by rw [hid]; nlinarith
  have hmul : 0 < (1+α)*h := by linarith
  exact pos_of_mul_pos_right hmul (by linarith : 0 ≤ 1+α)

theorem downward_multiplier_positive (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c a : ℝ) (hc0 : 0 < c) (hc1 : c < 1/2) (ha : a ≤ 1)
    (hac : 5/12 < a*c) (hrel : (k:ℝ)*(1-a) = a*c)
    (h : ℕ → ℝ) (hbase : h t = (t:ℝ)*((t:ℝ)-1)/2)
    (hrec : ∀ ℓ, 1 ≤ ℓ → ℓ < t →
      (1+Probability.ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1))*h ℓ =
        c/(ℓ:ℝ)*((1-(ℓ:ℝ)/(k:ℝ))*h (ℓ+1)-a)+
          ((t:ℝ)*((t:ℝ)-1)/2)*Probability.ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1)) :
    ∀ ℓ, 1 ≤ ℓ → ℓ ≤ t → 0 < h ℓ := by
  have hkR : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
  have hα (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓt : ℓ < t) :
      0 ≤ Probability.ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1) :=
    (Probability.ComparisonGeometry.chordSlope_pos ℓ t ((t:ℝ)+1)
      (by exact_mod_cast hℓ) (by exact_mod_cast (show ℓ+1 ≤ t by omega)) (by linarith)).le
  have hlarge : ∀ d : ℕ, d+3 ≤ t → 1 < h (t-d) := by
    intro d
    induction d with
    | zero => intro _; simpa [hbase] using (show (1:ℝ) < (t:ℝ)*((t:ℝ)-1)/2 by nlinarith)
    | succ d ih =>
        intro hd
        have hnext := ih (by omega)
        have heq : t-(d+1)+1 = t-d := by omega
        have hrl := hrec (t-(d+1)) (by omega) (by omega)
        rw [heq] at hrl
        exact large_multiplier_step hk0 (by exact_mod_cast (show 3 ≤ t-(d+1) by omega))
          (by exact_mod_cast (show t-(d+1) ≤ k by omega)) hc0.le hc1 ha
          (hα _ (by omega) (by omega)) (by linarith)
          (Probability.ComparisonGeometry.interpolation_slope_three ht (by omega) (by omega)) hrl
  have hthree : 1 < h 3 := by
    have hh := hlarge (t-3) (by omega)
    simpa only [Nat.sub_sub_self (by omega : 3 ≤ t)] using hh
  have htwo : (2:ℝ)/3 < h 2 := by
    have hh := hrec 2 (by omega) (by omega)
    norm_num only [Nat.cast_ofNat] at hh
    have hα2 : 0 ≤ Probability.ComparisonGeometry.chordSlope 2 t ((t:ℝ)+1) := by
      simpa only [Nat.cast_ofNat] using hα 2 (by omega) (by omega)
    exact second_multiplier_step hkR hc0.le hc1 ha hα2 hthree
      (Probability.ComparisonGeometry.interpolation_slope_two ht) hh
  have hone : 0 < h 1 := by
    have hh := hrec 1 (by omega) (by omega)
    norm_num only [Nat.cast_one, div_one] at hh
    have hα1 : 0 ≤ Probability.ComparisonGeometry.chordSlope 1 t ((t:ℝ)+1) := by
      simpa only [Nat.cast_one] using hα 1 (by omega) (by omega)
    exact first_multiplier_step hkR hc0 hc1 hac hrel hα1 htwo
      (Probability.ComparisonGeometry.interpolation_slope_one ht) hh
  intro ℓ hℓ hℓt
  rcases eq_or_lt_of_le hℓ with heq | hgt
  · subst ℓ; exact hone
  · by_cases hℓ2 : ℓ = 2
    · subst ℓ; linarith
    · have hh := hlarge (t-ℓ) (by omega)
      rw [Nat.sub_sub_self hℓt] at hh
      linarith

end SharpTailMatching.SlopeEstimates
