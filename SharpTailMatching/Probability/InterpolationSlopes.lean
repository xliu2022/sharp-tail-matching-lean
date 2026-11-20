module

public import SharpTailMatching.Probability.ComparisonNodes
public import SharpTailMatching.ReciprocalPower

/-! # Explicit lower bounds for the interpolation slopes -/

@[expose] public section

noncomputable section

open SharpTailMatching.SlopeEstimates

namespace SharpTailMatching.Probability.ComparisonGeometry

def slopeLower (ℓ t : ℝ) : ℝ :=
  ((2*t+1)*ℓ-t-1)/(2*t*(t+1)*(t-ℓ))

theorem adjacent_chord_formula {ℓ t : ℕ} (hℓ : 1 ≤ ℓ) (hℓt : ℓ < t) :
    chordSlope ℓ t ((t:ℝ)+1) =
      1/((t:ℝ)*((t:ℝ)+1)*(1-(1-1/(t:ℝ)^2)^(t-ℓ)))-1/(t:ℝ) := by
  have ht2 : 1 < t := by omega
  have htR : (1:ℝ) < t := by exact_mod_cast ht2
  have ht0 : (0:ℝ) < t := by linarith
  have hts : (0:ℝ) < (t:ℝ)+1 := by positivity
  let q := 1-1/(t:ℝ)^2
  let r := (t:ℝ)/((t:ℝ)+1)
  have hq0 : 0 < q := by
    dsimp [q]
    apply sub_pos.mpr
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hq1 : q < 1 := by dsimp [q]; linarith [one_div_pos.mpr (sq_pos_of_pos ht0)]
  have hp : q^(t-ℓ) < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrpow : 0 < r^(t-ℓ) := pow_pos hr _
  have hbase : 1-1/(t:ℝ) = q*r := by dsimp [q,r]; field_simp; ring
  have hnext : 1-1/((t:ℝ)+1) = r := by dsimp [r]; field_simp; ring
  have hshift : t+1-ℓ = (t-ℓ)+1 := by omega
  have hden : r^(t-ℓ)*((t:ℝ)*(1-q^(t-ℓ))) ≠ 0 := by positivity
  have hid : (-(ℓ:ℝ)+((t:ℝ)+1)*r^((t-ℓ)+1))-
      (-(ℓ:ℝ)+(t:ℝ)*(q*r)^(t-ℓ)) = r^(t-ℓ)*((t:ℝ)*(1-q^(t-ℓ))) := by
    rw [pow_succ, mul_pow]
    dsimp [r]
    field_simp
    ring
  have htop : (1-r^((t-ℓ)+1))-(1-(q*r)^(t-ℓ)) = r^(t-ℓ)*(q^(t-ℓ)-r) := by
    rw [pow_succ, mul_pow]
    ring
  unfold chordSlope
  rw [show (t:ℝ)+1 = ((t+1:ℕ):ℝ) by push_cast; rfl,
    ← nodeTailNat_eq_real ℓ t hℓt.le ht2,
    ← nodeTailNat_eq_real ℓ (t+1) (by omega) (by omega),
    ← nodeExcessNat_eq_real ℓ t hℓt.le ht2,
    ← nodeExcessNat_eq_real ℓ (t+1) (by omega) (by omega)]
  unfold nodeTailNat nodeExcessNat nodePowerNat
  rw [hshift]
  push_cast
  rw [hbase, hnext, hid, htop]
  change (r^(t-ℓ)*(q^(t-ℓ)-r))/(r^(t-ℓ)*((t:ℝ)*(1-q^(t-ℓ)))) =
    1/((t:ℝ)*((t:ℝ)+1)*(1-q^(t-ℓ)))-1/(t:ℝ)
  dsimp [r] at *
  field_simp [ne_of_gt (sub_pos.mpr hp)]
  ring

theorem adjacent_chord_lower {ℓ t : ℕ} (hℓ : 1 ≤ ℓ) (hℓt : ℓ < t) :
    slopeLower ℓ t ≤ chordSlope ℓ t ((t:ℝ)+1) := by
  have htR : (1:ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have ht0 : (0:ℝ) < t := by linarith
  have hd : (0:ℝ) < (t:ℝ)-(ℓ:ℝ) := sub_pos.mpr (by exact_mod_cast hℓt)
  let q := 1-1/(t:ℝ)^2
  have hq0 : 0 < q := by
    dsimp [q]
    apply sub_pos.mpr
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hq1 : q < 1 := by dsimp [q]; linarith [one_div_pos.mpr (sq_pos_of_pos ht0)]
  have h := reciprocal_power_lower hq0 hq1 (by omega : 1 ≤ t-ℓ)
  have hdiv := div_le_div_of_nonneg_right h (by positivity : 0 ≤ (t:ℝ)*((t:ℝ)+1))
  have hid : (1/(((t-ℓ:ℕ):ℝ)*(1-q))+(((t-ℓ:ℕ):ℝ)-1)/(2*((t-ℓ:ℕ):ℝ)))/
      ((t:ℝ)*((t:ℝ)+1))-1/(t:ℝ) = slopeLower ℓ t := by
    dsimp [q]
    unfold slopeLower
    rw [Nat.cast_sub hℓt.le]
    field_simp [ne_of_gt hd]
    ring
  rw [adjacent_chord_formula hℓ hℓt]
  change slopeLower ℓ t ≤ 1/((t:ℝ)*((t:ℝ)+1)*(1-q^(t-ℓ)))-1/(t:ℝ)
  have heq : (1/(1-q^(t-ℓ)))/((t:ℝ)*((t:ℝ)+1)) =
      1/((t:ℝ)*((t:ℝ)+1)*(1-q^(t-ℓ))) := by rw [div_div, mul_comm (1-q^(t-ℓ))]
  rw [heq] at hdiv
  linarith

theorem adjacent_chord_strict_lower {ℓ t : ℕ} (hℓ : 1 ≤ ℓ) (hℓt : ℓ+1 < t) :
    slopeLower ℓ t < chordSlope ℓ t ((t:ℝ)+1) := by
  have htR : (1:ℝ) < t := by exact_mod_cast (show 1 < t by omega)
  have ht0 : (0:ℝ) < t := by linarith
  have hd : (0:ℝ) < (t:ℝ)-(ℓ:ℝ) := sub_pos.mpr (by exact_mod_cast (show ℓ < t by omega))
  let q := 1-1/(t:ℝ)^2
  have hq0 : 0 < q := by
    dsimp [q]
    apply sub_pos.mpr
    apply (div_lt_one (by positivity)).mpr
    nlinarith
  have hq1 : q < 1 := by dsimp [q]; linarith [one_div_pos.mpr (sq_pos_of_pos ht0)]
  have h := reciprocal_power_strict_lower hq0 hq1 (by omega : 2 ≤ t-ℓ)
  have hdiv := div_lt_div_of_pos_right h (by positivity : 0 < (t:ℝ)*((t:ℝ)+1))
  have hid : (1/(((t-ℓ:ℕ):ℝ)*(1-q))+(((t-ℓ:ℕ):ℝ)-1)/(2*((t-ℓ:ℕ):ℝ)))/
      ((t:ℝ)*((t:ℝ)+1))-1/(t:ℝ) = slopeLower ℓ t := by
    dsimp [q]
    unfold slopeLower
    rw [Nat.cast_sub (by omega : ℓ ≤ t)]
    field_simp [ne_of_gt hd]
    ring
  rw [adjacent_chord_formula hℓ (by omega)]
  change slopeLower ℓ t < 1/((t:ℝ)*((t:ℝ)+1)*(1-q^(t-ℓ)))-1/(t:ℝ)
  have heq : (1/(1-q^(t-ℓ)))/((t:ℝ)*((t:ℝ)+1)) =
      1/((t:ℝ)*((t:ℝ)+1)*(1-q^(t-ℓ))) := by rw [div_div, mul_comm (1-q^(t-ℓ))]
  rw [heq] at hdiv
  linarith

theorem slope_three_numerical {ℓ t : ℝ} (ht : 4 ≤ t) (hℓ : 3 ≤ ℓ) (hℓt : ℓ < t) :
    5/4 < (t*(t-1)/2-1)*slopeLower ℓ t := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t-ℓ := by linarith
  have hid : (t*(t-1)/2-1)*slopeLower ℓ t-5/4 =
      (7*t-4+2*(t^2+t-1)*(ℓ-3))/(4*t*(t-ℓ)) := by
    unfold slopeLower
    field_simp [ne_of_gt hd]
    ring
  have hnum : 0 < 7*t-4+2*(t^2+t-1)*(ℓ-3) := by
    have hp := mul_nonneg (by nlinarith : 0 ≤ 2*(t^2+t-1)) (by linarith : 0 ≤ ℓ-3)
    linarith
  have hpos := div_pos hnum (by positivity : 0 < 4*t*(t-ℓ))
  linarith

theorem slope_two_numerical {t : ℝ} (ht : 4 ≤ t) :
    3/4 < (t*(t-1)/2-2/3)*slopeLower 2 t := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < t-2 := by linarith
  have hid : (t*(t-1)/2-2/3)*slopeLower 2 t-3/4 =
      (3*t^2+3*t-4)/(12*t*(t+1)*(t-2)) := by
    unfold slopeLower
    field_simp [ne_of_gt hd]
    ring
  have hpos := div_pos (by nlinarith : 0 < 3*t^2+3*t-4)
    (by positivity : 0 < 12*t*(t+1)*(t-2))
  linarith

theorem interpolation_slope_three {ℓ t : ℕ} (ht : 4 ≤ t) (hℓ : 3 ≤ ℓ) (hℓt : ℓ < t) :
    5/4 < ((t:ℝ)*((t:ℝ)-1)/2-1)*chordSlope ℓ t ((t:ℝ)+1) := by
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
  have h := adjacent_chord_lower (by omega : 1 ≤ ℓ) hℓt
  have hmul := mul_le_mul_of_nonneg_left h (by nlinarith : 0 ≤ (t:ℝ)*((t:ℝ)-1)/2-1)
  exact (slope_three_numerical htR (by exact_mod_cast hℓ) (by exact_mod_cast hℓt)).trans_le hmul

theorem interpolation_slope_two {t : ℕ} (ht : 4 ≤ t) :
    3/4 < ((t:ℝ)*((t:ℝ)-1)/2-2/3)*chordSlope 2 t ((t:ℝ)+1) := by
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
  have h := adjacent_chord_lower (by omega : 1 ≤ 2) (by omega : 2 < t)
  norm_num only [Nat.cast_ofNat] at h
  have hmul := mul_le_mul_of_nonneg_left h (by nlinarith : 0 ≤ (t:ℝ)*((t:ℝ)-1)/2-2/3)
  exact (slope_two_numerical htR).trans_le hmul

theorem interpolation_slope_one {t : ℕ} (ht : 4 ≤ t) :
    1/5 < ((t:ℝ)*((t:ℝ)-1)/2)*chordSlope 1 t ((t:ℝ)+1) := by
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) < t := by linarith
  have h := adjacent_chord_strict_lower (by omega : 1 ≤ 1) (by omega : 1+1 < t)
  norm_num only [Nat.cast_one] at h
  have hmul := mul_lt_mul_of_pos_left h (by nlinarith : 0 < (t:ℝ)*((t:ℝ)-1)/2)
  have hid : ((t:ℝ)*((t:ℝ)-1)/2)*slopeLower 1 t = (t:ℝ)/(4*((t:ℝ)+1)) := by
    unfold slopeLower
    field_simp [ne_of_gt (by linarith : (0:ℝ) < (t:ℝ)-1)]
    ring
  have hlow : (1:ℝ)/5 ≤ (t:ℝ)/(4*((t:ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by linarith)
  rw [hid] at hmul
  exact hlow.trans_lt hmul

end SharpTailMatching.Probability.ComparisonGeometry
