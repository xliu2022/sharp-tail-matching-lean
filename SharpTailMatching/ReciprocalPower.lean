module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # A reciprocal-power bound for the interpolation slopes -/

@[expose] public section

namespace SharpTailMatching.SlopeEstimates

theorem damped_linear_power_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    q^m*(1+(m:ℝ)*(1-q)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hp : 0 ≤ q^m := pow_nonneg hq0 m
      have hd : 0 ≤ ((m:ℝ)+1)*(1-q)^2 := by positivity
      have hm := mul_nonneg hp hd
      rw [pow_succ]
      push_cast
      nlinarith

theorem damped_linear_power_lt {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {m : ℕ} (hm : 1 ≤ m) : q^m*(1+(m:ℝ)*(1-q)) < 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
  have hprev := damped_linear_power_le hq0.le hq1.le j
  have hpos : 0 < q^j*(((j:ℝ)+1)*(1-q)^2) := by
    exact mul_pos (pow_pos hq0 j) (mul_pos (by positivity) (sq_pos_of_pos (by linarith)))
  rw [pow_succ]
  push_cast
  nlinarith

def powerGap (m : ℕ) (q : ℝ) : ℝ :=
  2*(m:ℝ)*(1-q)-(1-q^m)*(2+((m:ℝ)-1)*(1-q))

theorem powerGap_succ (m : ℕ) (q : ℝ) :
    powerGap (m+1) q = powerGap m q+(1-q)*(1-q^m*(1+(m:ℝ)*(1-q))) := by
  unfold powerGap
  rw [pow_succ]
  push_cast
  ring

theorem powerGap_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (m : ℕ) :
    0 ≤ powerGap m q := by
  induction m with
  | zero => simp [powerGap]
  | succ m ih =>
      rw [powerGap_succ]
      exact add_nonneg ih (mul_nonneg (sub_nonneg.mpr hq1)
        (sub_nonneg.mpr (damped_linear_power_le hq0 hq1 m)))

theorem powerGap_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {m : ℕ} (hm : 2 ≤ m) : 0 < powerGap m q := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
  rw [powerGap_succ]
  exact add_pos_of_nonneg_of_pos (powerGap_nonneg hq0.le hq1.le j)
    (mul_pos (sub_pos.mpr hq1) (sub_pos.mpr (damped_linear_power_lt hq0 hq1 (by omega))))

theorem reciprocal_power_lower {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    1/((m:ℝ)*(1-q))+((m:ℝ)-1)/(2*(m:ℝ)) ≤ 1/(1-q^m) := by
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hqpow : q^m < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hden : 0 < 2*(m:ℝ)*(1-q)*(1-q^m) := by positivity
  have hid : 1/(1-q^m)-(1/((m:ℝ)*(1-q))+((m:ℝ)-1)/(2*(m:ℝ))) =
      powerGap m q/(2*(m:ℝ)*(1-q)*(1-q^m)) := by
    unfold powerGap
    field_simp [ne_of_gt (sub_pos.mpr hq1), ne_of_gt (sub_pos.mpr hqpow)]
  have hnonneg := div_nonneg (powerGap_nonneg hq0.le hq1.le m) hden.le
  linarith

theorem reciprocal_power_strict_lower {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {m : ℕ} (hm : 2 ≤ m) :
    1/((m:ℝ)*(1-q))+((m:ℝ)-1)/(2*(m:ℝ)) < 1/(1-q^m) := by
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hqpow : q^m < 1 := pow_lt_one₀ hq0.le hq1 (by omega)
  have hden : 0 < 2*(m:ℝ)*(1-q)*(1-q^m) := by positivity
  have hid : 1/(1-q^m)-(1/((m:ℝ)*(1-q))+((m:ℝ)-1)/(2*(m:ℝ))) =
      powerGap m q/(2*(m:ℝ)*(1-q)*(1-q^m)) := by
    unfold powerGap
    field_simp [ne_of_gt (sub_pos.mpr hq1), ne_of_gt (sub_pos.mpr hqpow)]
  have hpos := div_pos (powerGap_pos hq0 hq1 hm) hden
  linarith

end SharpTailMatching.SlopeEstimates
