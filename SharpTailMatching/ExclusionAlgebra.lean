module

public import SharpTailMatching.CubicAlgebra
public import Mathlib.Tactic

public section

namespace SharpTailMatching.ExclusionAlgebra

@[expose] noncomputable def Φ (u : ℝ) : ℝ := (114 + 83 * u) * (1 - 3 * u) / 2400

theorem phi_le {u : ℝ} (hu : 0 ≤ u) : Φ u ≤ 19 / 400 := by
  unfold Φ
  nlinarith [sq_nonneg u]

theorem endpoint_quarter {b : ℝ} (hb : 0 ≤ b) :
    61731 / 1280000 ≤ 9 / 160 * (max (19 / 20 - 2 * b) 0) ^ 3 + 9 / 20 * b := by
  let y : ℝ := max (19 / 20 - 2 * b) 0
  have hy0 : 0 ≤ y := le_max_right _ _
  have hy1 : y ≤ 19 / 20 := max_le (by linarith) (by norm_num)
  have hy2 : 19 / 20 - 2 * b ≤ y := le_max_left _ _
  have hc := CubicAlgebra.cube_difference_bound hy0 hy1 (le_refl (19 / 20 : ℝ))
  change _ ≤ 9 / 160 * y ^ 3 + 9 / 20 * b
  nlinarith

theorem endpoint_three_quarters {b : ℝ} :
    41 / 800 < 27 / 160 * (max (19 / 20 - 2 * b) 0) ^ 3 + 3 / 20 * b := by
  let y : ℝ := max (19 / 20 - 2 * b) 0
  have hy : 0 ≤ y := le_max_right _ _
  have hrel : 19 / 20 - 2 * b ≤ y := le_max_left _ _
  have hcert : 135 * y ^ 3 - 60 * y + 16 =
      (y - 31 / 80) ^ 2 * (135 * y + 270 * (31 / 80)) +
      (405 * (31 / 80) ^ 2 - 60) * y + (16 - 270 * (31 / 80) ^ 3) := by ring
  have hpos : 0 < 135 * y ^ 3 - 60 * y + 16 := by
    rw [hcert]
    norm_num
    positivity
  change 41 / 800 < 27 / 160 * y ^ 3 + 3 / 20 * b
  nlinarith

theorem low_parameter_gap {σ b : ℝ} (hσ0 : 1 / 4 ≤ σ) (hσ1 : σ ≤ 3 / 4)
    (hb : 0 ≤ b) :
    19 / 400 < 9 * σ / 40 * (max (19 / 20 - 2 * b) 0) ^ 3 + 3 / 5 * (1 - σ) * b := by
  let y : ℝ := max (19 / 20 - 2 * b) 0
  have h₁ := endpoint_quarter hb
  have h₃ := endpoint_three_quarters (b := b)
  have h₃' : 61731 / 1280000 ≤ 27 / 160 * y ^ 3 + 3 / 20 * b := by
    change 41 / 800 < 27 / 160 * y ^ 3 + 3 / 20 * b at h₃
    linarith
  have hc₁ := mul_nonneg (by linarith : 0 ≤ 3 / 2 - 2 * σ) (sub_nonneg.mpr h₁)
  have hc₃ := mul_nonneg (by linarith : 0 ≤ 2 * σ - 1 / 2) (sub_nonneg.mpr h₃')
  change 0 ≤ (3 / 2 - 2 * σ) * (9 / 160 * y ^ 3 + 9 / 20 * b - 61731 / 1280000) at hc₁
  change _ < 9 * σ / 40 * y ^ 3 + 3 / 5 * (1 - σ) * b
  nlinarith

theorem high_parameter_gap {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 3) :
    Φ u < 1 / 6 * (7 / 10 - 3 * u / 4) ^ 3 := by
  have hcub : u ^ 3 ≤ u ^ 2 / 3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 3 - u) (sq_nonneg u)]
  have hpos : 0 < (1 : ℝ) / 4 * (u - 1 / 6) ^ 2 + 1 / 432 +
      (11745 * u ^ 2 + 3240 * u + 176) / 432000 := by positivity
  unfold Φ
  nlinarith

/-- The complete final numerical contradiction in Section 5. The variance
upper and lower bounds are the conclusions of the probabilistic lemmas;
this theorem performs the two parameter ranges without numerical oracles. -/
theorem normalized_variance_contradiction {θ u b v : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu0 : 0 ≤ u) (hu1 : u < 1 / 3)
    (hb0 : 0 ≤ b) (hb1 : b ≤ u + (7 - 5 * θ) / 32)
    (hvupper : v + 3 / 5 * (1 - θ) * b < Φ u)
    (hvlower : 9 * max θ (1 / 4) / 40 * (19 / 20 + 23 * u / 20 - 2 * b) ^ 3 < v) :
    False := by
  let D : ℝ := 19 / 20 + 23 * u / 20 - 2 * b
  have hD : 0 < D := by dsimp [D]; linarith
  have hΦ := phi_le hu0
  by_cases hθ : θ ≤ 3 / 4
  · let σ : ℝ := max θ (1 / 4)
    have hσ0 : 1 / 4 ≤ σ := le_max_right _ _
    have hσ1 : σ ≤ 3 / 4 := max_le hθ (by norm_num)
    have hθσ : θ ≤ σ := le_max_left _ _
    have hgap := low_parameter_gap hσ0 hσ1 hb0
    have hbase : max (19 / 20 - 2 * b) 0 ≤ D := by
      apply max_le <;> dsimp [D] at * <;> linarith
    have hcube := pow_le_pow_left₀ (le_max_right (19 / 20 - 2 * b) 0) hbase 3
    have hlower := mul_le_mul_of_nonneg_left hcube (by linarith : 0 ≤ 9 * σ / 40)
    have hlinear := mul_nonneg (sub_nonneg.mpr hθσ) hb0
    change 9 * σ / 40 * D ^ 3 < v at hvlower
    nlinarith
  · have hσ : max θ (1 / 4) = θ := max_eq_left (by linarith)
    rw [hσ] at hvlower
    have hb : b ≤ u + 13 / 128 := by linarith
    have hbase0 : 0 ≤ 7 / 10 - 3 * u / 4 := by linarith
    have hbase : 7 / 10 - 3 * u / 4 ≤ D := by dsimp [D]; linarith
    have hcube := pow_le_pow_left₀ hbase0 hbase 3
    have hcoefficient : 1 / 6 ≤ 9 * θ / 40 := by linarith
    have hlower := mul_le_mul hcoefficient hcube (pow_nonneg hbase0 3)
      (by linarith : 0 ≤ 9 * θ / 40)
    have hgap := high_parameter_gap hu0 hu1.le
    have hnonneg : 0 ≤ 3 / 5 * (1 - θ) * b := by positivity
    change 9 * θ / 40 * D ^ 3 < v at hvlower
    nlinarith

end SharpTailMatching.ExclusionAlgebra
