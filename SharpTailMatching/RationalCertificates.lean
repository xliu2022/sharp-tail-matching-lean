module

public import SharpTailMatching.ScalarCertificates
public import SharpTailMatching.PositivePolynomials

public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace SharpTailMatching.RationalCertificates

open ScalarCertificates PositivePolynomials

@[expose] noncomputable def phi (n k c : ℝ) : ℝ :=
  (1 + 3 / (6 * n + 4) + (3 / (6 * n + 4)) ^ 2 / 2 +
      (3 / (6 * n + 4)) ^ 3 / 6) *
    (1 + (k - 1) * (c / (k + c)) / n +
      (k - 1) * (k - 2) * (c / (k + c)) ^ 2 / (2 * n ^ 2)) *
    (1 + (1 / 2 - c) / k + 1 / (12 * k ^ 2)) - 1 -
    comparisonValue (n + 1) (k / (k + c))

@[expose] noncomputable def largeFactor (n k : ℝ) : ℝ :=
  (5 / 124416 : ℝ) * (6 * n + 4) ^ 3 * k ^ 2 * n ^ 3 *
    (24 * k + 11) ^ 2 * (n + 1) * ((n + 1) * (24 * k + 11) - 24 * k)

@[expose] noncomputable def clearedLarge (n k : ℝ) : ℝ :=
  (5 / 11943936 : ℝ) * n * (n + 1) * ((n + 1) * (24 * k + 11) - 24 * k) *
    (2 * (6 * n + 4) ^ 3 + 6 * (6 * n + 4) ^ 2 + 9 * (6 * n + 4) + 9) *
    (2 * n ^ 2 * (24 * k + 11) ^ 2 + 22 * n * (24 * k + 11) * (k - 1) +
      121 * (k - 1) * (k - 2)) * (24 * k ^ 2 + k + 2) -
    largeFactor n k -
    (1 / 20736 : ℝ) * (6 * n + 4) ^ 3 * k ^ 3 * n ^ 3 * (24 * k + 11) *
      (19 * (n + 1) * (24 * k + 11) + 96 * k) -
    (1 / 12441600 : ℝ) * (6 * n + 4) ^ 3 * k ^ 2 * (24 * k + 11) ^ 2 *
      (n + 1) * ((n + 1) * (24 * k + 11) - 24 * k)

theorem large_shift_identity (n k : ℝ) :
    clearedLarge n k = largePolynomial (n - 5) (k - n - 2) := by
  unfold clearedLarge largeFactor largePolynomial
  ring

theorem large_factor_pos {n k : ℝ} (hn : 5 ≤ n) (hk : n + 2 ≤ k) :
    0 < largeFactor n k := by
  have hn0 : 0 < n := by linarith
  have hk0 : 0 < k := by linarith
  have hu : 0 < (n + 1) * (24 * k + 11) - 24 * k := by
    nlinarith [mul_pos hn0 hk0]
  unfold largeFactor
  positivity

theorem large_clearing_identity {n k : ℝ} (hn : 5 ≤ n) (hk : n + 2 ≤ k) :
    largeFactor n k * (phi n k (11 / 24) - 1 / (500 * n ^ 3)) =
      clearedLarge n k := by
  have hn0 : 0 < n := by linarith
  have hk0 : 0 < k := by linarith
  have hd : 6 * n + 4 ≠ 0 := by positivity
  have hK : 24 * k + 11 ≠ 0 := by positivity
  have hkp : 0 < k + 11 / 24 := by positivity
  have hn1 : n + 1 ≠ 0 := by positivity
  have hu : (n + 1) * (24 * k + 11) - 24 * k ≠ 0 := by
    have hp : 0 < (n + 1) * (24 * k + 11) - 24 * k := by
      nlinarith [mul_pos hn0 hk0]
    exact ne_of_gt hp
  have hfrac : k / (k + 11 / 24) < 1 := by
    apply (div_lt_one hkp).2
    linarith
  have hdiff : n + 1 - k / (k + 11 / 24) ≠ 0 := by
    have hp : 0 < n + 1 - k / (k + 11 / 24) := by linarith
    exact ne_of_gt hp
  have hu' : 11 + k * n * 24 + n * 11 ≠ 0 := by positivity
  unfold clearedLarge largeFactor phi comparisonValue
  field_simp [ne_of_gt hn0, ne_of_gt hk0, hd, hK, ne_of_gt hkp, hn1, hu, hu', hdiff]
  ring_nf
  field_simp [hu']
  ring

theorem phi_lower_bound_large {n k : ℝ} (hn : 5 ≤ n) (hk : n + 2 ≤ k) :
    1 / (500 * n ^ 3) < phi n k (11 / 24) := by
  have hp : 0 < clearedLarge n k := by
    rw [large_shift_identity]
    apply largePolynomial_pos <;> linarith
  have hf := large_factor_pos hn hk
  have hid := large_clearing_identity hn hk
  by_contra h
  have hle : phi n k (11 / 24) - 1 / (500 * n ^ 3) ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt h)
  have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hf) hle
  linarith

@[expose] noncomputable def smallFactor (k : ℝ) : ℝ :=
  (5488000 / 56441883 : ℝ) * k ^ 2 * ((3 * k + 1) * (8 * k + 1)) ^ 2 *
    (5 * ((3 * k + 1) * (8 * k + 1)) - 24 * k ^ 2)

theorem small_factor_pos {k : ℝ} (hk : 6 ≤ k) : 0 < smallFactor k := by
  have hk0 : 0 < k := by linarith
  have hu : 0 < 5 * ((3 * k + 1) * (8 * k + 1)) - 24 * k ^ 2 := by
    nlinarith [sq_nonneg k]
  unfold smallFactor
  positivity

theorem small_clearing_identity {k : ℝ} (hk : 6 ≤ k) :
    smallFactor k * (phi 4 k (11 / 24 + 1 / (24 * k)) - 1 / 4000) =
      smallPolynomial (k - 6) := by
  have hk0 : 0 < k := by linarith
  have hc0 : 0 < (11 : ℝ) / 24 + 1 / (24 * k) := by positivity
  have hkp : 0 < k + (11 / 24 + 1 / (24 * k)) := by positivity
  have hfrac : k / (k + (11 / 24 + 1 / (24 * k))) < 1 := by
    apply (div_lt_one hkp).2
    linarith
  have hdiff : 5 - k / (k + (11 / 24 + 1 / (24 * k))) ≠ 0 := by
    have hp : 0 < 5 - k / (k + (11 / 24 + 1 / (24 * k))) := by linarith
    exact ne_of_gt hp
  have hK : 1 + k * 11 + k ^ 2 * 24 ≠ 0 := by positivity
  have hU : 5 + k * 55 + k ^ 2 * 96 ≠ 0 := by positivity
  unfold smallFactor phi comparisonValue smallPolynomial
  field_simp [ne_of_gt hk0, ne_of_gt hkp, hdiff, hK, hU]
  ring_nf
  field_simp (disch := positivity)
  ring

theorem phi_lower_bound_four {k : ℝ} (hk : 6 ≤ k) :
    1 / 4000 < phi 4 k (11 / 24 + 1 / (24 * k)) := by
  have hp : 0 < smallPolynomial (k - 6) := smallPolynomial_pos (by linarith)
  have hf := small_factor_pos hk
  have hid := small_clearing_identity hk
  by_contra h
  have hle : phi 4 k (11 / 24 + 1 / (24 * k)) - 1 / 4000 ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt h)
  have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hf) hle
  linarith

end SharpTailMatching.RationalCertificates
