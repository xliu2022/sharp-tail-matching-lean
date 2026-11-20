module

public import Mathlib.Tactic

public section

/-!
# Scalar identities used in the sharp tail proof

These are the exact algebraic identities in Appendix A of the readable
manuscript. Every identity is proved by kernel-checked field/ring reasoning.
This file contains no assertion of the main probability or matching theorem.
-/

namespace SharpTailMatching.ScalarCertificates

@[expose] noncomputable def fourthNodeG (c h : ℝ) : ℝ :=
  1 + (1 - h) * (2 * c - 1) / 2 +
    (1 - h) * (1 - 2 * h) * (3 * c ^ 2 - 3 * c + 1) / 6 +
    (1 - h) * (1 - 2 * h) * (1 - 3 * h) *
      (4 * c ^ 3 - 6 * c ^ 2 + 4 * c - 1) / 24

@[expose] noncomputable def fourthNodeA (c h : ℝ) : ℝ :=
  37 / 64 * c + 7 / 32 * (1 - h) * c ^ 2 +
    1 / 24 * (1 - h) * (1 - 2 * h) * c ^ 3

@[expose] noncomputable def fourthNodeT (c h : ℝ) : ℝ :=
  c ^ 4 * (1 - h) * (1 - 2 * h) * (1 - 3 * h) * (1 - 4 * h) /
    (24 * (1 - c / 5))

@[expose] noncomputable def fourthNodeR₀ (c : ℝ) : ℝ :=
  1 + 13 * (1 / 2 - c) + (1 / 2 - c) ^ 2 *
    (1732 - 728 * (1 / 2 - c) - 552 * (1 / 2 - c) ^ 2)

@[expose] noncomputable def fourthNodeR₁ (c : ℝ) : ℝ :=
  48 + (1 / 2 - c) * (114 + 1636 * (1 / 2 - c) +
    1128 * (1 / 2 - c) ^ 2 + 2000 * (1 / 2 - c) ^ 3)

@[expose] noncomputable def fourthNodeR₂ (c : ℝ) : ℝ :=
  -240 + c * (1008 - 1632 * c + c ^ 2 * (1248 - 2392 * c))

theorem fourth_node_identity {c h : ℝ} (hc : c ≠ 5) (hh : h ≠ 1) :
    81 / 256 - fourthNodeA c h - fourthNodeT c h / 4 +
      (4 - h) / (5 * (1 - h)) * (fourthNodeG c h - 1) =
    (1 - 4 * h) / (3840 * (5 - c)) *
      (fourthNodeR₀ c + h * fourthNodeR₁ c + h ^ 2 * fourthNodeR₂ c +
        1200 * c ^ 4 * h ^ 3) := by
  have hc' : 5 - c ≠ 0 := by intro he; apply hc; linarith
  have hc'' : 1 - c / 5 ≠ 0 := by intro he; apply hc; linarith
  have hh' : 1 - h ≠ 0 := by intro he; apply hh; linarith
  unfold fourthNodeA fourthNodeT fourthNodeG fourthNodeR₀ fourthNodeR₁ fourthNodeR₂
  field_simp [hc', hc'', hh']
  ring

@[expose] noncomputable def comparisonValue (t u : ℝ) : ℝ :=
  u * (19 * t + 4 * u) / (20 * t * (t - u))

@[expose] noncomputable def deficitTest (t u z : ℝ) : ℝ :=
  t - 2 * u + (t - u) * z - 19 * u / (20 * z)

theorem node_difference_three_two (c h : ℝ) :
    (15 / 8 * c + 9 / 16 * (1 - h) * c ^ 2) - 2 * c =
      c * (9 * (1 - h) * c - 2) / 16 := by
  ring

theorem node_difference_four_three (c h : ℝ) :
    (148 / 81 * c + 56 / 81 * (1 - h) * c ^ 2 +
      32 / 243 * (1 - h) * (1 - 2 * h) * c ^ 3) -
      (15 / 8 * c + 9 / 16 * (1 - h) * c ^ 2) =
    c * (501 * (1 - h) * c +
      512 * (1 - h) * (1 - 2 * h) * c ^ 2 - 186) / 3888 := by
  ring

theorem comparisonValue_pos {t u : ℝ}
    (hu : 0 < u) (htu : u < t) : 0 < comparisonValue t u := by
  have ht : 0 < t := lt_trans hu htu
  unfold comparisonValue
  positivity

theorem target_substitution {t u : ℝ}
    (hu : 0 < u) (htu : u < t) :
    deficitTest t u (comparisonValue t u) - 3 * u / 20 =
      u * (t - 4 * u) * (t - u) / (5 * t * (19 * t + 4 * u)) := by
  have ht : 0 < t := lt_trans hu htu
  have htu0 : t - u ≠ 0 := ne_of_gt (sub_pos.mpr htu)
  have hlin : 19 * t + 4 * u ≠ 0 := by positivity
  unfold deficitTest comparisonValue
  field_simp [ne_of_gt hu, ne_of_gt ht, htu0, hlin]
  ring

theorem target_substitution_strict {t u : ℝ}
    (hu : 0 < u) (htu : 4 * u < t) :
    3 * u / 20 < deficitTest t u (comparisonValue t u) := by
  have hut : u < t := by linarith
  have ht : 0 < t := lt_trans hu hut
  have hpos : 0 <
      u * (t - 4 * u) * (t - u) / (5 * t * (19 * t + 4 * u)) := by
    positivity
  have hid := target_substitution hu hut
  linarith

/-- The coefficient inequalities used after differentiating the rational bound. -/
theorem derivative_coefficient_bounds {c : ℝ}
    (hc0 : (11 : ℝ) / 24 ≤ c) (hc1 : c ≤ 1 / 2) :
    0 ≤ 3 - 6 * c ∧
    103 / 48 ≤ -5 / 6 + 14 * c - 15 * c ^ 2 ∧
    3325 / 1152 ≤ -1 / 6 - 5 * c / 3 + 21 * c ^ 2 - 5 * c ^ 3 ∧
    7205 / 13824 ≤ c * (7 * c ^ 2 - 1 / 3) := by
  have hc : 0 ≤ c := by linarith
  have hs0 : 0 ≤ (c - 11 / 24) * (1 / 2 - c) :=
    mul_nonneg (by linarith) (by linarith)
  have hs1 : 0 ≤ (c - 11 / 24) ^ 2 := sq_nonneg _
  have hs2 : 0 ≤ c * (c - 11 / 24) ^ 2 := mul_nonneg hc hs1
  have hs3 : 0 ≤ (c - 11 / 24) ^ 2 * (1 / 2 - c) :=
    mul_nonneg hs1 (by linarith)
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

theorem derivative_boundary_positive {k c : ℝ}
    (hk : 0 < k) (hc0 : (11 : ℝ) / 24 ≤ c) (hc1 : c ≤ 1 / 2) :
    0 < (3 - 6 * c) * k ^ 3 +
      (-5 / 6 + 14 * c - 15 * c ^ 2) * k ^ 2 +
      (-1 / 6 - 5 * c / 3 + 21 * c ^ 2 - 5 * c ^ 3) * k +
      c * (7 * c ^ 2 - 1 / 3) := by
  obtain ⟨h0, h1, h2, h3⟩ := derivative_coefficient_bounds hc0 hc1
  have hp0 : 0 ≤ (3 - 6 * c) * k ^ 3 := mul_nonneg h0 (by positivity)
  have hp1 : 0 ≤ (-5 / 6 + 14 * c - 15 * c ^ 2) * k ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg k)
  have hp2 : 0 ≤ (-1 / 6 - 5 * c / 3 + 21 * c ^ 2 - 5 * c ^ 3) * k :=
    mul_nonneg (by linarith) (le_of_lt hk)
  linarith

theorem fourth_node_positive_gap {c h : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 2)
    (hh0 : 0 < h) (hh1 : h ≤ 1 / 5)
    (hG : fourthNodeG c h ≤ 1) :
    fourthNodeT c h / 4 < 81 / 256 - fourthNodeA c h := by
  have hy0 : 0 ≤ 1 / 2 - c := by linarith
  have hy1 : 1 / 2 - c ≤ 1 / 2 := by linarith
  have hy2 : (1 / 2 - c) ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hy0 hc0]
  have hinner : 0 ≤ 1732 - 728 * (1 / 2 - c) - 552 * (1 / 2 - c) ^ 2 := by
    nlinarith
  have hR0 : 1 ≤ fourthNodeR₀ c := by
    unfold fourthNodeR₀
    nlinarith [mul_nonneg (sq_nonneg (1 / 2 - c)) hinner]
  have hR1 : 48 ≤ fourthNodeR₁ c := by
    have hp : 0 ≤ (1 / 2 - c) * (114 + 1636 * (1 / 2 - c) +
        1128 * (1 / 2 - c) ^ 2 + 2000 * (1 / 2 - c) ^ 3) := by positivity
    unfold fourthNodeR₁
    linarith
  have hcA : 0 ≤ 1008 - 1632 * c := by linarith
  have hcB : 0 ≤ 1248 - 2392 * c := by linarith
  have hR2 : -240 ≤ fourthNodeR₂ c := by
    have hp : 0 ≤ c * (1008 - 1632 * c + c ^ 2 * (1248 - 2392 * c)) := by
      positivity
    unfold fourthNodeR₂
    linarith
  have hhR1 : 48 * h ≤ h * fourthNodeR₁ c := by
    nlinarith [mul_nonneg (le_of_lt hh0) (sub_nonneg.mpr hR1)]
  have hhR2 : -240 * h ^ 2 ≤ h ^ 2 * fourthNodeR₂ c := by
    nlinarith [mul_nonneg (sq_nonneg h) (by linarith : 0 ≤ fourthNodeR₂ c + 240)]
  have htail : 0 ≤ 1200 * c ^ 4 * h ^ 3 := by positivity
  have hhquad : 0 ≤ 48 * h - 240 * h ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hh0) (by linarith : 0 ≤ 1 / 5 - h)]
  have hbracket : 0 < fourthNodeR₀ c + h * fourthNodeR₁ c +
      h ^ 2 * fourthNodeR₂ c + 1200 * c ^ 4 * h ^ 3 := by linarith
  have hfac : 0 < (1 - 4 * h) / (3840 * (5 - c)) := by
    apply div_pos <;> nlinarith
  have hm : 0 ≤ (4 - h) / (5 * (1 - h)) := by
    apply div_nonneg <;> nlinarith
  have hmG : (4 - h) / (5 * (1 - h)) * (fourthNodeG c h - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm (sub_nonpos.mpr hG)
  have hid := fourth_node_identity (c := c) (h := h) (by linarith) (by linarith)
  have hpos := mul_pos hfac hbracket
  linarith

end SharpTailMatching.ScalarCertificates
