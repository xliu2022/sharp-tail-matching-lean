module

public import Mathlib.Tactic

public section

/-!
# Quantitative contradictions in support separation

The interval minimum in Lemma 4.5 is proved by an exact positive polynomial
certificate, avoiding a separate derivative/sign case split. The measure-theoretic
derivation of the two conditional variance estimates is a separate obligation.
-/

namespace SharpTailMatching.SupportAlgebra

theorem conditional_variance_upper {u μ : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1 / 3)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ (1 - 3 * u) / 20) :
    μ * (1 + 13 * u / 24 - μ) ≤ (114 + 83 * u) * (1 - 3 * u) / 2400 ∧
      (114 + 83 * u) * (1 - 3 * u) / 2400 < 19 / 400 := by
  have hdiff : 0 ≤ ((1 - 3 * u) / 20 - μ) *
      (1 + 13 * u / 24 - (1 - 3 * u) / 20 - μ) := by
    apply mul_nonneg <;> linarith
  constructor
  · nlinarith
  · nlinarith [sq_nonneg u]

theorem cantelli_interval_gap {ξ : ℝ}
    (hξ0 : (1 : ℝ) / 16 ≤ ξ) (hξ1 : ξ ≤ 17 / 20) :
    19 / 400 < ξ * (19 / 20 - ξ) ^ 2 / (1 - ξ) := by
  let u : ℝ := (ξ - 1 / 16) / (17 / 20 - 1 / 16)
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; norm_num; linarith
  have hrem : 0 ≤ 1 - u := by linarith
  have hid : ξ * (19 / 20 - ξ) ^ 2 - 19 / 400 * (1 - ξ) =
      11 / 8000 + (481 / 102400 - 11 / 8000) * (1 - u) ^ 3 +
      3 * (4987 / 25600 - 11 / 8000) * u * (1 - u) ^ 2 +
      3 * (989 / 32000 - 11 / 8000) * u ^ 2 * (1 - u) := by
    dsimp [u]
    ring
  have hpos : 0 < ξ * (19 / 20 - ξ) ^ 2 - 19 / 400 * (1 - ξ) := by
    rw [hid]
    norm_num
    positivity
  apply (lt_div_iff₀ (by linarith : 0 < 1 - ξ)).2
  linarith

theorem no_intermediate_contact {u μ ξ v : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1 / 3)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ (1 - 3 * u) / 20)
    (hξ0 : (1 : ℝ) / 16 ≤ ξ) (hξ1 : ξ ≤ 17 / 20)
    (hupper : v ≤ μ * (1 + 13 * u / 24 - μ))
    (hlower : ξ * (1 - μ - ξ) ^ 2 / (1 - ξ) ≤ v) : False := by
  have hμsmall : μ ≤ 1 / 20 := by linarith
  have hξ : 0 ≤ ξ := by linarith
  have hsquare : (19 / 20 - ξ) ^ 2 ≤ (1 - μ - ξ) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 20 - μ)
      (by linarith : 0 ≤ 39 / 20 - μ - 2 * ξ)]
  have hcompare : ξ * (19 / 20 - ξ) ^ 2 / (1 - ξ) ≤
      ξ * (1 - μ - ξ) ^ 2 / (1 - ξ) := by
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 1 - ξ)
    exact mul_le_mul_of_nonneg_left hsquare hξ
  obtain ⟨hbound, hstrict⟩ := conditional_variance_upper hu0 hu1 hμ0 hμ1
  have hgap := cantelli_interval_gap hξ0 hξ1
  linarith

theorem upper_component_cubic_gap :
    (3 : ℝ) / 10 * (13 / 24) ^ 3 = 19 / 400 + 41 / 230400 := by
  norm_num

end SharpTailMatching.SupportAlgebra
