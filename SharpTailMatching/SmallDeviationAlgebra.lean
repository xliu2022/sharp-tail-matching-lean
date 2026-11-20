module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

public section

open Set Real
open scoped BigOperators

namespace SharpTailMatching.SmallDeviationAlgebra

theorem log_le_half_sub_inv {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (x - x⁻¹) / 2 := by
  let g : ℝ → ℝ := fun t => (t - t⁻¹) / 2 - Real.log t
  have hg (t : ℝ) (ht : 1 ≤ t) : HasDerivAt g ((t - 1) ^ 2 / (2 * t ^ 2)) t := by
    have ht0 : t ≠ 0 := by linarith
    convert (((hasDerivAt_id t).sub ((hasDerivAt_id t).inv ht0)).div_const 2).sub
      (Real.hasDerivAt_log ht0) using 1
    · funext y
      rfl
    · simp only [id_eq]
      field_simp
      ring
  have hmono : MonotoneOn g (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro t ht
      exact (hg t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hg t (interior_subset ht)).deriv]
      positivity
  have h := hmono (show (1 : ℝ) ∈ Ici 1 by simp) hx hx
  dsimp [g] at h
  norm_num at h
  linarith

theorem deficit_log_derivative {ε u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun t : ℝ => (t - ε) * Real.log (1 - 1 / t))
      (Real.log (1 - 1 / u) + (u - ε) / (u * (u - 1))) u := by
  have hu0 : u ≠ 0 := by linarith
  have hum : u - 1 ≠ 0 := by linarith
  have hi : 1 - 1 / u ≠ 0 := by
    have h : 1 / u < 1 := (div_lt_one (by linarith : 0 < u)).mpr hu
    linarith
  convert ((hasDerivAt_id u).sub_const ε).mul
    (((hasDerivAt_const u 1).sub ((hasDerivAt_const u 1).div (hasDerivAt_id u) hu0)).log hi)
    using 1
  · funext t
    rfl
  · simp only [Pi.sub_apply, Pi.div_apply, id_eq]
    field_simp
    ring

theorem deficit_log_derivative_nonneg {ε u : ℝ} (hε : ε ≤ 1 / 2) (hu : 1 < u) :
    0 ≤ Real.log (1 - 1 / u) + (u - ε) / (u * (u - 1)) := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u - 1 := by linarith
  have hx : 1 ≤ u / (u - 1) := (le_div_iff₀ hum).mpr (by linarith)
  have hlog := log_le_half_sub_inv hx
  have hid : 1 - 1 / u = (u / (u - 1))⁻¹ := by field_simp <;> ring
  rw [hid, Real.log_inv]
  have hrat : (u - ε) / (u * (u - 1)) - (u / (u - 1) - (u / (u - 1))⁻¹) / 2 =
      (1 / 2 - ε) / (u * (u - 1)) := by field_simp <;> ring
  have hpos : 0 ≤ (1 / 2 - ε) / (u * (u - 1)) := by positivity
  linarith

theorem deficit_log_monotone {ε : ℝ} (hε : ε ≤ 1 / 2) :
    MonotoneOn (fun u : ℝ => (u - ε) * Real.log (1 - 1 / u)) (Ioi 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi _)
  · intro u hu
    exact (deficit_log_derivative hu).continuousAt.continuousWithinAt
  · intro u hu
    exact (deficit_log_derivative (interior_subset hu)).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(deficit_log_derivative (ε := ε) (interior_subset hu)).deriv]
    exact deficit_log_derivative_nonneg hε (interior_subset hu)

theorem deficit_log_lower {ε ζ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hζ : 1 + ε ≤ ζ) :
    Real.log (ε / (1 + ε)) ≤ (ζ - ε) * Real.log (1 - 1 / ζ) := by
  have h := deficit_log_monotone hε1 (show 1 + ε ∈ Ioi (1 : ℝ) by change 1 < 1 + ε; linarith)
    (show ζ ∈ Ioi (1 : ℝ) by change 1 < ζ; linarith) hζ
  have hid : 1 - 1 / (1 + ε) = ε / (1 + ε) := by field_simp <;> ring
  simpa only [show 1 + ε - ε = 1 by ring, one_mul, hid] using h

theorem log_chord {m r z : ℝ} (hm : 0 < m) (hr : m < r)
    (hz0 : 0 ≤ z) (hzm : z ≤ m) :
    z / m * Real.log (1 - m / r) ≤ Real.log (1 - z / r) := by
  have hr0 : 0 < r := hm.trans hr
  have hα : 0 ≤ 1 - z / m := sub_nonneg.mpr ((div_le_one hm).mpr hzm)
  have hβ : 0 ≤ z / m := div_nonneg hz0 hm.le
  have hx : (1 : ℝ) ∈ Ioi 0 := by norm_num
  have hy : 1 - m / r ∈ Ioi (0 : ℝ) := by
    change 0 < 1 - m / r
    exact sub_pos.mpr ((div_lt_one hr0).mpr hr)
  have hc := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hα hβ
    (show (1 - z / m) + z / m = 1 by ring)
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, mul_one] at hc
  have hid : 1 - z / m + z / m * (1 - m / r) = 1 - z / r := by
    field_simp
    ring
  rwa [hid] at hc

theorem small_deviation_of_product (n : ℕ) (z : Fin n → ℝ) {m r ε ζ p : ℝ}
    (hm : 0 < m) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hζ : 1 + ε ≤ ζ) (hr : r = m * ζ)
    (hz0 : ∀ i, 0 ≤ z i) (hzm : ∀ i, z i ≤ m)
    (hsum : (∑ i, z i) = m * (ζ - ε))
    (hp : (∏ i, (1 - z i / r)) ≤ p) : ε / (1 + ε) ≤ p := by
  have hζ1 : 1 < ζ := by linarith
  have hmr : m < r := by rw [hr]; nlinarith
  have hr0 : 0 < r := hm.trans hmr
  have hf (i : Fin n) : 0 < 1 - z i / r :=
    sub_pos.mpr ((div_lt_one hr0).mpr ((hzm i).trans_lt hmr))
  have hprod : 0 < ∏ i, (1 - z i / r) := Finset.prod_pos fun i _ => hf i
  have hp0 : 0 < p := hprod.trans_le hp
  have hlog := Real.log_le_log hprod hp
  rw [Real.log_prod (fun i _ => (hf i).ne')] at hlog
  have hsumlog := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => log_chord hm hmr (hz0 i) (hzm i))
  rw [← Finset.sum_mul, ← Finset.sum_div, hsum] at hsumlog
  have hcoef : m * (ζ - ε) / m = ζ - ε := by field_simp
  have hquot : m / r = 1 / ζ := by rw [hr]; field_simp
  rw [hcoef, hquot] at hsumlog
  have hsmall := deficit_log_lower hε0 hε1 hζ
  apply (Real.log_le_log_iff (by positivity : 0 < ε / (1 + ε)) hp0).mp
  linarith

end SharpTailMatching.SmallDeviationAlgebra
