module

public import Mathlib.Tactic

public section

/-!
# Algebraic comparison behind weighted interpolation

This file proves the local multiplier inequality and the telescoping step
of Lemma 3.4 in the readable manuscript. The geometric hypotheses that
produce the slopes and multipliers belong to a separate probability module.
-/

namespace SharpTailMatching.InterpolationAlgebra

theorem local_multiplier_inequality
    (d dnext g κ c α γprev γ : ℝ)
    (hstep : d + g ≤ dnext)
    (hcap : g ≤ α * d)
    (hγ : 0 ≤ γ)
    (hκ : γ ≤ κ)
    (hrec : γ * (1 + α) = γprev - c + κ * α) :
    κ * g - c * d ≤ γ * dnext - γprev * d := by
  have hidentity := congrArg (fun z : ℝ => z * d) hrec
  have hfirst : 0 ≤ γ * (dnext - d - g) :=
    mul_nonneg hγ (by linarith)
  have hsecond : 0 ≤ (κ - γ) * (α * d - g) :=
    mul_nonneg (sub_nonneg.mpr hκ) (sub_nonneg.mpr hcap)
  nlinarith

theorem multiplier_nonnegative
    (γprev c κ α : ℝ)
    (hprev : 0 ≤ γprev) (hc : c = 0)
    (hκ : 0 ≤ κ) (hα : 0 ≤ α) :
    0 ≤ (γprev - c + κ * α) / (1 + α) := by
  subst c
  positivity

theorem multiplier_le_weight
    (γprev c κ α : ℝ)
    (hprev : γprev ≤ κ) (hc : 0 ≤ c) (hα : 0 ≤ α) :
    (γprev - c + κ * α) / (1 + α) ≤ κ := by
  apply (div_le_iff₀ (by linarith : 0 < 1 + α)).2
  nlinarith

theorem telescoping_comparison
    (N : ℕ) (term a : ℕ → ℝ)
    (hlocal : ∀ j < N, term j ≤ a (j + 1) - a j) :
    ∑ j ∈ Finset.range N, term j ≤ a N - a 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hprefix : ∀ j < N, term j ≤ a (j + 1) - a j := by
        intro j hj
        exact hlocal j (Nat.lt_succ_of_lt hj)
      have hlast := hlocal N (Nat.lt_succ_self N)
      rw [Finset.sum_range_succ]
      have hsum := ih hprefix
      linarith

theorem endpoint_comparison
    (N : ℕ) (term γ d : ℕ → ℝ)
    (hlocal : ∀ j < N,
      term j ≤ γ (j + 1) * d (j + 1) - γ j * d j)
    (hzero : d 0 = 0) (hend : d N ≤ 0) (hγ : 0 ≤ γ N) :
    ∑ j ∈ Finset.range N, term j ≤ 0 := by
  have hsum := telescoping_comparison N term (fun j => γ j * d j) hlocal
  have hlast : γ N * d N ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ hend
  simp only [hzero, mul_zero, sub_zero] at hsum
  exact hsum.trans hlast

end SharpTailMatching.InterpolationAlgebra
