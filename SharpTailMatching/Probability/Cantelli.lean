module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace SharpTailMatching.Probability

theorem shifted_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) (t : ℝ) :
    (∫ ω, (X ω - (∫ ω, X ω ∂μ) - t) ^ 2 ∂μ) = Var[X; μ] + t ^ 2 := by
  have hshift : MemLp (fun ω => X ω - ((∫ ω, X ω ∂μ) + t)) 2 μ := hX.sub (memLp_const _)
  have hmean : (∫ ω, X ω - ((∫ ω, X ω ∂μ) + t) ∂μ) = -t := by
    rw [integral_sub (hX.integrable one_le_two) (integrable_const _),
      integral_const, probReal_univ, one_smul]
    ring
  have hv := variance_eq_sub hshift
  rw [variance_sub_const hX.aestronglyMeasurable, hmean] at hv
  have heq : (fun ω => (X ω - (∫ ω, X ω ∂μ) - t) ^ 2) =
      (fun ω => (X ω - ((∫ ω, X ω ∂μ) + t)) ^ 2) := by
    funext ω
    ring
  rw [heq]
  change Var[X; μ] = (∫ ω, (X ω - ((∫ ω, X ω ∂μ) + t)) ^ 2 ∂μ) - (-t) ^ 2 at hv
  nlinarith

theorem cantelli_shifted_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) {y t : ℝ}
    (hy : y ≤ ∫ ω, X ω ∂μ) (ht : 0 ≤ t) :
    ((∫ ω, X ω ∂μ) - y + t) ^ 2 * μ.real {ω | X ω ≤ y} ≤
      Var[X; μ] + t ^ 2 := by
  let r : ℝ := ∫ ω, X ω ∂μ
  have hshift : MemLp (fun ω => X ω - r - t) 2 μ :=
    (hX.sub (memLp_const r)).sub (memLp_const t)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (X ω - r - t) ^ 2)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) hshift.integrable_sq ((r - y + t) ^ 2)
  have hsub : {ω | X ω ≤ y} ⊆ {ω | (r - y + t) ^ 2 ≤ (X ω - r - t) ^ 2} := by
    intro ω hω
    have hr : y ≤ r := hy
    change X ω ≤ y at hω
    change _ ≤ _
    have h₁ : 0 ≤ r - y + t := by linarith
    have h₂ : r - y + t ≤ r + t - X ω := by linarith
    have hsq := pow_le_pow_left₀ h₁ h₂ 2
    nlinarith
  have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := μ) hsub)
    (sq_nonneg (r - y + t))
  calc
    _ ≤ (r - y + t) ^ 2 * μ.real {ω | (r - y + t) ^ 2 ≤ (X ω - r - t) ^ 2} := hmono
    _ ≤ ∫ ω, (X ω - r - t) ^ 2 ∂μ := hmarkov
    _ = Var[X; μ] + t ^ 2 := shifted_square_integral hX t

/-- Cantelli's one-sided variance bound in a form with no division by the
variance and therefore valid also for constant random variables. -/
theorem cantelli_lower_tail {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) {y : ℝ} (hy : y < ∫ ω, X ω ∂μ) :
    μ.real {ω | X ω ≤ y} * ((∫ ω, X ω ∂μ) - y) ^ 2 ≤
      (1 - μ.real {ω | X ω ≤ y}) * Var[X; μ] := by
  let d : ℝ := (∫ ω, X ω ∂μ) - y
  let v : ℝ := Var[X; μ]
  let q : ℝ := μ.real {ω | X ω ≤ y}
  have hd : 0 < d := sub_pos.mpr hy
  have hv : 0 ≤ v := variance_nonneg _ _
  have h := cantelli_shifted_bound hX hy.le (div_nonneg hv hd.le)
  change (d + v / d) ^ 2 * q ≤ v + (v / d) ^ 2 at h
  have hs : (d ^ 2 + v) ^ 2 * q ≤ v * d ^ 2 + v ^ 2 := by
    calc
      _ = d ^ 2 * ((d + v / d) ^ 2 * q) := by field_simp
      _ ≤ d ^ 2 * (v + (v / d) ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg d)
      _ = v * d ^ 2 + v ^ 2 := by field_simp
  have hden : 0 < v + d ^ 2 := by positivity
  have hq : q * (v + d ^ 2) ≤ v := by
    apply (mul_le_mul_iff_left₀ hden).mp
    nlinarith [hs]
  change q * d ^ 2 ≤ (1 - q) * v
  nlinarith

theorem cantelli_variance_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : MemLp X 2 μ) {y ξ : ℝ} (hy : y < ∫ ω, X ω ∂μ)
    (hξ : ξ < 1) (hmass : ξ ≤ μ.real {ω | X ω ≤ y}) :
    ξ * ((∫ ω, X ω ∂μ) - y) ^ 2 / (1 - ξ) ≤ Var[X; μ] := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - ξ)).mpr
  have h := cantelli_lower_tail hX hy
  have hprod := mul_nonneg (sub_nonneg.mpr hmass)
    (add_nonneg (variance_nonneg X μ) (sq_nonneg ((∫ ω, X ω ∂μ) - y)))
  nlinarith

end SharpTailMatching.Probability
