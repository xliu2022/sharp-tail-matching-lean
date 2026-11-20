module

public import SharpTailMatching.Probability.LowerVariance

/-! # Positive variance of a nontrivial lower component -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem variance_pos_of_zero_atom (L : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hzero : 0 < (L : Measure ℝ≥0) {0})
    (hmean : 0 < ∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) :
    0 < variance (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0) := by
  by_contra hn
  have hz : variance (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0) = 0 :=
    le_antisymm (le_of_not_gt hn) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero hL hz
  have hnull : (L : Measure ℝ≥0) {0} = 0 := by
    apply measure_mono_null (t := {z : ℝ≥0 | ¬(z : ℝ) = ∫y : ℝ≥0,(y : ℝ) ∂(L : Measure ℝ≥0)})
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      simpa using hmean.ne
    · exact ae_iff.mp hae
  exact hzero.ne' hnull

theorem maximizer_zero_atom_pos {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : 0 < (μ : Measure ℝ≥0) {0} := by
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hkx : ((n+1 : ℕ) : ℝ)*x < 1 := by
    have h := mul_lt_mul_of_pos_left hxlt hk
    rwa [mul_inv_cancel₀ hk.ne'] at h
  have hdom := zero_atom_dominates μ (mul_nonneg hk.le hx.le)
    (maximizer_positive_mass_le (by omega) hx.le hxlt hμ)
  apply lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hkx))
  simpa using hdom {0}

theorem maximizer_lower_zero_atom_pos {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hU : ∀ᵐ z ∂(U : Measure ℝ≥0), 0 < z) : 0 < (L : Measure ℝ≥0) {0} := by
  have hμzero := maximizer_zero_atom_pos hx hxlt hμ
  have hUzero : (U : Measure ℝ≥0) {0} = 0 := by
    apply measure_mono_null (t := {z : ℝ≥0 | ¬0 < z})
    · intro z hz
      have hz0 : z = 0 := hz
      subst z
      simp
    · exact ae_iff.mp hU
  apply pos_iff_ne_zero.mpr
  intro hLzero
  rw [hmix,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,hUzero,hLzero,
    smul_zero,smul_zero,add_zero] at hμzero
  exact (lt_irrefl _ hμzero)

theorem maximizer_lower_variance_pos {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : ∀ᵐ z ∂(U : Measure ℝ≥0), 0 < z)
    (hmean : 0 < ∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) :
    0 < variance (fun z : ℝ≥0 => (z : ℝ)) (L : Measure ℝ≥0) :=
  variance_pos_of_zero_atom L hL (maximizer_lower_zero_atom_pos hx hxlt hμ hmix hU) hmean

end SharpTailMatching.Probability
