module

public import SharpTailMatching.Probability.ProductConsequences
public import SharpTailMatching.Probability.EnvelopeAlgebra
public import SharpTailMatching.Probability.WeightedInterpolation

/-!
# Probability envelopes from global product chords

The comparison power curves hold globally. In particular, no inverse of a
piecewise function is introduced in deriving the tail/deficit inequalities.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace SharpTailMatching.Probability.ProductBound

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def positiveExcess {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) : ℝ :=
  ∫ ω, max (total X ω - 1) 0 ∂μ

def scaledExcess {ι : Type*} [Fintype ι] (k : ℕ) (X : ι → Ω → ℝ) : ℝ :=
  (k : ℝ) * positiveExcess μ X

theorem positive_negative_deviation {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (hXi : ∀ i, Integrable (X i) μ) :
    positiveDeficit μ X = positiveExcess μ X + 1 - ∑ i, ∫ ω, X i ω ∂μ := by
  have hS := integrable_total μ X hXi
  have hpos : Integrable (fun ω => max (total X ω-1) 0) μ :=
    (hS.sub (integrable_const 1)).sup (integrable_const 0)
  have hneg := positiveDeficit_integrable μ X hXi
  have hpoint (ω : Ω) : max (total X ω-1) 0 - max (1-total X ω) 0 = total X ω-1 := by
    by_cases h : 1 ≤ total X ω
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
      ring
  have h := integral_congr_ae (μ := μ) (Filter.Eventually.of_forall hpoint)
  rw [integral_sub hpos hneg,integral_sub hS (integrable_const 1),
    integral_total μ X hXi,integral_const,probReal_univ,one_smul] at h
  change positiveExcess μ X-positiveDeficit μ X = _ at h
  linarith

/-- Every power curve supplies a global lower bound on the failure
probability for bounded independent variables of a common mean. -/
theorem global_failure_envelope (j n : ℕ) (hj : 0 < j) (hn : 0 < n)
    (X : Fin j → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (m : ℝ) (hm : 0 < m) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = m)
    (hjm : (j : ℝ)*m ≤ 1) :
    EnvelopeAlgebra.failureCurve ((1-(j : ℝ)*m)/m+n) n (positiveDeficit μ X/m) ≤
      failureProbability μ X := by
  let : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
  let p := failureProbability μ X
  let r := conditionalDeficit μ X
  let u := positiveDeficit μ X/m
  let T : ℝ := (1-(j : ℝ)*m)/m+n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hT : 0 < T := by
    have hnonneg := div_nonneg (sub_nonneg.mpr hjm) hm.le
    dsimp [T]
    linarith
  have hXi (i) : Integrable (X i) μ := Integrable.of_mem_Icc 0 M (hX i).aemeasurable (hbound i)
  have hp0 : 0 ≤ p := failureProbability_nonneg μ X
  have hdef0 : 0 ≤ positiveDeficit μ X := integral_nonneg (fun _ => le_max_right _ _)
  have hu0 : 0 ≤ u := div_nonneg hdef0 hm.le
  by_cases hp : 0 < p
  · have hrelation : positiveDeficit μ X = p*r := conditionalDeficit_relation μ X hp
    by_cases hmr : m < r
    · obtain ⟨z, hz, hsumz, hprod⟩ := bounded_independent_product_bound μ X hX hi M hM hbound hp
        (fun i => by rw [hmean i]; exact hmr)
      have hsum : (∑ i, ∫ ω, X i ω ∂μ) = (j : ℝ)*m := by simp [hmean]
      rw [balance, hsum] at hsumz
      have hchord := (EnvelopeAlgebra.bounded_global_chord j n z hm hmr
        (fun i => (hz i).1) (fun i => by simpa only [hmean i] using (hz i).2)).trans hprod
      let v := r/m
      have hv : 1 < v := (one_lt_div hm).mpr hmr
      have hu : u = p*v := by dsimp [u,v]; rw [hrelation]; ring
      apply EnvelopeAlgebra.failureCurve_le_of_chord T u p v n hT hn hp hv hu
      have hid : (1-m/r)^n * (1-((∑ i,z i)-n*m)/r) = T/v*(1-1/v)^n := by
        rw [hsumz]
        change (1-m/r)^n * (1-(r-1+(j : ℝ)*m-n*m)/r) = _
        have hr0 : 0 < r := hm.trans hmr
        have hq : 1-m/r = 1-1/v := by dsimp [v]; field_simp
        rw [hq]
        dsimp [T,v]
        field_simp
        ring
      rw [hid] at hchord
      exact hchord
    · apply EnvelopeAlgebra.failureCurve_le_of_deficit_le T u p n hT hn hu0
      have hrm : r ≤ m := le_of_not_gt hmr
      apply (div_le_iff₀ hm).mpr
      rw [hrelation]
      exact mul_le_mul_of_nonneg_left hrm hp0
  · have hpe : p = 0 := le_antisymm (le_of_not_gt hp) hp0
    have hdefle : positiveDeficit μ X ≤ p := positiveDeficit_le_failure μ X hX hXi
      (fun i => (hbound i).mono (fun _ h => h.1))
    have hdef : positiveDeficit μ X = 0 := le_antisymm (by linarith) hdef0
    apply EnvelopeAlgebra.failureCurve_le_of_deficit_le T u p n hT hn hu0
    simp only [u,hdef,zero_div,hpe,le_refl]

/-- The power-curve envelope for a partial sum of variables of mean `1/k`.
The integer `t` can be any value above `k-j`; no inverse-branch hypothesis
is required. -/
theorem normalized_partial_failure_envelope (k j t : ℕ)
    (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) (ht : k-j < t)
    (X : Fin j → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = (k : ℝ)⁻¹) :
    EnvelopeAlgebra.failureCurve (t : ℝ) (t-(k-j)) ((k-j : ℕ) + scaledExcess μ k X) ≤
      failureProbability μ X := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hm : 0 < (k : ℝ)⁻¹ := inv_pos.mpr hkR
  have hmeanTotal : (∑ i, ∫ ω, X i ω ∂μ) = (j : ℝ)*(k : ℝ)⁻¹ := by simp [hmean]
  have hjm : (j : ℝ)*(k : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hkR).mpr (Nat.cast_le.mpr hjk)
  have hXi (i) : Integrable (X i) μ := Integrable.of_mem_Icc 0 M (hX i).aemeasurable (hbound i)
  have hdef := positive_negative_deviation μ X hXi
  rw [hmeanTotal] at hdef
  have hT : (1-(j : ℝ)*(k : ℝ)⁻¹)/(k : ℝ)⁻¹+(t-(k-j) : ℕ) = (t : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt ht),Nat.cast_sub hjk]
    field_simp
    ring
  have hu : positiveDeficit μ X/(k : ℝ)⁻¹ = (k-j : ℕ)+scaledExcess μ k X := by
    rw [hdef,Nat.cast_sub hjk]
    unfold scaledExcess
    field_simp
    ring
  have h := global_failure_envelope μ j (t-(k-j)) hj (by omega) X hX hi M hM hbound
    (k : ℝ)⁻¹ hm hmean hjm
  rwa [hT,hu] at h

theorem normalized_partial_success_envelope (k j t : ℕ)
    (hk : 0 < k) (hj : 0 < j) (hjk : j ≤ k) (ht : k-j < t)
    (X : Fin j → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = (k : ℝ)⁻¹) :
    1-failureProbability μ X ≤
      EnvelopeAlgebra.successCurve (t : ℝ) (t-(k-j)) ((k-j : ℕ)+scaledExcess μ k X) := by
  have h := normalized_partial_failure_envelope μ k j t hk hj hjk ht X hX hi M hM hbound hmean
  unfold EnvelopeAlgebra.successCurve
  linarith

/-- Each displayed branch of `H` is a valid failure envelope globally and is
strictly concave on every nonnegative interval. -/
theorem normalized_failure_envelope (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (X : Fin k → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = (k : ℝ)⁻¹) :
    EnvelopeAlgebra.failureCurve (t : ℝ) t (scaledExcess μ k X) ≤ failureProbability μ X := by
  simpa only [Nat.sub_self,Nat.sub_zero,Nat.cast_zero,zero_add] using
    normalized_partial_failure_envelope μ k k t hk hk le_rfl (by simpa) X hX hi M hM hbound hmean

end SharpTailMatching.Probability.ProductBound
