module

public import SharpTailMatching.Probability.InitialExclusion
public import SharpTailMatching.Probability.EqualityReduction
public import SharpTailMatching.Probability.Normalization
public import SharpTailMatching.Probability.Exclusion
public import SharpTailMatching.Probability.ActualProximity
public import SharpTailMatching.CriticalProbabilityEstimates

/-! # From normalized endpoints to the critical extremizers

This file connects the comparison argument with arbitrary maximizing Borel
laws. The small values of the sample size are closed by the initial node
exclusion alone. The large values use the subsequent support analysis.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem normalized_representation_eq_addZero {k : ℕ} (hk : 1 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k : ℝ)⁻¹)
    {μ Q : ProbabilityMeasure ℝ≥0}
    (hrep : (μ : Measure ℝ≥0) =
      ENNReal.ofReal (1-(k:ℝ)*x) • Measure.dirac 0 +
        ENNReal.ofReal ((k:ℝ)*x) • (Q : Measure ℝ≥0)) :
    ∃ (ht : 0 ≤ 1-(k:ℝ)*x) (ht1 : 1-(k:ℝ)*x ≤ 1),
      μ = addZeroLaw Q (1-(k:ℝ)*x) ht ht1 := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have ha : 0 < (k:ℝ)*x := mul_pos hkpos hx
  have ha1 : (k:ℝ)*x < 1 := by
    simpa only [mul_inv_cancel₀ hkpos.ne'] using mul_lt_mul_of_pos_left hxlt hkpos
  refine ⟨by linarith, by linarith, ?_⟩
  apply Subtype.ext
  change (μ : Measure ℝ≥0) =
    ENNReal.ofReal (1-(1-(k:ℝ)*x)) • (Q : Measure ℝ≥0) +
      ENNReal.ofReal (1-(k:ℝ)*x) • Measure.dirac 0
  simpa only [sub_sub_cancel, add_comm] using hrep

theorem normalized_endpoints_classification {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k : ℝ)⁻¹)
    {μ Q : ProbabilityMeasure ℝ≥0}
    (hrep : (μ : Measure ℝ≥0) =
      ENNReal.ofReal (1-(k:ℝ)*x) • Measure.dirac 0 +
        ENNReal.ofReal ((k:ℝ)*x) • (Q : Measure ℝ≥0))
    (hsupp : (Q : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean Q = ENNReal.ofReal (k:ℝ)⁻¹)
    (hend : normalizedExcess k Q = 0 ∨
      normalizedExcess k Q = ComparisonGeometry.maxExcessNode k) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
      (μ : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  rcases hend with hzero | hmax
  · right
    rw [normalized_excess_zero_rigidity (by omega) Q hsupp hmean hzero] at hrep
    exact hrep
  · left
    rw [ComparisonGeometry.maxExcessNode_eq_maxNormalizedExcess] at hmax
    have hQ := normalized_excess_max_rigidity hk Q hsupp hmean hmax
    obtain ⟨ht, ht1, hμQ⟩ := normalized_representation_eq_addZero (by omega) hx hxlt hrep
    have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hi0 : 0 ≤ (k:ℝ)⁻¹ := inv_nonneg.mpr hkpos.le
    have hi1 : (k:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hkpos).mpr (by exact_mod_cast (show 1 ≤ k by omega))
    have hQeq : Q = unitBernoulliLaw (k:ℝ)⁻¹ hi0 hi1 := Subtype.ext hQ
    rw [hμQ, hQeq, addZero_unitBernoulli]
    congr 1
    rw [sub_sub_cancel]
    field_simp

theorem critical_maximizer_classification_small {k : ℕ} (hk : 2 ≤ k) (hk5 : k ≤ 5)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k:ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k:ℝ)*x)^k)
    {μ : ProbabilityMeasure ℝ≥0} (hμ : Maximizes k x μ) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
      (μ : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  obtain ⟨Q, hrep, hsupp, hmean⟩ := maximizer_normalized_representation (by omega) hx hxlt hμ
  apply normalized_endpoints_classification hk hx hxlt hrep hsupp hmean
  obtain ⟨ht, ht1, hμQ⟩ := normalized_representation_eq_addZero (by omega) hx hxlt hrep
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have ha : 0 < (k:ℝ)*x := mul_pos hkpos hx
  have ha1 : (k:ℝ)*x < 1 := by
    simpa only [mul_inv_cancel₀ hkpos.ne'] using mul_lt_mul_of_pos_left hxlt hkpos
  have hc := CriticalEstimates.critical_parameter_from_beta hk hx hxlt hcross
  have hratio : (1-(k:ℝ)*x)/((k:ℝ)*x) = (x⁻¹-k)/(k:ℝ) := by
    field_simp
  have hlarge := hμ.2 (smallBernoulliLaw k (by omega) x hx.le hxlt.le)
    (by rw [mean_smallBernoulliLaw])
  rw [tailProbability_smallBernoulliLaw, hμQ] at hlarge
  exact initial_exclusion_small k hk hk5 (x⁻¹-k) ((k:ℝ)*x) hc.1.le hc.2.2
    ha ha1.le hratio Q hsupp hmean hlarge

theorem critical_bound_of_maximizer_classification {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k:ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k:ℝ)*x)^k)
    (hclass : ∀ μ : ProbabilityMeasure ℝ≥0, Maximizes k x μ →
      (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)
    (ν : ProbabilityMeasure ℝ≥0) (hν : mean ν ≤ ENNReal.ofReal x) :
    tailProbability k ν ≤ ((k:ℝ)*x)^k := by
  obtain ⟨μ, hμ, _⟩ := exists_maximizer k x hx.le
  have hle := hμ.2 ν hν
  rcases hclass μ hμ with hunit | hsmall
  · have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
    have hx1 : x ≤ 1 := hxlt.le.trans ((inv_le_one₀ hkpos).mpr (by exact_mod_cast (show 1 ≤ k by omega)))
    have heq : μ = unitBernoulliLaw x hx.le hx1 := Subtype.ext hunit
    simpa only [heq, tailProbability_unitBernoulliLaw, hcross] using hle
  · have heq : μ = smallBernoulliLaw k (by omega) x hx.le hxlt.le := Subtype.ext hsmall
    simpa only [heq, tailProbability_smallBernoulliLaw] using hle

theorem critical_equality_of_maximizer_classification {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k:ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k:ℝ)*x)^k)
    (hclass : ∀ μ : ProbabilityMeasure ℝ≥0, Maximizes k x μ →
      (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)
    (ν : ProbabilityMeasure ℝ≥0) (hν : mean ν ≤ ENNReal.ofReal x)
    (htail : tailProbability k ν = ((k:ℝ)*x)^k) :
    (ν : Measure ℝ≥0) = unitBernoulliMeasure x ∨
      (ν : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  apply hclass ν
  refine ⟨hν, ?_⟩
  intro ρ hρ
  rw [htail]
  exact critical_bound_of_maximizer_classification hk hx hxlt hcross hclass ρ hρ

theorem sharp_tail_bound_small (k : ℕ) (hk : 1 ≤ k) (hk5 : k ≤ 5)
    (x : ℝ) (hx : 0 ≤ x) (μ : ProbabilityMeasure ℝ≥0)
    (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ sharpTailValue k x := by
  by_cases hk1 : k = 1
  · subst k
    exact one_sample_bound x hx μ hmean
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨β, hβ, _⟩ := critical_mean_exists_unique k hk2
    apply sharp_tail_bound_of_critical_bound k hk2 β hβ.1 hβ.2.1 hβ.2.2 _ x hx μ hmean
    exact critical_bound_of_maximizer_classification hk2 hβ.1 hβ.2.1 hβ.2.2
      (fun ν hν => critical_maximizer_classification_small hk2 hk5 hβ.1 hβ.2.1 hβ.2.2 hν)

theorem sharp_tail_equality_small (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < (k:ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ (k:ℝ)⁻¹)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ = sharpTailValue k x ↔
      (x < β ∧ (μ : Measure ℝ≥0) = unitBernoulliMeasure x) ∨
      (x = β ∧ ((μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)) ∨
      (β < x ∧ (μ : Measure ℝ≥0) = smallBernoulliMeasure k x) := by
  have hclass := fun ν hν =>
    critical_maximizer_classification_small hk hk5 hβpos hβlt hβcross (μ := ν) hν
  exact sharp_tail_equality_of_critical k hk β hβpos hβlt hβcross
    (critical_bound_of_maximizer_classification hk hβpos hβlt hβcross hclass)
    (critical_equality_of_maximizer_classification hk hβpos hβlt hβcross hclass)
    x hx hxle μ hmean

/-- The quantitative Section 5 hypotheses follow from the genuine positive
crossing. Only the preceding comparison estimate is needed at this boundary. -/
theorem critical_maximizer_proximity_rigid {n : ℕ} (hn : 6 ≤ n+1)
    {x : ℝ} (hx : 0 < x) (hxlt : x < ((n+1:ℕ):ℝ)⁻¹)
    (hcross : 1-(1-x)^(n+1) = (((n+1:ℕ):ℝ)*x)^(n+1))
    {μ : ProbabilityMeasure ℝ≥0} (hμ : Maximizes (n+1) x μ)
    (hprox : supportCutoff n x μ-conditionalDeficit n μ <
      (failureScale n x μ-3*x)/20) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  have hc := CriticalEstimates.critical_parameter_from_beta (by omega : 2 ≤ n+1) hx hxlt hcross
  have hcLower := CriticalEstimates.critical_parameter_lower (by omega : 2 ≤ n+1) hc.1.le hc.2.2
  have hpositive : 0 < 2/(25*((n+1:ℕ):ℝ)) := by positivity
  have hbasic := CriticalEstimates.critical_elementary_bounds hn hc.1.le hc.2.2
  have hcancel : ((n+1:ℕ):ℝ)+(x⁻¹-((n+1:ℕ):ℝ)) = x⁻¹ := by ring
  simp only [hcancel, one_div, inv_inv] at hbasic
  apply maximizer_proximity_rigid hn hx hxlt hμ hbasic.1
    (by linarith : 11/24 < x⁻¹-((n+1:ℕ):ℝ)) hc.2.1 _ hbasic.2.2.2.2.1 hprox
  field_simp

theorem critical_maximizer_classification_large {k : ℕ} (hk : 6 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k:ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k:ℝ)*x)^k)
    {μ : ProbabilityMeasure ℝ≥0} (hμ : Maximizes k x μ) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
      (μ : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
  obtain ⟨Q, hrep, hsupp, hmean⟩ := maximizer_normalized_representation (by omega) hx hxlt hμ
  by_cases hzero : normalizedExcess (n+1) Q = 0
  · exact normalized_endpoints_classification (by omega) hx hxlt hrep hsupp hmean (Or.inl hzero)
  · left
    apply critical_maximizer_proximity_rigid hk hx hxlt hcross hμ
    simpa only [Nat.add_sub_cancel] using
      critical_normalized_maximizer_proximity hk hx hxlt hcross hμ hrep hsupp hmean hzero

/-- Complete critical-mean classification, with every comparison and exclusion
estimate discharged for an arbitrary Borel probability law. -/
theorem critical_maximizer_classification {k : ℕ} (hk : 2 ≤ k)
    {x : ℝ} (hx : 0 < x) (hxlt : x < (k:ℝ)⁻¹)
    (hcross : 1-(1-x)^k = ((k:ℝ)*x)^k)
    {μ : ProbabilityMeasure ℝ≥0} (hμ : Maximizes k x μ) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
      (μ : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  by_cases hk5 : k ≤ 5
  · exact critical_maximizer_classification_small hk hk5 hx hxlt hcross hμ
  · exact critical_maximizer_classification_large (by omega) hx hxlt hcross hμ

end SharpTailMatching.Probability
