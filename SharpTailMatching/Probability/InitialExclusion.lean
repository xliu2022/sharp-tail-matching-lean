module

public import SharpTailMatching.Probability.NodeWeights

/-! # The complete initial exclusion of comparison segments -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability.ComparisonGeometry

theorem maxExcessNode_eq_maxNormalizedExcess (k : ℕ) :
    maxExcessNode k = maxNormalizedExcess k := by
  simp [maxExcessNode,nodeExcessNat,nodePowerNat,maxNormalizedExcess,one_div]

theorem exists_excess_segment (r : ℕ) (hr : 2 ≤ r) (w : ℝ) (hw : 0 ≤ w)
    (hwr : w ≤ maxExcessNode r) :
    ∃ t θ, 1 ≤ t ∧ t < r ∧ 0 ≤ θ ∧ θ ≤ 1 ∧ w = segmentExcess t θ := by
  obtain ⟨t,ht,htr,htw,hwt⟩ := exists_adjacent_bracket maxExcessNode 1 r (by omega) w
    (by simpa only [maxExcessNode_one] using hw) hwr
  have hWt : maxExcessNode t < maxExcessNode (t+1) :=
    maxExcessNode_strictMono ht (by change 1 ≤ t+1; omega) (by omega)
  let θ := (w-maxExcessNode t)/(maxExcessNode (t+1)-maxExcessNode t)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr htw) (sub_pos.mpr hWt).le
  have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hWt)).mpr (by linarith)
  refine ⟨t,θ,ht,htr,hθ0,hθ1,?_⟩
  unfold segmentExcess
  dsimp [θ]
  field_simp [ne_of_gt (sub_pos.mpr hWt)]
  ring

theorem node_comparison_forces_endpoints (r : ℕ) (hr : 2 ≤ r) (A : ℕ → ℝ)
    (w : ℝ) (hw : 0 ≤ w) (hwr : w ≤ maxExcessNode r)
    (hA : ∀ s, 1 ≤ s → s ≤ r → A s ≤ nodeFailureValue s)
    (hAstrict : ∀ s, 2 ≤ s → s < r → A s < nodeFailureValue s)
    (hcompare : ∀ t θ, 1 ≤ t → t < r → 0 ≤ θ → θ ≤ 1 → w = segmentExcess t θ →
      EnvelopeAlgebra.failureCurve (t : ℝ) t w ≤ (1-θ)*A t+θ*A (t+1)) :
    w = 0 ∨ w = maxExcessNode r := by
  obtain ⟨t,θ,ht,htr,hθ0,hθ1,hwseg⟩ := exists_excess_segment r hr w hw hwr
  have hcmp := hcompare t θ ht htr hθ0 hθ1 hwseg
  by_cases hθzero : θ = 0
  · subst θ
    have hweq : w = maxExcessNode t := by simpa only [segmentExcess,sub_zero,one_mul,zero_mul,add_zero] using hwseg
    rw [hweq,failureCurve_maxExcess_left t (by omega)] at hcmp
    simp only [sub_zero,one_mul,zero_mul,add_zero] at hcmp
    by_cases ht1 : t = 1
    · left
      simpa only [ht1,maxExcessNode_one] using hweq
    · have hgap := hAstrict t (by omega) htr
      change A t < (1-1/(t : ℝ))^t at hgap
      linarith
  · by_cases hθone : θ = 1
    · subst θ
      have hweq : w = maxExcessNode (t+1) := by simpa only [segmentExcess,sub_self,zero_mul,one_mul,zero_add] using hwseg
      rw [hweq,failureCurve_maxExcess_right t (by omega)] at hcmp
      simp only [sub_self,zero_mul,one_mul,zero_add] at hcmp
      by_cases hlast : t+1 = r
      · right
        simpa only [hlast] using hweq
      · have hgap := hAstrict (t+1) (by omega) (by omega)
        change A (t+1) < (1-1/((t+1 : ℕ) : ℝ))^(t+1) at hgap
        linarith
    · have hθpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hθzero)
      have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθone
      have hW : maxExcessNode t < maxExcessNode (t+1) :=
        maxExcessNode_strictMono ht (by change 1 ≤ t+1; omega) (by omega)
      have hc := (EnvelopeAlgebra.failureCurve_strictConcave (t : ℝ) t
        (by exact_mod_cast (show 0 < t by omega)) (by omega)).2
        (maxExcessNode_nonneg t ht) (maxExcessNode_nonneg (t+1) (by omega)) hW.ne
        (sub_pos.mpr hθlt) hθpos (by ring : 1-θ+θ = 1)
      simp only [smul_eq_mul,failureCurve_maxExcess_left t (by omega),
        failureCurve_maxExcess_right t (by omega)] at hc
      change (1-θ)*nodeFailureValue t+θ*nodeFailureValue (t+1) <
        EnvelopeAlgebra.failureCurve (t : ℝ) t (segmentExcess t θ) at hc
      rw [← hwseg] at hc
      have hlin := add_le_add (mul_le_mul_of_nonneg_left (hA t ht htr.le) (sub_nonneg.mpr hθ1))
        (mul_le_mul_of_nonneg_left (hA (t+1) (by omega) (by omega)) hθ0)
      linarith

theorem node_comparison_forces_zero (r : ℕ) (hr : 2 ≤ r) (A : ℕ → ℝ)
    (w : ℝ) (hw : 0 ≤ w) (hwr : w ≤ maxExcessNode r)
    (hA : ∀ s, 1 ≤ s → s ≤ r → A s ≤ nodeFailureValue s)
    (hAstrict : ∀ s, 2 ≤ s → s ≤ r → A s < nodeFailureValue s)
    (hcompare : ∀ t θ, 1 ≤ t → t < r → 0 ≤ θ → θ ≤ 1 → w = segmentExcess t θ →
      EnvelopeAlgebra.failureCurve (t : ℝ) t w ≤ (1-θ)*A t+θ*A (t+1)) :
    w = 0 := by
  rcases node_comparison_forces_endpoints r hr A w hw hwr hA
    (fun s hs hsr => hAstrict s hs hsr.le) hcompare with h | h
  · exact h
  · have hcmp := hcompare (r-1) 1 (by omega) (by omega) (by norm_num) (by norm_num)
      (by simpa only [segmentExcess,sub_self,zero_mul,one_mul,zero_add,Nat.sub_add_cancel (by omega : 1 ≤ r)] using h)
    have hnode := failureCurve_maxExcess_right (r-1) (by omega : 0 < r-1)
    simp only [Nat.sub_add_cancel (show 1 ≤ r by omega)] at hnode
    rw [h,hnode] at hcmp
    simp only [Nat.sub_add_cancel (show 1 ≤ r by omega),sub_self,zero_mul,one_mul,zero_add] at hcmp
    have hgap := hAstrict r hr le_rfl
    change A r < (1-1/(r : ℝ))^r at hgap
    linarith

end SharpTailMatching.Probability.ComparisonGeometry

namespace SharpTailMatching.Probability

open ComparisonGeometry

theorem critical_first_comparison (k t : ℕ) (hk : 2 ≤ k) (ht : 0 < t) (htk : t < k)
    (c a θ : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haratio : (1-a)/a = c/(k : ℝ))
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hlarge : a^k ≤ tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)))
    (hexcess : normalizedExcess k μ = segmentExcess t θ) :
    EnvelopeAlgebra.failureCurve (t : ℝ) t (normalizedExcess k μ) ≤
      (1-θ)*nodeComparisonSum k (c/(k : ℝ)) t+θ*nodeComparisonSum k (c/(k : ℝ)) (t+1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcHalf := CriticalEstimates.critical_parameter_le_half hk hc hcross
  have hrat : ((k : ℝ)-1)*((1-a)/a) ≤ 2 := by
    rw [haratio]
    have hle : ((k : ℝ)-1)*(c/(k : ℝ)) ≤ c := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hkpos).mpr
      nlinarith
    linarith
  have hcomp := first_comparison k t hk ht htk θ a ha ha1 hrat μ hsupp hmean hexcess
  rw [haratio,starComparisonSum] at hcomp
  have haPow : 0 < a^k := pow_pos ha _
  have hmul := hlarge.trans hcomp
  have hone : 1 ≤ 1-EnvelopeAlgebra.failureCurve (t : ℝ) t (normalizedExcess k μ)+
      (1-θ)*nodeComparisonSum k (c/(k : ℝ)) t+θ*nodeComparisonSum k (c/(k : ℝ)) (t+1) := by
    apply (mul_le_mul_iff_right₀ haPow).mp
    nlinarith only [hmul]
  linarith

theorem initial_exclusion_small (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5)
    (c a : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haratio : (1-a)/a = c/(k : ℝ))
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hlarge : a^k ≤ tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith))) :
    normalizedExcess k μ = 0 ∨ normalizedExcess k μ = maxExcessNode k := by
  have hbounds := normalized_excess_bounds (by omega : 1 ≤ k) μ hsupp hmean
  rw [← maxExcessNode_eq_maxNormalizedExcess] at hbounds
  apply node_comparison_forces_endpoints k hk (nodeComparisonSum k (c/(k : ℝ)))
    (normalizedExcess k μ) hbounds.1 hbounds.2
  · intro s hs hsk
    by_cases hs1 : s = 1
    · subst s
      rw [nodeComparisonSum_one,nodeFailureValue_one]
    · by_cases hskEq : s = k
      · subst s
        exact (nodeComparisonSum_at_crossing k (by omega) c hcross).le
      · exact (initial_node_strict hk hc hcross (by omega) (by omega) (by omega)).le
  · intro s hs hsk
    exact initial_node_strict hk hc hcross hs (by omega) hsk
  · intro t θ ht htk _ _ hseg
    exact critical_first_comparison k t hk (by omega) htk c a θ hc hcross ha ha1 haratio
      μ hsupp hmean hlarge hseg

theorem initial_exclusion_large (k : ℕ) (hk : 6 ≤ k)
    (c a : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haratio : (1-a)/a = c/(k : ℝ))
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hlarge : a^k ≤ tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith))) :
    normalizedExcess k μ = 0 ∨
      maxExcessNode 4 < normalizedExcess k μ ∧ normalizedExcess k μ ≤ maxExcessNode k := by
  have hbounds := normalized_excess_bounds (by omega : 1 ≤ k) μ hsupp hmean
  rw [← maxExcessNode_eq_maxNormalizedExcess] at hbounds
  by_cases hw4 : normalizedExcess k μ ≤ maxExcessNode 4
  · left
    apply node_comparison_forces_zero 4 (by omega) (nodeComparisonSum k (c/(k : ℝ)))
      (normalizedExcess k μ) hbounds.1 hw4
    · intro s hs hs4
      by_cases hs1 : s = 1
      · subst s
        rw [nodeComparisonSum_one,nodeFailureValue_one]
      · exact (initial_node_strict (by omega : 2 ≤ k) hc hcross (by omega) hs4 (by omega)).le
    · intro s hs hs4
      exact initial_node_strict (by omega : 2 ≤ k) hc hcross hs hs4 (by omega)
    · intro t θ ht ht4 _ _ hseg
      exact critical_first_comparison k t (by omega) (by omega) (by omega) c a θ
        hc hcross ha ha1 haratio μ hsupp hmean hlarge hseg
  · exact Or.inr ⟨lt_of_not_ge hw4,hbounds.2⟩

end SharpTailMatching.Probability
