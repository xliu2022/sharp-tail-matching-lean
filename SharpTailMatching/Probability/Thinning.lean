module

public import SharpTailMatching.Probability.BinaryProducts
public import SharpTailMatching.Probability.IidInterpolation

/-! # Exact binomial thinning identities -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

instance iidSumLaw_isProbability (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (iidSumLaw k μ) := by
  unfold iidSumLaw
  infer_instance

theorem tailProbability_eq_sumLaw (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ = (iidSumLaw k (μ : Measure ℝ≥0)).real (Set.Ici 1) := by
  rw [Measure.real,iidSumLaw,Measure.map_apply (by fun_prop) measurableSet_Ici]
  rfl

theorem tail_addZeroLaw_binomial (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    tailProbability k (addZeroLaw μ t ht htle) =
      ∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*(1-t)^j*t^(k-j)*tailProbability j μ := by
  rw [tailProbability_eq_sumLaw]
  change (iidSumLaw k (ENNReal.ofReal (1-t) • (μ : Measure ℝ≥0)+
    ENNReal.ofReal t • Measure.dirac 0)).real (Set.Ici 1) = _
  rw [iidSumLaw_binary k (μ : Measure ℝ≥0) _ _ ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    Measure.real,Measure.finsetSum_apply,ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast,
      ENNReal.toReal_pow,ENNReal.toReal_ofReal (sub_nonneg.mpr htle),ENNReal.toReal_ofReal ht,
      tailProbability_eq_sumLaw,Measure.real]
  · intro j _
    simp only [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      (measure_ne_top _ _)

theorem integral_iidSumLaw (j : ℕ) (μ : Measure ℝ≥0) (f : ℝ≥0 → ℝ)
    (hf : Measurable f) :
    (∫ s,f s ∂iidSumLaw j μ) = ∫ w : Fin j → ℝ≥0,f (∑ i,w i)
      ∂Measure.pi (fun _ : Fin j => μ) := by
  exact integral_map (by fun_prop) hf.aestronglyMeasurable

theorem integral_iidSumLaw_binary (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (f : ℝ≥0 → ℝ)
    (hf : ∀ j ∈ Finset.range (k+1),Integrable f (iidSumLaw j μ)) :
    (∫ s,f s ∂iidSumLaw k (a • μ+b • Measure.dirac 0)) =
      ∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a.toReal^j*b.toReal^(k-j)*
        (∫ s,f s ∂iidSumLaw j μ) := by
  rw [iidSumLaw_binary k μ a b ha hb,integral_finsetSum_measure (fun j hj => (hf j hj).smul_measure
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top ha)) (ENNReal.pow_ne_top hb)))]
  simp only [integral_smul_measure,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_natCast,smul_eq_mul]

theorem partialExcess_addZeroLaw_binomial (k n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    partialExcess k n (addZeroLaw μ t ht htle) =
      ∑ j ∈ Finset.range (n+1),(n.choose j : ℝ)*(1-t)^j*t^(n-j)*partialExcess k j μ := by
  let f : ℝ≥0 → ℝ := fun s => max ((s : ℝ)-1) 0
  have hfm : Measurable f := by fun_prop
  have hfi (j : ℕ) : Integrable f (iidSumLaw j (μ : Measure ℝ≥0)) := by
    apply (integrable_map_measure hfm.aestronglyMeasurable (by fun_prop)).mpr
    have h := (((unit_supported_iidSum_memLp j μ hsupp 1).integrable (by norm_num)).sub
      (integrable_const (1 : ℝ))).pos_part
    simpa only [Function.comp_def,Pi.sub_apply,f,iidSum,NNReal.coe_sum] using h
  have hint := integral_iidSumLaw_binary n (μ : Measure ℝ≥0)
    (ENNReal.ofReal (1-t)) (ENNReal.ofReal t) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top f
    (fun j _ => hfi j)
  simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr htle),ENNReal.toReal_ofReal ht] at hint
  have hmap (j : ℕ) (ν : ProbabilityMeasure ℝ≥0) :
      (∫ s,f s ∂iidSumLaw j (ν : Measure ℝ≥0)) =
      ∫ w : Fin j → ℝ≥0,max (iidSum j w-1) 0 ∂Measure.pi (fun _ : Fin j => (ν : Measure ℝ≥0)) := by
    rw [integral_iidSumLaw j (ν : Measure ℝ≥0) f hfm]
    simp only [f,iidSum,NNReal.coe_sum]
  change (∫ s,f s ∂iidSumLaw n (addZeroLaw μ t ht htle : Measure ℝ≥0)) = _ at hint
  rw [hmap] at hint
  simp_rw [hmap] at hint
  unfold partialExcess
  rw [hint,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tailProbability_zero (μ : ProbabilityMeasure ℝ≥0) : tailProbability 0 μ = 0 := by
  simp [tailProbability]

theorem partialExcess_zero (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) : partialExcess k 0 μ = 0 := by
  simp [partialExcess,iidSum]

theorem sum_range_without_endpoints (k : ℕ) (hk : 1 ≤ k) (f : ℕ → ℝ) (hf0 : f 0 = 0) :
    (∑ j ∈ Finset.range (k+1),f j) = f k+∑ j ∈ Finset.range (k-1),f (j+1) := by
  rw [Finset.sum_range_succ]
  have hsplit : (∑ j ∈ Finset.range k,f j) = ∑ j ∈ Finset.range (k-1),f (j+1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [Finset.sum_range_succ',hf0,add_zero]
  rw [hsplit,add_comm]

theorem thinning_coefficient (k j : ℕ) (hj : j ≤ k) (a : ℝ) (ha : a ≠ 0) :
    a^j*(1-a)^(k-j) = a^k*((1-a)/a)^(k-j) := by
  have hp : a^k = a^j*a^(k-j) := by rw [← pow_add,Nat.add_sub_of_le hj]
  rw [hp,div_pow]
  field_simp

theorem thinning_tail (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) =
      a^k*(tailProbability k μ+
        ∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*((1-a)/a)^(k-(j+1))*tailProbability (j+1) μ) := by
  rw [tail_addZeroLaw_binomial]
  have haid : 1-(1-a) = a := by ring
  rw [haid,sum_range_without_endpoints k hk _ (by simp [tailProbability_zero])]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j+1 ≤ k := by have := Finset.mem_range.mp hj; omega
  have hc := thinning_coefficient k (j+1) hjk a ha.ne'
  calc
    _ = (k.choose (j+1) : ℝ)*(a^(j+1)*(1-a)^(k-(j+1)))*tailProbability (j+1) μ := by ring
    _ = _ := by rw [hc]; ring

theorem thinning_excess (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    normalizedExcess k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) =
      a^k*(normalizedExcess k μ+
        ∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*((1-a)/a)^(k-(j+1))*partialExcess k (j+1) μ) := by
  rw [← partialExcess_last,partialExcess_addZeroLaw_binomial k k μ hsupp]
  have haid : 1-(1-a) = a := by ring
  rw [haid,sum_range_without_endpoints k hk _ (by simp [partialExcess_zero])]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one,partialExcess_last]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j+1 ≤ k := by have := Finset.mem_range.mp hj; omega
  have hc := thinning_coefficient k (j+1) hjk a ha.ne'
  calc
    _ = (k.choose (j+1) : ℝ)*(a^(j+1)*(1-a)^(k-(j+1)))*partialExcess k (j+1) μ := by ring
    _ = _ := by rw [hc]; ring

theorem normalized_failure_branch (k t : ℕ) (hk : 0 < k) (ht : 0 < t)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    EnvelopeAlgebra.failureCurve (t : ℝ) t (normalizedExcess k μ) ≤ 1-tailProbability k μ := by
  have h := partial_success_envelope k k t hk hk le_rfl (by simpa) μ hsupp hmean
  simp only [Nat.sub_self,Nat.sub_zero,Nat.cast_zero,zero_add,partialExcess_last,
    EnvelopeAlgebra.successCurve] at h
  linarith

theorem first_comparison (k t : ℕ) (hk : 2 ≤ k) (ht : 0 < t) (htk : t < k)
    (θ a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (haratio : ((k : ℝ)-1)*((1-a)/a) ≤ 2)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ) :
    tailProbability k (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) ≤
      a^k*(1-EnvelopeAlgebra.failureCurve (t : ℝ) t (normalizedExcess k μ)+
        ∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*((1-a)/a)^(k-(j+1))*
          ComparisonGeometry.tailStar k (j+1) t θ) := by
  rw [thinning_tail k (by omega) μ a ha ha1]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha.le _)
  have hsum := iid_binomial_interpolation k t hk ht htk θ ((1-a)/a)
    (div_nonneg (sub_nonneg.mpr ha1) ha.le) haratio μ hsupp hmean hexcess
  have hfail := normalized_failure_branch k t (by omega) ht μ hsupp hmean
  linarith

end SharpTailMatching.Probability
