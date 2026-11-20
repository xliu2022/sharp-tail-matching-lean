module

public import SharpTailMatching.Probability.NodeProximity
public import SharpTailMatching.Probability.CostInterpolation

/-! # Actual thinning tails and excesses satisfy the weighted comparison -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem normalized_short_binomial_sum (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : a ≠ 0)
    (f : ℕ → ℝ) (hf : f 0 = 0) :
    (∑ j ∈ Finset.range k,((k-1).choose j : ℝ)*a^j*(1-a)^(k-1-j)*f j) =
      ∑ j ∈ Finset.range (k-1),shortBinomialWeight k a ((1-a)/a) (j+1)*f (j+1) := by
  have hsum := Finset.sum_range_succ'
    (fun j => ((k-1).choose j : ℝ)*a^j*(1-a)^(k-1-j)*f j) (k-1)
  rw [Nat.sub_add_cancel hk] at hsum
  rw [hsum]
  simp only [hf,mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := thinning_coefficient (k-1) (j+1) (by have := Finset.mem_range.mp hj; omega) a ha
  unfold shortBinomialWeight binomialWeight
  rw [ite_eq_right (Nat.add_one_ne_zero _)]
  calc
    _ = ((k-1).choose (j+1) : ℝ)*(a^(j+1)*(1-a)^(k-1-(j+1)))*f (j+1) := by ring
    _ = _ := by rw [hc]; ring

theorem thinning_short_tail (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    tailProbability (k-1) (addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)) =
      ∑ j ∈ Finset.range (k-1),shortBinomialWeight k a ((1-a)/a) (j+1)*tailProbability (j+1) μ := by
  rw [tail_addZeroLaw_binomial,show 1-(1-a) = a by ring,Nat.sub_add_cancel hk]
  exact normalized_short_binomial_sum k hk a ha.ne' _ (tailProbability_zero μ)

namespace ComparisonGeometry

theorem shortTailStarSum_eq_full_sum (k t : ℕ) (a θ : ℝ) :
    shortTailStarSum k a t θ =
      ∑ j ∈ Finset.range k,((k-1).choose j : ℝ)*a^j*(1-a)^(k-1-j)*tailStar k j t θ := by
  unfold shortTailStarSum shortTailNodeSum tailStar
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem shortTailStarSum_eq_weighted (k t : ℕ) (htk : t < k) (a : ℝ) (ha : a ≠ 0) (θ : ℝ) :
    shortTailStarSum k a t θ =
      ∑ j ∈ Finset.range (k-1),shortBinomialWeight k a ((1-a)/a) (j+1)*tailStar k (j+1) t θ := by
  rw [shortTailStarSum_eq_full_sum]
  apply normalized_short_binomial_sum k (by omega) a ha
  simp [tailStar,tailNode,show t ≤ k by omega,show t+1 ≤ k by omega]

theorem scaledExcessStarSum_eq_full_sum (k t : ℕ) (a θ : ℝ) :
    scaledExcessStarSum k a t θ =
      ∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a^j*(1-a)^(k-j)*excessStar k j t θ := by
  unfold scaledExcessStarSum scaledExcessNodeSum excessStar
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem scaledExcessStarSum_eq_weighted (k t : ℕ) (ht : 0 < t) (htk : t < k)
    (a : ℝ) (ha : a ≠ 0) (θ : ℝ) :
    scaledExcessStarSum k a t θ = a^k*(segmentExcess t θ+
      ∑ j ∈ Finset.range (k-1),binomialWeight k ((1-a)/a) (j+1)*excessStar k (j+1) t θ) := by
  rw [scaledExcessStarSum_eq_full_sum,normalized_binomial_sum k (by omega) a ha _
    (by simp [excessStar,excessNode,show t ≤ k by omega,show t+1 ≤ k by omega]),
    excessStar_last k t ht θ]
  simp only [binomialWeight,ite_eq_right (Nat.add_one_ne_zero _)]

end ComparisonGeometry

theorem weighted_cost_sum (k : ℕ) (a r L : ℝ) (f e : ℕ → ℝ) :
    (∑ j ∈ Finset.range (k-1),(L*shortBinomialWeight k a r (j+1)*f (j+1)-
        binomialCost k a r (j+1)*e (j+1))) =
      L*(∑ j ∈ Finset.range (k-1),shortBinomialWeight k a r (j+1)*f (j+1))-
      a^k/(k : ℝ)*(∑ j ∈ Finset.range (k-1),binomialWeight k r (j+1)*e (j+1)) := by
  rw [Finset.sum_sub_distrib,Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j hj
  · ring
  · unfold binomialCost
    ring

theorem critical_thinning_comparisons (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c θ a : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (ha : 0 < a) (ha1 : a ≤ 1) (haeq : a = (k : ℝ)/((k : ℝ)+c))
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ) :
    let P := addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)
    let L := (t : ℝ)*((t : ℝ)-1)/(2*(k : ℝ))
    tailProbability (k-1) P ≤ ComparisonGeometry.shortTailStarSum k a t θ ∧
      ComparisonGeometry.scaledExcessStarSum k a t θ/(k : ℝ)-L*ComparisonGeometry.shortTailStarSum k a t θ ≤
        normalizedExcess k P/(k : ℝ)-L*tailProbability (k-1) P := by
  let P := addZeroLaw μ (1-a) (sub_nonneg.mpr ha1) (by linarith)
  let L := (t : ℝ)*((t : ℝ)-1)/(2*(k : ℝ))
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hr : (1-a)/a = c/(k : ℝ) := by rw [haeq]; field_simp; ring
  have hshort := thinning_short_tail k (by omega) μ a ha ha1
  have hstar := ComparisonGeometry.shortTailStarSum_eq_weighted k t htk a ha.ne' θ
  rw [hr] at hshort hstar
  have hv : ∀ j < k, 0 ≤ shortBinomialWeight k a (c/(k : ℝ)) j :=
    fun j _ => shortBinomialWeight_nonneg k ha.le (div_nonneg hc hkpos.le) j
  have hvmono : ∀ j, j+1 < k → shortBinomialWeight k a (c/(k : ℝ)) j ≤
      shortBinomialWeight k a (c/(k : ℝ)) (j+1) := by
    intro j hj
    rw [haeq]
    exact critical_short_weights_monotone k hk c hc hcross j hj
  have hzero := iid_weighted_interpolation k t (by omega) htk θ μ hsupp hmean hexcess
    (shortBinomialWeight k a (c/(k : ℝ))) hv hvmono
  have hcost := critical_iid_cost_interpolation k t hk ht htk c θ hc hcross μ hsupp hmean hexcess
  dsimp at hcost
  rw [← haeq] at hcost
  change (∑ j ∈ Finset.range (k-1),(L*shortBinomialWeight k a (c/(k : ℝ)) (j+1)*tailProbability (j+1) μ-
      binomialCost k a (c/(k : ℝ)) (j+1)*partialExcess k (j+1) μ)) ≤ _ at hcost
  rw [weighted_cost_sum k a (c/(k : ℝ)) L (fun j => tailProbability j μ) (fun j => partialExcess k j μ),
    weighted_cost_sum k a (c/(k : ℝ)) L (fun j => ComparisonGeometry.tailStar k j t θ)
      (fun j => ComparisonGeometry.excessStar k j t θ),← hshort,← hstar] at hcost
  have hE := thinning_excess k (by omega) μ hsupp a ha ha1
  have hEs := ComparisonGeometry.scaledExcessStarSum_eq_weighted k t (by omega) htk a ha.ne' θ
  rw [hr,hexcess] at hE
  rw [hr] at hEs
  have hEb : normalizedExcess k P = a^k*(ComparisonGeometry.segmentExcess t θ+
      ∑ j ∈ Finset.range (k-1),binomialWeight k (c/(k : ℝ)) (j+1)*partialExcess k (j+1) μ) := by
    simpa only [binomialWeight,ite_eq_right (Nat.add_one_ne_zero _)] using hE
  constructor
  · change tailProbability (k-1) P ≤ _
    rw [hshort,hstar]
    exact hzero
  · change _ ≤ normalizedExcess k P/(k : ℝ)-L*tailProbability (k-1) P
    rw [hEb,hEs]
    dsimp only [P,L] at hcost ⊢
    ring_nf at hcost ⊢
    linarith only [hcost]

end SharpTailMatching.Probability
