module

public import SharpTailMatching.Probability.CostMultipliers

/-! # The full cost comparison for actual iid partial sums -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem binomialWeight_monotone_endpoint (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrn : (n : ℝ)*r ≤ 1) (j : ℕ) (hjn : j+1 ≤ n) :
    binomialWeight n r j ≤ binomialWeight n r (j+1) := by
  by_cases hj0 : j = 0
  · subst j
    simpa [binomialWeight] using binomialWeight_nonneg n r hr 1
  · have hpow : n-j = (n-(j+1))+1 := by omega
    have hcoeff : (n.choose j : ℝ)*r ≤ (n.choose (j+1) : ℝ) := by
      have hchoose : (n.choose (j+1) : ℝ)*((j : ℝ)+1) =
          (n.choose j : ℝ)*((n : ℝ)-(j : ℝ)) := by
        have h := congrArg (fun q : ℕ => (q : ℝ)) (Nat.choose_succ_right_eq n j)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (show j ≤ n by omega)] using h
      have hjnR : (j : ℝ)+1 ≤ n := by exact_mod_cast hjn
      have hrj : ((j : ℝ)+1)*r ≤ (n : ℝ)-(j : ℝ) :=
        (mul_le_mul_of_nonneg_right hjnR hr).trans (hrn.trans (by linarith))
      have hmul := mul_le_mul_of_nonneg_left hrj (Nat.cast_nonneg (n.choose j) : (0 : ℝ) ≤ _)
      have hjpos : 0 < (j : ℝ)+1 := by positivity
      nlinarith
    simp only [binomialWeight,ite_eq_right hj0,ite_eq_right (show j+1 ≠ 0 by omega),hpow,pow_succ]
    have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr (n-(j+1)))
    nlinarith

theorem iid_interpolation_with_costs (k t : ℕ) (ht : 0 < t) (htk : t < k)
    (θ : ℝ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ)
    (κ cost : ℕ → ℝ) (hκ : ∀ j < k, 0 ≤ κ j)
    (hκmono : ∀ j, j+1 < k → κ j ≤ κ (j+1))
    (hcost : ∀ j < k, 0 ≤ cost j)
    (hΓ : ∀ j < k, 0 ≤ interpolationMultiplier (k-t) κ cost
      (fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t ((t : ℝ)+1)) j) :
    (∑ j ∈ Finset.range (k-1),(κ (j+1)*tailProbability (j+1) μ-cost (j+1)*partialExcess k (j+1) μ)) ≤
      ∑ j ∈ Finset.range (k-1),(κ (j+1)*ComparisonGeometry.tailStar k (j+1) t θ-
        cost (j+1)*ComparisonGeometry.excessStar k (j+1) t θ) := by
  let q := k-t
  let α : ℕ → ℝ := fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t ((t : ℝ)+1)
  let Γ := interpolationMultiplier q κ cost α
  have hα : ∀ j, q < j → j < k → 0 ≤ α j := by
    intro j hj hjk
    have hlevel : 1 ≤ k-j := by omega
    have hlt : k-j < t := by dsimp [q] at hj; omega
    exact (ComparisonGeometry.chordSlope_pos (k-j : ℕ) t ((t : ℝ)+1)
      (by exact_mod_cast hlevel) (by exact_mod_cast hlt) (by linarith)).le
  have hbase : ∀ j ≤ q, Γ j = κ j := interpolationMultiplier_base q κ cost α
  exact weighted_interpolation k q (by omega)
    (fun j => partialExcess k j μ) (fun j => tailProbability j μ)
    (fun j => ComparisonGeometry.excessStar k j t θ)
    (fun j => ComparisonGeometry.tailStar k j t θ) κ cost α Γ
    (partialExcess_one k μ hsupp) (ComparisonGeometry.excessStar_one k t (by omega) htk θ)
    (fun j _ _ => partialExcess_rec k j (by omega) μ hsupp hmean)
    (fun j _ hj => ComparisonGeometry.excessStar_rec k j t hj θ)
    (by rw [partialExcess_last,ComparisonGeometry.excessStar_last k t ht θ,hexcess])
    (fun j _ hj => ⟨(partialExcess_bounds k j (by omega) (by dsimp [q] at hj; omega) μ hsupp hmean).1,
      ComparisonGeometry.excessStar_prefix k j t htk.le hj θ⟩)
    (fun j hj hjk => by
      simpa only [Nat.cast_add,Nat.cast_one] using partial_star_slope_bound k j t (by omega) hjk
        (by dsimp [q] at hj; omega) htk θ μ hsupp hmean)
    hκ hκmono hcost hα hbase
    (fun j hj hjk => interpolationMultiplier_rec q κ cost α j hj (hα j hj hjk)) hΓ

theorem critical_short_weights_monotone (k : ℕ) (hk : 6 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (hcross : CriticalEstimates.criticalDifference k c = 1) (j : ℕ) (hj : j+1 < k) :
    shortBinomialWeight k ((k : ℝ)/((k : ℝ)+c)) (c/(k : ℝ)) j ≤
      shortBinomialWeight k ((k : ℝ)/((k : ℝ)+c)) (c/(k : ℝ)) (j+1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hc1 := CriticalEstimates.critical_parameter_lt_half (by omega : 3 ≤ k) hc hcross
  have hr : 0 ≤ c/(k : ℝ) := div_nonneg hc hkpos.le
  have hrn : ((k-1 : ℕ) : ℝ)*(c/(k : ℝ)) ≤ 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega),Nat.cast_one,← mul_div_assoc]
    apply (div_le_iff₀ hkpos).mpr
    have hkn : 0 ≤ (k : ℝ)-1 := by
      have h : (6 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hmul := mul_le_mul_of_nonneg_left hc1.le hkn
    linarith
  exact mul_le_mul_of_nonneg_left
    (binomialWeight_monotone_endpoint (k-1) (c/(k : ℝ)) hr hrn j (by omega))
    (pow_nonneg (by positivity) _)

theorem critical_iid_cost_interpolation (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c θ : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let L := (t : ℝ)*((t : ℝ)-1)/(2*(k : ℝ))
    (∑ j ∈ Finset.range (k-1),(L*shortBinomialWeight k a (c/(k : ℝ)) (j+1)*tailProbability (j+1) μ-
      binomialCost k a (c/(k : ℝ)) (j+1)*partialExcess k (j+1) μ)) ≤
    ∑ j ∈ Finset.range (k-1),(L*shortBinomialWeight k a (c/(k : ℝ)) (j+1)*
      ComparisonGeometry.tailStar k (j+1) t θ-
      binomialCost k a (c/(k : ℝ)) (j+1)*ComparisonGeometry.excessStar k (j+1) t θ) := by
  let a := (k : ℝ)/((k : ℝ)+c)
  let L := (t : ℝ)*((t : ℝ)-1)/(2*(k : ℝ))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hr : 0 ≤ c/(k : ℝ) := div_nonneg hc (Nat.cast_nonneg k)
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := by
    have htm : 0 ≤ (t : ℝ)-1 := by linarith
    dsimp [L]
    positivity
  apply iid_interpolation_with_costs k t (by omega) htk θ μ hsupp hmean hexcess
    (fun j => L*shortBinomialWeight k a (c/(k : ℝ)) j) (binomialCost k a (c/(k : ℝ)))
  · intro j _
    exact mul_nonneg hL (shortBinomialWeight_nonneg k ha hr j)
  · intro j hj
    exact mul_le_mul_of_nonneg_left (critical_short_weights_monotone k hk c hc hcross j hj) hL
  · intro j _
    exact mul_nonneg (div_nonneg (pow_nonneg ha _) (Nat.cast_nonneg k)) (binomialWeight_nonneg k _ hr j)
  · exact critical_cost_multipliers_nonnegative k t hk ht htk c hc hcross

end SharpTailMatching.Probability
