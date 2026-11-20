module

public import SharpTailMatching.Matching.CompactStability
public import SharpTailMatching.Probability.Sections
public import SharpTailMatching.Probability.Endpoints

/-! # Exact atom-cost rigidity from the probability law classification -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Matching

open Probability

theorem realUnitMean_eq (μ : ProbabilityMeasure UnitInterval) :
    realUnitMean μ = (mean (liftUnitLaw μ)).toReal := by
  rw [mean_liftUnitLaw]
  have h := integral_toReal (μ := (μ : Measure UnitInterval))
    (f := fun t : UnitInterval => ((t : ℝ≥0) : ℝ≥0∞)) (by fun_prop)
    (ae_of_all _ fun t => ENNReal.coe_lt_top)
  simpa only [realUnitMean,unitMean,ENNReal.coe_toReal] using h

theorem unitMean_le_one (μ : ProbabilityMeasure UnitInterval) : unitMean μ ≤ 1 := by
  calc
    _ ≤ ∫⁻_t : UnitInterval,(1 : ℝ≥0∞) ∂(μ : Measure UnitInterval) :=
      lintegral_mono (fun t => by simpa only [ENNReal.coe_one] using ENNReal.coe_le_coe.mpr t.property.2)
    _ = 1 := by simp

theorem lift_mean_le_of_real {x : ℝ} (μ : ProbabilityMeasure UnitInterval)
    (hm : realUnitMean μ ≤ x) : mean (liftUnitLaw μ) ≤ ENNReal.ofReal x := by
  have hfin : mean (liftUnitLaw μ) ≠ ∞ := by
    rw [mean_liftUnitLaw]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (unitMean_le_one μ)
  rw [← ENNReal.ofReal_toReal hfin,← realUnitMean_eq]
  exact ENNReal.ofReal_le_ofReal hm

theorem unitAtomCost_eq_integral_lift (a : ℝ) (μ : ProbabilityMeasure UnitInterval) :
    unitAtomCost a μ = ∫t : ℝ≥0,twoAtomCost a (t : ℝ) ∂(liftUnitLaw μ : Measure ℝ≥0) := by
  rw [liftUnitLaw,ProbabilityMeasure.toMeasure_map]
  have h := integral_map (μ := (μ : Measure UnitInterval)) measurable_subtype_coe.aemeasurable
    (f := fun t : ℝ≥0 => twoAtomCost a (t : ℝ))
    (show Measurable (fun t : ℝ≥0 => twoAtomCost a (t : ℝ)) from
      ((continuous_twoAtomCost a).comp NNReal.continuous_coe).measurable).aestronglyMeasurable
  exact h.symm

theorem unitAtomCost_zero_of_unitBernoulli {x : ℝ} {μ : ProbabilityMeasure UnitInterval}
    (hμ : (liftUnitLaw μ : Measure ℝ≥0) = unitBernoulliMeasure x) : unitAtomCost 1 μ = 0 := by
  rw [unitAtomCost_eq_integral_lift,hμ]
  have hzero : ∀ᵐ t : ℝ≥0 ∂unitBernoulliMeasure x, twoAtomCost 1 (t : ℝ) = 0 := by
    rw [unitBernoulliMeasure,ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _,Measure.ae_smul_measure (by simp) _⟩
  rw [integral_congr_ae hzero,integral_zero]

theorem unitAtomCost_zero_of_smallBernoulli {k : ℕ} {x : ℝ} {μ : ProbabilityMeasure UnitInterval}
    (hμ : (liftUnitLaw μ : Measure ℝ≥0) = smallBernoulliMeasure k x) :
    unitAtomCost (k : ℝ)⁻¹ μ = 0 := by
  rw [unitAtomCost_eq_integral_lift,hμ]
  have hzero : ∀ᵐ t : ℝ≥0 ∂smallBernoulliMeasure k x, twoAtomCost (k : ℝ)⁻¹ (t : ℝ) = 0 := by
    rw [smallBernoulliMeasure,ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _,Measure.ae_smul_measure (by simp) _⟩
  rw [integral_congr_ae hzero,integral_zero]

theorem unit_rigidity_of_classification (k : ℕ) (hk : 1 ≤ k)
    (hclass : ∀ (x : ℝ), 0 < x → x ≤ (k : ℝ)⁻¹ →
      ∀ ρ : ProbabilityMeasure ℝ≥0, mean ρ ≤ ENNReal.ofReal x →
        max (1-(1-x)^k) (((k : ℝ)*x)^k) ≤ tailProbability k ρ →
        (ρ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
          (ρ : Measure ℝ≥0) = smallBernoulliMeasure k x)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ (k : ℝ)⁻¹)
    (μ : ProbabilityMeasure UnitInterval) (hm : realUnitMean μ ≤ x)
    (ht : max (1-(1-x)^k) (((k : ℝ)*x)^k) ≤ (unitTail k μ).toReal) :
    realUnitMean μ = x ∧ (unitAtomCost 1 μ = 0 ∨ unitAtomCost (k : ℝ)⁻¹ μ = 0) := by
  have hmean := lift_mean_le_of_real μ hm
  by_cases hx : x = 0
  · subst x
    have hm0 : mean (liftUnitLaw μ) = 0 := by
      rw [ENNReal.ofReal_zero] at hmean
      exact le_antisymm hmean bot_le
    have hdirac := (mean_eq_zero_iff (liftUnitLaw μ)).mp hm0
    refine ⟨le_antisymm hm (realUnitMean_nonneg μ),Or.inl ?_⟩
    rw [unitAtomCost_eq_integral_lift,hdirac]
    simp
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have htail : max (1-(1-x)^k) (((k : ℝ)*x)^k) ≤ tailProbability k (liftUnitLaw μ) := by
      rwa [tailProbability_liftUnitLaw]
    rcases hclass x hxpos hx1 (liftUnitLaw μ) hmean htail with hu | hs
    · have hxle : x ≤ 1 := hx1.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hk))
      have hlaw : liftUnitLaw μ = unitBernoulliLaw x hx0 hxle := Subtype.ext hu
      refine ⟨?_,Or.inl (unitAtomCost_zero_of_unitBernoulli hu)⟩
      rw [realUnitMean_eq,hlaw,mean_unitBernoulliLaw,ENNReal.toReal_ofReal hx0]
    · have hlaw : liftUnitLaw μ = smallBernoulliLaw k hk x hx0 hx1 := Subtype.ext hs
      refine ⟨?_,Or.inr (unitAtomCost_zero_of_smallBernoulli hs)⟩
      rw [realUnitMean_eq,hlaw,mean_smallBernoulliLaw,ENNReal.toReal_ofReal hx0]

end SharpTailMatching.Matching
