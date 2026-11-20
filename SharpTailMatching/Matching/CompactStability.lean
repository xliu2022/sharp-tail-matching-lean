module

public import SharpTailMatching.Matching.AtomCosts

/-! # Uniform quantitative stability on the compact interval

An exact rigidity theorem supplies the only mathematical input. Compactness
then makes its modulus uniform over the full mean interval, including both
endpoints and the crossing of the two extremal curves.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Matching

open Probability

def realUnitMean (μ : ProbabilityMeasure UnitInterval) : ℝ :=
  ∫t : UnitInterval, ((t : ℝ≥0) : ℝ) ∂(μ : Measure UnitInterval)

def unitAtomCost (a : ℝ) (μ : ProbabilityMeasure UnitInterval) : ℝ :=
  ∫t : UnitInterval, twoAtomCost a ((t : ℝ≥0) : ℝ) ∂(μ : Measure UnitInterval)

@[fun_prop] theorem continuous_realUnitMean : Continuous realUnitMean := by
  let f : C(UnitInterval,ℝ) := ⟨fun t => ((t : ℝ≥0) : ℝ),by fun_prop⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

@[fun_prop] theorem continuous_unitAtomCost (a : ℝ) : Continuous (unitAtomCost a) := by
  let f : C(UnitInterval,ℝ) := ⟨fun t => twoAtomCost a ((t : ℝ≥0) : ℝ),
    (continuous_twoAtomCost a).comp (by fun_prop)⟩
  exact ProbabilityMeasure.continuous_integral_continuousMap f

theorem realUnitMean_nonneg (μ : ProbabilityMeasure UnitInterval) : 0 ≤ realUnitMean μ :=
  integral_nonneg (fun t => (t : ℝ≥0).coe_nonneg)

theorem unitAtomCost_nonneg (a : ℝ) (μ : ProbabilityMeasure UnitInterval) : 0 ≤ unitAtomCost a μ :=
  integral_nonneg (fun t => twoAtomCost_nonneg a _)

theorem upperSemicontinuous_realUnitTail (k : ℕ) :
    UpperSemicontinuous (fun μ : ProbabilityMeasure UnitInterval => (unitTail k μ).toReal) := by
  have h := (ENNReal.continuous_truncateToReal (t := 1) (by simp)).comp_upperSemicontinuous
    (upperSemicontinuous_unitTail k) (ENNReal.monotone_truncateToReal (t := 1) (by simp))
  have heq : ENNReal.truncateToReal 1 ∘ unitTail k =
      (fun μ : ProbabilityMeasure UnitInterval => (unitTail k μ).toReal) := by
    funext μ
    exact ENNReal.truncateToReal_eq_toReal (by simp) (show unitTail k μ ≤ 1 from prob_le_one)
  rwa [heq] at h

/-- Compactness turns exact zero-gap rigidity into a uniform modulus. -/
theorem compact_quantitative_rigidity {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {gap cost : X → ℝ} (hgap : LowerSemicontinuous gap) (hcost : Continuous cost)
    (hrigid : ∀ z, gap z ≤ 0 → cost z ≤ 0) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z, gap z ≤ δ → cost z < η := by
  let B : Set X := {z | η ≤ cost z}
  have hclosed : IsClosed B := isClosed_le continuous_const hcost
  by_cases hB : B.Nonempty
  · obtain ⟨z₀,hz₀,hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hB hclosed.isCompact
      (hgap.lowerSemicontinuousOn B)
    have hpos : 0 < gap z₀ := by
      by_contra h
      have hz := hrigid z₀ (le_of_not_gt h)
      change η ≤ cost z₀ at hz₀
      linarith
    refine ⟨gap z₀/2,by positivity,?_⟩
    intro z hz
    by_contra hc
    have hm := hmin (show z ∈ B from le_of_not_gt hc)
    change gap z₀ ≤ gap z at hm
    linarith
  · refine ⟨1,by norm_num,?_⟩
    intro z _
    by_contra hc
    exact hB ⟨z,le_of_not_gt hc⟩

/-- Uniform probability stability obtained from the exact two-atom rigidity
statement. The tolerance is uniform in both the allowed mean and the law. -/
theorem compact_law_stability (k : ℕ)
    (hrigid : ∀ (x : ℝ), 0 ≤ x → x ≤ (k : ℝ)⁻¹ →
      ∀ μ : ProbabilityMeasure UnitInterval, realUnitMean μ ≤ x →
        max (1-(1-x)^k) (((k : ℝ)*x)^k) ≤ (unitTail k μ).toReal →
        realUnitMean μ = x ∧ (unitAtomCost 1 μ = 0 ∨ unitAtomCost (k : ℝ)⁻¹ μ = 0))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : ℝ), 0 ≤ x → x ≤ (k : ℝ)⁻¹ →
      ∀ μ : ProbabilityMeasure UnitInterval, realUnitMean μ ≤ x+δ →
        max (1-(1-x)^k) (((k : ℝ)*x)^k)-δ ≤ (unitTail k μ).toReal →
        |realUnitMean μ-x| < η ∧
          (unitAtomCost 1 μ < η ∨ unitAtomCost (k : ℝ)⁻¹ μ < η) := by
  let I := ↥(Set.Icc (0 : ℝ) (k : ℝ)⁻¹)
  let X := I × ProbabilityMeasure UnitInterval
  letI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let mean : X → ℝ := fun z => realUnitMean z.2
  let param : X → ℝ := fun z => z.1.1
  let target : X → ℝ := fun z => max (1-(1-param z)^k) (((k : ℝ)*param z)^k)
  let tail : X → ℝ := fun z => (unitTail k z.2).toReal
  let gap : X → ℝ := fun z => max (mean z-param z) (target z-tail z)
  let cost : X → ℝ := fun z => max |mean z-param z|
    (min (unitAtomCost 1 z.2) (unitAtomCost (k : ℝ)⁻¹ z.2))
  have hmean : Continuous mean := continuous_realUnitMean.comp continuous_snd
  have hparam : Continuous param := continuous_subtype_val.comp continuous_fst
  have htarget : Continuous target := by dsimp only [target]; fun_prop
  have htail : UpperSemicontinuous tail := (upperSemicontinuous_realUnitTail k).comp continuous_snd
  have hneg : LowerSemicontinuous (fun z : X => -tail z) := by
    exact continuous_neg.comp_upperSemicontinuous_antitone htail (fun _ _ h => neg_le_neg h)
  have hgap : LowerSemicontinuous gap := by
    have h := (hmean.sub hparam).lowerSemicontinuous.sup (htarget.lowerSemicontinuous.add hneg)
    simpa only [gap,sub_eq_add_neg,Pi.add_apply,Pi.neg_apply] using h
  have hcost : Continuous cost := by
    exact ((hmean.sub hparam).abs).max
      ((continuous_unitAtomCost 1).comp continuous_snd |>.min
        ((continuous_unitAtomCost (k : ℝ)⁻¹).comp continuous_snd))
  have hexact (z : X) (hz : gap z ≤ 0) : cost z ≤ 0 := by
    have hm : mean z ≤ param z := by
      have h := (le_max_left (mean z-param z) (target z-tail z)).trans hz
      linarith
    have ht : target z ≤ tail z := by
      have h := (le_max_right (mean z-param z) (target z-tail z)).trans hz
      linarith
    obtain ⟨hm,hatom⟩ := hrigid (param z) z.1.property.1 z.1.property.2 z.2 hm ht
    change max |realUnitMean z.2-(z.1 : ℝ)|
      (min (unitAtomCost 1 z.2) (unitAtomCost (k : ℝ)⁻¹ z.2)) ≤ 0
    change realUnitMean z.2 = (z.1 : ℝ) at hm
    rw [hm,sub_self,abs_zero,max_le_iff]
    refine ⟨le_rfl,?_⟩
    rcases hatom with h | h
    · exact (min_le_left _ _).trans_eq h
    · exact (min_le_right _ _).trans_eq h
  obtain ⟨δ,hδ,hδcost⟩ := compact_quantitative_rigidity hgap hcost hexact hη
  refine ⟨δ,hδ,?_⟩
  intro x hx0 hx1 μ hm ht
  let z : X := (⟨x,hx0,hx1⟩,μ)
  have hzgap : gap z ≤ δ := by
    apply max_le <;> change _- _ ≤ δ <;> dsimp only [mean,param,target,tail,z] <;> linarith
  have hc := hδcost z hzgap
  change max |realUnitMean μ-x| (min (unitAtomCost 1 μ) (unitAtomCost (k : ℝ)⁻¹ μ)) < η at hc
  exact ⟨(max_lt_iff.mp hc).1,min_lt_iff.mp (max_lt_iff.mp hc).2⟩

end SharpTailMatching.Matching
