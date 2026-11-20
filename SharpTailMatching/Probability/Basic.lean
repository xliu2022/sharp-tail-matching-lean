module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Tactic

/-!
# Probability laws, exact endpoint cases, and standard distributions

The definitions in this proof module are intentionally identical to the
independent Challenge definitions. This module never imports Challenge.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching

/-- The nonnegative extended expectation of a law on the nonnegative reals. -/
def mean (μ : ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ t : ℝ≥0, (t : ℝ≥0∞) ∂(μ : Measure ℝ≥0)

/-- Success probability under the `k`-fold product of the same probability law. -/
def tailProbability (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  ((Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
    {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i}).toReal

/-- The unit Bernoulli measure. It has total mass one when `0 ≤ x ≤ 1`. -/
def unitBernoulliMeasure (x : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1 - x) • Measure.dirac 0 +
    ENNReal.ofReal x • Measure.dirac 1

/-- The Bernoulli measure with its nonzero atom at `1/k`. -/
def smallBernoulliMeasure (k : ℕ) (x : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1 - (k : ℝ) * x) • Measure.dirac 0 +
    ENNReal.ofReal ((k : ℝ) * x) • Measure.dirac ((k : ℝ≥0)⁻¹)

/-- The sharp candidate value, including the saturated regime. -/
def sharpTailValue (k : ℕ) (x : ℝ) : ℝ :=
  if x ≤ (k : ℝ)⁻¹ then
    max (1 - (1 - x) ^ k) (((k : ℝ) * x) ^ k)
  else 1

namespace Probability

theorem mean_eq_zero_iff (μ : ProbabilityMeasure ℝ≥0) :
    mean μ = 0 ↔ (μ : Measure ℝ≥0) = Measure.dirac 0 := by
  constructor
  · intro h
    have hae : (fun t : ℝ≥0 => (t : ℝ≥0∞)) =ᵐ[(μ : Measure ℝ≥0)] 0 :=
      (lintegral_eq_zero_iff measurable_coe_nnreal_ennreal).mp h
    have hae' : (fun t : ℝ≥0 => t) =ᵐ[(μ : Measure ℝ≥0)] (fun _ => 0) := by
      filter_upwards [hae] with t ht
      change (t : ℝ≥0∞) = 0 at ht
      exact_mod_cast ht
    have hm : (μ : Measure ℝ≥0).map (fun t : ℝ≥0 => t) =
        (μ : Measure ℝ≥0).map (fun _ => (0 : ℝ≥0)) := Measure.map_congr hae'
    simpa using hm
  · intro h
    simp [mean, h]

theorem tailProbability_nonneg (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    0 ≤ tailProbability k μ := ENNReal.toReal_nonneg

theorem tailProbability_le_one (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ ≤ 1 := by
  unfold tailProbability
  exact measureReal_le_one

/-- A product-box argument proves the saturated-tail classification without
any integrability assumption or approximation by finitely supported laws. -/
theorem tail_eq_one_iff (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ = 1 ↔
      (μ : Measure ℝ≥0) (Set.Iio ((k : ℝ≥0)⁻¹)) = 0 := by
  have hk0 : k ≠ 0 := by omega
  have hknn : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk0
  let : NeZero k := ⟨hk0⟩
  let ν := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))
  let A : Set (Fin k → ℝ≥0) := {z | 1 ≤ ∑ i, z i}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hsum : (∑ _ : Fin k, (k : ℝ≥0)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hknn]
  change (ν A).toReal = 1 ↔ _
  rw [ENNReal.toReal_eq_one_iff]
  constructor
  · intro hone
    have hzero : ν Aᶜ = 0 := (prob_compl_eq_zero_iff hA).mpr hone
    have hsub : Set.pi Set.univ (fun _ : Fin k => Set.Iio ((k : ℝ≥0)⁻¹)) ⊆ Aᶜ := by
      intro z hz
      have hlt : (∑ i, z i) < ∑ _ : Fin k, (k : ℝ≥0)⁻¹ :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hz i (Set.mem_univ i)
      simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, A, hsum] using hlt
    have hpow : ((μ : Measure ℝ≥0) (Set.Iio ((k : ℝ≥0)⁻¹))) ^ k = 0 := by
      have hle := measure_mono (μ := ν) hsub
      rw [hzero] at hle
      have hbox0 := le_antisymm hle bot_le
      dsimp [ν] at hbox0
      rw [Measure.pi_pi] at hbox0
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hbox0
    exact (pow_eq_zero_iff hk0).mp hpow
  · intro hzero
    have hlarge : (μ : Measure ℝ≥0) (Set.Ici ((k : ℝ≥0)⁻¹)) = 1 := by
      simpa using (prob_compl_eq_one_iff measurableSet_Iio).mpr hzero
    have hbox : ν (Set.pi Set.univ (fun _ : Fin k => Set.Ici ((k : ℝ≥0)⁻¹))) = 1 := by
      change (Measure.pi _) (Set.pi Set.univ _) = 1
      rw [Measure.pi_pi]
      simp only [hlarge, Finset.prod_const_one]
    have hsub : Set.pi Set.univ (fun _ : Fin k => Set.Ici ((k : ℝ≥0)⁻¹)) ⊆ A := by
      intro z hz
      have hle : (∑ _ : Fin k, (k : ℝ≥0)⁻¹) ≤ ∑ i, z i :=
        Finset.sum_le_sum fun i _ => hz i (Set.mem_univ i)
      simpa only [A, Set.mem_ofPred_eq, hsum] using hle
    exact le_antisymm prob_le_one (hbox ▸ measure_mono hsub)

theorem tailProbability_one (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability 1 μ = ((μ : Measure ℝ≥0) (Set.Ici 1)).toReal := by
  have hset : {z : Fin 1 → ℝ≥0 | 1 ≤ ∑ i, z i} =
      Set.pi Set.univ (fun _ : Fin 1 => Set.Ici (1 : ℝ≥0)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_Ici, Fin.sum_univ_one, Fin.forall_fin_one]
  unfold tailProbability
  rw [hset, Measure.pi_pi]
  simp

theorem sharpTailValue_one_of_le (x : ℝ) (hx : x ≤ 1) :
    sharpTailValue 1 x = x := by
  simp only [sharpTailValue, Nat.cast_one, inv_one, hx, ite_eq_left, pow_one, one_mul]
  rw [show 1 - (1 - x) = x by ring, max_self]

/-- The one-sample sharp upper bound is Markov's inequality, including the
saturated regime when the allowed mean is at least one. -/
theorem one_sample_bound (x : ℝ) (hx : 0 ≤ x) (μ : ProbabilityMeasure ℝ≥0)
    (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability 1 μ ≤ sharpTailValue 1 x := by
  by_cases hxle : x ≤ 1
  · rw [sharpTailValue_one_of_le x hxle, tailProbability_one]
    have hm : (μ : Measure ℝ≥0) (Set.Ici 1) ≤ mean μ := by
      have h := mul_meas_ge_le_lintegral (μ := (μ : Measure ℝ≥0))
        measurable_coe_nnreal_ennreal 1
      simpa only [one_mul, ENNReal.one_le_coe_iff, mean, Set.Ici_def] using h
    exact ENNReal.toReal_le_of_le_ofReal hx (hm.trans hmean)
  · simpa [sharpTailValue, hxle] using tailProbability_le_one 1 μ

theorem unitBernoulliMeasure_probability (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1) :
    IsProbabilityMeasure (unitBernoulliMeasure x) := by
  constructor
  simp only [unitBernoulliMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hxle) hx]
  norm_num

/-- The unit Bernoulli law as a bundled probability measure. -/
def unitBernoulliLaw (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1) : ProbabilityMeasure ℝ≥0 :=
  ⟨unitBernoulliMeasure x, unitBernoulliMeasure_probability x hx hxle⟩

@[simp] theorem mean_unitBernoulliLaw (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1) :
    mean (unitBernoulliLaw x hx hxle) = ENNReal.ofReal x := by
  simp [mean, unitBernoulliLaw, unitBernoulliMeasure, lintegral_add_measure,
    lintegral_smul_measure]

@[simp] theorem tailProbability_one_unitBernoulliLaw (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1) :
    tailProbability 1 (unitBernoulliLaw x hx hxle) = x := by
  rw [tailProbability_one]
  simp [unitBernoulliLaw, unitBernoulliMeasure, Measure.add_apply, Measure.smul_apply, hx]

end Probability

end SharpTailMatching
