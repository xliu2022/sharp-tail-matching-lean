module

public import SharpTailMatching.Probability.Basic

/-!
# Adding an atom at one

When one of the samples comes from the atom at one, the nonnegative sum
succeeds automatically. We prove the exact mixture formula by restricting
the product measures to the box whose coordinates are all below one.
This proof works for arbitrary Borel probability laws, not just finite support.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

/-- Scaling every factor of a finite product measure scales the product by
the corresponding power. This version includes the empty product. -/
theorem pi_const_smul (k : ℕ) (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (a : ℝ≥0∞) (ha : a ≠ ∞) :
    Measure.pi (fun _ : Fin k => a • μ) =
      a^k • Measure.pi (fun _ : Fin k => μ) := by
  let : IsFiniteMeasure (a • μ) := μ.smul_finite ha
  apply Measure.pi_eq
  intro s hs
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib]

/-- An atom at one contributes no mass to the failure event. -/
theorem failure_measure_add_dirac_one (k : ℕ) (μ : Measure ℝ≥0)
    [IsFiniteMeasure μ] (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    (Measure.pi (fun _ : Fin k => a • μ + b • Measure.dirac 1))
      {z : Fin k → ℝ≥0 | ∑ i, z i < 1} =
      a^k * (Measure.pi (fun _ : Fin k => μ))
        {z : Fin k → ℝ≥0 | ∑ i, z i < 1} := by
  let : IsFiniteMeasure (a • μ) := μ.smul_finite ha
  let : IsFiniteMeasure (b • Measure.dirac (1 : ℝ≥0)) :=
    (Measure.dirac (1 : ℝ≥0)).smul_finite hb
  let F : Set (Fin k → ℝ≥0) := {z | ∑ i, z i < 1}
  let B : Set (Fin k → ℝ≥0) := Set.univ.pi (fun _ => Iio 1)
  have hFB : F ⊆ B := by
    intro z hz
    simp only [B, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iio]
    intro i
    exact lt_of_le_of_lt (Finset.single_le_sum (fun j _ => (by positivity : 0 ≤ z j))
      (Finset.mem_univ i)) hz
  have hres : (a • μ + b • Measure.dirac (1 : ℝ≥0)).restrict (Iio 1) =
      a • μ.restrict (Iio 1) := by
    simp [MeasureTheory.restrict_dirac]
  change (Measure.pi (fun _ : Fin k => a • μ + b • Measure.dirac 1)) F =
    a^k * (Measure.pi (fun _ : Fin k => μ)) F
  calc
    (Measure.pi (fun _ : Fin k => a • μ + b • Measure.dirac 1)) F =
        ((Measure.pi (fun _ : Fin k => a • μ + b • Measure.dirac 1)).restrict B) F :=
      (Measure.restrict_eq_self _ hFB).symm
    _ = (Measure.pi (fun _ : Fin k =>
        (a • μ + b • Measure.dirac 1).restrict (Iio 1))) F := by
      rw [show B = Set.univ.pi (fun _ : Fin k => Iio (1 : ℝ≥0)) from rfl,
        Measure.restrict_pi_pi]
    _ = (Measure.pi (fun _ : Fin k => a • μ.restrict (Iio 1))) F := by rw [hres]
    _ = (a^k • Measure.pi (fun _ : Fin k => μ.restrict (Iio 1))) F := by
      rw [pi_const_smul k (μ.restrict (Iio 1)) a ha]
    _ = a^k * ((Measure.pi (fun _ : Fin k => μ)).restrict B) F := by
      rw [Measure.smul_apply, smul_eq_mul]
      rw [show B = Set.univ.pi (fun _ : Fin k => Iio (1 : ℝ≥0)) from rfl,
        Measure.restrict_pi_pi]
    _ = a^k * (Measure.pi (fun _ : Fin k => μ)) F := by
      rw [Measure.restrict_eq_self _ hFB]

/-- The unnormalized description of a mixture with an atom at one. -/
def addOneMeasure (μ : ProbabilityMeasure ℝ≥0) (t : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1-t) • (μ : Measure ℝ≥0) +
    ENNReal.ofReal t • Measure.dirac 1

theorem addOneMeasure_probability (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    IsProbabilityMeasure (addOneMeasure μ t) := by
  constructor
  simp only [addOneMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr htle) ht]
  simp

/-- A probability law obtained by replacing a sample by one with probability `t`. -/
def addOneLaw (μ : ProbabilityMeasure ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    ProbabilityMeasure ℝ≥0 :=
  ⟨addOneMeasure μ t, addOneMeasure_probability μ t ht htle⟩

theorem mean_addOneLaw (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    mean (addOneLaw μ t ht htle) =
      ENNReal.ofReal (1-t) * mean μ + ENNReal.ofReal t := by
  simp [mean, addOneLaw, addOneMeasure, lintegral_add_measure,
    lintegral_smul_measure]

/-- The failure event is the measurable complement of the success event. -/
theorem failure_toReal_eq_one_sub_tail (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    ((Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
      {z : Fin k → ℝ≥0 | ∑ i, z i < 1}).toReal =
      1 - tailProbability k μ := by
  have hA : MeasurableSet {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i} := by measurability
  have h := probReal_compl_eq_one_sub (μ := Measure.pi
    (fun _ : Fin k => (μ : Measure ℝ≥0))) hA
  simpa [Measure.real, tailProbability, Set.compl_ofPred, not_le] using h

/-- Exact tail identity for adding an atom at one. -/
theorem tail_addOneLaw (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    tailProbability k (addOneLaw μ t ht htle) =
      1 - (1-t)^k * (1-tailProbability k μ) := by
  have h := failure_measure_add_dirac_one k (μ : Measure ℝ≥0)
    (ENNReal.ofReal (1-t)) (ENNReal.ofReal t) (by simp) (by simp)
  have hreal := congrArg ENNReal.toReal h
  change ((Measure.pi (fun _ : Fin k =>
      ((addOneLaw μ t ht htle) : Measure ℝ≥0)))
        {z : Fin k → ℝ≥0 | ∑ i, z i < 1}).toReal = _ at hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr htle),
    failure_toReal_eq_one_sub_tail, failure_toReal_eq_one_sub_tail] at hreal
  linarith

/-- Domination of the coordinate measures implies domination of their finite
products. Only the smaller measure needs to be sigma-finite. -/
theorem pi_const_mono (k : ℕ) (μ ν : Measure ℝ≥0) [SigmaFinite μ]
    (hμν : μ ≤ ν) :
    Measure.pi (fun _ : Fin k => μ) ≤ Measure.pi (fun _ : Fin k => ν) := by
  have hout : (Measure.pi (fun _ : Fin k => μ)).toOuterMeasure ≤
      OuterMeasure.pi (fun _ : Fin k => ν.toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro s hs
    change (Measure.pi (fun _ : Fin k => μ)) (Set.univ.pi s) ≤ _
    rw [Measure.pi_pi]
    exact Finset.prod_le_prod (fun i _ => hμν (s i))
  apply Measure.le_iff.mpr
  intro s hs
  calc
    (Measure.pi (fun _ : Fin k => μ)) s ≤
        (OuterMeasure.pi (fun _ : Fin k => ν.toOuterMeasure)) s := hout s
    _ = (Measure.pi (fun _ : Fin k => ν)) s := by
      rw [Measure.pi, toMeasure_apply _ _ hs]

/-- A mixture which replaces a sample by zero with probability `t`. -/
def addZeroMeasure (μ : ProbabilityMeasure ℝ≥0) (t : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1-t) • (μ : Measure ℝ≥0) +
    ENNReal.ofReal t • Measure.dirac 0

theorem addZeroMeasure_probability (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    IsProbabilityMeasure (addZeroMeasure μ t) := by
  constructor
  simp only [addZeroMeasure, Measure.add_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr htle) ht]
  simp

def addZeroLaw (μ : ProbabilityMeasure ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    ProbabilityMeasure ℝ≥0 :=
  ⟨addZeroMeasure μ t, addZeroMeasure_probability μ t ht htle⟩

theorem mean_addZeroLaw (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    mean (addZeroLaw μ t ht htle) = ENNReal.ofReal (1-t) * mean μ := by
  simp [mean, addZeroLaw, addZeroMeasure, lintegral_add_measure,
    lintegral_smul_measure]

/-- The event that all samples retain their original law gives the lower bound
needed to transfer a critical-mean estimate to larger means. -/
theorem tail_addZeroLaw_lower_bound (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (t : ℝ) (ht : 0 ≤ t) (htle : t ≤ 1) :
    (1-t)^k * tailProbability k μ ≤ tailProbability k (addZeroLaw μ t ht htle) := by
  let a := ENNReal.ofReal (1-t)
  let : IsFiniteMeasure (a • (μ : Measure ℝ≥0)) := (μ : Measure ℝ≥0).smul_finite (by simp [a])
  have hdom : a • (μ : Measure ℝ≥0) ≤ (addZeroLaw μ t ht htle : Measure ℝ≥0) := by
    change a • (μ : Measure ℝ≥0) ≤ a • (μ : Measure ℝ≥0) + _
    apply Measure.le_iff'.mpr
    intro s
    simp only [Measure.add_apply]
    exact le_add_right le_rfl
  have hpi := pi_const_mono k (a • (μ : Measure ℝ≥0))
    (addZeroLaw μ t ht htle : Measure ℝ≥0) hdom
  rw [pi_const_smul k (μ : Measure ℝ≥0) a (by simp [a])] at hpi
  have hmass := Measure.le_iff'.mp hpi {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i}
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hmass
  simpa [tailProbability, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, a, ENNReal.toReal_ofReal (sub_nonneg.mpr htle)] using hr

/-- A Bernoulli-type upper bound at one mean gives that same branch at every
smaller mean. The allowed mean need not equal the actual expectation. -/
theorem unit_bound_below_of_bound_at_mean (k : ℕ) (β x : ℝ)
    (hβlt : β < 1) (hx : 0 ≤ x) (hxβ : x ≤ β)
    (hcritical : ∀ ν : ProbabilityMeasure ℝ≥0,
      mean ν ≤ ENNReal.ofReal β → tailProbability k ν ≤ 1-(1-β)^k)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ 1-(1-x)^k := by
  have hxlt : x < 1 := hxβ.trans_lt hβlt
  have hden : 0 < 1-x := sub_pos.mpr hxlt
  let t : ℝ := (β-x)/(1-x)
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hxβ) hden.le
  have htlt : t < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hid : (1-t)*x+t = β := by
    dsimp [t]
    field_simp
    ring
  have hfactor : (1-t)*(1-x) = 1-β := by nlinarith only [hid]
  have hmixedMean : mean (addOneLaw μ t ht htlt.le) ≤ ENNReal.ofReal β := by
    rw [mean_addOneLaw]
    calc
      ENNReal.ofReal (1-t) * mean μ + ENNReal.ofReal t ≤
          ENNReal.ofReal (1-t) * ENNReal.ofReal x + ENNReal.ofReal t :=
        by gcongr
      _ = ENNReal.ofReal ((1-t)*x+t) := by
        rw [ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr htlt.le) hx) ht,
          ENNReal.ofReal_mul (sub_nonneg.mpr htlt.le)]
      _ = ENNReal.ofReal β := by rw [hid]
  have hmixed := hcritical (addOneLaw μ t ht htlt.le) hmixedMean
  rw [tail_addOneLaw] at hmixed
  have hpower : (1-β)^k = (1-t)^k * (1-x)^k := by rw [← mul_pow, hfactor]
  apply le_of_mul_le_mul_left _ (pow_pos (sub_pos.mpr htlt) k)
  nlinarith only [hmixed, hpower]

/-- A small-Bernoulli upper bound at a positive mean gives that same branch
at every larger mean, by adding an atom at zero. -/
theorem small_bound_above_of_bound_at_mean (k : ℕ) (β x : ℝ)
    (hβpos : 0 < β) (hβx : β ≤ x)
    (hcritical : ∀ ν : ProbabilityMeasure ℝ≥0,
      mean ν ≤ ENNReal.ofReal β → tailProbability k ν ≤ ((k : ℝ)*β)^k)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ ((k : ℝ)*x)^k := by
  have hxpos : 0 < x := hβpos.trans_le hβx
  let t : ℝ := 1-β/x
  have hquot : β/x ≤ 1 := (div_le_one hxpos).2 hβx
  have ht : 0 ≤ t := sub_nonneg.mpr hquot
  have htlt : t < 1 := by
    have hqpos : 0 < β/x := div_pos hβpos hxpos
    dsimp [t]
    linarith
  have hid : (1-t)*x = β := by
    dsimp [t]
    field_simp
    ring
  have hmixedMean : mean (addZeroLaw μ t ht htlt.le) ≤ ENNReal.ofReal β := by
    rw [mean_addZeroLaw]
    calc
      ENNReal.ofReal (1-t) * mean μ ≤ ENNReal.ofReal (1-t) * ENNReal.ofReal x :=
        by gcongr
      _ = ENNReal.ofReal ((1-t)*x) := (ENNReal.ofReal_mul (sub_nonneg.mpr htlt.le)).symm
      _ = ENNReal.ofReal β := by rw [hid]
  have hmixed := hcritical (addZeroLaw μ t ht htlt.le) hmixedMean
  have hbound := (tail_addZeroLaw_lower_bound k μ t ht htlt.le).trans hmixed
  have hpower : ((k : ℝ)*β)^k = (1-t)^k * ((k : ℝ)*x)^k := by
    rw [← mul_pow]
    congr 1
    calc
      (k : ℝ)*β = (k : ℝ)*((1-t)*x) := by rw [hid]
      _ = (1-t)*((k : ℝ)*x) := by ring
  rw [hpower] at hbound
  exact le_of_mul_le_mul_left hbound (pow_pos (sub_pos.mpr htlt) k)

/-- Exact reduction of the full upper-bound theorem to its critical-mean case.
The critical bound is an explicit hypothesis; this theorem does not claim to
have proved that remaining probability inequality. -/
theorem sharp_tail_bound_of_critical_bound (k : ℕ) (hk : 2 ≤ k)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < (k : ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k : ℝ)*β)^k)
    (critical_bound : ∀ ν : ProbabilityMeasure ℝ≥0,
      mean ν ≤ ENNReal.ofReal β → tailProbability k ν ≤ ((k : ℝ)*β)^k)
    (x : ℝ) (hx : 0 ≤ x) (μ : ProbabilityMeasure ℝ≥0)
    (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ sharpTailValue k x := by
  have hkreal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hβone : β < 1 := hβlt.trans ((inv_lt_one₀ hkpos).2 (by linarith))
  by_cases hxrange : x ≤ (k : ℝ)⁻¹
  · rw [sharpTailValue, ite_eq_left hxrange]
    by_cases hxβ : x ≤ β
    · apply (unit_bound_below_of_bound_at_mean k β x hβone hx hxβ ?_ μ hmean).trans
        (le_max_left _ _)
      intro ν hν
      rw [hβcross]
      exact critical_bound ν hν
    · exact (small_bound_above_of_bound_at_mean k β x hβpos (le_of_not_ge hxβ)
        critical_bound μ hmean).trans (le_max_right _ _)
  · simpa [sharpTailValue, hxrange] using tailProbability_le_one k μ

end SharpTailMatching.Probability
