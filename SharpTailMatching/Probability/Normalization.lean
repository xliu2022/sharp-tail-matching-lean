module

public import SharpTailMatching.Probability.Basic
public import SharpTailMatching.Probability.Reduction
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Sub
public import Mathlib.Topology.Semicontinuity.Basic

/-! # General-law truncation and maximizing distributions -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

/-- A feasible law whose success probability is at least that of every
feasible law. This definition has no existence or extremal-classification
assumption built into it. -/
def Maximizes (k : ℕ) (x : ℝ) (μ : ProbabilityMeasure ℝ≥0) : Prop :=
  mean μ ≤ ENNReal.ofReal x ∧
    ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal x →
      tailProbability k ν ≤ tailProbability k μ

theorem mean_map {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (f : Ω → ℝ≥0) (hf : Measurable f) :
    mean (μ.map f) = ∫⁻ t, (f t : ℝ≥0∞) ∂(μ : Measure Ω) := by
  unfold mean
  rw [ProbabilityMeasure.toMeasure_map, lintegral_map measurable_coe_nnreal_ennreal hf]

theorem tailProbability_map {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (μ : ProbabilityMeasure Ω) (f : Ω → ℝ≥0) (hf : Measurable f) :
    tailProbability k (μ.map f) =
      ((Measure.pi (fun _ : Fin k => (μ : Measure Ω)))
        {z : Fin k → Ω | 1 ≤ ∑ i, f (z i)}).toReal := by
  unfold tailProbability
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [← Measure.pi_map_pi (fun _ : Fin k => hf.aemeasurable)]
  rw [Measure.map_apply (by fun_prop) (by measurability)]
  rfl

/-- Capping a nonnegative sample at one. -/
def capLaw (μ : ProbabilityMeasure ℝ≥0) : ProbabilityMeasure ℝ≥0 :=
  μ.map (fun t => min t 1)

theorem mean_capLaw_le (μ : ProbabilityMeasure ℝ≥0) : mean (capLaw μ) ≤ mean μ := by
  rw [capLaw, mean_map μ (fun t : ℝ≥0 => min t 1) (by fun_prop)]
  apply lintegral_mono
  intro t
  exact ENNReal.coe_le_coe.mpr (min_le_left t 1)

theorem capLaw_no_mass_above_one (μ : ProbabilityMeasure ℝ≥0) :
    (capLaw μ : Measure ℝ≥0) (Set.Ioi 1) = 0 := by
  rw [capLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (show Measurable (fun t : ℝ≥0 => min t 1) by fun_prop) measurableSet_Ioi]
  simp [Set.preimage, lt_min_iff]

theorem capped_sum_ge_one_iff (k : ℕ) (z : Fin k → ℝ≥0) :
    (1 ≤ ∑ i, min (z i) 1) ↔ 1 ≤ ∑ i, z i := by
  constructor
  · intro h
    exact h.trans (Finset.sum_le_sum fun i _ => min_le_left (z i) 1)
  · intro h
    by_cases hlarge : ∃ i, 1 ≤ z i
    · obtain ⟨i, hi⟩ := hlarge
      have hle := Finset.single_le_sum (s := Finset.univ) (f := fun j => min (z j) 1)
        (fun _ _ => zero_le) (Finset.mem_univ i)
      simpa [min_eq_right hi] using hle
    · have hsmall : ∀ i, min (z i) 1 = z i := by
        intro i
        exact min_eq_left (le_of_not_ge (not_exists.mp hlarge i))
      simpa only [hsmall] using h

theorem tailProbability_capLaw (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k (capLaw μ) = tailProbability k μ := by
  rw [capLaw, tailProbability_map k μ (fun t : ℝ≥0 => min t 1) (by fun_prop)]
  unfold tailProbability
  congr 2
  ext z
  exact capped_sum_ge_one_iff k z

theorem capLaw_maximizes {k : ℕ} {x : ℝ} {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) : Maximizes k x (capLaw μ) := by
  refine ⟨(mean_capLaw_le μ).trans hμ.1, ?_⟩
  intro ν hν
  rw [tailProbability_capLaw]
  exact hμ.2 ν hν

/-- The compact sample space used only to obtain a maximizing law. -/
abbrev UnitInterval := ↥(Set.Icc (0 : ℝ≥0) 1)

instance : CompactSpace UnitInterval :=
  isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1))

/-- Regard a probability law on the unit interval as a law on `ℝ≥0`. -/
def liftUnitLaw (μ : ProbabilityMeasure UnitInterval) : ProbabilityMeasure ℝ≥0 :=
  μ.map Subtype.val

/-- Map an arbitrary nonnegative law into the compact unit interval. -/
def unitCapLaw (μ : ProbabilityMeasure ℝ≥0) : ProbabilityMeasure UnitInterval :=
  μ.map (fun t => ⟨min t 1, zero_le, min_le_right t 1⟩)

theorem lift_unitCapLaw (μ : ProbabilityMeasure ℝ≥0) :
    liftUnitLaw (unitCapLaw μ) = capLaw μ := by
  apply Subtype.ext
  change Measure.map (Subtype.val : UnitInterval → ℝ≥0)
    (Measure.map (fun t : ℝ≥0 => (⟨min t 1, by exact ⟨zero_le, min_le_right t 1⟩⟩ : UnitInterval))
      (μ : Measure ℝ≥0)) = (μ : Measure ℝ≥0).map (fun t => min t 1)
  rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
  rfl

theorem liftUnitLaw_no_mass_above_one (μ : ProbabilityMeasure UnitInterval) :
    (liftUnitLaw μ : Measure ℝ≥0) (Set.Ioi 1) = 0 := by
  rw [liftUnitLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply measurable_subtype_coe measurableSet_Ioi]
  have h : (Subtype.val : UnitInterval → ℝ≥0) ⁻¹' Set.Ioi 1 = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
    exact t.property.2
  rw [h, measure_empty]

/-- The extended mean on the compact interval. -/
def unitMean (μ : ProbabilityMeasure UnitInterval) : ℝ≥0∞ :=
  ∫⁻ t : UnitInterval, ((t : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure UnitInterval)

/-- The unconverted product-event probability on the compact interval. -/
def unitTail (k : ℕ) (μ : ProbabilityMeasure UnitInterval) : ℝ≥0∞ :=
  (Measure.pi (fun _ : Fin k => (μ : Measure UnitInterval)))
    {z : Fin k → UnitInterval | 1 ≤ ∑ i, (z i : ℝ≥0)}

theorem mean_liftUnitLaw (μ : ProbabilityMeasure UnitInterval) :
    mean (liftUnitLaw μ) = unitMean μ :=
  mean_map μ Subtype.val measurable_subtype_coe

theorem tailProbability_liftUnitLaw (k : ℕ) (μ : ProbabilityMeasure UnitInterval) :
    tailProbability k (liftUnitLaw μ) = (unitTail k μ).toReal :=
  tailProbability_map k μ Subtype.val measurable_subtype_coe

theorem continuous_unitMean : Continuous unitMean := by
  let f : C(UnitInterval, ℝ≥0) := ⟨Subtype.val, continuous_subtype_val⟩
  exact ProbabilityMeasure.continuous_lintegral_continuousMap f

theorem upperSemicontinuous_unitTail (k : ℕ) : UpperSemicontinuous (unitTail k) := by
  rw [upperSemicontinuous_iff_limsup_le]
  intro μ
  have hcont : Continuous (fun ρ : ProbabilityMeasure UnitInterval =>
      ProbabilityMeasure.pi (fun _ : Fin k => ρ)) := by fun_prop
  have hclosed : IsClosed {z : Fin k → UnitInterval | 1 ≤ ∑ i, (z i : ℝ≥0)} := by
    apply isClosed_le <;> fun_prop
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hcont.continuousAt hclosed

/-- A maximizing law exists for every nonnegative allowed mean, and one can
be chosen supported on the unit interval. The proof uses compactness of
probability measures on a compact space and the closed-set Portmanteau bound. -/
theorem exists_maximizer (k : ℕ) (x : ℝ) (_hx : 0 ≤ x) :
    ∃ μ : ProbabilityMeasure ℝ≥0,
      Maximizes k x μ ∧ (μ : Measure ℝ≥0) (Set.Ioi 1) = 0 := by
  let S : Set (ProbabilityMeasure UnitInterval) := {μ | unitMean μ ≤ ENNReal.ofReal x}
  have hSclosed : IsClosed S := isClosed_le continuous_unitMean continuous_const
  have hScompact : IsCompact S := hSclosed.isCompact
  have hSne : S.Nonempty := by
    let z : UnitInterval := ⟨0, by simp⟩
    refine ⟨(Measure.dirac z).toProbabilityMeasure, ?_⟩
    simp [S, unitMean, z]
  obtain ⟨ρ, hρ, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn hSne hScompact
    ((upperSemicontinuous_unitTail k).upperSemicontinuousOn S)
  refine ⟨liftUnitLaw ρ, ⟨?_, ?_⟩, liftUnitLaw_no_mass_above_one ρ⟩
  · rwa [mean_liftUnitLaw]
  · intro ν hν
    have hcap : unitCapLaw ν ∈ S := by
      change unitMean (unitCapLaw ν) ≤ ENNReal.ofReal x
      rw [← mean_liftUnitLaw, lift_unitCapLaw]
      exact (mean_capLaw_le ν).trans hν
    have hle : unitTail k (unitCapLaw ν) ≤ unitTail k ρ := hmax hcap
    have hreal := ENNReal.toReal_mono (show unitTail k ρ ≠ ∞ from measure_ne_top _ _) hle
    simpa only [← tailProbability_liftUnitLaw, lift_unitCapLaw, tailProbability_capLaw] using hreal

/-- The mean of a finite independent sum, in the extended nonnegative reals. -/
theorem iid_sum_lintegral (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫⁻ z : Fin k → ℝ≥0, ((∑ i, z i : ℝ≥0) : ℝ≥0∞)
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
        (k : ℝ≥0∞) * mean μ := by
  simp only [ENNReal.ofNNReal_finsetSum]
  rw [lintegral_finsetSum Finset.univ (f := fun (i : Fin k) (z : Fin k → ℝ≥0) => (z i : ℝ≥0∞)) (fun i _ =>
    measurable_coe_nnreal_ennreal.comp (measurable_pi_apply i))]
  have hi (i : Fin k) :
      (∫⁻ z : Fin k → ℝ≥0, (z i : ℝ≥0∞)
        ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = mean μ :=
    (measurePreserving_eval (fun _ : Fin k => (μ : Measure ℝ≥0)) i).lintegral_comp
      measurable_coe_nnreal_ennreal
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The first-moment bound, valid without bounded-support assumptions. -/
theorem tailProbability_le_mul_mean (k : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (μ : ProbabilityMeasure ℝ≥0) (hμ : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ (k : ℝ) * x := by
  have hmarkov := mul_meas_ge_le_lintegral
    (μ := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
    (show Measurable (fun z : Fin k → ℝ≥0 => ((∑ i, z i : ℝ≥0) : ℝ≥0∞)) by
      fun_prop) 1
  simp only [one_mul, ENNReal.one_le_coe_iff, iid_sum_lintegral] at hmarkov
  have hbound :
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
        {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i} ≤ ENNReal.ofReal ((k : ℝ) * x) := by
    refine hmarkov.trans ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
    exact mul_le_mul' le_rfl hμ
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg k) hx) hbound

/-- Below the saturation mean every feasible law has success probability below one. -/
theorem tailProbability_lt_one {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) (μ : ProbabilityMeasure ℝ≥0)
    (hμ : mean μ ≤ ENNReal.ofReal x) : tailProbability k μ < 1 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  apply lt_of_le_of_lt (tailProbability_le_mul_mean k x hx μ hμ)
  calc
    (k : ℝ) * x < (k : ℝ) * (k : ℝ)⁻¹ := mul_lt_mul_of_pos_left hxlt hkpos
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hkpos)

/-- An extremizing law uses its entire mean budget below saturation. -/
theorem maximizer_mean_eq {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) : mean μ = ENNReal.ofReal x := by
  have hfin : mean μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμ.1
  let m : ℝ := (mean μ).toReal
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hmle : m ≤ x := ENNReal.toReal_le_of_le_ofReal hx hμ.1
  have hm : mean μ = ENNReal.ofReal m := (ENNReal.ofReal_toReal hfin).symm
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx1 : x < 1 := hxlt.trans_le ((inv_le_one₀ (by positivity)).mpr hkreal)
  by_contra hne
  have hmx : m < x := lt_of_le_of_ne hmle (fun heq => hne (hm.trans (congrArg _ heq)))
  let t : ℝ := (x - m) / (1 - m)
  have hden : 0 < 1 - m := by linarith
  have ht : 0 < t := div_pos (sub_pos.mpr hmx) hden
  have ht1 : t < 1 := (div_lt_one hden).mpr (by linarith)
  have hmix : (1 - t) * m + t = x := by
    dsimp [t]
    field_simp
    ring
  have hν : mean (addOneLaw μ t ht.le ht1.le) = ENNReal.ofReal x := by
    rw [mean_addOneLaw, hm, ← ENNReal.ofReal_mul (sub_nonneg.mpr ht1.le),
      ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ht1.le) hm0) ht.le, hmix]
  have hp : tailProbability k μ < 1 := tailProbability_lt_one hk hx hxlt μ hμ.1
  have hpow : (1 - t)^k < 1 := pow_lt_one₀ (sub_nonneg.mpr ht1.le)
    (by linarith) (by omega)
  have hstrict : tailProbability k μ < tailProbability k (addOneLaw μ t ht.le ht1.le) := by
    rw [tail_addOneLaw]
    have := mul_lt_mul_of_pos_right hpow (sub_pos.mpr hp)
    nlinarith
  exact (not_lt_of_ge (hμ.2 _ hν.le)) hstrict

/-- Every maximizing law is supported below one, including laws originally
allowed to have unbounded support. -/
theorem maximizer_no_mass_above_one {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0 := by
  have hm := maximizer_mean_eq hk hx hxlt hμ
  have hmc := maximizer_mean_eq hk hx hxlt (capLaw_maximizes hμ)
  have hae : (fun t : ℝ≥0 => ((min t 1 : ℝ≥0) : ℝ≥0∞)) =ᵐ[(μ : Measure ℝ≥0)]
      (fun t : ℝ≥0 => (t : ℝ≥0∞)) := by
    apply ae_eq_of_ae_le_of_lintegral_le
      (ae_of_all _ fun t => ENNReal.coe_le_coe.mpr (min_le_left t 1))
    · rw [← mean_map μ (fun t : ℝ≥0 => min t 1) (by fun_prop)]
      change mean (capLaw μ) ≠ ∞
      rw [hmc]
      exact ENNReal.ofReal_ne_top
    · exact measurable_coe_nnreal_ennreal.aemeasurable
    · rw [← mean_map μ (fun t : ℝ≥0 => min t 1) (by fun_prop)]
      change mean μ ≤ mean (capLaw μ)
      rw [hm, hmc]
  have hs : ∀ᵐ t ∂(μ : Measure ℝ≥0), t ≤ 1 := by
    filter_upwards [hae] with t ht
    have ht' : min t 1 = t := ENNReal.coe_injective ht
    exact ht' ▸ min_le_right t 1
  simpa [ae_iff, Set.Ioi] using hs

/-- The one-sided threshold perturbation used to control the atom at zero. -/
def shiftScaleLaw (k : ℕ) (t : ℝ≥0) (μ : ProbabilityMeasure ℝ≥0) :
    ProbabilityMeasure ℝ≥0 := μ.map (fun y => (y - t) / (1 - (k : ℝ≥0) * t))

theorem shiftScale_sum_ge_one {k : ℕ} {t : ℝ≥0}
    (ht : (k : ℝ≥0) * t < 1) (z : Fin k → ℝ≥0)
    (hz : 1 ≤ ∑ i, z i) :
    1 ≤ ∑ i, (z i - t) / (1 - (k : ℝ≥0) * t) := by
  have hd : 0 < 1 - (k : ℝ≥0) * t := tsub_pos_iff_lt.mpr ht
  rw [← Finset.sum_div]
  apply (le_div_iff₀ hd).mpr
  rw [one_mul]
  have hs : ∑ i, z i ≤ (∑ i, (z i - t)) + (k : ℝ≥0) * t := by
    calc
      ∑ i, z i ≤ ∑ i, ((z i - t) + t) := Finset.sum_le_sum fun _ _ => le_tsub_add
      _ = (∑ i, (z i - t)) + (k : ℝ≥0) * t := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hbig : (1 - (k : ℝ≥0) * t) + (k : ℝ≥0) * t ≤
      (∑ i, (z i - t)) + (k : ℝ≥0) * t := by
    rw [tsub_add_cancel_of_le ht.le]
    exact hz.trans hs
  exact le_of_add_le_add_right hbig

theorem tailProbability_shiftScaleLaw_ge {k : ℕ} {t : ℝ≥0}
    (ht : (k : ℝ≥0) * t < 1) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ ≤ tailProbability k (shiftScaleLaw k t μ) := by
  rw [shiftScaleLaw, tailProbability_map k μ
    (fun y : ℝ≥0 => (y - t) / (1 - (k : ℝ≥0) * t)) (by fun_prop)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  exact measure_mono (fun z hz => shiftScale_sum_ge_one ht z hz)

/-- Splitting each sample into its part below the threshold and its excess. -/
theorem mean_shiftScaleLaw_identity {k : ℕ} {t : ℝ≥0}
    (ht : (k : ℝ≥0) * t < 1) (μ : ProbabilityMeasure ℝ≥0) :
    mean (shiftScaleLaw k t μ) * ((1 - (k : ℝ≥0) * t : ℝ≥0) : ℝ≥0∞) +
      (∫⁻ y : ℝ≥0, ((min y t : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure ℝ≥0)) = mean μ := by
  have hd : 1 - (k : ℝ≥0) * t ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr ht)
  rw [shiftScaleLaw, mean_map μ
    (fun y : ℝ≥0 => (y - t) / (1 - (k : ℝ≥0) * t)) (by fun_prop)]
  rw [← lintegral_mul_const _ (show Measurable
    (fun y : ℝ≥0 => (((y - t) / (1 - (k : ℝ≥0) * t) : ℝ≥0) : ℝ≥0∞)) by fun_prop)]
  simp only [← ENNReal.coe_mul, div_mul_cancel₀ _ hd]
  rw [← lintegral_add_left (show Measurable
    (fun y : ℝ≥0 => ((y - t : ℝ≥0) : ℝ≥0∞)) by fun_prop)]
  simp only [← ENNReal.coe_add, tsub_add_min]
  rfl

theorem maximizer_mean_shiftScaleLaw_ge {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) {t : ℝ≥0} (ht : (k : ℝ≥0) * t < 1) :
    ENNReal.ofReal x ≤ mean (shiftScaleLaw k t μ) := by
  by_cases hmean : mean (shiftScaleLaw k t μ) ≤ ENNReal.ofReal x
  · have hν : Maximizes k x (shiftScaleLaw k t μ) := by
      refine ⟨hmean, ?_⟩
      intro ρ hρ
      exact (hμ.2 ρ hρ).trans (tailProbability_shiftScaleLaw_ge ht μ)
    exact (maximizer_mean_eq hk hx hxlt hν).ge
  · exact (lt_of_not_ge hmean).le

/-- Each positive cutoff already satisfies the desired mass estimate. -/
theorem maximizer_mass_Ici_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (k : ℝ≥0) * t < 1) :
    (μ : Measure ℝ≥0) (Set.Ici t) ≤ ENNReal.ofReal ((k : ℝ) * x) := by
  let d : ℝ≥0 := 1 - (k : ℝ≥0) * t
  let I : ℝ≥0∞ := ∫⁻ y : ℝ≥0, ((min y t : ℝ≥0) : ℝ≥0∞) ∂(μ : Measure ℝ≥0)
  have hmean := maximizer_mean_shiftScaleLaw_ge hk hx hxlt hμ ht
  have hle : ENNReal.ofReal x * (d : ℝ≥0∞) + I ≤ ENNReal.ofReal x := by
    calc
      _ ≤ mean (shiftScaleLaw k t μ) * (d : ℝ≥0∞) + I :=
        add_le_add (mul_le_mul' hmean le_rfl) le_rfl
      _ = mean μ := mean_shiftScaleLaw_identity ht μ
      _ = ENNReal.ofReal x := maximizer_mean_eq hk hx hxlt hμ
  have hsplit : ENNReal.ofReal x = ENNReal.ofReal x * (d : ℝ≥0∞) +
      ENNReal.ofReal x * (((k : ℝ≥0) * t : ℝ≥0) : ℝ≥0∞) := by
    rw [← mul_add, ← ENNReal.coe_add]
    rw [show d + (k : ℝ≥0) * t = 1 from tsub_add_cancel_of_le ht.le]
    simp
  have hI : I ≤ ENNReal.ofReal x * (((k : ℝ≥0) * t : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.add_le_add_iff_left (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top)).mp
      (hle.trans_eq hsplit)
  have hmarkov := mul_meas_ge_le_lintegral (μ := (μ : Measure ℝ≥0))
    (show Measurable (fun y : ℝ≥0 => ((min y t : ℝ≥0) : ℝ≥0∞)) by fun_prop)
    (t : ℝ≥0∞)
  have hmass : (t : ℝ≥0∞) * (μ : Measure ℝ≥0) (Set.Ici t) ≤ I := by
    simpa [I, Set.Ici] using hmarkov
  have hmass' : (t : ℝ≥0∞) * (μ : Measure ℝ≥0) (Set.Ici t) ≤
      (t : ℝ≥0∞) * ENNReal.ofReal ((k : ℝ) * x) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
    simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm, mul_left_comm, mul_assoc]
      using hmass.trans hI
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast ht0.ne') ENNReal.coe_ne_top).mp hmass'

/-- Every maximizing law has positive mass at most `k*x`. Continuity from
below replaces the bounded-convergence limit in the informal argument. -/
theorem maximizer_positive_mass_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x)
    (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) :
    (μ : Measure ℝ≥0) (Set.Ioi 0) ≤ ENNReal.ofReal ((k : ℝ) * x) := by
  have hkpos : (0 : ℝ≥0) < k := Nat.cast_pos.mpr (by omega)
  obtain ⟨u, hu, hmem, hlim⟩ := exists_seq_strictAnti_tendsto' (inv_pos.mpr hkpos)
  have hunion : (⋃ n : ℕ, Set.Ici (u n)) = Set.Ioi 0 :=
    iUnion_Ici_eq_Ioi_of_lt_of_tendsto (fun n => (hmem n).1) hlim
  have hmono : Monotone (fun n : ℕ => Set.Ici (u n)) := by
    intro i j hij y hy
    exact (hu.antitone hij).trans hy
  rw [← hunion, hmono.measure_iUnion]
  apply iSup_le
  intro n
  apply maximizer_mass_Ici_le hk hx hxlt hμ (hmem n).1
  calc
    (k : ℝ≥0) * u n < (k : ℝ≥0) * (k : ℝ≥0)⁻¹ :=
      mul_lt_mul_of_pos_left (hmem n).2 hkpos
    _ = 1 := mul_inv_cancel₀ hkpos.ne'

theorem zero_atom_dominates (μ : ProbabilityMeasure ℝ≥0) {r : ℝ}
    (hr : 0 ≤ r) (hpos : (μ : Measure ℝ≥0) (Set.Ioi 0) ≤ ENNReal.ofReal r) :
    ENNReal.ofReal (1 - r) • Measure.dirac (0 : ℝ≥0) ≤ (μ : Measure ℝ≥0) := by
  have hcompl : (Set.Ioi (0 : ℝ≥0))ᶜ = {0} := by
    ext y
    simp
  have hzero : ENNReal.ofReal (1 - r) ≤ (μ : Measure ℝ≥0) {0} := by
    rw [ENNReal.ofReal_sub 1 hr, ENNReal.ofReal_one, ← hcompl,
      prob_compl_eq_one_sub measurableSet_Ioi]
    exact tsub_le_tsub_left hpos 1
  apply Measure.le_iff.mpr
  intro s hs
  by_cases hz : (0 : ℝ≥0) ∈ s
  · simpa only [Measure.smul_apply, Measure.dirac_apply_of_mem hz, smul_eq_mul, mul_one]
      using hzero.trans (measure_mono (Set.singleton_subset_iff.mpr hz))
  · simp [Measure.smul_apply, Measure.dirac_apply, hz]

/-- A maximizing law admits the exact normalization used in the comparison
inequalities. The residual law is a probability measure on the unit interval
with mean `1/k`; no atomic or finite-support assumption is imposed. -/
theorem maximizer_normalized_representation {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (hx : 0 < x) (hxlt : x < (k : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes k x μ) :
    ∃ Q : ProbabilityMeasure ℝ≥0,
      (μ : Measure ℝ≥0) = ENNReal.ofReal (1 - (k : ℝ) * x) • Measure.dirac 0 +
        ENNReal.ofReal ((k : ℝ) * x) • (Q : Measure ℝ≥0) ∧
      (Q : Measure ℝ≥0) (Set.Ioi 1) = 0 ∧
      mean Q = ENNReal.ofReal (k : ℝ)⁻¹ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < (k : ℝ) * x := mul_pos hkpos hx
  have hrlt : (k : ℝ) * x < 1 := by
    calc
      (k : ℝ) * x < (k : ℝ) * (k : ℝ)⁻¹ := mul_lt_mul_of_pos_left hxlt hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  let a : ℝ≥0∞ := ENNReal.ofReal (1 - (k : ℝ) * x)
  let b : ℝ≥0∞ := ENNReal.ofReal ((k : ℝ) * x)
  let ρ : Measure ℝ≥0 := (μ : Measure ℝ≥0) - a • Measure.dirac 0
  have hb0 : b ≠ 0 := (ENNReal.ofReal_pos.mpr hrpos).ne'
  have hbtop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have ha : a • Measure.dirac (0 : ℝ≥0) ≤ (μ : Measure ℝ≥0) :=
    zero_atom_dominates μ hrpos.le (maximizer_positive_mass_le hk hx.le hxlt hμ)
  let : IsFiniteMeasure (a • Measure.dirac (0 : ℝ≥0)) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  have hsum : ρ + a • Measure.dirac 0 = (μ : Measure ℝ≥0) :=
    Measure.sub_add_cancel_of_le ha
  have hρuniv : ρ Set.univ = b := by
    rw [Measure.sub_apply MeasurableSet.univ ha]
    simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one]
    change 1 - ENNReal.ofReal (1 - (k : ℝ) * x) = ENNReal.ofReal ((k : ℝ) * x)
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (sub_nonneg.mpr hrlt.le)]
    congr 1
    ring
  have hQprob : IsProbabilityMeasure (b⁻¹ • ρ) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, hρuniv, ENNReal.inv_mul_cancel hb0 hbtop]
  let Q : ProbabilityMeasure ℝ≥0 := ⟨b⁻¹ • ρ, hQprob⟩
  refine ⟨Q, ?_, ?_, ?_⟩
  · change (μ : Measure ℝ≥0) = a • Measure.dirac 0 + b • (b⁻¹ • ρ)
    rw [smul_smul, ENNReal.mul_inv_cancel hb0 hbtop, one_smul, add_comm]
    exact hsum.symm
  · have hρle : ρ ≤ (μ : Measure ℝ≥0) := Measure.sub_le
    have hρzero : ρ (Set.Ioi 1) = 0 :=
      le_antisymm ((hρle _).trans_eq (maximizer_no_mass_above_one hk hx.le hxlt hμ)) bot_le
    change (b⁻¹ • ρ) (Set.Ioi 1) = 0
    simp [Measure.smul_apply, hρzero]
  · have hmeanρ : (∫⁻ y : ℝ≥0, (y : ℝ≥0∞) ∂ρ) = ENNReal.ofReal x := by
      have hh := congrArg (fun ν : Measure ℝ≥0 => ∫⁻ y : ℝ≥0, (y : ℝ≥0∞) ∂ν) hsum
      simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
        ENNReal.coe_zero, smul_zero, add_zero] at hh
      exact hh.trans (maximizer_mean_eq hk hx.le hxlt hμ)
    change (∫⁻ y : ℝ≥0, (y : ℝ≥0∞) ∂(b⁻¹ • ρ)) = ENNReal.ofReal (k : ℝ)⁻¹
    rw [lintegral_smul_measure, smul_eq_mul, hmeanρ, mul_comm, ← div_eq_mul_inv]
    change ENNReal.ofReal x / ENNReal.ofReal ((k : ℝ) * x) = ENNReal.ofReal (k : ℝ)⁻¹
    rw [← ENNReal.ofReal_div_of_pos hrpos]
    congr 1
    field_simp

end SharpTailMatching.Probability
