module

public import SharpTailMatching.Probability.Basic

/-! # Equality at one sample and the standard laws -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

/-- Equality in the one-sample bound forces the identity function to agree
almost everywhere with the success-event indicator. -/
theorem one_sample_equality (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability 1 μ = sharpTailValue 1 x ↔
      (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  constructor
  · intro h
    have hp : (μ : Measure ℝ≥0) (Set.Ici 1) = ENNReal.ofReal x := by
      rw [tailProbability_one, sharpTailValue_one_of_le x hxle] at h
      rw [← h, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    let f : ℝ≥0 → ℝ≥0∞ := (Set.Ici (1 : ℝ≥0)).indicator (fun _ => 1)
    have hfint : ∫⁻ t, f t ∂(μ : Measure ℝ≥0) =
        (μ : Measure ℝ≥0) (Set.Ici 1) := by
      simp [f, lintegral_indicator measurableSet_Ici]
    have hfle : f ≤ᵐ[(μ : Measure ℝ≥0)] (fun t : ℝ≥0 => (t : ℝ≥0∞)) := by
      apply Filter.Eventually.of_forall
      intro t
      by_cases ht : 1 ≤ t
      · simp [f, ht]
      · simp [f, ht]
    have hae : f =ᵐ[(μ : Measure ℝ≥0)] (fun t : ℝ≥0 => (t : ℝ≥0∞)) :=
      ae_eq_of_ae_le_of_lintegral_le hfle
        (by rw [hfint]; exact measure_ne_top _ _)
        measurable_coe_nnreal_ennreal.aemeasurable
        (by simpa only [hfint, hp, mean] using hmean)
    have hae01 : ∀ᵐ t ∂(μ : Measure ℝ≥0), t = 0 ∨ t = 1 := by
      filter_upwards [hae] with t ht
      by_cases htge : 1 ≤ t
      · right
        have ht' : (1 : ℝ≥0∞) = (t : ℝ≥0∞) := by simpa [f, htge] using ht
        exact_mod_cast ht'.symm
      · left
        have ht' : (0 : ℝ≥0∞) = (t : ℝ≥0∞) := by simpa [f, htge] using ht
        exact_mod_cast ht'.symm
    have hevent : (Set.Ici (1 : ℝ≥0)) =ᵐ[(μ : Measure ℝ≥0)] {1} := by
      filter_upwards [hae01] with t ht
      rcases ht with rfl | rfl <;> norm_num
    have hevent0 : (Set.Ici (1 : ℝ≥0))ᶜ =ᵐ[(μ : Measure ℝ≥0)] {0} := by
      filter_upwards [hae01] with t ht
      rcases ht with rfl | rfl <;> norm_num
    have hp1 : (μ : Measure ℝ≥0) {1} = ENNReal.ofReal x :=
      (measure_congr hevent).symm.trans hp
    have hp0 : (μ : Measure ℝ≥0) {0} = ENNReal.ofReal (1 - x) := by
      rw [← measure_congr hevent0, prob_compl_eq_one_sub measurableSet_Ici, hp]
      rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one]
    have hdecomp :=
      (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac (by norm_num : (0 : ℝ≥0) ≠ 1)).mp hae01
    simpa only [hp0, hp1, unitBernoulliMeasure] using hdecomp
  · intro h
    have hμ : μ = unitBernoulliLaw x hx hxle := by
      apply Subtype.ext
      exact h
    rw [hμ, tailProbability_one_unitBernoulliLaw, sharpTailValue_one_of_le x hxle]

/-- The all-zero product box is precisely the failure event for the unit
Bernoulli law, up to a null set. -/
theorem tailProbability_unitBernoulliLaw (k : ℕ) (x : ℝ)
    (hx : 0 ≤ x) (hxle : x ≤ 1) :
    tailProbability k (unitBernoulliLaw x hx hxle) = 1 - (1 - x) ^ k := by
  let μ := unitBernoulliLaw x hx hxle
  let ν := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))
  let A : Set (Fin k → ℝ≥0) := {z | 1 ≤ ∑ i, z i}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hsingle : ∀ᵐ t ∂(μ : Measure ℝ≥0), t = 0 ∨ t = 1 := by
    change ∀ᵐ t ∂(unitBernoulliMeasure x), t = 0 ∨ t = 1
    rw [unitBernoulliMeasure, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _, Measure.ae_smul_measure (by simp) _⟩
  have hprod : ∀ᵐ z ∂ν, ∀ i : Fin k, z i = 0 ∨ z i = 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
      (i := i)).eventually hsingle
  have hevent : Aᶜ =ᵐ[ν] Set.pi Set.univ (fun _ : Fin k => ({0} : Set ℝ≥0)) := by
    filter_upwards [hprod] with z hz
    apply propext
    change (¬ 1 ≤ ∑ i, z i) ↔ ∀ i : Fin k, i ∈ Set.univ → z i ∈ ({0} : Set ℝ≥0)
    constructor
    · intro hf i _
      change z i = 0
      rcases hz i with hi | hi
      · exact hi
      · exfalso
        apply hf
        have hle := Finset.single_le_sum (s := Finset.univ) (f := z)
          (fun j _ => show 0 ≤ z j from zero_le) (Finset.mem_univ i)
        simpa [hi] using hle
    · intro hz0
      have hsum : ∑ i, z i = 0 :=
        Finset.sum_eq_zero fun i _ => hz0 i (Set.mem_univ i)
      simp [hsum]
  have hzero : (μ : Measure ℝ≥0) {0} = ENNReal.ofReal (1 - x) := by
    simp [μ, unitBernoulliLaw, unitBernoulliMeasure, Measure.add_apply, Measure.smul_apply]
  have hfail : ν Aᶜ = ENNReal.ofReal (1 - x) ^ k := by
    rw [measure_congr hevent]
    dsimp [ν]
    rw [Measure.pi_pi]
    simp only [hzero, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hsuccess : ν A = 1 - ENNReal.ofReal (1 - x) ^ k := by
    have hc := prob_compl_eq_one_sub (μ := ν) hA.compl
    simpa only [compl_compl, hfail] using hc
  have hpow : ENNReal.ofReal (1 - x) ^ k ≤ 1 := by
    rw [← hfail]
    exact prob_le_one
  change (ν A).toReal = _
  rw [hsuccess, ENNReal.toReal_sub_of_le hpow ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofReal (sub_nonneg.mpr hxle)]

theorem smallBernoulliMeasure_probability (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ (k : ℝ)⁻¹) :
    IsProbabilityMeasure (smallBernoulliMeasure k x) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hple : (k : ℝ) * x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hxle (Nat.cast_nonneg (α := ℝ) k)
    simpa [ne_of_gt hkpos] using h
  constructor
  simp only [smallBernoulliMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hple) (mul_nonneg (Nat.cast_nonneg k) hx)]
  norm_num

/-- The standard law concentrated at zero and `1/k`. -/
def smallBernoulliLaw (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (hxle : x ≤ (k : ℝ)⁻¹) : ProbabilityMeasure ℝ≥0 :=
  ⟨smallBernoulliMeasure k x, smallBernoulliMeasure_probability k hk x hx hxle⟩

@[simp] theorem mean_smallBernoulliLaw (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ (k : ℝ)⁻¹) :
    mean (smallBernoulliLaw k hk x hx hxle) = ENNReal.ofReal x := by
  have hk0 : k ≠ 0 := by omega
  have hknn : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk0
  simp only [mean, smallBernoulliLaw, ProbabilityMeasure.coe_mk, smallBernoulliMeasure,
    lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, ENNReal.coe_zero,
    smul_eq_mul, mul_zero, zero_add]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  simp only [ENNReal.ofReal_natCast, ENNReal.coe_inv hknn, ENNReal.coe_natCast]
  rw [mul_right_comm, ENNReal.mul_inv_cancel (by exact_mod_cast hk0) (ENNReal.natCast_ne_top k),
    one_mul]

/-- For the small Bernoulli law, success requires all `k` coordinates to be
the nonzero atom. -/
theorem tailProbability_smallBernoulliLaw (k : ℕ) (hk : 1 ≤ k)
    (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ (k : ℝ)⁻¹) :
    tailProbability k (smallBernoulliLaw k hk x hx hxle) = ((k : ℝ) * x) ^ k := by
  have hk0 : k ≠ 0 := by omega
  have hknn : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk0
  have hcpos : (0 : ℝ≥0) < (k : ℝ≥0)⁻¹ := inv_pos.mpr (by exact_mod_cast hk)
  let μ := smallBernoulliLaw k hk x hx hxle
  let ν := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))
  let A : Set (Fin k → ℝ≥0) := {z | 1 ≤ ∑ i, z i}
  have hsum : (∑ _ : Fin k, (k : ℝ≥0)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hknn]
  have hsingle : ∀ᵐ t ∂(μ : Measure ℝ≥0), t = 0 ∨ t = (k : ℝ≥0)⁻¹ := by
    change ∀ᵐ t ∂(smallBernoulliMeasure k x), t = 0 ∨ t = (k : ℝ≥0)⁻¹
    rw [smallBernoulliMeasure, ae_add_measure_iff]
    exact ⟨Measure.ae_smul_measure (by simp) _, Measure.ae_smul_measure (by simp) _⟩
  have hprod : ∀ᵐ z ∂ν, ∀ i : Fin k, z i = 0 ∨ z i = (k : ℝ≥0)⁻¹ := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
      (i := i)).eventually hsingle
  have hevent : A =ᵐ[ν]
      Set.pi Set.univ (fun _ : Fin k => ({(k : ℝ≥0)⁻¹} : Set ℝ≥0)) := by
    filter_upwards [hprod] with z hz
    apply propext
    change (1 ≤ ∑ i, z i) ↔
      ∀ i : Fin k, i ∈ Set.univ → z i ∈ ({(k : ℝ≥0)⁻¹} : Set ℝ≥0)
    constructor
    · intro hs i _
      change z i = (k : ℝ≥0)⁻¹
      rcases hz i with hi | hi
      · exfalso
        have hle : ∀ j : Fin k, z j ≤ (k : ℝ≥0)⁻¹ := by
          intro j
          rcases hz j with hj | hj <;> simp [hj]
        have hlt : (∑ j, z j) < ∑ _ : Fin k, (k : ℝ≥0)⁻¹ :=
          Finset.sum_lt_sum (fun j _ => hle j)
            ⟨i, Finset.mem_univ i, by simpa [hi] using hcpos⟩
        exact (not_lt_of_ge hs) (hsum ▸ hlt)
      · exact hi
    · intro h
      have hsum' : (∑ i, z i) = 1 := by
        calc
          (∑ i, z i) = ∑ _ : Fin k, (k : ℝ≥0)⁻¹ :=
            Finset.sum_congr rfl fun i _ => h i (Set.mem_univ i)
          _ = 1 := hsum
      simp [hsum']
  have hatom : (μ : Measure ℝ≥0) {(k : ℝ≥0)⁻¹} = ENNReal.ofReal ((k : ℝ) * x) := by
    simp [μ, smallBernoulliLaw, smallBernoulliMeasure, Measure.add_apply,
      Measure.smul_apply, (ne_of_gt hcpos).symm]
  have hmass : ν A = ENNReal.ofReal ((k : ℝ) * x) ^ k := by
    rw [measure_congr hevent]
    dsimp [ν]
    rw [Measure.pi_pi]
    simp only [hatom, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change (ν A).toReal = _
  rw [hmass, ENNReal.toReal_pow, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg k) hx)]

/-- Each candidate is attained by its explicit standard law. Choosing the
larger candidate gives attainment for every allowed mean, without assuming
the upper-bound theorem. -/
theorem sharp_tail_attained (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    ∃ μ : ProbabilityMeasure ℝ≥0,
      mean μ ≤ ENNReal.ofReal x ∧ tailProbability k μ = sharpTailValue k x := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkinvle : (k : ℝ)⁻¹ ≤ 1 :=
    (inv_le_one₀ hkpos).mpr (by exact_mod_cast hk)
  by_cases hxle : x ≤ (k : ℝ)⁻¹
  · by_cases hbranch : ((k : ℝ) * x) ^ k ≤ 1 - (1 - x) ^ k
    · refine ⟨unitBernoulliLaw x hx (hxle.trans hkinvle), ?_, ?_⟩
      · simp
      · rw [tailProbability_unitBernoulliLaw]
        simp only [sharpTailValue, hxle, ite_eq_left, max_eq_left hbranch]
    · refine ⟨smallBernoulliLaw k hk x hx hxle, ?_, ?_⟩
      · simp
      · rw [tailProbability_smallBernoulliLaw]
        simp only [sharpTailValue, hxle, ite_eq_left, max_eq_right (le_of_not_ge hbranch)]
  · refine ⟨smallBernoulliLaw k hk ((k : ℝ)⁻¹) (le_of_lt (inv_pos.mpr hkpos)) le_rfl, ?_, ?_⟩
    · rw [mean_smallBernoulliLaw]
      exact ENNReal.ofReal_le_ofReal (le_of_not_ge hxle)
    · rw [tailProbability_smallBernoulliLaw]
      simp [sharpTailValue, hxle, ne_of_gt hkpos]

end SharpTailMatching.Probability
