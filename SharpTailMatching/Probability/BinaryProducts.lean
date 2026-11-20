module

public import SharpTailMatching.Probability.Variation
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Data.Nat.Choose.Sum

/-! # Binary product mixtures and active-coordinate sums -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem pi_projection_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    (ν : κ → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)]
    (f : ι → κ) (hf : Function.Injective f) :
    (Measure.pi ν).map (fun w i => w (f i)) = Measure.pi (fun i => ν (f i)) := by
  have hI : iIndepFun (fun i (w : κ → ℝ≥0) => w i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h := (iIndepFun.precomp hf hI).map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (f i)).aemeasurable)
  have hcoords (i : ι) : (Measure.pi ν).map (fun w => w (f i)) = ν (f i) :=
    (measurePreserving_eval ν (f i)).map_eq
  simpa only [hcoords] using h

def iidSumLaw (k : ℕ) (μ : Measure ℝ≥0) : Measure ℝ≥0 :=
  (Measure.pi (fun _ : Fin k => μ)).map (fun w => ∑ i,w i)

def selectedMeasure (k : ℕ) (μ : Measure ℝ≥0) (S : Finset (Fin k)) (i : Fin k) : Measure ℝ≥0 :=
  if i ∈ S then μ else Measure.dirac 0

def binaryMeasure (k : ℕ) (U L : Measure ℝ≥0) (S : Finset (Fin k)) (i : Fin k) : Measure ℝ≥0 :=
  if i ∈ S then U else L

instance binaryMeasure_isProbability (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L]
    (S : Finset (Fin k)) (i : Fin k) : IsProbabilityMeasure (binaryMeasure k U L S i) := by
  unfold binaryMeasure
  split <;> infer_instance

instance selectedMeasure_isProbability (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (S : Finset (Fin k)) (i : Fin k) : IsProbabilityMeasure (selectedMeasure k μ S i) := by
  unfold selectedMeasure
  split <;> infer_instance

/-- Dropping coordinates fixed at zero leaves exactly as many iid samples as
there are active coordinates. This is an equality of full sum distributions. -/
theorem selected_sumLaw (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (S : Finset (Fin k)) :
    (Measure.pi (selectedMeasure k μ S)).map (fun w => ∑ i,w i) = iidSumLaw S.card μ := by
  classical
  let e : S ≃ Fin S.card := Finset.equivFin S
  let f : Fin S.card → Fin k := fun i => (e.symm i).val
  have hf : Function.Injective f := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hsel (i : Fin S.card) : selectedMeasure k μ S (f i) = μ := by
    simp only [selectedMeasure,f,ite_eq_left (e.symm i).property]
  have hproj := pi_projection_map (selectedMeasure k μ S) f hf
  simp only [hsel] at hproj
  have hzero : ∀ᵐ w ∂Measure.pi (selectedMeasure k μ S), ∀ i, i ∉ S → w i = 0 := by
    apply ae_all_iff.mpr
    intro i
    by_cases hi : i ∈ S
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hcoord : ∀ᵐ z ∂selectedMeasure k μ S i, z = 0 := by
        simp [selectedMeasure,hi]
      exact ((Measure.tendsto_eval_ae_ae (μ := selectedMeasure k μ S) (i := i)).eventually hcoord).mono
        (fun _ hw _ => hw)
  have hsum : (fun w : Fin k → ℝ≥0 => ∑ i,w i) =ᵐ[Measure.pi (selectedMeasure k μ S)]
      (fun w => ∑ i : Fin S.card,w (f i)) := by
    filter_upwards [hzero] with w hw
    have hfull : (∑ i ∈ S,w i) = ∑ i : Fin k,w i :=
      Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hw i hi)
    have hsub : (∑ i : Fin S.card,w (f i)) = ∑ i ∈ S,w i := by
      rw [Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => w i)]
      exact e.symm.sum_comp (fun i : S => w i.val)
    exact hfull.symm.trans hsub.symm
  calc
    _ = (Measure.pi (selectedMeasure k μ S)).map (fun w => ∑ i : Fin S.card,w (f i)) :=
      Measure.map_congr hsum
    _ = ((Measure.pi (selectedMeasure k μ S)).map (fun w i => w (f i))).map (fun w => ∑ i,w i) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = iidSumLaw S.card μ := by rw [hproj]; rfl

/-- Product expansion indexed by the active subset. Its coefficients already
separate into powers of the two scalar weights. -/
theorem pi_binary_expansion (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    Measure.pi (fun _ : Fin k => a • μ+b • Measure.dirac 0) =
      ∑ S : Finset (Fin k), (a^S.card*b^(k-S.card)) • Measure.pi (selectedMeasure k μ S) := by
  classical
  let : IsFiniteMeasure (a • μ) := μ.smul_finite ha
  let : IsFiniteMeasure (b • (Measure.dirac (0 : ℝ≥0))) := (Measure.dirac 0).smul_finite hb
  apply Measure.pi_eq
  intro s _
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,Measure.pi_pi,
    Measure.add_apply,Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  have hrect (i : Fin k) : selectedMeasure k μ S i (s i) =
      if i ∈ S then μ (s i) else (Measure.dirac 0) (s i) := by
    unfold selectedMeasure
    split <;> rfl
  simp only [hrect]
  rw [← Finset.prod_mul_prod_compl S (fun i => if i ∈ S then μ (s i) else (Measure.dirac 0) (s i))]
  simp only [Finset.prod_ite_of_true (fun i hi => hi),
    Finset.prod_ite_of_false (fun (i : Fin k) (hi : i ∈ Sᶜ) => Finset.mem_compl.mp hi),Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_compl,Fintype.card_fin]
  ring

/-- Exact binomial expansion of the full sum distribution of a zero-thinned
law. The identity is independent of the event or integrand subsequently used. -/
theorem iidSumLaw_binary (k : ℕ) (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    iidSumLaw k (a • μ+b • Measure.dirac 0) =
      ∑ j ∈ Finset.range (k+1), ((k.choose j : ℝ≥0∞)*a^j*b^(k-j)) • iidSumLaw j μ := by
  classical
  unfold iidSumLaw at ⊢
  rw [pi_binary_expansion k μ a b ha hb]
  have hmap : (∑ S : Finset (Fin k), (a^S.card*b^(k-S.card)) •
      Measure.pi (selectedMeasure k μ S)).map (fun w => ∑ i,w i) =
      ∑ S : Finset (Fin k), (a^S.card*b^(k-S.card)) • iidSumLaw S.card μ := by
    rw [← Measure.mapₗ_apply_of_measurable (by fun_prop)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro S _
    rw [map_smul,Measure.mapₗ_apply_of_measurable (by fun_prop),selected_sumLaw]
  rw [hmap]
  have hgroup := Finset.sum_powerset_apply_card
    (fun j => (a^j*b^(k-j)) • iidSumLaw j μ) (x := (Finset.univ : Finset (Fin k)))
  simpa [Finset.powerset_univ,← Nat.cast_smul_eq_nsmul ℝ≥0∞,smul_smul,mul_assoc,iidSumLaw] using hgroup

theorem pi_binary_expansion_general (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    Measure.pi (fun _ : Fin k => a • U+b • L) =
      ∑ S : Finset (Fin k), (a^S.card*b^(k-S.card)) • Measure.pi (binaryMeasure k U L S) := by
  classical
  let : IsFiniteMeasure (a • U) := U.smul_finite ha
  let : IsFiniteMeasure (b • L) := L.smul_finite hb
  apply Measure.pi_eq
  intro s _
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,Measure.pi_pi,
    Measure.add_apply,Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  have hrect (i : Fin k) : binaryMeasure k U L S i (s i) =
      if i ∈ S then U (s i) else L (s i) := by
    unfold binaryMeasure
    split <;> rfl
  simp only [hrect]
  rw [← Finset.prod_mul_prod_compl S (fun i => if i ∈ S then U (s i) else L (s i))]
  simp only [Finset.prod_ite_of_true (fun i hi => hi),
    Finset.prod_ite_of_false (fun (i : Fin k) (hi : i ∈ Sᶜ) => Finset.mem_compl.mp hi),Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_compl,Fintype.card_fin]
  ring

def binaryLevelMeasure (k : ℕ) (U L : Measure ℝ≥0) (j : ℕ) : Measure (Fin k → ℝ≥0) :=
  ∑ S ∈ (Finset.univ : Finset (Fin k)).powersetCard j, Measure.pi (binaryMeasure k U L S)

instance binaryLevelMeasure_isFinite (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L] (j : ℕ) :
    IsFiniteMeasure (binaryLevelMeasure k U L j) := by
  unfold binaryLevelMeasure
  infer_instance

theorem pi_binary_levels (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) :
    Measure.pi (fun _ : Fin k => a • U+b • L) =
      ∑ j ∈ Finset.range (k+1), (a^j*b^(k-j)) • binaryLevelMeasure k U L j := by
  classical
  rw [pi_binary_expansion_general k U L a b ha hb]
  have hgroup := (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Finset (Fin k)))) (t := Finset.range (k+1))
    (g := fun S : Finset (Fin k) => S.card)
    (fun S _ => Finset.mem_range.mpr (by
      have h := Finset.card_le_card (Finset.subset_univ S)
      simpa using Nat.lt_succ_of_le h))
    (fun S => (a^S.card*b^(k-S.card)) • Measure.pi (binaryMeasure k U L S))).symm
  rw [hgroup]
  apply Finset.sum_congr rfl
  intro j _
  unfold binaryLevelMeasure
  rw [Finset.smul_sum]
  rw [Finset.powersetCard_eq_filter,Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_filter.mp hS).2]

theorem binaryLevelMeasure_univ (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L] (j : ℕ) :
    binaryLevelMeasure k U L j Set.univ = (k.choose j : ℝ≥0∞) := by
  classical
  simp [binaryLevelMeasure,Measure.finsetSum_apply,Finset.card_powersetCard]

theorem binaryLevelMeasure_zero (k : ℕ) (U L : Measure ℝ≥0) :
    binaryLevelMeasure k U L 0 = Measure.pi (fun _ : Fin k => L) := by
  classical
  simp only [binaryLevelMeasure,Finset.powersetCard_zero,Finset.sum_singleton]
  congr 1

theorem binaryLevelMeasure_last (k : ℕ) (U L : Measure ℝ≥0) :
    binaryLevelMeasure k U L k = Measure.pi (fun _ : Fin k => U) := by
  classical
  have hpowerset : (Finset.univ : Finset (Fin k)).powersetCard k = {Finset.univ} := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.powersetCard_self (Finset.univ : Finset (Fin k))
  rw [binaryLevelMeasure,hpowerset,Finset.sum_singleton]
  congr 1
  funext i
  simp [binaryMeasure]

theorem lintegral_pi_binary_levels (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (f : (Fin k → ℝ≥0) → ℝ≥0∞) :
    (∫⁻ w,f w ∂Measure.pi (fun _ : Fin k => a • U+b • L)) =
      ∑ j ∈ Finset.range (k+1),(a^j*b^(k-j))*(∫⁻ w,f w ∂binaryLevelMeasure k U L j) := by
  rw [pi_binary_levels k U L a b ha hb,lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure,smul_eq_mul]

theorem integral_pi_binary_levels (k : ℕ) (U L : Measure ℝ≥0)
    [IsProbabilityMeasure U] [IsProbabilityMeasure L]
    (a b : ℝ≥0∞) (ha : a ≠ ∞) (hb : b ≠ ∞) (f : (Fin k → ℝ≥0) → ℝ)
    (hf : ∀ j ∈ Finset.range (k+1),Integrable f (binaryLevelMeasure k U L j)) :
    (∫ w,f w ∂Measure.pi (fun _ : Fin k => a • U+b • L)) =
      ∑ j ∈ Finset.range (k+1),(a.toReal^j*b.toReal^(k-j))*(∫ w,f w ∂binaryLevelMeasure k U L j) := by
  rw [pi_binary_levels k U L a b ha hb,
    integral_finsetSum_measure (fun j hj => (hf j hj).smul_measure
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ha) (ENNReal.pow_ne_top hb)))]
  simp only [integral_smul_measure,ENNReal.toReal_mul,ENNReal.toReal_pow,smul_eq_mul]

end SharpTailMatching.Probability
