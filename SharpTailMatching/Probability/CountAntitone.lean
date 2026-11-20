module

public import SharpTailMatching.Probability.BinaryProducts
public import SharpTailMatching.Probability.LowerEvent
public import Mathlib.Logic.Equiv.Fintype

/-! # Failure decreases with the number of upper observations -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def binaryFailure (k : ℕ) (U L : ProbabilityMeasure ℝ≥0) (S : Finset (Fin k)) : ℝ :=
  (Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)).real
    {w | ∑ i,w i < 1}

theorem binaryFailure_eq (k : ℕ) (U L : ProbabilityMeasure ℝ≥0) (S : Finset (Fin k)) :
    binaryFailure k U L S = 1-tailForm k (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S) := by
  have h := probReal_compl_eq_one_sub (μ := Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S))
    (show MeasurableSet {w : Fin k → ℝ≥0 | 1 ≤ ∑ i,w i} by measurability)
  unfold binaryFailure tailForm Measure.real
  simpa only [Set.compl_ofPred, not_le, Measure.real] using h

theorem binaryFailure_sameCard (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    (S T : Finset (Fin k)) (hST : S.card = T.card) :
    binaryFailure k U L S = binaryFailure k U L T := by
  classical
  obtain ⟨e,he⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  have hmem (i : Fin k) : e i ∈ T ↔ i ∈ S := by
    rw [← he]
    simp
  have hfamily : (fun i => binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) T (e i)) =
      binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S := by
    funext i
    simp only [binaryMeasure, hmem]
  rw [binaryFailure_eq, binaryFailure_eq, ← hfamily,
    tailForm_permute k (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) T) e]

theorem binaryFailure_antitone_subset (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z) :
    Antitone (binaryFailure k U L) := by
  classical
  intro S T hST
  let ν := (U : Measure ℝ≥0).prod (L : Measure ℝ≥0)
  let select (S : Finset (Fin k)) (i : Fin k) (p : ℝ≥0 × ℝ≥0) := if i ∈ S then p.1 else p.2
  have hmp (S : Finset (Fin k)) :
      MeasurePreserving (fun w i => select S i (w i)) (Measure.pi (fun _ : Fin k => ν))
        (Measure.pi (binaryMeasure k (U : Measure ℝ≥0) (L : Measure ℝ≥0) S)) := by
    apply measurePreserving_pi
    intro i
    by_cases hi : i ∈ S
    · simpa only [select,binaryMeasure,ite_eq_left hi] using
        (measurePreserving_fst : MeasurePreserving Prod.fst ν (U : Measure ℝ≥0))
    · simpa only [select,binaryMeasure,ite_eq_right hi] using
        (measurePreserving_snd : MeasurePreserving Prod.snd ν (L : Measure ℝ≥0))
  have hbound : ∀ᵐ p ∂ν, p.2 ≤ b ∧ b < p.1 := by
    have hfst : ∀ᵐ p ∂ν, b < p.1 := measurePreserving_fst.quasiMeasurePreserving.ae hUb
    have hsnd : ∀ᵐ p ∂ν, p.2 ≤ b := measurePreserving_snd.quasiMeasurePreserving.ae hLb
    exact hsnd.and hfst
  have hall : ∀ᵐ w ∂Measure.pi (fun _ : Fin k => ν), ∀ i, (w i).2 ≤ b ∧ b < (w i).1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => ν) (i := i)).eventually hbound
  have horder : ∀ᵐ w ∂Measure.pi (fun _ : Fin k => ν),
      (∑ i,select S i (w i)) ≤ ∑ i,select T i (w i) := by
    filter_upwards [hall] with w hw
    apply Finset.sum_le_sum
    intro i _
    by_cases hiS : i ∈ S
    · simp only [select,ite_eq_left hiS,ite_eq_left (hST hiS),le_refl]
    · by_cases hiT : i ∈ T
      · simpa only [select,ite_eq_right hiS,ite_eq_left hiT] using (hw i).1.trans (hw i).2.le
      · simp only [select,ite_eq_right hiS,ite_eq_right hiT,le_refl]
  let F : Set (Fin k → ℝ≥0) := {w | ∑ i,w i < 1}
  have hF : MeasurableSet F := by measurability
  unfold binaryFailure Measure.real
  rw [← (hmp T).map_eq, ← (hmp S).map_eq, Measure.map_apply (hmp T).measurable hF,
    Measure.map_apply (hmp S).measurable hF]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [horder] with w hw hF
  exact lt_of_le_of_lt hw hF

theorem binaryFailure_antitone_card (k : ℕ) (U L : ProbabilityMeasure ℝ≥0)
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b < z)
    (S T : Finset (Fin k)) (hST : S.card ≤ T.card) :
    binaryFailure k U L T ≤ binaryFailure k U L S := by
  obtain ⟨R,hRT,hR⟩ := Finset.exists_subset_card_eq hST
  rw [← binaryFailure_sameCard k U L R S hR]
  exact binaryFailure_antitone_subset k U L hLb hUb hRT

/-- The weighted opposite-monotonicity inequality, without normalizing the weights. -/
theorem weighted_antitone_covariance {ι : Type*} (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∀i∈s,0 ≤ w i)
    (hfg : ∀i∈s,∀j∈s,(f i-f j)*(g i-g j) ≤ 0) :
    (∑i∈s,w i)*(∑i∈s,w i*f i*g i) ≤
      (∑i∈s,w i*f i)*(∑i∈s,w i*g i) := by
  have hsum : (∑i∈s,∑j∈s,w i*w j*((f i-f j)*(g i-g j))) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i hi) (hw j hj)) (hfg i hi j hj)
  have heq : (∑i∈s,∑j∈s,w i*w j*((f i-f j)*(g i-g j))) =
      2*((∑i∈s,w i)*(∑i∈s,w i*f i*g i)-
        (∑i∈s,w i*f i)*(∑i∈s,w i*g i)) := by
    calc
      _ = ∑i∈s,∑j∈s, (w j*(w i*f i*g i)-(w i*f i)*(w j*g j)-
          (w j*f j)*(w i*g i)+w i*(w j*f j*g j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
        simp_rw [mul_assoc,← Finset.mul_sum]
        ring
  rw [heq] at hsum
  linarith

end SharpTailMatching.Probability
