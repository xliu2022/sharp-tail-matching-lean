module

public import SharpTailMatching.CubicAlgebra
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi

public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SharpTailMatching.Probability

open CubicAlgebra

theorem continuous_cappedCubic (b τ z : ℝ) : Continuous (cappedCubic b τ z) := by
  unfold cappedCubic clippedRamp
  fun_prop

theorem measurable_failureQuadratic (τ z : ℝ) : Measurable (failureQuadratic τ z) := by
  unfold failureQuadratic
  exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const

theorem failureQuadratic_nonneg (τ z w : ℝ) : 0 ≤ failureQuadratic τ z w := by
  unfold failureQuadratic
  split_ifs <;> positivity

theorem failureQuadratic_le_of_abs {τ z w C : ℝ} (hw : |w| ≤ C) :
    failureQuadratic τ z w ≤ (C + |z|) ^ 2 := by
  unfold failureQuadratic
  split_ifs
  · have ha : |w + z| ≤ C + |z| := (abs_add_le _ _).trans (by linarith)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (w + z)) ha 2
  · positivity

theorem integrable_bounded_real {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {C : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ C) : Integrable X μ :=
  Integrable.of_bound hX.aestronglyMeasurable C (by simpa only [Real.norm_eq_abs] using hbound)

theorem integrable_bounded_square {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {C : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ C) :
    Integrable (fun ω => X ω ^ 2) μ := by
  apply integrable_bounded_real (hX.pow_const 2) (C := C ^ 2)
  filter_upwards [hbound] with ω hω
  simpa only [abs_pow, sq_abs] using pow_le_pow_left₀ (abs_nonneg (X ω)) hω 2

theorem integrable_capped_product {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {C : ℝ}
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ C) (b τ z : ℝ) :
    Integrable (fun ω => X ω * cappedCubic b τ z (Y ω)) μ := by
  apply integrable_bounded_real (hX.mul ((continuous_cappedCubic b τ z).measurable.comp hY))
    (C := C * (max (τ + z - 2 * b) 0) ^ 3 / 3)
  filter_upwards [hbound] with ω hω
  change |X ω * cappedCubic b τ z (Y ω)| ≤ _
  rw [abs_mul, abs_of_nonneg (cappedCubic_nonneg b τ z (Y ω))]
  have hC : 0 ≤ C := (abs_nonneg _).trans hω
  have h := mul_le_mul hω (cappedCubic_le b τ z (Y ω))
    (cappedCubic_nonneg _ _ _ _) hC
  simpa only [mul_div_assoc] using h

theorem integrable_failureQuadratic {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : Measurable X) {C : ℝ} (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ C) (τ z : ℝ) :
    Integrable (fun ω => failureQuadratic τ z (X ω)) μ := by
  apply integrable_bounded_real ((measurable_failureQuadratic τ z).comp hX)
    (C := (C + |z|) ^ 2)
  filter_upwards [hbound] with ω hω
  change |failureQuadratic τ z (X ω)| ≤ _
  rw [abs_of_nonneg (failureQuadratic_nonneg _ _ _)]
  exact failureQuadratic_le_of_abs hω

/-- Integrating the direct secant estimate over an independent copy of a
centered, bounded coordinate. No differentiability assumption is required. -/
theorem centered_coordinate_cubic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (ha : a ≤ 0) (hab : 0 ≤ a + b)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Set.Icc a (a + b))
    (hcenter : ∫ x, x ∂μ = 0) (τ z t : ℝ) :
    (∫ x, x * cappedCubic b τ z (t + x) ∂μ) ≤
      (∫ x, x ^ 2 ∂μ) * (∫ x, failureQuadratic τ z (t + x) ∂μ) := by
  have hb : 0 ≤ b := by linarith
  have habs : ∀ᵐ x ∂μ, |x| ≤ b := by
    filter_upwards [hsupport] with x hx
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hshift : ∀ᵐ x ∂μ, |t + x| ≤ |t| + b := by
    filter_upwards [habs] with x hx
    exact (abs_add_le _ _).trans (by linarith)
  have hXint : Integrable (fun x : ℝ => x) μ := integrable_bounded_real measurable_id habs
  have hsqint : Integrable (fun x : ℝ => x ^ 2) μ := integrable_bounded_square measurable_id habs
  have hfint : Integrable (fun x : ℝ => x * cappedCubic b τ z (t + x)) μ :=
    integrable_capped_product measurable_id (by fun_prop) habs b τ z
  have hGint : Integrable (fun x : ℝ => failureQuadratic τ z (t + x)) μ :=
    integrable_failureQuadratic (by fun_prop) hshift τ z
  have hpoint : ∀ᵐ x ∂μ,
      x * (cappedCubic b τ z (t + x) - cappedCubic b τ z t) ≤
        x ^ 2 * (∫ y, failureQuadratic τ z (t + y) ∂μ) := by
    filter_upwards [hsupport] with x hx
    have h := integral_mono_ae
      (integrable_const (x * (cappedCubic b τ z (t + x) - cappedCubic b τ z t)))
      (hGint.const_mul (x ^ 2)) ?_
    · simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
        one_smul, integral_const_mul] using h
    · filter_upwards [hsupport, habs] with y hy hyabs
      exact cappedCubic_test_pointwise hyabs
        (abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩)
  have hleftint : Integrable
      (fun x => x * (cappedCubic b τ z (t + x) - cappedCubic b τ z t)) μ := by
    convert hfint.sub (hXint.mul_const (cappedCubic b τ z t)) using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have h := integral_mono_ae hleftint
    (hsqint.mul_const (∫ y, failureQuadratic τ z (t + y) ∂μ)) hpoint
  simpa only [mul_sub, integral_sub hfint (hXint.mul_const _), integral_mul_const,
    hcenter, zero_mul, sub_zero] using h

theorem centered_coordinate_cubic_prod (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {a b C : ℝ} (ha : a ≤ 0) (hab : 0 ≤ a + b)
    (hsupport : ∀ᵐ x ∂μ, x ∈ Set.Icc a (a + b))
    (hcenter : ∫ x, x ∂μ = 0) (hT : ∀ᵐ t ∂ν, |t| ≤ C) (τ z : ℝ) :
    (∫ p : ℝ × ℝ, p.2 * cappedCubic b τ z (p.1 + p.2) ∂ν.prod μ) ≤
      (∫ x, x ^ 2 ∂μ) *
        (∫ p : ℝ × ℝ, failureQuadratic τ z (p.1 + p.2) ∂ν.prod μ) := by
  have habs : ∀ᵐ x ∂μ, |x| ≤ b := by
    filter_upwards [hsupport] with x hx
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxp : ∀ᵐ p : ℝ × ℝ ∂ν.prod μ, |p.2| ≤ b := by
    exact Measure.quasiMeasurePreserving_snd.ae habs
  have htp : ∀ᵐ p : ℝ × ℝ ∂ν.prod μ, |p.1| ≤ C := by
    exact Measure.quasiMeasurePreserving_fst.ae hT
  have hsum : ∀ᵐ p : ℝ × ℝ ∂ν.prod μ, |p.1 + p.2| ≤ C + b := by
    filter_upwards [htp, hxp] with p hp₁ hp₂
    exact (abs_add_le _ _).trans (by linarith)
  have hfint : Integrable (fun p : ℝ × ℝ => p.2 * cappedCubic b τ z (p.1 + p.2)) (ν.prod μ) :=
    integrable_capped_product measurable_snd (by fun_prop) hxp b τ z
  have hGint : Integrable (fun p : ℝ × ℝ => failureQuadratic τ z (p.1 + p.2)) (ν.prod μ) :=
    integrable_failureQuadratic (by fun_prop) hsum τ z
  rw [integral_prod _ hfint, integral_prod _ hGint, ← integral_const_mul]
  apply integral_mono_ae hfint.integral_prod_left
    (hGint.integral_prod_left.const_mul (∫ x, x ^ 2 ∂μ))
  exact Filter.Eventually.of_forall fun t => centered_coordinate_cubic μ ha hab hsupport hcenter τ z t

theorem centered_coordinate_cubic_indep {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X T : Ω → ℝ}
    (hX : Measurable X) (hT : Measurable T) (hXT : IndepFun X T μ)
    {a b C : ℝ} (ha : a ≤ 0) (hab : 0 ≤ a + b)
    (hsupport : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a (a + b))
    (hcenter : ∫ ω, X ω ∂μ = 0)
    (hTbound : ∀ᵐ ω ∂μ, |T ω| ≤ C) (τ z : ℝ) :
    (∫ ω, X ω * cappedCubic b τ z (T ω + X ω) ∂μ) ≤
      (∫ ω, X ω ^ 2 ∂μ) *
        (∫ ω, failureQuadratic τ z (T ω + X ω) ∂μ) := by
  have hsupport' : ∀ᵐ x ∂μ.map X, x ∈ Set.Icc a (a + b) :=
    (ae_map_iff hX.aemeasurable measurableSet_Icc).mpr hsupport
  have hcenter' : ∫ x, x ∂μ.map X = 0 := by
    calc
      _ = ∫ ω, X ω ∂μ := integral_map hX.aemeasurable (by fun_prop)
      _ = 0 := hcenter
  have hTbound' : ∀ᵐ t ∂μ.map T, |t| ≤ C := by
    apply (ae_map_iff hT.aemeasurable
      (measurableSet_le continuous_abs.measurable measurable_const)).mpr
    exact hTbound
  have htransport (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
      (∫ p, f p ∂(μ.map T).prod (μ.map X)) = ∫ ω, f (T ω, X ω) ∂μ := by
    rw [← hXT.symm.map_prod_eq_prod_map_map hT.aemeasurable hX.aemeasurable]
    exact integral_map (hT.prodMk hX).aemeasurable hf.aestronglyMeasurable
  have h := centered_coordinate_cubic_prod (μ.map X) (μ.map T)
    ha hab hsupport' hcenter' hTbound' τ z
  have hfmeas : Measurable (fun p : ℝ × ℝ => p.2 * cappedCubic b τ z (p.1 + p.2)) := by
    exact measurable_snd.mul ((continuous_cappedCubic b τ z).measurable.comp
      (show Measurable (fun p : ℝ × ℝ => p.1 + p.2) by fun_prop))
  have hGmeas : Measurable (fun p : ℝ × ℝ => failureQuadratic τ z (p.1 + p.2)) :=
    (measurable_failureQuadratic τ z).comp (by fun_prop)
  have hsqmap : (∫ x, x ^ 2 ∂μ.map X) = ∫ ω, X ω ^ 2 ∂μ :=
    integral_map hX.aemeasurable (by fun_prop)
  rw [htransport _ hfmeas, htransport _ hGmeas, hsqmap] at h
  exact h

theorem centered_interval_contains_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {a b : ℝ} (hsupport : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b)
    (hcenter : ∫ ω, X ω ∂μ = 0) : a ≤ 0 ∧ 0 ≤ b := by
  have hint : Integrable X μ := (memLp_of_bounded hsupport hX.aestronglyMeasurable 1).integrable le_rfl
  have hlo := integral_mono_ae (integrable_const a) hint (hsupport.mono fun _ h => h.1)
  have hhi := integral_mono_ae hint (integrable_const b) (hsupport.mono fun _ h => h.2)
  simpa only [integral_const, probReal_univ, one_smul, hcenter] using And.intro hlo hhi

theorem ae_abs_finset_sum_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (X : ι → Ω → ℝ) (s : Finset ι) {b : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b) :
    ∀ᵐ ω ∂μ, |∑ i ∈ s, X i ω| ≤ ∑ _i ∈ s, b := by
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hω i)

/-- The upper test-function inequality for any finite family of independent
centered random variables with intervals of length at most `b`. -/
theorem independent_sum_cubic_test {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {a : ι → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (a i + b))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) (τ z : ℝ) :
    (∫ ω, (∑ i, X i ω) * cappedCubic b τ z (∑ i, X i ω) ∂μ) ≤
      Var[(fun ω => ∑ i, X i ω); μ] *
        (∫ ω, failureQuadratic τ z (∑ i, X i ω) ∂μ) := by
  classical
  have hinterval (i : ι) := centered_interval_contains_zero (hX i) (hsupport i) (hcenter i)
  have habs (i : ι) : ∀ᵐ ω ∂μ, |X i ω| ≤ b := by
    filter_upwards [hsupport i] with ω hω
    exact abs_le.mpr ⟨by linarith [hω.1, (hinterval i).2],
      by linarith [hω.2, (hinterval i).1]⟩
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hLp (i : ι) : MemLp (X i) 2 μ :=
    memLp_of_bounded (hsupport i) (hX i).aestronglyMeasurable 2
  have hvar : Var[S; μ] = ∑ i, ∫ ω, X i ω ^ 2 ∂μ := by
    have hv := IndepFun.variance_sum (s := Finset.univ)
      (fun i _ => hLp i) (fun i _ j _ hij => hindep.indepFun hij)
    have hfun : (∑ i, X i) = S := by ext ω; simp [S]
    rw [hfun] at hv
    rw [hv]
    apply Finset.sum_congr rfl
    intro i _
    rw [variance_eq_integral (hX i).aemeasurable, hcenter i]
    simp only [sub_zero]
  have hcoord (i : ι) :
      (∫ ω, X i ω * cappedCubic b τ z (S ω) ∂μ) ≤
        (∫ ω, X i ω ^ 2 ∂μ) * (∫ ω, failureQuadratic τ z (S ω) ∂μ) := by
    let T : Ω → ℝ := fun ω => ∑ j ∈ Finset.univ.erase i, X j ω
    have hT : Measurable T := by dsimp [T]; fun_prop
    have hTi : IndepFun (X i) T μ := by
      have h := (hindep.indepFun_finsetSum_of_notMem hX (Finset.notMem_erase i Finset.univ)).symm
      have hTfun : (∑ j ∈ Finset.univ.erase i, X j) = T := by
        ext ω
        simp only [Finset.sum_apply, T]
      rwa [hTfun] at h
    have hsum : (fun ω => T ω + X i ω) = S := by
      funext ω
      dsimp [T, S]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
    have h := centered_coordinate_cubic_indep μ (hX i) hT hTi
      (hinterval i).1 (hinterval i).2 (hsupport i) (hcenter i)
      (ae_abs_finset_sum_le X (Finset.univ.erase i) habs) τ z
    simp_rw [show ∀ ω, T ω + X i ω = S ω from congrFun hsum] at h
    exact h
  have hints (i : ι) : Integrable (fun ω => X i ω * cappedCubic b τ z (S ω)) μ :=
    integrable_capped_product (hX i) hS (habs i) b τ z
  calc
    _ = ∑ i, ∫ ω, X i ω * cappedCubic b τ z (S ω) ∂μ := by
      simp_rw [S, Finset.sum_mul]
      exact integral_finsetSum Finset.univ (fun i _ => hints i)
    _ ≤ ∑ i, (∫ ω, X i ω ^ 2 ∂μ) * (∫ ω, failureQuadratic τ z (S ω) ∂μ) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by rw [← Finset.sum_mul, ← hvar]

/-- The full capped cubic inequality (manuscript Lemma 4.4), for arbitrary
measurable independent centered variables with bounded intervals of support.
The proof also covers zero variance and intervals of length zero. -/
theorem capped_cubic_inequality {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    {a : ι → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hsupport : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (a i + b))
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) {τ : ℝ} (hτ : 0 < τ) (z : ℝ) :
    (Var[(fun ω => ∑ i, X i ω); μ] + (max (z - b) 0) ^ 2 / 12) *
        (∫ ω, if (∑ i, X i ω) < τ then ((∑ i, X i ω) + z) ^ 2 else 0 ∂μ) ≥
      (max (τ + z - 2 * b) 0) ^ 3 / 3 *
        (∫ ω, if τ ≤ (∑ i, X i ω) then (∑ i, X i ω) else 0 ∂μ) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hinterval (i : ι) := centered_interval_contains_zero (hX i) (hsupport i) (hcenter i)
  have habs (i : ι) : ∀ᵐ ω ∂μ, |X i ω| ≤ b := by
    filter_upwards [hsupport i] with ω hω
    exact abs_le.mpr ⟨by linarith [hω.1, (hinterval i).2],
      by linarith [hω.2, (hinterval i).1]⟩
  have hSbound : ∀ᵐ ω ∂μ, |S ω| ≤ ∑ _i : ι, b := ae_abs_finset_sum_le X Finset.univ habs
  have hSint := integrable_bounded_real hS hSbound
  have hfint : Integrable (fun ω => S ω * cappedCubic b τ z (S ω)) μ :=
    integrable_capped_product hS hS hSbound b τ z
  have hGint : Integrable (fun ω => failureQuadratic τ z (S ω)) μ :=
    integrable_failureQuadratic hS hSbound τ z
  have hTailInt : Integrable (fun ω => if τ ≤ S ω then S ω else 0) μ := by
    convert hSint.indicator (s := {ω | τ ≤ S ω})
      (measurableSet_le measurable_const hS) using 1
    ext ω
    simp only [Set.indicator, Set.mem_setOf_eq]
  have hLeftInt : Integrable (fun ω =>
      (max (τ + z - 2 * b) 0) ^ 3 / 3 * (if τ ≤ S ω then S ω else 0) -
      (max (z - b) 0) ^ 2 / 12 * failureQuadratic τ z (S ω)) μ := by
    convert (hTailInt.const_mul ((max (τ + z - 2 * b) 0) ^ 3 / 3)).sub
      (hGint.const_mul ((max (z - b) 0) ^ 2 / 12)) using 1
  have hlow := integral_mono_ae hLeftInt hfint
    (Filter.Eventually.of_forall fun ω => cappedCubic_lower (w := S ω) hb hτ)
  rw [integral_sub (hTailInt.const_mul _) (hGint.const_mul _),
    integral_const_mul, integral_const_mul] at hlow
  have hupp := independent_sum_cubic_test μ X hX hindep hb hsupport hcenter τ z
  change (Var[S; μ] + (max (z - b) 0) ^ 2 / 12) *
      (∫ ω, failureQuadratic τ z (S ω) ∂μ) ≥
        (max (τ + z - 2 * b) 0) ^ 3 / 3 *
          (∫ ω, if τ ≤ S ω then S ω else 0 ∂μ)
  change (∫ ω, S ω * cappedCubic b τ z (S ω) ∂μ) ≤
    Var[S; μ] * (∫ ω, failureQuadratic τ z (S ω) ∂μ) at hupp
  nlinarith

end SharpTailMatching.Probability
