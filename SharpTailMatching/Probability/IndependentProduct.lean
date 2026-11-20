module

public import SharpTailMatching.Probability.ProductLimits
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Product bounds on probability spaces

This file connects finite independent distributions to measurable random
variables and constructs the upward finite-grid approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

namespace SharpTailMatching.Probability

namespace FiniteProduct

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}

def atomWeight (Y : ι → Ω → Fin (n+1)) (i : ι) (a : Fin (n+1)) : ℝ :=
  (μ.map (Y i)).real {a}

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ] in
theorem atomWeight_nonneg (Y : ι → Ω → Fin (n+1)) : ∀ i a, 0 ≤ atomWeight μ Y i a :=
  fun _ _ => ENNReal.toReal_nonneg

omit [Fintype ι] [DecidableEq ι] in
theorem atomWeight_total (Y : ι → Ω → Fin (n+1)) (i : ι) :
    ∑ a, atomWeight μ Y i a = 1 := by
  have h := integral_fintype (μ := μ.map (Y i))
    (Integrable.of_finite : Integrable (fun _ : Fin (n+1) => (1 : ℝ)) (μ.map (Y i)))
  simpa only [atomWeight, integral_const, probReal_univ, one_smul, smul_eq_mul, mul_one] using h.symm

/-- The exact expectation formula for any statistic of independent finite-valued
random variables. It follows from the product pushforward identity. -/
theorem integral_eq_expect (Y : ι → Ω → Fin (n+1))
    (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ)
    (f : (ι → Fin (n+1)) → ℝ) :
    (∫ ω, f (fun i => Y i ω) ∂μ) = expect (atomWeight μ Y) f := by
  have hmap : μ.map (fun ω i => Y i ω) = Measure.pi (fun i => μ.map (Y i)) :=
    hi.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)
  rw [← integral_map_of_stronglyMeasurable (Measurable.of_eval hY) (.of_discrete), hmap]
  rw [integral_fintype Integrable.of_finite]
  unfold expect weight atomWeight
  apply Finset.sum_congr rfl
  intro ω _
  simp only [smul_eq_mul, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]

omit [Fintype ι] [DecidableEq ι] in
theorem integral_coordinate_eq_mean (Y : ι → Ω → Fin (n+1))
    (hY : ∀ i, Measurable (Y i)) (v : ι → Fin (n+1) → ℝ) (i : ι) :
    (∫ ω, v i (Y i ω) ∂μ) = mean (atomWeight μ Y) v i := by
  rw [← integral_map_of_stronglyMeasurable (hY i) (.of_discrete),
    integral_fintype Integrable.of_finite]
  rfl

end FiniteProduct

namespace ProductBound

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]

def gridSize (M : ℝ) (q : ℕ) : ℕ := ⌈((q : ℝ) + 1) * M⌉₊

def roundIndex (q N : ℕ) (x : ℝ) : Fin (N+1) :=
  ⟨min ⌈((q : ℝ) + 1) * x⌉₊ N, Nat.lt_succ_of_le (min_le_right _ _)⟩

def gridValue (q : ℕ) {N : ℕ} (a : Fin (N+1)) : ℝ := (a : ℝ) / ((q : ℝ) + 1)

def roundUp (M : ℝ) (q : ℕ) (x : ℝ) : ℝ := gridValue q (roundIndex q (gridSize M q) x)

theorem measurable_roundIndex (q N : ℕ) : Measurable (roundIndex q N) := by
  have hnat : Measurable (fun x : ℝ => min ⌈((q : ℝ) + 1) * x⌉₊ N) :=
    (measurable_const.mul measurable_id).nat_ceil.min measurable_const
  apply measurable_to_countable'
  intro a
  convert hnat (measurableSet_singleton (a.val)) using 1
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, roundIndex]

theorem measurable_roundUp (M : ℝ) (q : ℕ) : Measurable (roundUp M q) :=
  Measurable.of_discrete.comp (measurable_roundIndex q (gridSize M q))

theorem gridValue_nonneg (q N : ℕ) (a : Fin (N+1)) : 0 ≤ gridValue q a := by
  unfold gridValue
  positivity

theorem gridValue_monotone (q N : ℕ) : Monotone (gridValue q : Fin (N+1) → ℝ) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hab

theorem roundUp_eq_ceil (M x : ℝ) (q : ℕ) (hxM : x ≤ M) :
    roundUp M q x = (⌈((q : ℝ) + 1) * x⌉₊ : ℝ) / ((q : ℝ) + 1) := by
  have hceil : ⌈((q : ℝ) + 1) * x⌉₊ ≤ gridSize M q := by
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left hxM (by positivity)
  simp only [roundUp, gridValue, roundIndex, min_eq_left hceil]

theorem roundUp_nonneg (M x : ℝ) (q : ℕ) : 0 ≤ roundUp M q x := gridValue_nonneg _ _ _

theorem le_roundUp (M x : ℝ) (q : ℕ) (hxM : x ≤ M) : x ≤ roundUp M q x := by
  rw [roundUp_eq_ceil M x q hxM]
  apply (le_div_iff₀ (by positivity)).mpr
  simpa only [mul_comm x] using Nat.le_ceil (((q : ℝ) + 1) * x)

theorem roundUp_le (M x : ℝ) (q : ℕ) (hx : 0 ≤ x) (hxM : x ≤ M) :
    roundUp M q x ≤ x + 1 / ((q : ℝ) + 1) := by
  rw [roundUp_eq_ceil M x q hxM]
  apply (div_le_iff₀ (by positivity)).mpr
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ ((q : ℝ) + 1) * x by positivity)).le
  have hden : (x + 1 / ((q : ℝ) + 1)) * ((q : ℝ) + 1) = ((q : ℝ) + 1) * x + 1 := by
    field_simp
  rw [hden]
  exact hc

theorem roundUp_tendsto (M x : ℝ) (hx : 0 ≤ x) (hxM : x ≤ M) :
    Tendsto (fun q => roundUp M q x) atTop (𝓝 x) := by
  have hu : Tendsto (fun q : ℕ => x + 1 / ((q : ℝ) + 1)) atTop (𝓝 x) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := x)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun q => le_roundUp M x q hxM) (fun q => roundUp_le M x q hx hxM)

theorem roundUp_bound (M x : ℝ) (hM : 0 ≤ M) (q : ℕ) : roundUp M q x ≤ M + 1 := by
  have hindex : (roundIndex q (gridSize M q) x).val ≤ gridSize M q := min_le_right _ _
  have hle : roundUp M q x ≤ roundUp M q M := by
    rw [roundUp_eq_ceil M M q le_rfl]
    apply div_le_div_of_nonneg_right _ (by positivity)
    change ((roundIndex q (gridSize M q) x).val : ℝ) ≤ (gridSize M q : ℝ)
    exact Nat.cast_le.mpr hindex
  have hε : 1 / ((q : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) q]
  exact hle.trans ((roundUp_le M M q hM le_rfl).trans (by linarith))

theorem measurable_failureIndicator : Measurable FiniteProduct.failureIndicator := by
  change Measurable ((Set.Iio (1 : ℝ)).indicator (fun _ => (1 : ℝ)))
  exact measurable_const.indicator measurableSet_Iio

theorem failureIndicator_tendsto_of_above (sN : ℕ → ℝ) (s : ℝ)
    (hs : Tendsto sN atTop (𝓝 s)) (habove : ∀ n, s ≤ sN n) :
    Tendsto (fun n => FiniteProduct.failureIndicator (sN n)) atTop
      (𝓝 (FiniteProduct.failureIndicator s)) := by
  by_cases h : s < 1
  · rw [FiniteProduct.failureIndicator, ite_eq_left h]
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp hs).2 1 h] with n hn
    simp only [FiniteProduct.failureIndicator, ite_eq_left hn]
  · have hN (n) : ¬ sN n < 1 := by linarith [habove n]
    simpa only [FiniteProduct.failureIndicator, ite_eq_right h, ite_eq_right (hN _)] using
      (tendsto_const_nhds (x := (0 : ℝ)) (f := atTop))

def total (X : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, X i ω

def failureProbability (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  ∫ ω, FiniteProduct.failureIndicator (total X ω) ∂μ

def positiveDeficit (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  ∫ ω, max (1 - total X ω) 0 ∂μ

def conditionalDeficit (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  positiveDeficit μ X / failureProbability μ X

def balance (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  conditionalDeficit μ X - 1 + ∑ i, ∫ ω, X i ω ∂μ

omit [DecidableEq ι] in
theorem failureProbability_eq_measure (μ : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) :
    failureProbability μ X = μ.real {ω | total X ω < 1} := by
  have hs : MeasurableSet {ω | total X ω < 1} :=
    measurableSet_lt (Finset.measurable_sum Finset.univ (fun i _ => hX i)) measurable_const
  change (∫ ω, Set.indicator {ω | total X ω < 1} (fun _ => (1 : ℝ)) ω ∂μ) = _
  exact integral_indicator_one hs

/-- Applying the finite-distribution result to independent finite-valued
random variables gives a theorem about their actual expectations. -/
theorem finite_grid_product_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (Y : ι → Ω → Fin (n+1)) (v : ι → Fin (n+1) → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ)
    (hvmono : ∀ i, Monotone (v i)) (hv : ∀ i a, 0 ≤ v i a)
    (hp : 0 < failureProbability μ (fun i ω => v i (Y i ω)))
    (hr : 0 < conditionalDeficit μ (fun i ω => v i (Y i ω)))
    (hm : ∀ i, (∫ ω, v i (Y i ω) ∂μ) < conditionalDeficit μ (fun i ω => v i (Y i ω))) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ ∫ ω, v i (Y i ω) ∂μ) ∧
      (∑ i, z i = balance μ (fun i ω => v i (Y i ω))) ∧
      (∏ i, (1 - z i / conditionalDeficit μ (fun i ω => v i (Y i ω)))) ≤
        failureProbability μ (fun i ω => v i (Y i ω)) := by
  let w := FiniteProduct.atomWeight μ Y
  have hfailure : failureProbability μ (fun i ω => v i (Y i ω)) = FiniteProduct.failure w v :=
    FiniteProduct.integral_eq_expect μ Y hY hi
      (fun z => FiniteProduct.failureIndicator (FiniteProduct.total v z))
  have hdef : positiveDeficit μ (fun i ω => v i (Y i ω)) = FiniteProduct.positiveDeficit w v :=
    FiniteProduct.integral_eq_expect μ Y hY hi (fun z => max (1 - FiniteProduct.total v z) 0)
  have hrval : conditionalDeficit μ (fun i ω => v i (Y i ω)) = FiniteProduct.conditionalDeficit w v := by
    unfold conditionalDeficit FiniteProduct.conditionalDeficit
    rw [hdef, hfailure]
  have hmval (i) : (∫ ω, v i (Y i ω) ∂μ) = FiniteProduct.mean w v i :=
    FiniteProduct.integral_coordinate_eq_mean μ Y hY v i
  have hbalance : balance μ (fun i ω => v i (Y i ω)) = FiniteProduct.balance w v := by
    simp only [balance, hrval, hmval, FiniteProduct.balance]
  simp only [hrval, hfailure, hmval, hbalance] at hp hr hm ⊢
  exact FiniteProduct.finite_product_bound_nonnegative w v
    (FiniteProduct.atomWeight_nonneg μ Y) (FiniteProduct.atomWeight_total μ Y)
    hvmono hv hp hr hm

omit [MeasurableSpace Ω] [DecidableEq ι] in
theorem total_roundUp_tendsto (X : ι → Ω → ℝ) (M : ℝ) (ω : Ω)
    (hX : ∀ i, 0 ≤ X i ω ∧ X i ω ≤ M) :
    Tendsto (fun q => total (fun i ω => roundUp M q (X i ω)) ω) atTop (𝓝 (total X ω)) :=
  tendsto_finsetSum Finset.univ (fun i _ => roundUp_tendsto M (X i ω) (hX i).1 (hX i).2)

theorem integral_roundUp_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ M) :
    Tendsto (fun q => ∫ ω, roundUp M q (X ω) ∂μ) atTop (𝓝 (∫ ω, X ω ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M + 1)
  · intro q
    exact ((measurable_roundUp M q).comp hX).aestronglyMeasurable
  · exact integrable_const _
  · intro q
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (roundUp_nonneg M (X ω) q)]
      exact roundUp_bound M (X ω) hM q)
  · filter_upwards [hbound] with ω hω
    exact roundUp_tendsto M (X ω) hω.1 hω.2

omit [DecidableEq ι] in
theorem failureProbability_roundUp_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (M : ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M) :
    Tendsto (fun q => failureProbability μ (fun i ω => roundUp M q (X i ω)))
      atTop (𝓝 (failureProbability μ X)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro q
    apply Measurable.aestronglyMeasurable
    apply measurable_failureIndicator.comp
    exact Finset.measurable_sum Finset.univ
      (fun i _ => (measurable_roundUp M q).comp (hX i))
  · exact integrable_const _
  · intro q
    apply Filter.Eventually.of_forall
    intro ω
    unfold FiniteProduct.failureIndicator
    split_ifs <;> norm_num
  · have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω ∧ X i ω ≤ M := ae_all_iff.mpr hbound
    filter_upwards [hall] with ω hω
    apply failureIndicator_tendsto_of_above _ _ (total_roundUp_tendsto X M ω hω)
    intro q
    exact Finset.sum_le_sum (fun i _ => le_roundUp M (X i ω) q (hω i).2)

omit [DecidableEq ι] in
theorem positiveDeficit_roundUp_tendsto (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (M : ℝ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M) :
    Tendsto (fun q => positiveDeficit μ (fun i ω => roundUp M q (X i ω)))
      atTop (𝓝 (positiveDeficit μ X)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro q
    apply Measurable.aestronglyMeasurable
    apply Measurable.max _ measurable_const
    apply Measurable.sub measurable_const
    exact Finset.measurable_sum Finset.univ
      (fun i _ => (measurable_roundUp M q).comp (hX i))
  · exact integrable_const _
  · intro q
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    apply max_le
    · have hs : 0 ≤ total (fun i ω => roundUp M q (X i ω)) ω :=
        Finset.sum_nonneg (fun i _ => roundUp_nonneg M (X i ω) q)
      linarith
    · norm_num
  · have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω ∧ X i ω ≤ M := ae_all_iff.mpr hbound
    filter_upwards [hall] with ω hω
    exact (tendsto_const_nhds.sub (total_roundUp_tendsto X M ω hω)).max tendsto_const_nhds

/-- Failure-probability product bound for independent bounded nonnegative
random variables on an arbitrary probability space. The finite capping
argument and passage from upward grid approximations are both proved. -/
theorem bounded_independent_product_bound [Nonempty ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (hp : 0 < failureProbability μ X)
    (hm : ∀ i, (∫ ω, X i ω ∂μ) < conditionalDeficit μ X) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ ∫ ω, X i ω ∂μ) ∧
      (∑ i, z i = balance μ X) ∧
      (∏ i, (1 - z i / conditionalDeficit μ X)) ≤ failureProbability μ X := by
  classical
  let XR : ℕ → ι → Ω → ℝ := fun q i ω => roundUp M q (X i ω)
  have hr : 0 < conditionalDeficit μ X := by
    let i : ι := Classical.choice inferInstance
    have hnonneg : 0 ≤ ∫ ω, X i ω ∂μ :=
      integral_nonneg_of_ae ((hbound i).mono (fun _ h => h.1))
    exact hnonneg.trans_lt (hm i)
  have hplim : Tendsto (fun q => failureProbability μ (XR q)) atTop (𝓝 (failureProbability μ X)) :=
    failureProbability_roundUp_tendsto μ X hX M hbound
  have hdeflim : Tendsto (fun q => positiveDeficit μ (XR q)) atTop (𝓝 (positiveDeficit μ X)) :=
    positiveDeficit_roundUp_tendsto μ X hX M hbound
  have hrlim : Tendsto (fun q => conditionalDeficit μ (XR q)) atTop (𝓝 (conditionalDeficit μ X)) :=
    hdeflim.div hplim (ne_of_gt hp)
  have hmlim (i : ι) : Tendsto (fun q => ∫ ω, XR q i ω ∂μ) atTop (𝓝 (∫ ω, X i ω ∂μ)) :=
    integral_roundUp_tendsto μ (X i) (hX i) M hM (hbound i)
  have hBlim : Tendsto (fun q => balance μ (XR q)) atTop (𝓝 (balance μ X)) :=
    (hrlim.sub_const 1).add (tendsto_finsetSum Finset.univ (fun i _ => hmlim i))
  apply product_certificate_limit
    (fun q => failureProbability μ (XR q)) (fun q => conditionalDeficit μ (XR q))
    (fun q => balance μ (XR q)) (fun q i => ∫ ω, XR q i ω ∂μ)
    (failureProbability μ X) (conditionalDeficit μ X) (balance μ X) (fun i => ∫ ω, X i ω ∂μ)
    (ne_of_gt hr) hplim hrlim hBlim hmlim
  have hposp : ∀ᶠ q in atTop, 0 < failureProbability μ (XR q) :=
    tendsto_const_nhds.eventually_lt hplim hp
  have hposr : ∀ᶠ q in atTop, 0 < conditionalDeficit μ (XR q) :=
    tendsto_const_nhds.eventually_lt hrlim hr
  have hstrict : ∀ᶠ q in atTop, ∀ i, (∫ ω, XR q i ω ∂μ) < conditionalDeficit μ (XR q) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hmlim i).eventually_lt hrlim (hm i)
  filter_upwards [hposp, hposr, hstrict] with q hpq hrq hmq
  let Y : ι → Ω → Fin (gridSize M q + 1) := fun i ω => roundIndex q (gridSize M q) (X i ω)
  have hY (i : ι) : Measurable (Y i) := (measurable_roundIndex q (gridSize M q)).comp (hX i)
  have hYind : iIndepFun Y μ := hi.comp (fun _ => roundIndex q (gridSize M q))
    (fun _ => measurable_roundIndex q (gridSize M q))
  exact finite_grid_product_bound μ Y (fun _ => gridValue q) hY hYind
    (fun _ => gridValue_monotone q (gridSize M q))
    (fun _ => gridValue_nonneg q (gridSize M q)) hpq hrq hmq

end ProductBound

end SharpTailMatching.Probability
