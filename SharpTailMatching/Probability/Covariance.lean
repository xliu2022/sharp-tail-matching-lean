module

public import SharpTailMatching.Probability.StopLoss

/-! # Covariance identities and the conditional variance bound -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem iid_integral_coordinate_sumFn (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (φ : ℝ≥0 → ℝ) (g : ℝ → ℝ) (i j : Fin k) :
    (∫ w : Fin k → ℝ≥0, φ (w i) * g (iidSum k w)
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
    (∫ w : Fin k → ℝ≥0, φ (w j) * g (iidSum k w)
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) := by
  let e := Equiv.swap j i
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ≥0) e
  have hsum (w : Fin k → ℝ≥0) : iidSum k (E w) = iidSum k w := by
    unfold iidSum
    rw [← Equiv.sum_comp e (fun l => (E w l : ℝ))]
    simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
  have hcoord (w : Fin k → ℝ≥0) : E w j = w i := by
    simpa [e, E] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin k => ℝ≥0) e w i
  have hp := measurePreserving_piCongrLeft (fun _ : Fin k => (μ : Measure ℝ≥0)) e
  have h := hp.integral_comp' (fun w : Fin k → ℝ≥0 => φ (w j) * g (iidSum k w))
  change (∫ w : Fin k → ℝ≥0, φ (E w j) * g (iidSum k (E w))
    ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = _ at h
  simpa only [hsum, hcoord] using h

theorem sum_mul_deficit_integral (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (hm : mean μ ≠ ∞) :
    (∫ w : Fin (n+1) → ℝ≥0, iidSum (n+1) w * max (1 - iidSum (n+1) w) 0
      ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      ((n+1 : ℕ) : ℝ) * ∫ z : ℝ≥0, (z : ℝ) * stopLoss n μ z ∂(μ : Measure ℝ≥0) := by
  have hdmeas : Measurable (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) := by
    unfold iidSum
    fun_prop
  have hcoord (i : Fin (n+1)) : Integrable
      (fun w : Fin (n+1) → ℝ≥0 => (w i : ℝ) * max (1 - iidSum (n+1) w) 0)
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) := by
    apply ((measurePreserving_eval (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) i).integrable_comp_of_integrable
      (integrable_coe_of_mean_ne_top μ hm)).mul_bdd (c := 1) hdmeas.aestronglyMeasurable
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := iidSum_nonneg (n+1) w; linarith) (by norm_num)
  have hfun : (fun w : Fin (n+1) → ℝ≥0 => iidSum (n+1) w * max (1 - iidSum (n+1) w) 0) =
      (fun w => ∑ i : Fin (n+1), (w i : ℝ) * max (1 - iidSum (n+1) w) 0) := by
    funext w
    exact Finset.sum_mul ..
  rw [hfun, integral_finsetSum _ (fun i _ => hcoord i)]
  have hs (i : Fin (n+1)) := iid_integral_coordinate_sumFn (n+1) μ (fun z => (z : ℝ))
    (fun s => max (1-s) 0) i 0
  simp_rw [hs]
  rw [← integral_mul_stopLoss n μ (fun z : ℝ≥0 => (z : ℝ)) (by fun_prop)
    (integrable_coe_of_mean_ne_top μ hm)]
  simp [nsmul_eq_mul]

theorem integral_sum_mul_deficit_eq (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) :
    (∫ w : Fin (n+1) → ℝ≥0, iidSum (n+1) w * max (1 - iidSum (n+1) w) 0
      ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) = failureDeficit n μ -
      ∫ w : Fin (n+1) → ℝ≥0, (max (1 - iidSum (n+1) w) 0)^2
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0)) := by
  have hmem : MemLp (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0) 2
      (Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) := by
    apply MemLp.of_bound (show Measurable (fun w : Fin (n+1) → ℝ≥0 => max (1 - iidSum (n+1) w) 0)
      from by unfold iidSum; fun_prop).aestronglyMeasurable 1
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := iidSum_nonneg (n+1) w; linarith) (by norm_num)
  have hpoint (w : Fin (n+1) → ℝ≥0) :
      iidSum (n+1) w * max (1 - iidSum (n+1) w) 0 =
        max (1 - iidSum (n+1) w) 0 - (max (1 - iidSum (n+1) w) 0)^2 := by
    by_cases hs : iidSum (n+1) w ≤ 1
    · rw [max_eq_left (sub_nonneg.mpr hs)]
      ring
    · simp [max_eq_right (sub_nonpos.mpr (le_of_not_ge hs))]
  simp_rw [hpoint]
  exact integral_sub (integrable_failure_deficit n μ) hmem.integrable_sq

theorem maximizer_stopLoss_covariance {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    ((n+1 : ℕ) : ℝ) * covariance (fun z : ℝ≥0 => (z : ℝ)) (stopLoss n μ) (μ : Measure ℝ≥0) =
      -(1 - tailProbability (n+1) μ) * (conditionalVariance n μ +
        conditionalDeficit n μ * failureExcessParameter n x μ) := by
  have hm := maximizer_mean_eq (by omega : 1 ≤ n+1) hx.le hxlt hμ
  have hmfin : mean μ ≠ ∞ := by rw [hm]; exact ENNReal.ofReal_ne_top
  have hmean : (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = x := by
    rw [integral_coe_eq_mean_toReal, hm, ENNReal.toReal_ofReal hx.le]
  have hp := (sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)).ne'
  have hsum := (sum_mul_deficit_integral n μ hmfin).symm.trans (integral_sum_mul_deficit_eq n μ)
  have hr : failureDeficit n μ = (1 - tailProbability (n+1) μ) * conditionalDeficit n μ := by
    dsimp [conditionalDeficit]
    field_simp
  have hv := maximizer_conditionalVariance_eq hx hxlt hμ
  have hsquare :
      (∫ w : Fin (n+1) → ℝ≥0, (max (1 - iidSum (n+1) w) 0)^2
        ∂Measure.pi (fun _ : Fin (n+1) => (μ : Measure ℝ≥0))) =
      (1 - tailProbability (n+1) μ) * (conditionalVariance n μ + (conditionalDeficit n μ)^2) := by
    rw [hv]
    field_simp
    ring
  rw [covariance_eq_sub (maximizer_memLp_coe hx hxlt hμ 2) (memLp_stopLoss n μ 2),
    hmean, integral_stopLoss]
  change ((n+1 : ℕ) : ℝ) *
      ((∫ z : ℝ≥0, (z : ℝ) * stopLoss n μ z ∂(μ : Measure ℝ≥0)) - x * failureDeficit n μ) = _
  rw [mul_sub, hsum, hsquare, hr]
  dsimp [failureExcessParameter]
  ring

theorem covariance_coe_monotone (μ : ProbabilityMeasure ℝ≥0) (g : ℝ≥0 → ℝ)
    (hX : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (μ : Measure ℝ≥0))
    (hg : MemLp g 2 (μ : Measure ℝ≥0)) (hmono : Monotone g) :
    0 ≤ covariance (fun z : ℝ≥0 => (z : ℝ)) g (μ : Measure ℝ≥0) := by
  let m : ℝ≥0 := ⟨∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0),
    integral_nonneg (fun z => z.coe_nonneg)⟩
  have hpoint (z : ℝ≥0) : ((z : ℝ) - (m : ℝ)) * (g z - g m) ≥ 0 := by
    by_cases hz : z ≤ m
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hz) (sub_nonpos.mpr (hmono hz))
    · exact mul_nonneg (sub_nonneg.mpr (le_of_not_ge hz)) (sub_nonneg.mpr (hmono (le_of_not_ge hz)))
  have hxint := hX.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hgint := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hmean : (∫ z : ℝ≥0, (z : ℝ) - (m : ℝ) ∂(μ : Measure ℝ≥0)) = 0 := by
    rw [integral_sub hxint (integrable_const _), integral_const, probReal_univ, one_smul]
    change (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) -
      (∫ z : ℝ≥0, (z : ℝ) ∂(μ : Measure ℝ≥0)) = 0
    ring
  have hcov := covariance_eq_sub (hX.sub (memLp_const (m : ℝ))) (hg.sub (memLp_const (g m)))
  change covariance (fun z : ℝ≥0 => (z : ℝ) - (m : ℝ)) (fun z => g z - g m) (μ : Measure ℝ≥0) =
    (∫ z : ℝ≥0, ((z : ℝ) - (m : ℝ)) * (g z - g m) ∂(μ : Measure ℝ≥0)) -
      (∫ z : ℝ≥0, (z : ℝ) - (m : ℝ) ∂(μ : Measure ℝ≥0)) *
        (∫ z : ℝ≥0, g z - g m ∂(μ : Measure ℝ≥0)) at hcov
  rw [hmean, zero_mul, sub_zero, covariance_sub_const_left hxint,
    covariance_sub_const_right hgint] at hcov
  rw [hcov]
  exact integral_nonneg hpoint

theorem maximizer_stopLoss_covariance_lower {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    -(1 - tailProbability n μ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) ≤
      covariance (fun z : ℝ≥0 => (z : ℝ)) (stopLoss n μ) (μ : Measure ℝ≥0) := by
  have hX := maximizer_memLp_coe hx hxlt hμ 2
  have hK := memLp_stopLoss n μ 2
  have h := covariance_coe_monotone μ _ hX (hK.add (hX.const_mul (1-tailProbability n μ)))
    (monotone_adjusted_stopLoss n μ)
  rw [covariance_add_right hX hK (hX.const_mul _), covariance_const_mul_right,
    covariance_self hX.aemeasurable] at h
  linarith

/-- The conditional variance estimate from the covariance argument. Its
conditional law, cutoff, deficit, and excess parameter are all derived from μ. -/
theorem maximizer_conditionalVariance_bound {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) :
    conditionalVariance n μ ≤ failureExcessParameter n x μ *
      (supportCutoff n x μ - conditionalDeficit n μ) := by
  have hk : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hp : 0 < 1 - tailProbability (n+1) μ :=
    sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  have hgap := (maximizer_tail_gap_pos hx hxlt hμ).ne'
  have hfirst := maximizer_stopLoss_covariance hx hxlt hμ
  have hlow := maximizer_stopLoss_covariance_lower hx hxlt hμ
  have hvar : ((n+1 : ℕ) : ℝ) * variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) =
      failureScale n x μ * failureExcessParameter n x μ := by
    rw [← variance_iidSum _ μ (maximizer_memLp_coe hx hxlt hμ 2), maximizer_variance_identity hx hxlt hμ]
  have hbridge : (1 - tailProbability n μ) * failureScale n x μ =
      (1 - tailProbability (n+1) μ) * supportCutoff n x μ := by
    dsimp [supportCutoff, failureScale]
    field_simp
  have hlowk : -(1 - tailProbability n μ) * (failureScale n x μ * failureExcessParameter n x μ) ≤
      ((n+1 : ℕ) : ℝ) * covariance (fun z : ℝ≥0 => (z : ℝ)) (stopLoss n μ) (μ : Measure ℝ≥0) := by
    calc
      _ = ((n+1 : ℕ) : ℝ) * (-(1 - tailProbability n μ) *
          variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0)) := by rw [← hvar]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hk.le
  rw [hfirst] at hlowk
  have hbridgeB := congrArg (fun t : ℝ => t * failureExcessParameter n x μ) hbridge
  have hscaled : (1 - tailProbability (n+1) μ) *
      (conditionalVariance n μ + conditionalDeficit n μ * failureExcessParameter n x μ) ≤
      (1 - tailProbability (n+1) μ) * (supportCutoff n x μ * failureExcessParameter n x μ) := by
    nlinarith
  have h := le_of_mul_le_mul_left hscaled hp
  nlinarith

theorem maximizer_conditionalDeficit_le_cutoff {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) : conditionalDeficit n μ ≤ supportCutoff n x μ := by
  have h := maximizer_conditionalVariance_bound hx hxlt hμ
  have hv : 0 ≤ conditionalVariance n μ := variance_nonneg _ _
  have hB := maximizer_failureExcessParameter_pos hx hxlt hμ
  nlinarith

end SharpTailMatching.Probability
