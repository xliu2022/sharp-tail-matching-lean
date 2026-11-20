module

public import SharpTailMatching.Probability.LowerTailMoments
public import SharpTailMatching.Probability.LowerPositive

/-! # The cubic estimate for the actual sum of lower observations -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem iid_capped_cubic_inequality (k : ℕ) (L : ProbabilityMeasure ℝ≥0)
    {x₀ b τ : ℝ} (hb : 0 ≤ b)
    (hLb : ∀ᵐ z : ℝ≥0 ∂(L : Measure ℝ≥0), (z : ℝ) ≤ b)
    (hmean : (∫z : ℝ≥0,(z : ℝ) ∂(L : Measure ℝ≥0)) = x₀) (hτ : 0 < τ) (z : ℝ) :
    ((k : ℝ)*variance (fun t : ℝ≥0 => (t : ℝ)) (L : Measure ℝ≥0)+(max (z-b) 0)^2/12)*
      (∫w,if centeredSum k x₀ w < τ then (centeredSum k x₀ w+z)^2 else 0
        ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) ≥
      (max (τ+z-2*b) 0)^3/3*
        (∫w,if τ ≤ centeredSum k x₀ w then centeredSum k x₀ w else 0
          ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) := by
  let X : Fin k → (Fin k → ℝ≥0) → ℝ := fun i w => (w i : ℝ)-x₀
  have hX (i : Fin k) : Measurable (X i) := by dsimp [X]; fun_prop
  have hindep : iIndepFun X (Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) :=
    iIndepFun_pi (X := fun _ : Fin k => fun t : ℝ≥0 => (t : ℝ)-x₀) (fun _ => by fun_prop)
  have hsupport (i : Fin k) : ∀ᵐ w ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0)),
      X i w ∈ Set.Icc (-x₀) (-x₀+b) := by
    filter_upwards [(measurePreserving_eval (fun _ : Fin k => (L : Measure ℝ≥0)) i).quasiMeasurePreserving.ae hLb]
      with w hw
    exact ⟨by dsimp [X]; have := (w i).coe_nonneg; linarith,by dsimp [X]; linarith⟩
  have hL2 := memLp_coe_of_ae_le L hLb 2
  have hcenter (i : Fin k) : (∫w,X i w ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) = 0 := by
    have hi := integral_comp_eval (μ := fun _ : Fin k => (L : Measure ℝ≥0)) (i := i)
      (f := fun t : ℝ≥0 => (t : ℝ)-x₀) (by fun_prop)
    change (∫w,(w i : ℝ)-x₀ ∂Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) = 0
    rw [hi,integral_sub (hL2.integrable one_le_two) (integrable_const _),hmean,
      integral_const,probReal_univ,one_smul,sub_self]
  have h := capped_cubic_inequality (Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0)))
    X hX hindep hb hsupport hcenter hτ z
  have hsum (w : Fin k → ℝ≥0) : ∑i,X i w = centeredSum k x₀ w := by
    simp [X,centeredSum,iidSum,Finset.sum_sub_distrib,nsmul_eq_mul]
  simp_rw [hsum] at h
  have hvar : variance (centeredSum k x₀) (Measure.pi (fun _ : Fin k => (L : Measure ℝ≥0))) =
      (k : ℝ)*variance (fun t : ℝ≥0 => (t : ℝ)) (L : Measure ℝ≥0) := by
    change variance (fun w : Fin k → ℝ≥0 => iidSum k w-(k : ℝ)*x₀) _ = _
    rw [variance_sub_const (show Measurable (iidSum k) from by unfold iidSum; fun_prop).aestronglyMeasurable,
      variance_iidSum k L hL2]
  rwa [hvar] at h

theorem lower_cubic_integrals (n : ℕ) (μ L : ProbabilityMeasure ℝ≥0) (x₀ : ℝ) :
    (∫w,if centeredSum (n+1) x₀ w < 1-((n+1 : ℕ) : ℝ)*x₀ then
      (centeredSum (n+1) x₀ w+(conditionalDeficit n μ-(1-((n+1 : ℕ) : ℝ)*x₀)))^2 else 0
        ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) = lowerFailureQuadratic n μ L ∧
    (∫w,if 1-((n+1 : ℕ) : ℝ)*x₀ ≤ centeredSum (n+1) x₀ w then centeredSum (n+1) x₀ w else 0
        ∂Measure.pi (fun _ : Fin (n+1) => (L : Measure ℝ≥0))) = lowerTailFirstMoment n x₀ L := by
  have hevent (w : Fin (n+1) → ℝ≥0) : centeredSum (n+1) x₀ w < 1-((n+1 : ℕ) : ℝ)*x₀ ↔
      ∑i,w i < 1 := by
    have hR : iidSum (n+1) w < 1 ↔ ∑i,w i < 1 := by unfold iidSum; norm_cast
    change iidSum (n+1) w-((n+1 : ℕ) : ℝ)*x₀ < 1-((n+1 : ℕ) : ℝ)*x₀ ↔ _
    rw [sub_lt_sub_iff_right]
    exact hR
  constructor
  · rw [lowerFailureQuadratic,← integral_indicator (by measurability)]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : ∑i,w i < 1
    · simp only [ite_eq_left ((hevent w).mpr hw),Set.indicator_of_mem (s := {w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1}) hw]
      unfold centeredSum
      ring
    · simp only [ite_eq_right (not_congr (hevent w) |>.mpr hw),Set.indicator_of_notMem (s := {w : Fin (n+1) → ℝ≥0 | ∑i,w i < 1}) hw]
  · rw [lowerTailFirstMoment,← integral_indicator (by measurability)]
    apply integral_congr_ae
    filter_upwards [] with w
    by_cases hw : ∑i,w i < 1
    · have hnot : ¬1-((n+1 : ℕ) : ℝ)*x₀ ≤ centeredSum (n+1) x₀ w :=
        not_le.mpr ((hevent w).mpr hw)
      simp only [ite_eq_right hnot,Set.indicator_of_notMem (s := {w : Fin (n+1) → ℝ≥0 | 1 ≤ ∑i,w i}) (not_le.mpr hw)]
    · have hyes : 1-((n+1 : ℕ) : ℝ)*x₀ ≤ centeredSum (n+1) x₀ w :=
        le_of_not_gt ((not_congr (hevent w)).mpr hw)
      simp only [ite_eq_left hyes,Set.indicator_of_mem (s := {w : Fin (n+1) → ℝ≥0 | 1 ≤ ∑i,w i}) (le_of_not_gt hw)]

/-- The lower-sum cubic inequality with its failure quadratic controlled by
the full mixture's actual conditional variance. -/
theorem maximizer_lower_cubic_bound {n : ℕ} {x q x₀ : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq : 0 ≤ q)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ t ∂(L : Measure ℝ≥0), t ≤ b)
    (hUb : ∀ᵐ t ∂(U : Measure ℝ≥0), b < t)
    (hmean : (∫t : ℝ≥0,(t : ℝ) ∂(L : Measure ℝ≥0)) = x₀)
    (hδ : 0 < 1-((n+1 : ℕ) : ℝ)*x₀) :
    (((n+1 : ℕ) : ℝ)*variance (fun t : ℝ≥0 => (t : ℝ)) (L : Measure ℝ≥0)+
      (max (conditionalDeficit n μ-(1-((n+1 : ℕ) : ℝ)*x₀)-(b : ℝ)) 0)^2/12)*conditionalVariance n μ ≥
      (max (conditionalDeficit n μ-2*(b : ℝ)) 0)^3/3*
        (q^(n+1)/(1-tailProbability (n+1) μ)*lowerTailFirstMoment n x₀ L) := by
  have hLreal : ∀ᵐ t : ℝ≥0 ∂(L : Measure ℝ≥0), (t : ℝ) ≤ (b : ℝ) := hLb
  have hc := iid_capped_cubic_inequality (n+1) L b.coe_nonneg hLreal hmean hδ
    (conditionalDeficit n μ-(1-((n+1 : ℕ) : ℝ)*x₀))
  rw [(lower_cubic_integrals n μ L x₀).1,(lower_cubic_integrals n μ L x₀).2] at hc
  have harg : 1-((n+1 : ℕ) : ℝ)*x₀+(conditionalDeficit n μ-(1-((n+1 : ℕ) : ℝ)*x₀))-2*(b : ℝ) =
      conditionalDeficit n μ-2*(b : ℝ) := by ring
  rw [harg] at hc
  have hQ := allLower_failure_quadratic_le hx hxlt hμ hq hmix hLb hUb
  have hp := sub_pos.mpr (tailProbability_lt_one (by omega) hx.le hxlt μ hμ.1)
  have hdiv : q^(n+1)/(1-tailProbability (n+1) μ)*lowerFailureQuadratic n μ L ≤ conditionalVariance n μ := by
    apply (mul_le_mul_iff_right₀ hp).mp
    have heq : (1-tailProbability (n+1) μ)*(q^(n+1)/(1-tailProbability (n+1) μ)*lowerFailureQuadratic n μ L) =
        q^(n+1)*lowerFailureQuadratic n μ L := by field_simp
    rw [heq]
    nlinarith [hQ]
  have hcoef : 0 ≤ ((n+1 : ℕ) : ℝ)*variance (fun t : ℝ≥0 => (t : ℝ)) (L : Measure ℝ≥0)+
      (max (conditionalDeficit n μ-(1-((n+1 : ℕ) : ℝ)*x₀)-(b : ℝ)) 0)^2/12 := by
    have hv := variance_nonneg (fun t : ℝ≥0 => (t : ℝ)) (L : Measure ℝ≥0)
    positivity
  have h1 := mul_le_mul_of_nonneg_left hdiv hcoef
  have h2 := mul_le_mul_of_nonneg_left hc (div_nonneg (pow_nonneg hq (n+1)) hp.le)
  nlinarith [h1,h2]

end SharpTailMatching.Probability
