module

public import SharpTailMatching.Probability.MixtureMoments

/-! # Retaining the two cross-component contributions to covariance -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem mixture_cross_measure_le {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q : ℝ} (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U) :
    (ENNReal.ofReal q * ENNReal.ofReal (1-q)) • L.prod U +
      (ENNReal.ofReal q * ENNReal.ofReal (1-q)) • U.prod L ≤ μ.prod μ := by
  calc
    _ ≤ ((ENNReal.ofReal q * ENNReal.ofReal (1-q)) • L.prod U +
        (ENNReal.ofReal q * ENNReal.ofReal (1-q)) • U.prod L) +
        ((ENNReal.ofReal q * ENNReal.ofReal q) • L.prod L +
          (ENNReal.ofReal (1-q) * ENNReal.ofReal (1-q)) • U.prod U) :=
      by
        intro s
        simp only [Measure.add_apply]
        exact le_add_of_nonneg_right zero_le
    _ = _ := by
      rw [hmix]
      simp only [Measure.add_prod, Measure.prod_add, Measure.prod_smul_left,
        Measure.prod_smul_right, smul_add, smul_smul]
      rw [mul_comm (ENNReal.ofReal (1-q)) (ENNReal.ofReal q)]
      abel

theorem mixture_pair_integral_ge_cross {Ω : Type*} [MeasurableSpace Ω]
    (μ L U : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure L] [IsProbabilityMeasure U]
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : μ = ENNReal.ofReal q • L + ENNReal.ofReal (1-q) • U)
    (f : Ω × Ω → ℝ) (hf : Integrable f (μ.prod μ))
    (hnonneg : ∀ z, 0 ≤ f z) (hsymm : ∀ z, f z.swap = f z) :
    2*q*(1-q)*(∫ z, f z ∂L.prod U) ≤ ∫ z, f z ∂μ.prod μ := by
  have hcross := mixture_cross_measure_le μ L U hmix
  have hint := hf.mono_measure hcross
  have h := integral_mono_measure hcross (ae_of_all _ hnonneg) hf
  rw [integral_add_measure hint.left_of_add_measure hint.right_of_add_measure,
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (sub_nonneg.mpr hq1)] at h
  have hswap : (∫ z, f z ∂U.prod L) = ∫ z, f z ∂L.prod U := by
    simpa only [hsymm] using (integral_prod_swap (μ := L) (ν := U) f)
  rw [hswap] at h
  simpa only [smul_eq_mul] using h.trans_eq (by rfl) |>.trans' (by ring_nf; rfl)

def covariancePair (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0 × ℝ≥0) : ℝ :=
  ((z.1 : ℝ)-(z.2 : ℝ)) * (stopLoss n μ z.1-stopLoss n μ z.2 +
    (1-tailProbability n μ)*((z.1 : ℝ)-(z.2 : ℝ)))

theorem covariancePair_nonneg (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0 × ℝ≥0) :
    0 ≤ covariancePair n μ z := by
  have hmono := monotone_adjusted_stopLoss n μ
  by_cases hz : z.1 ≤ z.2
  · apply mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (show (z.1 : ℝ) ≤ z.2 from hz))
    have h := hmono hz
    dsimp only at h
    nlinarith
  · apply mul_nonneg (sub_nonneg.mpr (show (z.2 : ℝ) ≤ z.1 from le_of_not_ge hz))
    have h := hmono (le_of_not_ge hz)
    dsimp only at h
    nlinarith

theorem covariancePair_swap (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0 × ℝ≥0) :
    covariancePair n μ z.swap = covariancePair n μ z := by unfold covariancePair; simp only [Prod.swap]; ring

theorem integrable_covariancePair (n : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hX : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (μ : Measure ℝ≥0)) :
    Integrable (covariancePair n μ) ((μ : Measure ℝ≥0).prod (μ : Measure ℝ≥0)) := by
  let g : ℝ≥0 → ℝ := fun z => stopLoss n μ z + (1-tailProbability n μ)*(z : ℝ)
  have hg : MemLp g 2 (μ : Measure ℝ≥0) := (memLp_stopLoss n μ 2).add (hX.const_mul _)
  have h := ((hX.comp_fst (μ : Measure ℝ≥0)).sub (hX.comp_snd (μ : Measure ℝ≥0))).integrable_mul
    ((hg.comp_fst (μ : Measure ℝ≥0)).sub (hg.comp_snd (μ : Measure ℝ≥0)))
  apply h.congr
  filter_upwards [] with z
  dsimp [g, covariancePair]
  ring

theorem maximizer_covarianceRemainder_cross {n : ℕ} {x q : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmix : (μ : Measure ℝ≥0) = ENNReal.ofReal q • (L : Measure ℝ≥0) +
      ENNReal.ofReal (1-q) • (U : Measure ℝ≥0)) :
    2*q*(1-q)*(∫ z, covariancePair n μ z ∂(L : Measure ℝ≥0).prod (U : Measure ℝ≥0)) ≤
      covarianceRemainder n μ :=
  mixture_pair_integral_ge_cross (μ : Measure ℝ≥0) (L : Measure ℝ≥0) (U : Measure ℝ≥0)
    hq0 hq1 hmix (covariancePair n μ)
    (integrable_covariancePair n μ (maximizer_memLp_coe hx hxlt hμ 2))
    (covariancePair_nonneg n μ) (covariancePair_swap n μ)

theorem memLp_stopLoss_on (n : ℕ) (μ ν : ProbabilityMeasure ℝ≥0) (p : ℝ≥0∞) :
    MemLp (stopLoss n μ) p (ν : Measure ℝ≥0) := by
  apply MemLp.of_bound (measurable_stopLoss n μ).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (stopLoss_bounds n μ z).1]
  exact (stopLoss_bounds n μ z).2

theorem integrable_covariancePair_mixed (n : ℕ) (μ L U : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0)) :
    Integrable (covariancePair n μ) ((L : Measure ℝ≥0).prod (U : Measure ℝ≥0)) := by
  let g : ℝ≥0 → ℝ := fun z => stopLoss n μ z+(1-tailProbability n μ)*(z : ℝ)
  have hgL : MemLp g 2 (L : Measure ℝ≥0) := (memLp_stopLoss_on n μ L 2).add (hL.const_mul _)
  have hgU : MemLp g 2 (U : Measure ℝ≥0) := (memLp_stopLoss_on n μ U 2).add (hU.const_mul _)
  have h := ((hL.comp_fst (U : Measure ℝ≥0)).sub (hU.comp_snd (L : Measure ℝ≥0))).integrable_mul
    ((hgL.comp_fst (U : Measure ℝ≥0)).sub (hgU.comp_snd (L : Measure ℝ≥0)))
  apply h.congr
  filter_upwards [] with z
  dsimp [g, covariancePair]
  ring

theorem maximizer_cross_integral_lower {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n+1 : ℕ) : ℝ)⁻¹) {μ L U : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n+1) x μ)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0))
    {b : ℝ≥0} (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z ∂(U : Measure ℝ≥0), b ≤ z)
    (hcontact : sectionTail n μ b = tailProbability n μ+
      ((tailProbability (n+1) μ-tailProbability n μ)/x)*(b : ℝ)) :
    ((1-tailProbability (n+1) μ)*(b : ℝ)/failureScale n x μ) *
      (∫ z : ℝ≥0 × ℝ≥0, ((z.2 : ℝ)-(z.1 : ℝ))*((z.2 : ℝ)-(b : ℝ))
        ∂(L : Measure ℝ≥0).prod (U : Measure ℝ≥0)) ≤
      ∫ z, covariancePair n μ z ∂(L : Measure ℝ≥0).prod (U : Measure ℝ≥0) := by
  have hdiff : MemLp (fun z : ℝ≥0 × ℝ≥0 => (z.2 : ℝ)-(z.1 : ℝ)) 2
      ((L : Measure ℝ≥0).prod (U : Measure ℝ≥0)) :=
    (hU.comp_snd (L : Measure ℝ≥0)).sub (hL.comp_fst (U : Measure ℝ≥0))
  have hprod : Integrable (fun z : ℝ≥0 × ℝ≥0 => ((z.2 : ℝ)-(z.1 : ℝ))*((z.2 : ℝ)-(b : ℝ)))
      ((L : Measure ℝ≥0).prod (U : Measure ℝ≥0)) :=
    hdiff.integrable_mul ((hU.comp_snd (L : Measure ℝ≥0)).sub (memLp_const (b : ℝ)))
  rw [← integral_const_mul]
  apply integral_mono_ae (hprod.const_mul _) (integrable_covariancePair_mixed n μ L U hL hU)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hLb,
    Measure.quasiMeasurePreserving_snd.ae hUb] with z hzL hzU
  simpa only [covariancePair, mul_assoc] using maximizer_contact_pair_cross_lower hx hxlt hμ hzL hzU hcontact

theorem integral_lt_of_ae_lt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : ∀ᵐ z ∂μ, f z < g z) :
    (∫ z, f z ∂μ) < ∫ z, g z ∂μ := by
  have hpos : ∀ᵐ z ∂μ, 0 < g z-f z := hfg.mono (fun _ h => sub_pos.mpr h)
  have h := integral_const_lt_of_ae_lt μ (fun z => g z-f z) (hg.sub hf) hpos
  rw [integral_sub hg hf] at h
  linarith

theorem cross_product_integral_strict (L U : ProbabilityMeasure ℝ≥0)
    (hL : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (L : Measure ℝ≥0))
    (hU : MemLp (fun z : ℝ≥0 => (z : ℝ)) 2 (U : Measure ℝ≥0))
    {b : ℝ≥0} {d : ℝ} (hd : 0 < d) (hLb : ∀ᵐ z ∂(L : Measure ℝ≥0), z ≤ b)
    (hUb : ∀ᵐ z : ℝ≥0 ∂(U : Measure ℝ≥0), (b : ℝ)+d < (z : ℝ)) :
    d*((∫ z : ℝ≥0, (z : ℝ) ∂(U : Measure ℝ≥0))-(∫ z : ℝ≥0, (z : ℝ) ∂(L : Measure ℝ≥0))) <
      ∫ z : ℝ≥0 × ℝ≥0, ((z.2 : ℝ)-(z.1 : ℝ))*((z.2 : ℝ)-(b : ℝ))
        ∂(L : Measure ℝ≥0).prod (U : Measure ℝ≥0) := by
  let ν := (L : Measure ℝ≥0).prod (U : Measure ℝ≥0)
  have hdiff : MemLp (fun z : ℝ≥0 × ℝ≥0 => (z.2 : ℝ)-(z.1 : ℝ)) 2 ν :=
    (hU.comp_snd (L : Measure ℝ≥0)).sub (hL.comp_fst (U : Measure ℝ≥0))
  have hprod : Integrable (fun z : ℝ≥0 × ℝ≥0 => ((z.2 : ℝ)-(z.1 : ℝ))*((z.2 : ℝ)-(b : ℝ))) ν :=
    hdiff.integrable_mul ((hU.comp_snd (L : Measure ℝ≥0)).sub (memLp_const (b : ℝ)))
  have hlt : ∀ᵐ z : ℝ≥0 × ℝ≥0 ∂ν,
      d*((z.2 : ℝ)-(z.1 : ℝ)) < ((z.2 : ℝ)-(z.1 : ℝ))*((z.2 : ℝ)-(b : ℝ)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hLb,
      Measure.quasiMeasurePreserving_snd.ae hUb] with z hzL hzU
    have hLr : (z.1 : ℝ) ≤ b := hzL
    have hpos : 0 < (z.2 : ℝ)-(z.1 : ℝ) := by linarith
    nlinarith
  have h := integral_lt_of_ae_lt ν _ _ ((hdiff.integrable one_le_two).const_mul d) hprod hlt
  rw [integral_const_mul, integral_sub ((hU.comp_snd (L : Measure ℝ≥0)).integrable one_le_two)
    ((hL.comp_fst (U : Measure ℝ≥0)).integrable one_le_two)] at h
  have hfst := integral_prod (μ := (L : Measure ℝ≥0)) (ν := (U : Measure ℝ≥0))
    (fun z : ℝ≥0 × ℝ≥0 => (z.1 : ℝ)) ((hL.integrable one_le_two).comp_fst _)
  have hsnd := integral_prod (μ := (L : Measure ℝ≥0)) (ν := (U : Measure ℝ≥0))
    (fun z : ℝ≥0 × ℝ≥0 => (z.2 : ℝ)) ((hU.integrable one_le_two).comp_snd _)
  simp only [integral_const, probReal_univ, one_smul] at hfst hsnd
  change d*((∫ z : ℝ≥0 × ℝ≥0, (z.2 : ℝ) ∂ν)-(∫ z : ℝ≥0 × ℝ≥0, (z.1 : ℝ) ∂ν)) < _ at h
  rw [hfst, hsnd] at h
  exact h

end SharpTailMatching.Probability
