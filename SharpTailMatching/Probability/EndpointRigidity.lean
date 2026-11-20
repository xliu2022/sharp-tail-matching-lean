module

public import SharpTailMatching.Probability.FailureMoments
public import SharpTailMatching.ProductAlgebra
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Rigidity at the two endpoints of the normalized excess

The statements in this file concern arbitrary probability laws on the unit
interval. In particular, the equality arguments do not presuppose finite
support, a density, or an atomic optimizer.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem positive_deficit_le_product (k : ℕ) (y : Fin k → ℝ)
    (hy0 : ∀ i, 0 ≤ y i) (hy1 : ∀ i, y i ≤ 1) :
    max (1 - ∑ i, y i) 0 ≤ ∏ i, (1 - y i) := by
  by_cases hs : (∑ i, y i) ≤ 1
  · have h := ProductAlgebra.unit_cube_product_lower k 0 y
      (q := 0) (by norm_num) (by norm_num) hy0 hy1
      (by simpa using Finset.sum_nonneg (fun i _ => hy0 i)) (by simpa using hs)
    simpa [max_eq_left (sub_nonneg.mpr hs)] using h
  · rw [max_eq_right (by linarith : 1 - ∑ i, y i ≤ 0)]
    exact Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hy1 i)

theorem positive_deficit_lt_product {k : ℕ} (hk : 2 ≤ k) (y : Fin k → ℝ)
    (hy0 : ∀ i, 0 < y i) (hy1 : ∀ i, y i < 1) :
    max (1 - ∑ i, y i) 0 < ∏ i, (1 - y i) := by
  by_cases hs : 1 ≤ ∑ i, y i
  · rw [max_eq_right (sub_nonpos.mpr hs)]
    exact Finset.prod_pos fun i _ => sub_pos.mpr (hy1 i)
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
    let s : ℝ := ∑ i : Fin (n+1), y i.succ
    have hsum : (∑ i : Fin (n+2), y i) = y 0 + s := Fin.sum_univ_succ y
    have hspos : 0 < s := by
      apply (hy0 (Fin.succ (0 : Fin (n+1)))).trans_le
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin (n+1) => y i.succ)
        (fun i _ => (hy0 i.succ).le) (Finset.mem_univ 0)
    have hrest : 1 - s ≤ ∏ i : Fin (n+1), (1 - y i.succ) :=
      (le_max_left _ _).trans (positive_deficit_le_product (n+1) (fun i => y i.succ)
        (fun i => (hy0 i.succ).le) (fun i => (hy1 i.succ).le))
    have hmul := mul_le_mul_of_nonneg_left hrest (sub_pos.mpr (hy1 0)).le
    rw [hsum, max_eq_left (by linarith [hsum] : 0 ≤ 1 - (y 0 + s)),
      Fin.prod_univ_succ]
    nlinarith [mul_pos (hy0 0) hspos]

theorem unit_supported_ae_le_one (μ : ProbabilityMeasure ℝ≥0)
    (hμ : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) :
    ∀ᵐ z ∂(μ : Measure ℝ≥0), z ≤ 1 := by
  apply ae_iff.mpr
  simpa only [Set.Ioi, not_le] using hμ

theorem unit_supported_memLp (μ : ProbabilityMeasure ℝ≥0)
    (hμ : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) (p : ℝ≥0∞) :
    MemLp (fun z : ℝ≥0 => (z : ℝ)) p (μ : Measure ℝ≥0) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [unit_supported_ae_le_one μ hμ] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg z.coe_nonneg]
  exact_mod_cast hz

theorem unit_supported_iidSum_memLp (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hμ : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) (p : ℝ≥0∞) :
    MemLp (iidSum k) p (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) := by
  have hae : ∀ᵐ w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)),
      ∀ i, w i ≤ 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
      (i := i)).eventually (unit_supported_ae_le_one μ hμ)
  apply MemLp.of_bound (show Measurable (iidSum k) from by
    unfold iidSum; fun_prop).aestronglyMeasurable k
  filter_upwards [hae] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (iidSum_nonneg k w)]
  have h : (∑ i : Fin k, (w i : ℝ)) ≤ ∑ _i : Fin k, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => by exact_mod_cast hw i
  simpa [iidSum] using h

/-- The zero endpoint of the normalized excess forces a point mass. -/
theorem normalized_zero_excess_rigidity {k : ℕ} (hk : 1 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : (∫ w : Fin k → ℝ≥0, max (iidSum k w - 1) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = 0) :
    (μ : Measure ℝ≥0) = Measure.dirac ((k : ℝ≥0)⁻¹) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hS := (unit_supported_iidSum_memLp k μ hsupp 1).integrable (by norm_num)
  have he := (hS.sub (integrable_const (1 : ℝ))).pos_part
  have hzero : (fun w : Fin k → ℝ≥0 => max (iidSum k w - 1) 0) =ᵐ[
      Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun _ => le_max_right _ _) he).mp hexcess
  have hle : iidSum k ≤ᵐ[Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [hzero] with w hw
    have hh := le_max_left (iidSum k w - 1) 0
    change max (iidSum k w - 1) 0 = 0 at hw
    linarith
  have hES : (∫ w, iidSum k w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = 1 := by
    rw [integral_iidSum k μ (by rw [hmean]; exact ENNReal.ofReal_ne_top), hmean,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hkpos.le), mul_inv_cancel₀ hkpos.ne']
  have hconst : iidSum k =ᵐ[Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))]
      (fun _ => (1 : ℝ)) :=
    (integral_eq_iff_of_ae_le hS (integrable_const 1) hle).mp (by simpa using hES)
  have hvSum : variance (iidSum k) (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) = 0 := by
    rw [variance_congr hconst]
    simp [variance, evariance]
  rw [variance_iidSum k μ (unit_supported_memLp μ hsupp 2)] at hvSum
  have hv : variance (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) = 0 :=
    (mul_eq_zero.mp hvSum).resolve_left hkpos.ne'
  have hc := ae_eq_integral_of_variance_eq_zero (unit_supported_memLp μ hsupp 2) hv
  rw [integral_coe_eq_mean_toReal, hmean, ENNReal.toReal_ofReal (inv_nonneg.mpr hkpos.le)] at hc
  have hc' : (fun z : ℝ≥0 => z) =ᵐ[(μ : Measure ℝ≥0)]
      (fun _ => (k : ℝ≥0)⁻¹) := by
    filter_upwards [hc] with z hz
    apply NNReal.coe_injective
    simpa only [NNReal.coe_inv, NNReal.coe_natCast] using hz
  have hh : (μ : Measure ℝ≥0).map (fun z : ℝ≥0 => z) =
      (μ : Measure ℝ≥0).map (fun _ => (k : ℝ≥0)⁻¹) := Measure.map_congr hc'
  simpa using hh

/-- Equality in the independent product comparison excludes every interior
atom and, more generally, all mass in the open unit interval. -/
theorem deficit_product_equality_no_interior {k : ℕ} (hk : 2 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (heq : (∫ w : Fin k → ℝ≥0, max (1 - iidSum k w) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
        (1 - (mean μ).toReal) ^ k) :
    (μ : Measure ℝ≥0) (Set.Ioo 0 1) = 0 := by
  let ν := Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))
  have hx : Integrable (fun z : ℝ≥0 => (z : ℝ)) (μ : Measure ℝ≥0) :=
    (unit_supported_memLp μ hsupp 1).integrable (by norm_num)
  have hdef : Integrable (fun w : Fin k → ℝ≥0 => max (1 - iidSum k w) 0) ν := by
    apply Integrable.of_bound (show Measurable
      (fun w : Fin k → ℝ≥0 => max (1 - iidSum k w) 0) from by
        unfold iidSum; fun_prop).aestronglyMeasurable 1
    filter_upwards [] with w
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := iidSum_nonneg k w; linarith) (by norm_num)
  have hprod : Integrable (fun w : Fin k → ℝ≥0 => ∏ i, (1 - (w i : ℝ))) ν :=
    Integrable.fintype_prod (fun _ => (integrable_const (1 : ℝ)).sub hx)
  have hprodint : (∫ w : Fin k → ℝ≥0, ∏ i, (1 - (w i : ℝ)) ∂ν) =
      (1 - (mean μ).toReal) ^ k := by
    dsimp only [ν]
    rw [integral_fintype_prod_eq_pow (fun z : ℝ≥0 => 1 - (z : ℝ))]
    simp [integral_sub (integrable_const (1 : ℝ)) hx, integral_coe_eq_mean_toReal]
  have hcoords : ∀ᵐ w ∂ν, ∀ i, w i ≤ 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
      (i := i)).eventually (unit_supported_ae_le_one μ hsupp)
  have hle : (fun w : Fin k → ℝ≥0 => max (1 - iidSum k w) 0) ≤ᵐ[ν]
      (fun w => ∏ i, (1 - (w i : ℝ))) := by
    filter_upwards [hcoords] with w hw
    exact positive_deficit_le_product k (fun i => (w i : ℝ))
      (fun i => (w i).coe_nonneg) (fun i => by exact_mod_cast hw i)
  have hae := (integral_eq_iff_of_ae_le hdef hprod hle).mp (heq.trans hprodint.symm)
  have hbox : ν (Set.pi Set.univ (fun _ : Fin k => Set.Ioo (0 : ℝ≥0) 1)) = 0 := by
    apply measure_mono_null (t := {w : Fin k → ℝ≥0 |
      ¬ max (1 - iidSum k w) 0 = ∏ i, (1 - (w i : ℝ))})
    · intro w hw
      exact (positive_deficit_lt_product hk (fun i => (w i : ℝ))
        (fun i => by exact_mod_cast (hw i (Set.mem_univ i)).1)
        (fun i => by exact_mod_cast (hw i (Set.mem_univ i)).2)).ne
    · exact ae_iff.mp hae
  have hpow : ((μ : Measure ℝ≥0) (Set.Ioo 0 1)) ^ k = 0 := by
    simpa only [ν, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hbox
  exact (pow_eq_zero_iff (by omega : k ≠ 0)).mp hpow

/-- A unit-interval law with no interior mass is identified by its mean. -/
theorem unit_supported_no_interior_bernoulli (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hinterior : (μ : Measure ℝ≥0) (Set.Ioo 0 1) = 0)
    {x : ℝ} (hx : 0 ≤ x) (hmean : mean μ = ENNReal.ofReal x) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  have hnot : ∀ᵐ z ∂(μ : Measure ℝ≥0), z ∉ Set.Ioo 0 1 := by
    apply ae_iff.mpr
    simpa [Set.Ioo] using hinterior
  have hae : ∀ᵐ z ∂(μ : Measure ℝ≥0), z = 0 ∨ z = 1 := by
    filter_upwards [unit_supported_ae_le_one μ hsupp, hnot] with z hz hzi
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      have hzpos : 0 < z := lt_of_le_of_ne zero_le (Ne.symm hz0)
      exact le_antisymm hz (le_of_not_gt fun h => hzi ⟨hzpos, h⟩)
  have hdecomp :=
    (Measure.ae_eq_or_eq_iff_eq_dirac_add_dirac (by norm_num : (0 : ℝ≥0) ≠ 1)).mp hae
  have hm1 : (μ : Measure ℝ≥0) {1} = ENNReal.ofReal x := by
    rw [← hmean, mean, hdecomp]
    simp [lintegral_add_measure, lintegral_smul_measure]
  have hcompl : ({1} : Set ℝ≥0)ᶜ =ᵐ[(μ : Measure ℝ≥0)] {0} := by
    filter_upwards [hae] with z hz
    rcases hz with rfl | rfl <;> norm_num
  have hm0 : (μ : Measure ℝ≥0) {0} = ENNReal.ofReal (1 - x) := by
    rw [← measure_congr hcompl, prob_compl_eq_one_sub (measurableSet_singleton 1), hm1]
    rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one]
  simpa only [hm0, hm1, unitBernoulliMeasure] using hdecomp

/-- The upper deficit endpoint forces the Bernoulli law on `{0,1}`. -/
theorem normalized_max_deficit_rigidity {k : ℕ} (hk : 2 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hdeficit : (∫ w : Fin k → ℝ≥0, max (1 - iidSum k w) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
        (1 - (k : ℝ)⁻¹) ^ k) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure (k : ℝ)⁻¹ := by
  apply unit_supported_no_interior_bernoulli μ hsupp
  · apply deficit_product_equality_no_interior hk μ hsupp
    simpa only [hmean, ENNReal.toReal_ofReal (by positivity : 0 ≤ (k : ℝ)⁻¹)] using hdeficit
  · positivity
  · exact hmean

/-- The parameter `w` used for the normalized comparison curves. -/
def normalizedExcess (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  (k : ℝ) * ∫ w : Fin k → ℝ≥0, max (iidSum k w - 1) 0
    ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))

/-- The last comparison node `W_k`. -/
def maxNormalizedExcess (k : ℕ) : ℝ :=
  (k : ℝ) * (1 - (k : ℝ)⁻¹) ^ k

theorem normalized_positive_negative_deviation {k : ℕ} (hk : 1 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    (∫ w : Fin k → ℝ≥0, max (iidSum k w - 1) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) =
    (∫ w : Fin k → ℝ≥0, max (1 - iidSum k w) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hS := (unit_supported_iidSum_memLp k μ hsupp 1).integrable (by norm_num)
  have hp : Integrable (fun w : Fin k → ℝ≥0 => max (iidSum k w - 1) 0)
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) :=
    (hS.sub (integrable_const (1 : ℝ))).pos_part
  have hn : Integrable (fun w : Fin k → ℝ≥0 => max (1 - iidSum k w) 0)
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) :=
    ((integrable_const (1 : ℝ)).sub hS).pos_part
  have hfun : (fun w : Fin k → ℝ≥0 =>
      max (iidSum k w - 1) 0 - max (1 - iidSum k w) 0) =
      (fun w => iidSum k w - 1) := by
    funext w
    by_cases hw : 1 ≤ iidSum k w
    · rw [max_eq_left (sub_nonneg.mpr hw), max_eq_right (sub_nonpos.mpr hw)]
      ring
    · have h : iidSum k w ≤ 1 := (le_of_not_ge hw)
      rw [max_eq_right (sub_nonpos.mpr h), max_eq_left (sub_nonneg.mpr h)]
      ring
  have hint := congrArg (fun f : (Fin k → ℝ≥0) → ℝ =>
    ∫ w, f w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) hfun
  rw [integral_sub hp hn, integral_sub hS (integrable_const 1),
    integral_iidSum k μ (by rw [hmean]; exact ENNReal.ofReal_ne_top),
    hmean, ENNReal.toReal_ofReal (inv_nonneg.mpr hkpos.le), mul_inv_cancel₀ hkpos.ne'] at hint
  simpa using sub_eq_zero.mp (by simpa using hint)

theorem unit_supported_deficit_product_bound (k : ℕ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0) :
    (∫ w : Fin k → ℝ≥0, max (1 - iidSum k w) 0
      ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) ≤
      (1 - (mean μ).toReal) ^ k := by
  have hx := (unit_supported_memLp μ hsupp 1).integrable (by norm_num)
  have hS := (unit_supported_iidSum_memLp k μ hsupp 1).integrable (by norm_num)
  have hn := ((integrable_const (1 : ℝ)).sub hS).pos_part
  have hprod : Integrable (fun w : Fin k → ℝ≥0 => ∏ i, (1 - (w i : ℝ)))
      (Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))) :=
    Integrable.fintype_prod (fun _ => (integrable_const (1 : ℝ)).sub hx)
  have hcoords : ∀ᵐ w ∂Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)),
      ∀ i, w i ≤ 1 := by
    apply ae_all_iff.mpr
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin k => (μ : Measure ℝ≥0))
      (i := i)).eventually (unit_supported_ae_le_one μ hsupp)
  have hle := integral_mono_ae hn hprod (show
      (fun w : Fin k → ℝ≥0 => max (1 - iidSum k w) 0) ≤ᵐ[
        Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0))]
      (fun w => ∏ i, (1 - (w i : ℝ))) from by
    filter_upwards [hcoords] with w hw
    exact positive_deficit_le_product k (fun i => (w i : ℝ))
      (fun i => (w i).coe_nonneg) (fun i => by exact_mod_cast hw i))
  rw [integral_fintype_prod_eq_pow (fun z : ℝ≥0 => 1 - (z : ℝ))] at hle
  simpa [integral_sub (integrable_const (1 : ℝ)) hx, integral_coe_eq_mean_toReal] using hle

theorem normalized_excess_bounds {k : ℕ} (hk : 1 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹) :
    0 ≤ normalizedExcess k μ ∧ normalizedExcess k μ ≤ maxNormalizedExcess k := by
  constructor
  · exact mul_nonneg (Nat.cast_nonneg k) (integral_nonneg fun _ => le_max_right _ _)
  · unfold normalizedExcess maxNormalizedExcess
    rw [normalized_positive_negative_deviation hk μ hsupp hmean]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    simpa only [hmean, ENNReal.toReal_ofReal (by positivity : 0 ≤ (k : ℝ)⁻¹)]
      using unit_supported_deficit_product_bound k μ hsupp

theorem normalized_excess_zero_rigidity {k : ℕ} (hk : 1 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hw : normalizedExcess k μ = 0) :
    (μ : Measure ℝ≥0) = Measure.dirac ((k : ℝ≥0)⁻¹) := by
  apply normalized_zero_excess_rigidity hk μ hsupp hmean
  exact (mul_eq_zero.mp hw).resolve_left (by exact_mod_cast (by omega : k ≠ 0))

theorem normalized_excess_max_rigidity {k : ℕ} (hk : 2 ≤ k)
    (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hw : normalizedExcess k μ = maxNormalizedExcess k) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure (k : ℝ)⁻¹ := by
  apply normalized_max_deficit_rigidity hk μ hsupp hmean
  rw [← normalized_positive_negative_deviation (by omega) μ hsupp hmean]
  exact mul_left_cancel₀ (by exact_mod_cast (by omega : k ≠ 0) : (k : ℝ) ≠ 0) hw

end SharpTailMatching.Probability
