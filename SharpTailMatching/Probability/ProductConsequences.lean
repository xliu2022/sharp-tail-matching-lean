module

public import SharpTailMatching.Probability.IndependentProduct
public import SharpTailMatching.ProductAlgebra
public import SharpTailMatching.SmallDeviationAlgebra

/-!
# Equal means and small deviations

These results apply the fully proved independent product bound to probability
spaces and include the cases where the conditional deficit does not exceed a
coordinate mean.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace SharpTailMatching.Probability.ProductBound

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem measurable_total (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Measurable (total X) := Finset.measurable_sum Finset.univ (fun i _ => hX i)

omit [IsProbabilityMeasure μ] in
theorem integrable_total (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    Integrable (total X) μ := integrable_finsetSum Finset.univ (fun i _ => hX i)

omit [IsProbabilityMeasure μ] in
theorem integral_total (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    (∫ ω, total X ω ∂μ) = ∑ i, ∫ ω, X i ω ∂μ :=
  integral_finsetSum Finset.univ (fun i _ => hX i)

theorem integrable_failureIndicator (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    Integrable (fun ω => FiniteProduct.failureIndicator (total X ω)) μ := by
  change Integrable (({ω | total X ω < 1} : Set Ω).indicator (fun _ => (1 : ℝ))) μ
  exact (integrable_const 1).indicator (measurableSet_lt (measurable_total X hX) measurable_const)

omit [IsProbabilityMeasure μ] in
theorem failureProbability_nonneg (X : ι → Ω → ℝ) : 0 ≤ failureProbability μ X := by
  apply integral_nonneg
  intro ω
  change 0 ≤ if total X ω < 1 then (1 : ℝ) else 0
  split_ifs <;> norm_num

theorem failureProbability_le_one (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    failureProbability μ X ≤ 1 := by
  rw [failureProbability_eq_measure μ X hX]
  simpa only [probReal_univ] using (measureReal_mono (μ := μ) (Set.subset_univ {ω | total X ω < 1}))

theorem positiveDeficit_integrable (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    Integrable (fun ω => max (1 - total X ω) 0) μ :=
  ((integrable_const 1).sub (integrable_total μ X hX)).sup (integrable_const 0)

theorem positiveDeficit_lower (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    1 - ∑ i, ∫ ω, X i ω ∂μ ≤ positiveDeficit μ X := by
  have h := integral_mono ((integrable_const 1).sub (integrable_total μ X hX))
    (positiveDeficit_integrable μ X hX) (fun ω => le_max_left (1-total X ω) 0)
  change (∫ ω, 1 - total X ω ∂μ) ≤ positiveDeficit μ X at h
  rwa [integral_sub (integrable_const 1) (integrable_total μ X hX),
    integral_const, probReal_univ, one_smul, integral_total μ X hX] at h

theorem positiveDeficit_le_failure (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω) :
    positiveDeficit μ X ≤ failureProbability μ X := by
  apply integral_mono_ae (positiveDeficit_integrable μ X hXi) (integrable_failureIndicator μ X hX)
  have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω := ae_all_iff.mpr hnonneg
  filter_upwards [hall] with ω hω
  have hs : 0 ≤ total X ω := Finset.sum_nonneg (fun i _ => hω i)
  unfold FiniteProduct.failureIndicator
  split_ifs with h
  · apply max_le <;> linarith
  · rw [max_eq_right (by linarith)]

omit [IsProbabilityMeasure μ] in
theorem conditionalDeficit_relation (X : ι → Ω → ℝ) (hp : 0 < failureProbability μ X) :
    positiveDeficit μ X = failureProbability μ X * conditionalDeficit μ X := by
  unfold conditionalDeficit
  field_simp

theorem conditionalDeficit_pos (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (hp : 0 < failureProbability μ X) : 0 < conditionalDeficit μ X := by
  have hsupport : Function.support (fun ω => max (1 - total X ω) 0) = {ω | total X ω < 1} := by
    ext ω
    simp only [Function.mem_support, Set.mem_ofPred_eq]
    constructor
    · intro hn
      by_contra h
      exact hn (max_eq_right (by linarith))
    · intro h hz
      have hpos : 0 < max (1 - total X ω) 0 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      linarith
  have hdefpos : 0 < positiveDeficit μ X := by
    apply (integral_pos_iff_support_of_nonneg (fun ω => le_max_right (1-total X ω) 0)
      (positiveDeficit_integrable μ X hXi)).mpr
    rw [hsupport]
    rw [failureProbability_eq_measure μ X hX] at hp
    exact (ENNReal.toReal_pos_iff.mp hp).1
  exact div_pos hdefpos hp

omit [IsProbabilityMeasure μ] in
theorem balance_eq_integral_total (X : ι → Ω → ℝ) (hX : ∀ i, Integrable (X i) μ) :
    balance μ X = conditionalDeficit μ X - 1 + ∫ ω, total X ω ∂μ := by
  rw [integral_total μ X hX]
  rfl

/-- The equal-means corollary, including the low-deficit cases where the
product lemma itself does not apply. -/
theorem equal_mean_failure_lower (j ℓ : ℕ) (hj : 0 < j)
    (X : Fin j → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (m : ℝ) (hmean : ∀ i, (∫ ω, X i ω ∂μ) = m) (hjm : (j : ℝ) * m ≤ 1)
    (hp : 0 < failureProbability μ X)
    (hrlo : 1 - ((j : ℝ) - ℓ) * m ≤ conditionalDeficit μ X)
    (hrhi : conditionalDeficit μ X ≤ 1 - ((j : ℝ) - ℓ - 1) * m) :
    (1 - m / conditionalDeficit μ X) ^ ℓ * (1 - ((j : ℝ) - ℓ) * m) /
      conditionalDeficit μ X ≤ failureProbability μ X := by
  let : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
  have hXi (i) : Integrable (X i) μ := Integrable.of_mem_Icc 0 M (hX i).aemeasurable (hbound i)
  have hm0 : 0 ≤ m := by
    rw [← hmean ⟨0, hj⟩]
    exact integral_nonneg_of_ae ((hbound ⟨0, hj⟩).mono (fun _ h => h.1))
  let r := conditionalDeficit μ X
  have hr0 : 0 < r := conditionalDeficit_pos μ X hX hXi hp
  have hsum : (∑ i, ∫ ω, X i ω ∂μ) = (j : ℝ) * m := by simp [hmean]
  by_cases hmr : m < r
  · obtain ⟨z, hz, hsz, hpz⟩ := bounded_independent_product_bound μ X hX hi M hM hbound hp
      (fun i => by rw [hmean i]; exact hmr)
    apply ProductAlgebra.equal_mean_product_corollary j ℓ z hm0 hmr
      (fun i => (hz i).1) (fun i => by simpa only [hmean i] using (hz i).2)
      _ hrlo hrhi hpz
    simpa only [balance, hsum, r] using hsz
  · have hrm : r ≤ m := le_of_not_gt hmr
    have hmpos : 0 < m := hr0.trans_le hrm
    have hℓle : ℓ ≤ 1 := by
      by_contra h
      have hℓ : (2 : ℝ) ≤ ℓ := by exact_mod_cast (show 2 ≤ ℓ by omega)
      change 1 - ((j : ℝ) - ℓ) * m ≤ r at hrlo
      nlinarith
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hℓle with hℓ | hℓ
    · subst ℓ
      have hdef := positiveDeficit_lower μ X hXi
      rw [hsum, conditionalDeficit_relation μ X hp] at hdef
      simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
      exact (div_le_iff₀ hr0).mpr (by nlinarith)
    · subst ℓ
      have hre : r = m := by
        change 1 - ((j : ℝ) - (1 : ℕ)) * m ≤ r at hrlo
        norm_num only [Nat.cast_one] at hrlo
        nlinarith
      norm_num only [Nat.cast_one]
      change (1 - m / r) ^ 1 * (1 - ((j : ℝ) - 1) * m) / r ≤ _
      rw [hre, div_self (ne_of_gt hmpos)]
      simpa using (failureProbability_nonneg μ X)

/-- Small deviations in the threshold-one normalization. -/
theorem small_deviation_normalized (j : ℕ) (hj : 0 < j)
    (X : Fin j → Ω → ℝ) (hX : ∀ i, Measurable (X i)) (hi : iIndepFun X μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ M)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = ((j : ℝ) + ε)⁻¹) :
    ε / (1 + ε) ≤ failureProbability μ X := by
  let : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
  let m : ℝ := ((j : ℝ) + ε)⁻¹
  let p : ℝ := failureProbability μ X
  let r : ℝ := conditionalDeficit μ X
  let ζ : ℝ := r / m
  have hden : 0 < (j : ℝ) + ε := by positivity
  have hmpos : 0 < m := inv_pos.mpr hden
  have hXi (i) : Integrable (X i) μ := Integrable.of_mem_Icc 0 M (hX i).aemeasurable (hbound i)
  have hsum : (∑ i, ∫ ω, X i ω ∂μ) = (j : ℝ) * m := by simp [hmean, m]
  have hidentity : 1 - (j : ℝ) * m = ε * m := by
    dsimp [m]
    field_simp
    ring
  have hdef : ε * m ≤ positiveDeficit μ X := by
    simpa only [hsum, hidentity] using positiveDeficit_lower μ X hXi
  have hp : 0 < p := (mul_pos hε hmpos).trans_le
    (hdef.trans (positiveDeficit_le_failure μ X hX hXi
      (fun i => (hbound i).mono (fun _ h => h.1))))
  have hpr : ε * m ≤ p * r := by
    simpa only [conditionalDeficit_relation μ X hp] using hdef
  have hrζ : r = m * ζ := by dsimp [ζ]; field_simp
  have hpζ : ε ≤ p * ζ := by
    apply (mul_le_mul_iff_left₀ hmpos).mp
    rw [hrζ] at hpr
    nlinarith
  by_cases hζsmall : ζ ≤ 1 + ε
  · apply (div_le_iff₀ (by linarith : 0 < 1 + ε)).mpr
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hζsmall)]
  · have hζ : 1 + ε ≤ ζ := (le_of_not_ge hζsmall)
    have hmr : m < r := by rw [hrζ]; nlinarith
    obtain ⟨z, hz, hsumz, hprod⟩ := bounded_independent_product_bound μ X hX hi M hM hbound hp
      (fun i => by rw [hmean i]; exact hmr)
    apply SmallDeviationAlgebra.small_deviation_of_product j z hmpos hε hεhalf hζ hrζ
      (fun i => (hz i).1) (fun i => by simpa only [hmean i] using (hz i).2) _ hprod
    rw [balance, hsum] at hsumz
    change (∑ i, z i) = r - 1 + (j : ℝ) * m at hsumz
    nlinarith

/-- Bounded independent nonnegative variables of mean one satisfy the
small-deviation bound at the original threshold `j + ε`. -/
theorem bounded_small_deviation_mean_one (j : ℕ) (hj : 0 < j)
    (Y : Fin j → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Y i ω ∧ Y i ω ≤ M)
    (hmean : ∀ i, (∫ ω, Y i ω ∂μ) = 1)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ε / (1 + ε) ≤ μ.real {ω | (∑ i, Y i ω) < (j : ℝ) + ε} := by
  let m : ℝ := ((j : ℝ) + ε)⁻¹
  let X : Fin j → Ω → ℝ := fun i ω => m * Y i ω
  have hden : 0 < (j : ℝ) + ε := by positivity
  have hmpos : 0 < m := inv_pos.mpr hden
  have hX (i) : Measurable (X i) := measurable_const.mul (hY i)
  have hXind : iIndepFun X μ := hi.comp (fun _ y => m * y) (fun _ => by fun_prop)
  have hXbound (i) : ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ m * M := by
    filter_upwards [hbound i] with ω hω
    exact ⟨mul_nonneg hmpos.le hω.1, mul_le_mul_of_nonneg_left hω.2 hmpos.le⟩
  have hXmean (i) : (∫ ω, X i ω ∂μ) = ((j : ℝ) + ε)⁻¹ := by
    change (∫ ω, m * Y i ω ∂μ) = m
    rw [integral_const_mul, hmean i, mul_one]
  have h := small_deviation_normalized μ j hj X hX hXind (m*M) (mul_nonneg hmpos.le hM)
    hXbound ε hε hεhalf hXmean
  rw [failureProbability_eq_measure μ X hX] at h
  have hevent : {ω | total X ω < 1} = {ω | (∑ i, Y i ω) < (j : ℝ) + ε} := by
    ext ω
    simp only [Set.mem_ofPred_eq, total, X, ← Finset.mul_sum]
    have hid : m * (∑ i, Y i ω) = (∑ i, Y i ω) / ((j : ℝ) + ε) := by
      dsimp [m]
      ring
    rw [hid]
    exact div_lt_one hden
  simpa only [hevent] using h

theorem capped_sum_lt_iff (y : ι → ℝ) (L : ℝ) (hL : 0 ≤ L) (hy : ∀ i, 0 ≤ y i) :
    ((∑ i, min (y i) L) < L) ↔ (∑ i, y i) < L := by
  have hge : (L ≤ ∑ i, min (y i) L) ↔ L ≤ ∑ i, y i := by
    constructor
    · intro h
      exact h.trans (Finset.sum_le_sum (fun i _ => min_le_left (y i) L))
    · intro h
      by_cases hlarge : ∃ i, L ≤ y i
      · obtain ⟨i, hi⟩ := hlarge
        have hle := Finset.single_le_sum (s := Finset.univ) (f := fun j => min (y j) L)
          (fun j _ => le_min (hy j) hL) (Finset.mem_univ i)
        simpa only [min_eq_right hi] using hle
      · have hsmall (i) : min (y i) L = y i := min_eq_left (le_of_not_ge (not_exists.mp hlarge i))
        simpa only [hsmall] using h
  simpa only [not_le] using not_congr hge

/-- The small-deviation inequality for arbitrary nonnegative integrable
independent variables whose means are at most one. Truncation at the target
threshold preserves the event, and deterministic mean completion reduces
the assertion to the proved bounded mean-one case. -/
theorem small_deviation (j : ℕ) (Y : Fin j → Ω → ℝ)
    (hY : ∀ i, Measurable (Y i)) (hYi : ∀ i, Integrable (Y i) μ)
    (hi : iIndepFun Y μ) (hnonneg : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ Y i ω)
    (hmean : ∀ i, (∫ ω, Y i ω ∂μ) ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ε / (1 + ε) ≤ μ.real {ω | (∑ i, Y i ω) < (j : ℝ) + ε} := by
  by_cases hj0 : j = 0
  · subst j
    have hfrac : ε / (1 + ε) ≤ 1 :=
      (div_le_one (by linarith : 0 < 1 + ε)).mpr (by linarith)
    simpa [hε] using hfrac
  have hj : 0 < j := Nat.pos_of_ne_zero hj0
  let L : ℝ := (j : ℝ) + ε
  have hL : 0 < L := by dsimp [L]; positivity
  let C : Fin j → Ω → ℝ := fun i ω => min (max (Y i ω) 0) L
  have hC (i) : Measurable (C i) := ((hY i).max measurable_const).min measurable_const
  have hCbound (i ω) : 0 ≤ C i ω ∧ C i ω ≤ L :=
    ⟨le_min (le_max_right _ _) hL.le, min_le_right _ _⟩
  have hCi (i) : Integrable (C i) μ :=
    Integrable.of_mem_Icc 0 L (hC i).aemeasurable (Filter.Eventually.of_forall (hCbound i))
  have hCmean0 (i) : 0 ≤ ∫ ω, C i ω ∂μ := integral_nonneg (fun ω => (hCbound i ω).1)
  have hCmean1 (i) : (∫ ω, C i ω ∂μ) ≤ 1 := by
    apply (integral_mono_ae (hCi i) (hYi i) _).trans (hmean i)
    filter_upwards [hnonneg i] with ω hω
    change min (max (Y i ω) 0) L ≤ Y i ω
    rw [max_eq_left hω]
    exact min_le_left _ _
  let δ : Fin j → ℝ := fun i => 1 - ∫ ω, C i ω ∂μ
  have hδ (i) : 0 ≤ δ i ∧ δ i ≤ 1 := by dsimp [δ]; constructor <;> linarith [hCmean0 i, hCmean1 i]
  let Z : Fin j → Ω → ℝ := fun i ω => C i ω + δ i
  have hZ (i) : Measurable (Z i) := (hC i).add measurable_const
  have hZind : iIndepFun Z μ := hi.comp
    (fun i y => min (max y 0) L + δ i) (fun _ => by fun_prop)
  have hZbound (i) : ∀ᵐ ω ∂μ, 0 ≤ Z i ω ∧ Z i ω ≤ L + 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    change 0 ≤ C i ω + δ i ∧ C i ω + δ i ≤ L + 1
    constructor <;> linarith [(hCbound i ω).1, (hCbound i ω).2, (hδ i).1, (hδ i).2]
  have hZmean (i) : (∫ ω, Z i ω ∂μ) = 1 := by
    change (∫ ω, C i ω + δ i ∂μ) = 1
    rw [integral_add (hCi i) (integrable_const _), integral_const, probReal_univ, one_smul]
    dsimp [δ]
    ring
  have hsmall := bounded_small_deviation_mean_one μ j hj Z hZ hZind (L+1) (by linarith)
    hZbound hZmean ε hε hεhalf
  have hsub : {ω | (∑ i, Z i ω) < L} ⊆ {ω | (∑ i, C i ω) < L} := by
    intro ω hω
    have hsum : (∑ i, C i ω) ≤ ∑ i, Z i ω := by
      apply Finset.sum_le_sum
      intro i _
      change C i ω ≤ C i ω + δ i
      linarith [(hδ i).1]
    exact hsum.trans_lt hω
  have hevent : {ω | (∑ i, C i ω) < L} =ᵐ[μ] {ω | (∑ i, Y i ω) < L} := by
    have hall : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ Y i ω := ae_all_iff.mpr hnonneg
    filter_upwards [hall] with ω hω
    apply propext
    have hc (i) : C i ω = min (Y i ω) L := by
      change min (max (Y i ω) 0) L = _
      rw [max_eq_left (hω i)]
    simp only [hc]
    exact capped_sum_lt_iff (fun i => Y i ω) L hL.le hω
  have hmeasure : μ.real {ω | (∑ i, C i ω) < L} = μ.real {ω | (∑ i, Y i ω) < L} :=
    congrArg ENNReal.toReal (measure_congr hevent)
  exact hsmall.trans ((measureReal_mono hsub).trans_eq hmeasure)

end SharpTailMatching.Probability.ProductBound
