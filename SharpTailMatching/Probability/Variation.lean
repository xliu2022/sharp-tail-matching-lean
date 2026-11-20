module

public import SharpTailMatching.Probability.Normalization
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Integral.Pi

/-! # Finite-mixture expansions and first variations -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

/-- Finite products distribute over finite sums of finite measures. -/
theorem pi_sum_finite (k m : ℕ) (ν : Fin k → Fin m → Measure ℝ≥0)
    [∀ i j, IsFiniteMeasure (ν i j)] :
    Measure.pi (fun i : Fin k => ∑ j : Fin m, ν i j) =
      ∑ σ : Fin k → Fin m, Measure.pi (fun i => ν i (σ i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply, Measure.pi_pi]
  exact (Fintype.prod_sum (fun i j => ν i j (s i))).symm

/-- Coordinate-dependent scalar factors leave a product measure as their product. -/
theorem pi_smul_finite (k : ℕ) (ν : Fin k → Measure ℝ≥0)
    [∀ i, IsFiniteMeasure (ν i)] (c : Fin k → ℝ≥0∞) (hc : ∀ i, c i ≠ ∞) :
    Measure.pi (fun i => c i • ν i) =
      (∏ i, c i) • Measure.pi ν := by
  let (i : Fin k) : IsFiniteMeasure (c i • ν i) := (ν i).smul_finite (hc i)
  apply Measure.pi_eq
  intro s hs
  simp [Measure.smul_apply, Measure.pi_pi, Finset.prod_mul_distrib]

/-- The exact mixture expansion, with arbitrary coordinate laws and weights. -/
theorem pi_mixture_finite (k m : ℕ) (ν : Fin k → Fin m → Measure ℝ≥0)
    [∀ i j, IsFiniteMeasure (ν i j)] (c : Fin k → Fin m → ℝ≥0∞)
    (hc : ∀ i j, c i j ≠ ∞) :
    Measure.pi (fun i : Fin k => ∑ j : Fin m, c i j • ν i j) =
      ∑ σ : Fin k → Fin m, (∏ i, c i (σ i)) • Measure.pi (fun i => ν i (σ i)) := by
  let (i : Fin k) (j : Fin m) : IsFiniteMeasure (c i j • ν i j) :=
    (ν i j).smul_finite (hc i j)
  rw [pi_sum_finite]
  apply Finset.sum_congr rfl
  intro σ _
  exact pi_smul_finite k _ _ (fun i => hc i (σ i))

/-- Success probability for coordinate laws that need not have unit mass. -/
def tailForm (k : ℕ) (ν : Fin k → Measure ℝ≥0) : ℝ :=
  ((Measure.pi ν) {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i}).toReal

/-- The real polynomial that computes a finite mixture's success probability
whenever the coefficients are nonnegative. It remains a polynomial for signed
coefficient values, which is useful when taking derivatives at zero. -/
def tailPolynomial (k m : ℕ) (ν : Fin m → Measure ℝ≥0) (c : Fin m → ℝ) : ℝ :=
  ∑ σ : Fin k → Fin m, (∏ i, c (σ i)) * tailForm k (fun i => ν (σ i))

theorem tailForm_mixture (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    [∀ j, IsFiniteMeasure (ν j)] (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) :
    tailForm k (fun _ : Fin k => ∑ j : Fin m, ENNReal.ofReal (c j) • ν j) =
      tailPolynomial k m ν c := by
  unfold tailForm tailPolynomial
  rw [pi_mixture_finite k m (fun _ j => ν j) (fun _ j => ENNReal.ofReal (c j))
    (fun _ _ => ENNReal.ofReal_ne_top), Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro σ _
    simp [tailForm, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_ofReal (hc _)]
  · intro σ _
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)

theorem hasDerivAt_tailPolynomial_affine (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    (c d : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => tailPolynomial k m ν (fun j => c j + t * d j))
      (∑ σ : Fin k → Fin m,
        (∑ i : Fin k, d (σ i) * ∏ j ∈ Finset.univ.erase i, c (σ j)) *
          tailForm k (fun i => ν (σ i))) 0 := by
  classical
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.mul_const
  convert HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => ((hasDerivAt_id (0 : ℝ)).mul_const (d (σ i))).const_add (c (σ i))) using 1 <;>
    simp [mul_comm]

/-- The same finite expansion with a separate weight vector in each coordinate. -/
def tailMultiPolynomial (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    (c : Fin k → Fin m → ℝ) : ℝ :=
  ∑ σ : Fin k → Fin m, (∏ i, c i (σ i)) * tailForm k (fun i => ν (σ i))

theorem tailForm_mixture_rows (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    [∀ j, IsFiniteMeasure (ν j)] (c : Fin k → Fin m → ℝ)
    (hc : ∀ i j, 0 ≤ c i j) :
    tailForm k (fun i : Fin k => ∑ j : Fin m, ENNReal.ofReal (c i j) • ν j) =
      tailMultiPolynomial k m ν c := by
  unfold tailForm tailMultiPolynomial
  rw [pi_mixture_finite k m (fun _ j => ν j) (fun i j => ENNReal.ofReal (c i j))
    (fun _ _ => ENNReal.ofReal_ne_top), Measure.finsetSum_apply]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro σ _
    simp [tailForm, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_ofReal (hc _ _)]
  · intro σ _
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
      (measure_ne_top _ _)

/-- A linear functional representing variation in one coordinate. -/
def tailCoefficient (k m : ℕ) (ν : Fin m → Measure ℝ≥0) (c : Fin m → ℝ)
    (i : Fin k) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun d := ∑ σ : Fin k → Fin m,
    (d (σ i) * ∏ j ∈ Finset.univ.erase i, c (σ j)) * tailForm k (fun j => ν (σ j))
  map_add' d e := by
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r d := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem tailCoefficient_update (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    (c d : Fin m → ℝ) (i : Fin k) :
    tailCoefficient k m ν c i d =
      tailMultiPolynomial k m ν (Function.update (fun _ => c) i d) := by
  classical
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => Function.update (fun _ : Fin k => c) i d j (σ j)) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem tailCoefficient_base (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    (c : Fin m → ℝ) (i : Fin k) :
    tailCoefficient k m ν c i c = tailPolynomial k m ν c := by
  rw [tailCoefficient_update]
  simp [tailMultiPolynomial, tailPolynomial]

theorem tailCoefficient_basis (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    [∀ j, IsFiniteMeasure (ν j)] (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (i : Fin k) (j : Fin m) :
    tailCoefficient k m ν c i (Pi.single j 1) =
      tailForm k (Function.update (fun _ : Fin k => ∑ l : Fin m,
        ENNReal.ofReal (c l) • ν l) i (ν j)) := by
  classical
  rw [tailCoefficient_update, ← tailForm_mixture_rows]
  · congr 1
    funext l
    by_cases hl : l = i
    · subst l
      simp [Pi.single_apply, apply_ite, ite_smul]
    · simp [Function.update_of_ne hl]
  · intro l r
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self, Pi.single_apply]
      split_ifs <;> norm_num
    · simpa [Function.update_of_ne hl] using hc r

theorem hasDerivAt_tailPolynomial_coefficients (k m : ℕ) (ν : Fin m → Measure ℝ≥0)
    (c d : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => tailPolynomial k m ν (fun j => c j + t * d j))
      (∑ i : Fin k, tailCoefficient k m ν c i d) 0 := by
  convert hasDerivAt_tailPolynomial_affine k m ν c d using 1
  simp only [tailCoefficient, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  exact Finset.sum_comm

theorem tailForm_permute (k : ℕ) (ν : Fin k → Measure ℝ≥0)
    [∀ i, IsFiniteMeasure (ν i)] (e : Equiv.Perm (Fin k)) :
    tailForm k (fun i => ν (e i)) = tailForm k ν := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ≥0) e
  have hE := measurePreserving_piCongrLeft ν e
  have hevent : E ⁻¹' {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i} =
      {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i} := by
    ext z
    have hsum : ∑ i, E z i = ∑ i, z i := by
      rw [← Equiv.sum_comp e (fun i => E z i)]
      simp [E, MeasurableEquiv.piCongrLeft_apply_apply]
    change (1 ≤ ∑ i, E z i) ↔ (1 ≤ ∑ i, z i)
    rw [hsum]
  have hh := congrArg (fun ρ : Measure (Fin k → ℝ≥0) =>
    ρ {z | 1 ≤ ∑ i, z i}) hE.map_eq
  rw [Measure.map_apply hE.measurable (by measurability)] at hh
  change (Measure.pi (fun i => ν (e i))) (E ⁻¹' {z | 1 ≤ ∑ i, z i}) = _ at hh
  rw [hevent] at hh
  exact congrArg ENNReal.toReal hh

/-- Replacing one coordinate in an identically distributed product gives the
same success probability whichever coordinate is selected. -/
theorem tailForm_update_independent (k : ℕ) (μ ν : Measure ℝ≥0)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i j : Fin k) :
    tailForm k (Function.update (fun _ => μ) i ν) =
      tailForm k (Function.update (fun _ => μ) j ν) := by
  classical
  let (l : Fin k) : IsFiniteMeasure (Function.update (fun _ => μ) i ν l) := by
    by_cases hl : l = i
    · subst l
      simpa using (inferInstance : IsFiniteMeasure ν)
    · simpa [Function.update_of_ne hl] using (inferInstance : IsFiniteMeasure μ)
  have hp := tailForm_permute k (Function.update (fun _ => μ) i ν) (Equiv.swap i j)
  have hfun : (fun l => Function.update (fun _ : Fin k => μ) i ν (Equiv.swap i j l)) =
      Function.update (fun _ : Fin k => μ) j ν := by
    simpa [Function.comp_def] using
      Function.update_comp_equiv (fun _ : Fin k => μ) (Equiv.swap i j) i ν
  rw [hfun] at hp
  exact hp.symm

/-- The one-coordinate success function; its finite-product definition avoids
any choice of conditional versions. -/
def sectionTail (n : ℕ) (μ : ProbabilityMeasure ℝ≥0) (z : ℝ≥0) : ℝ :=
  tailForm (n + 1) (Function.update (fun _ => (μ : Measure ℝ≥0)) 0 (Measure.dirac z))

/-- A right-sided local maximum makes an existing ordinary derivative nonpositive. -/
theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hmax : ∀ᶠ t in 𝓝[>] 0, f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [hmax, self_mem_nhdsWithin] with t ht ht0
  simpa only [zero_add, smul_eq_mul] using
    mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht0)) (sub_nonpos.mpr ht)

def pointLaw (z : ℝ≥0) : ProbabilityMeasure ℝ≥0 := ⟨Measure.dirac z, inferInstance⟩

@[simp] theorem mean_pointLaw (z : ℝ≥0) : mean (pointLaw z) = (z : ℝ≥0∞) := by
  simp [mean, pointLaw]

/-- A finite convex mixture, bundled together with its probability proof. -/
def finiteMixtureLaw (m : ℕ) (ν : Fin m → ProbabilityMeasure ℝ≥0)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ j, c j = 1) :
    ProbabilityMeasure ℝ≥0 :=
  ⟨∑ j, ENNReal.ofReal (c j) • (ν j : Measure ℝ≥0), ⟨by
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hc j), hsum, ENNReal.ofReal_one]⟩⟩

theorem mean_finiteMixtureLaw (m : ℕ) (ν : Fin m → ProbabilityMeasure ℝ≥0)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ j, c j = 1) :
    mean (finiteMixtureLaw m ν c hc hsum) = ∑ j, ENNReal.ofReal (c j) * mean (ν j) := by
  change (∫⁻ t : ℝ≥0, (t : ℝ≥0∞) ∂(∑ j, ENNReal.ofReal (c j) • (ν j : Measure ℝ≥0))) = _
  rw [lintegral_finsetSum_measure]
  simp [mean, lintegral_smul_measure, smul_eq_mul]

theorem tail_finiteMixtureLaw (k m : ℕ) (ν : Fin m → ProbabilityMeasure ℝ≥0)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ j, c j = 1) :
    tailProbability k (finiteMixtureLaw m ν c hc hsum) =
      tailPolynomial k m (fun j => (ν j : Measure ℝ≥0)) c :=
  tailForm_mixture k m (fun j => (ν j : Measure ℝ≥0)) c hc

theorem mean_finiteMixtureLaw_of_real_means (m : ℕ) (ν : Fin m → ProbabilityMeasure ℝ≥0)
    (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j) (hsum : ∑ j, c j = 1)
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (hmean : ∀ j, mean (ν j) = ENNReal.ofReal (a j)) :
    mean (finiteMixtureLaw m ν c hc hsum) = ENNReal.ofReal (∑ j, c j * a j) := by
  rw [mean_finiteMixtureLaw, ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hc j) (ha j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [hmean j, ENNReal.ofReal_mul (hc j)]

/-- The supporting affine majorant follows from a genuine feasible first
variation of any maximizing law. The assertion holds at every nonnegative
test value, including values outside the original unit support. -/
theorem maximizer_supporting_line {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hxlt : x < ((n + 1 : ℕ) : ℝ)⁻¹) {μ : ProbabilityMeasure ℝ≥0}
    (hμ : Maximizes (n + 1) x μ) (z : ℝ≥0) :
    sectionTail n μ z ≤ sectionTail n μ 0 +
      ((tailProbability (n + 1) μ - sectionTail n μ 0) / x) * (z : ℝ) := by
  classical
  obtain ⟨Q, hrepr, _, hQmean⟩ :=
    maximizer_normalized_representation (by omega : 1 ≤ n + 1) hx hxlt hμ
  let K : ℝ := ((n + 1 : ℕ) : ℝ)
  let a : ℝ := K * x
  have hK : 0 < K := by dsimp [K]; positivity
  have ha : 0 < a := mul_pos hK hx
  have ha1 : a < 1 := by
    calc
      a < K * K⁻¹ := mul_lt_mul_of_pos_left hxlt hK
      _ = 1 := mul_inv_cancel₀ hK.ne'
  let v : Fin 3 → ProbabilityMeasure ℝ≥0 := ![Q, pointLaw 0, pointLaw z]
  let ν : Fin 3 → Measure ℝ≥0 := fun j => (v j : Measure ℝ≥0)
  let c : Fin 3 → ℝ := ![a, 1-a, 0]
  let d : Fin 3 → ℝ := ![-K*(z : ℝ), K*(z : ℝ)-1, 1]
  have hc : ∀ j, 0 ≤ c j := by
    intro j
    fin_cases j <;> simp only [c]
    · exact ha.le
    · exact sub_nonneg.mpr ha1.le
    · rfl
  have hmix : (∑ j : Fin 3, ENNReal.ofReal (c j) • ν j) = (μ : Measure ℝ≥0) := by
    simpa [ν, v, c, a, K, pointLaw, Fin.sum_univ_succ, add_comm] using hrepr.symm
  have hbase : tailPolynomial (n+1) 3 ν c = tailProbability (n+1) μ := by
    rw [← tailForm_mixture _ _ ν c hc, hmix]
    rfl
  have hd : d = (-(z : ℝ) / x) • c + (((z : ℝ) / x) - 1) • Pi.single 1 1 +
      Pi.single 2 1 := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases j <;> simp [d, c, a]
    all_goals field_simp
    all_goals ring
  have hcoeff (i : Fin (n+1)) : tailCoefficient (n+1) 3 ν c i d =
      (-(z : ℝ) / x) * tailProbability (n+1) μ +
        (((z : ℝ) / x) - 1) * sectionTail n μ 0 + sectionTail n μ z := by
    rw [hd, map_add, map_add, map_smul, map_smul, tailCoefficient_base, hbase,
      tailCoefficient_basis _ _ ν c hc i 1, tailCoefficient_basis _ _ ν c hc i 2, hmix]
    change _ * _ + _ * tailForm (n+1)
      (Function.update (fun _ => (μ : Measure ℝ≥0)) i (Measure.dirac 0)) +
      tailForm (n+1) (Function.update (fun _ => (μ : Measure ℝ≥0)) i (Measure.dirac z)) = _
    rw [tailForm_update_independent _ _ _ i 0, tailForm_update_independent _ _ _ i 0]
    rfl
  have hsum (t : ℝ) : ∑ j : Fin 3, (c j + t * d j) = 1 := by
    simp [c, d, Fin.sum_univ_succ]
    ring
  let m : Fin 3 → ℝ := ![K⁻¹, 0, (z : ℝ)]
  have hm0 : ∀ j, 0 ≤ m j := by
    intro j
    fin_cases j <;> simp [m, hK.le]
  have hvm : ∀ j, mean (v j) = ENNReal.ofReal (m j) := by
    intro j
    fin_cases j
    · exact hQmean
    · simp [v, m]
    · simp [v, m]
  have hmean (t : ℝ) (ht : ∀ j, 0 ≤ c j + t * d j) :
      mean (finiteMixtureLaw 3 v (fun j => c j + t*d j) ht (hsum t)) = ENNReal.ofReal x := by
    rw [mean_finiteMixtureLaw_of_real_means _ _ _ _ _ m hm0 hvm]
    congr 1
    simp [c, d, m, a, Fin.sum_univ_succ]
    field_simp
    ring
  have hpos0 : ∀ᶠ t : ℝ in 𝓝 0, 0 < c 0 + t*d 0 :=
    continuousAt_const.eventually_lt (by fun_prop) (by simpa [c] using ha)
  have hpos1 : ∀ᶠ t : ℝ in 𝓝 0, 0 < c 1 + t*d 1 :=
    continuousAt_const.eventually_lt (by fun_prop) (by simpa [c] using sub_pos.mpr ha1)
  have hmax : ∀ᶠ t : ℝ in 𝓝[>] 0,
      tailPolynomial (n+1) 3 ν (fun j => c j + t*d j) ≤
        tailPolynomial (n+1) 3 ν (fun j => c j + 0*d j) := by
    filter_upwards [hpos0.filter_mono nhdsWithin_le_nhds,
      hpos1.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht0 ht1 ht
    have hct : ∀ j, 0 ≤ c j + t*d j := by
      intro j
      fin_cases j
      · exact ht0.le
      · exact ht1.le
      · simpa [c, d] using (le_of_lt ht)
    have hbound := hμ.2 (finiteMixtureLaw 3 v (fun j => c j + t*d j) hct (hsum t))
      (hmean t hct).le
    rw [tail_finiteMixtureLaw] at hbound
    simpa only [zero_mul, add_zero, hbase] using hbound
  have hderiv := hasDerivAt_tailPolynomial_coefficients (n+1) 3 ν c d
  have hnonpos := deriv_nonpos_of_right_max hderiv hmax
  simp_rw [hcoeff] at hnonpos
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hnonpos
  have hexpr : (-(z : ℝ) / x) * tailProbability (n+1) μ +
      (((z : ℝ) / x) - 1) * sectionTail n μ 0 + sectionTail n μ z ≤ 0 := by
    nlinarith
  simp only [div_eq_mul_inv] at hexpr ⊢
  nlinarith

end SharpTailMatching.Probability
