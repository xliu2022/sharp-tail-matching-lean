module

public import SharpTailMatching.Probability.Reduction
public import SharpTailMatching.Probability.Endpoints
public import SharpTailMatching.Probability.CriticalMean

/-! # Recovering a probability law from an atomic mixture

All cancellation arguments are for finite measures. They apply to arbitrary
Borel probability laws and do not assume that the original law is atomic.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem atom_mixture_injective (v : ℝ≥0) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (μ ν : ProbabilityMeasure ℝ≥0)
    (h : ENNReal.ofReal a • (μ : Measure ℝ≥0) + ENNReal.ofReal b • Measure.dirac v =
      ENNReal.ofReal a • (ν : Measure ℝ≥0) + ENNReal.ofReal b • Measure.dirac v) :
    μ = ν := by
  apply Subtype.ext
  apply Measure.ext
  intro s hs
  have heq := congrArg (fun ρ : Measure ℝ≥0 => (ρ s).toReal) h
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul] at heq
  have hμ : ENNReal.ofReal a*(μ : Measure ℝ≥0) s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hν : ENNReal.ofReal a*(ν : Measure ℝ≥0) s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hv : ENNReal.ofReal b*Measure.dirac v s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [ENNReal.toReal_add hμ hv, ENNReal.toReal_add hν hv] at heq
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le] at heq
  have hr : ((μ : Measure ℝ≥0) s).toReal = ((ν : Measure ℝ≥0) s).toReal := by nlinarith
  exact (ENNReal.ofReal_toReal (measure_ne_top (μ : Measure ℝ≥0) s)).symm.trans
    ((congrArg ENNReal.ofReal hr).trans (ENNReal.ofReal_toReal (measure_ne_top (ν : Measure ℝ≥0) s)))

theorem addOneLaw_injective {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (μ ν : ProbabilityMeasure ℝ≥0)
    (h : (addOneLaw μ t ht ht1.le : Measure ℝ≥0) =
      (addOneLaw ν t ht ht1.le : Measure ℝ≥0)) : μ = ν :=
  atom_mixture_injective 1 (by linarith) ht μ ν h

theorem addZeroLaw_injective {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (μ ν : ProbabilityMeasure ℝ≥0)
    (h : (addZeroLaw μ t ht ht1.le : Measure ℝ≥0) =
      (addZeroLaw ν t ht ht1.le : Measure ℝ≥0)) : μ = ν :=
  atom_mixture_injective 0 (by linarith) ht μ ν h

theorem mix_zero_twoAtom (v : ℝ≥0) {p t : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ENNReal.ofReal (1-t) •
      (ENNReal.ofReal (1-p) • Measure.dirac 0 + ENNReal.ofReal p • Measure.dirac v) +
      ENNReal.ofReal t • Measure.dirac 0 =
    ENNReal.ofReal (1-(1-t)*p) • Measure.dirac 0 +
      ENNReal.ofReal ((1-t)*p) • Measure.dirac v := by
  have h0 : ENNReal.ofReal (1-t)*ENNReal.ofReal (1-p)+ENNReal.ofReal t =
      ENNReal.ofReal (1-(1-t)*p) := by
    rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) ht0]
    congr 1
    ring
  have h1 : ENNReal.ofReal (1-t)*ENNReal.ofReal p = ENNReal.ofReal ((1-t)*p) :=
    (ENNReal.ofReal_mul (by linarith)).symm
  rw [smul_add, smul_smul, smul_smul, add_right_comm, ← add_smul, h0, h1]

theorem addZero_unitBernoulli (x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (addZeroLaw (unitBernoulliLaw x hx0 hx1) t ht0 ht1 : Measure ℝ≥0) =
      unitBernoulliMeasure ((1-t)*x) := by
  exact mix_zero_twoAtom 1 hx0 hx1 ht0 ht1

theorem addZero_smallBernoulli (k : ℕ) (hk : 1 ≤ k) (x t : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ (k:ℝ)⁻¹) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (addZeroLaw (smallBernoulliLaw k hk x hx0 hx1) t ht0 ht1 : Measure ℝ≥0) =
      smallBernoulliMeasure k ((1-t)*x) := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hpx : (k:ℝ)*x ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hx1 hkpos.le
    simpa [hkpos.ne'] using h
  have h := mix_zero_twoAtom (k:ℝ≥0)⁻¹ (mul_nonneg hkpos.le hx0) hpx ht0 ht1
  have hid : (1-t)*((k:ℝ)*x) = (k:ℝ)*((1-t)*x) := by ring
  change ENNReal.ofReal (1-t) •
      (ENNReal.ofReal (1-(k:ℝ)*x) • Measure.dirac 0 +
        ENNReal.ofReal ((k:ℝ)*x) • Measure.dirac (k:ℝ≥0)⁻¹) +
      ENNReal.ofReal t • Measure.dirac 0 =
    ENNReal.ofReal (1-(k:ℝ)*((1-t)*x)) • Measure.dirac 0 +
      ENNReal.ofReal ((k:ℝ)*((1-t)*x)) • Measure.dirac (k:ℝ≥0)⁻¹
  rw [← hid]
  exact h

theorem addOne_unitBernoulli (x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (addOneLaw (unitBernoulliLaw x hx0 hx1) t ht0 ht1 : Measure ℝ≥0) =
      unitBernoulliMeasure ((1-t)*x+t) := by
  have h0 : ENNReal.ofReal (1-t)*ENNReal.ofReal (1-x) =
      ENNReal.ofReal (1-((1-t)*x+t)) := by
    rw [← ENNReal.ofReal_mul (by linarith)]
    congr 1
    ring
  have h1 : ENNReal.ofReal (1-t)*ENNReal.ofReal x+ENNReal.ofReal t =
      ENNReal.ofReal ((1-t)*x+t) := by
    rw [← ENNReal.ofReal_mul (by linarith),
      ← ENNReal.ofReal_add (mul_nonneg (by linarith) hx0) ht0]
  change ENNReal.ofReal (1-t) •
      (ENNReal.ofReal (1-x) • Measure.dirac 0 + ENNReal.ofReal x • Measure.dirac 1) +
      ENNReal.ofReal t • Measure.dirac 1 = _
  rw [smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, h0, h1]
  rfl

theorem addOne_ne_smallBernoulli {k : ℕ} (hk : 2 ≤ k) (μ : ProbabilityMeasure ℝ≥0)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (β : ℝ) :
    (addOneLaw μ t ht.le ht1 : Measure ℝ≥0) ≠ smallBernoulliMeasure k β := by
  have hk1 : (1:ℝ≥0) < k := by exact_mod_cast (show 1 < k by omega)
  have hinv : (k:ℝ≥0)⁻¹ ≠ 1 := by
    exact ne_of_lt ((inv_lt_one₀ (zero_lt_one.trans hk1)).mpr hk1)
  intro h
  have hm := congrArg (fun ρ : Measure ℝ≥0 => ρ {1}) h
  simp only [addOneLaw, addOneMeasure, smallBernoulliMeasure, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul] at hm
  simp [hinv] at hm
  exact not_le_of_gt ht hm.2

end SharpTailMatching.Probability
