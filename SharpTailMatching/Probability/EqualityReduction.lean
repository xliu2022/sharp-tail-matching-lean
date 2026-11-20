module

public import SharpTailMatching.Probability.MixtureRigidity

/-! # Equality at every mean from equality at the critical mean

The critical bound and critical classification are explicit hypotheses here.
The main theorem will discharge them with the maximizer analysis. Above the
crossing, cancellation of the zero mixture identifies either candidate law;
strict comparison of their success probabilities eliminates the unit law.
This avoids any extra assumption about the support of the original law.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

theorem sharpTailValue_eq_unit_before {k : ℕ} (hk : 2 ≤ k) {β x : ℝ}
    (hβpos : 0 < β) (hβlt : β < (k:ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (hx : 0 < x) (hxβ : x < β) :
    sharpTailValue k x = 1-(1-x)^k := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hki : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
  have h := unit_candidate_gt_before_critical k hk β x hβpos (hβlt.trans hki).le hβcross hx hxβ
  simp only [sharpTailValue, (hxβ.trans hβlt).le, ite_true, max_eq_left h.le]

theorem sharpTailValue_eq_small_after {k : ℕ} (hk : 2 ≤ k) {β x : ℝ}
    (hβpos : 0 < β) (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (hβx : β < x) (hxle : x ≤ (k:ℝ)⁻¹) :
    sharpTailValue k x = ((k:ℝ)*x)^k := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hki : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
  have h := small_candidate_gt_after_critical k hk β x hβpos hβcross hβx (hxle.trans hki.le)
  simp only [sharpTailValue, hxle, ite_true, max_eq_right h.le]

theorem sharpTailValue_eq_critical {k : ℕ} {β : ℝ} (hβlt : β < (k:ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k) :
    sharpTailValue k β = ((k:ℝ)*β)^k := by
  simp only [sharpTailValue, hβlt.le, ite_true, hβcross, max_self]

theorem equality_below_of_critical_classification {k : ℕ} (hk : 2 ≤ k)
    {β x : ℝ} (hβpos : 0 < β) (hβlt : β < (k:ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (hclass : ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal β →
      tailProbability k ν = ((k:ℝ)*β)^k →
      (ν : Measure ℝ≥0) = unitBernoulliMeasure β ∨
        (ν : Measure ℝ≥0) = smallBernoulliMeasure k β)
    (hx : 0 < x) (hxβ : x < β) (μ : ProbabilityMeasure ℝ≥0)
    (hmean : mean μ ≤ ENNReal.ofReal x)
    (hmax : tailProbability k μ = sharpTailValue k x) :
    (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hki : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
  have hβ1 : β < 1 := hβlt.trans hki
  have hx1 : x < 1 := hxβ.trans hβ1
  let t := (β-x)/(1-x)
  have htpos : 0 < t := div_pos (sub_pos.mpr hxβ) (sub_pos.mpr hx1)
  have ht1 : t < 1 := by
    apply (div_lt_one (sub_pos.mpr hx1)).mpr
    linarith
  have hid : (1-t)*x+t = β := by
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr hx1)]
    ring
  have hfactor : (1-t)*(1-x) = 1-β := by nlinarith only [hid]
  have hpower : (1-t)^k*(1-x)^k = (1-β)^k := by rw [← mul_pow, hfactor]
  let ν := addOneLaw μ t htpos.le ht1.le
  have hνmean : mean ν ≤ ENNReal.ofReal β := by
    rw [show mean ν = mean (addOneLaw μ t htpos.le ht1.le) from rfl, mean_addOneLaw]
    calc
      _ ≤ ENNReal.ofReal (1-t)*ENNReal.ofReal x+ENNReal.ofReal t := by gcongr
      _ = ENNReal.ofReal ((1-t)*x+t) := by
        rw [ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr ht1.le) hx.le) htpos.le,
          ENNReal.ofReal_mul (sub_nonneg.mpr ht1.le)]
      _ = ENNReal.ofReal β := by rw [hid]
  have hμtail : tailProbability k μ = 1-(1-x)^k :=
    hmax.trans (sharpTailValue_eq_unit_before hk hβpos hβlt hβcross hx hxβ)
  have hνtail : tailProbability k ν = ((k:ℝ)*β)^k := by
    dsimp [ν]
    rw [tail_addOneLaw, hμtail, show 1-(1-(1-x)^k) = (1-x)^k by ring, hpower]
    exact hβcross
  rcases hclass ν hνmean hνtail with hunit | hsmall
  · have hstandard := addOne_unitBernoulli x t hx.le hx1.le htpos.le ht1.le
    rw [hid] at hstandard
    have heq : μ = unitBernoulliLaw x hx.le hx1.le :=
      addOneLaw_injective htpos.le ht1 μ _ (hunit.trans hstandard.symm)
    exact congrArg (fun ρ : ProbabilityMeasure ℝ≥0 => (ρ : Measure ℝ≥0)) heq
  · exact (addOne_ne_smallBernoulli hk μ htpos ht1.le β hsmall).elim

theorem equality_above_of_critical_classification {k : ℕ} (hk : 2 ≤ k)
    {β x : ℝ} (hβpos : 0 < β)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (hbound : ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal β →
      tailProbability k ν ≤ ((k:ℝ)*β)^k)
    (hclass : ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal β →
      tailProbability k ν = ((k:ℝ)*β)^k →
      (ν : Measure ℝ≥0) = unitBernoulliMeasure β ∨
        (ν : Measure ℝ≥0) = smallBernoulliMeasure k β)
    (hβx : β < x) (hxle : x ≤ (k:ℝ)⁻¹) (μ : ProbabilityMeasure ℝ≥0)
    (hmean : mean μ ≤ ENNReal.ofReal x)
    (hmax : tailProbability k μ = sharpTailValue k x) :
    (μ : Measure ℝ≥0) = smallBernoulliMeasure k x := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hki : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
  have hx : 0 < x := hβpos.trans hβx
  have hx1 : x ≤ 1 := hxle.trans hki.le
  let t := 1-β/x
  have hq : 0 < β/x := div_pos hβpos hx
  have hq1 : β/x < 1 := (div_lt_one hx).mpr hβx
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hid : (1-t)*x = β := by dsimp [t]; field_simp; ring
  have hpower : (1-t)^k*((k:ℝ)*x)^k = ((k:ℝ)*β)^k := by
    rw [← mul_pow]
    congr 1
    nlinarith only [hid]
  let ν := addZeroLaw μ t ht ht1.le
  have hνmean : mean ν ≤ ENNReal.ofReal β := by
    rw [show mean ν = mean (addZeroLaw μ t ht ht1.le) from rfl, mean_addZeroLaw]
    calc
      _ ≤ ENNReal.ofReal (1-t)*ENNReal.ofReal x := by gcongr
      _ = ENNReal.ofReal ((1-t)*x) := (ENNReal.ofReal_mul (sub_nonneg.mpr ht1.le)).symm
      _ = ENNReal.ofReal β := by rw [hid]
  have hμtail : tailProbability k μ = ((k:ℝ)*x)^k :=
    hmax.trans (sharpTailValue_eq_small_after hk hβpos hβcross hβx hxle)
  have hνtail : tailProbability k ν = ((k:ℝ)*β)^k := by
    apply le_antisymm (hbound ν hνmean)
    have h := tail_addZeroLaw_lower_bound k μ t ht ht1.le
    rw [hμtail, hpower] at h
    exact h
  rcases hclass ν hνmean hνtail with hunit | hsmall
  · have hstandard := addZero_unitBernoulli x t hx.le hx1 ht ht1.le
    rw [hid] at hstandard
    have heq : μ = unitBernoulliLaw x hx.le hx1 :=
      addZeroLaw_injective ht ht1 μ _ (hunit.trans hstandard.symm)
    have hstrict := small_candidate_gt_after_critical k hk β x hβpos hβcross hβx hx1
    rw [heq, tailProbability_unitBernoulliLaw] at hμtail
    exact (ne_of_lt hstrict hμtail).elim
  · have hstandard := addZero_smallBernoulli k (by omega) x t hx.le hxle ht ht1.le
    rw [hid] at hstandard
    have heq : μ = smallBernoulliLaw k (by omega) x hx.le hxle :=
      addZeroLaw_injective ht ht1 μ _ (hsmall.trans hstandard.symm)
    exact congrArg (fun ρ : ProbabilityMeasure ℝ≥0 => (ρ : Measure ℝ≥0)) heq

theorem sharp_tail_equality_of_critical (k : ℕ) (hk : 2 ≤ k)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < (k:ℝ)⁻¹)
    (hβcross : 1-(1-β)^k = ((k:ℝ)*β)^k)
    (hbound : ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal β →
      tailProbability k ν ≤ ((k:ℝ)*β)^k)
    (hclass : ∀ ν : ProbabilityMeasure ℝ≥0, mean ν ≤ ENNReal.ofReal β →
      tailProbability k ν = ((k:ℝ)*β)^k →
      (ν : Measure ℝ≥0) = unitBernoulliMeasure β ∨
        (ν : Measure ℝ≥0) = smallBernoulliMeasure k β)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ (k:ℝ)⁻¹)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ = sharpTailValue k x ↔
      (x < β ∧ (μ : Measure ℝ≥0) = unitBernoulliMeasure x) ∨
      (x = β ∧ ((μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)) ∨
      (β < x ∧ (μ : Measure ℝ≥0) = smallBernoulliMeasure k x) := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hki : (k:ℝ)⁻¹ < 1 := (inv_lt_one₀ hkpos).mpr (by exact_mod_cast (show 1 < k by omega))
  have hx1 : x ≤ 1 := hxle.trans hki.le
  constructor
  · intro hmax
    rcases lt_trichotomy x β with hlt | heq | hgt
    · exact Or.inl ⟨hlt, equality_below_of_critical_classification hk hβpos hβlt hβcross hclass
        hx hlt μ hmean hmax⟩
    · right; left
      refine ⟨heq, ?_⟩
      subst x
      apply hclass μ hmean
      exact hmax.trans (sharpTailValue_eq_critical hβlt hβcross)
    · right; right
      exact ⟨hgt, equality_above_of_critical_classification hk hβpos hβcross hbound hclass
        hgt hxle μ hmean hmax⟩
  · intro h
    rcases h with ⟨hlt, hμ⟩ | ⟨heq, hμ | hμ⟩ | ⟨hgt, hμ⟩
    · have heq : μ = unitBernoulliLaw x hx.le hx1 := Subtype.ext hμ
      rw [heq, tailProbability_unitBernoulliLaw,
        sharpTailValue_eq_unit_before hk hβpos hβlt hβcross hx hlt]
    · have hμeq : μ = unitBernoulliLaw x hx.le hx1 := Subtype.ext hμ
      rw [hμeq, tailProbability_unitBernoulliLaw, heq,
        sharpTailValue_eq_critical hβlt hβcross, hβcross]
    · have hμeq : μ = smallBernoulliLaw k (by omega) x hx.le hxle := Subtype.ext hμ
      rw [hμeq, tailProbability_smallBernoulliLaw, heq, sharpTailValue_eq_critical hβlt hβcross]
    · have hμeq : μ = smallBernoulliLaw k (by omega) x hx.le hxle := Subtype.ext hμ
      rw [hμeq, tailProbability_smallBernoulliLaw,
        sharpTailValue_eq_small_after hk hβpos hβcross hgt hxle]

end SharpTailMatching.Probability
