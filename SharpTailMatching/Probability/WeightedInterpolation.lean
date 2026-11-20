module

public import SharpTailMatching.InterpolationAlgebra
public import Mathlib.Analysis.Convex.Slope

/-!
# Weighted interpolation

The prefix with zero interpolated excess is included, and the multiplier
upper bounds and their automatic nonnegativity for zero penalties are proved.
-/

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Probability

/-- An affine segment of a concave function supplies a supporting line on
the whole nonnegative domain, including both endpoints of the segment. -/
theorem concave_affine_segment_support (C : ℝ → ℝ) (hC : ConcaveOn ℝ (Set.Ici 0) C)
    (a b slope : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hsegment : ∀ x ∈ Set.Icc a b, C x = C a + slope*(x-a))
    (y : ℝ) (hy : 0 ≤ y) : C y ≤ C a + slope*(y-a) := by
  have hb : 0 ≤ b := ha.trans hab.le
  have hCb := hsegment b ⟨hab.le, le_rfl⟩
  have hsecant : (C b-C a)/(b-a) = slope := by
    rw [hCb]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  by_cases hya : y < a
  · have hsl := hC.slope_anti_adjacent hy hb hya hab
    rw [hsecant] at hsl
    have hmul := (le_div_iff₀ (sub_pos.mpr hya)).mp hsl
    nlinarith
  · have hay : a ≤ y := le_of_not_gt hya
    by_cases hyb : y ≤ b
    · exact (hsegment y ⟨hay, hyb⟩).le
    · have hby : b < y := lt_of_not_ge hyb
      have hsl := hC.slope_anti_adjacent ha hy hab hby
      rw [hsecant] at hsl
      have hmul := (div_le_iff₀ (sub_pos.mpr hby)).mp hsl
      nlinarith

theorem interpolation_slope_bound (C : ℝ → ℝ) (hC : ConcaveOn ℝ (Set.Ici 0) C)
    (a b slope xStar y f fStar : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hsegment : ∀ x ∈ Set.Icc a b, C x = C a + slope*(x-a))
    (hxStar : xStar ∈ Set.Icc a b) (hy : 0 ≤ y) (hf : f ≤ C y) (hfStar : fStar = C xStar) :
    f-fStar ≤ slope*(y-xStar) := by
  have hsupport := concave_affine_segment_support C hC a b slope ha hab hsegment y hy
  rw [hfStar, hsegment xStar hxStar]
  nlinarith

theorem interpolation_multiplier_le_weight (k q : ℕ) (κ c α Γ : ℕ → ℝ)
    (hbase : ∀ j ≤ q, Γ j = κ j)
    (hκmono : ∀ j, j+1 < k → κ j ≤ κ (j+1))
    (hc : ∀ j < k, 0 ≤ c j) (hα : ∀ j, q < j → j < k → 0 ≤ α j)
    (hrec : ∀ j, q < j → j < k →
      Γ j * (1+α j) = Γ (j-1) - c j + κ j * α j) :
    ∀ j < k, Γ j ≤ κ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjq : j ≤ q
    · rw [hbase j hjq]
    · have hqj : q < j := Nat.lt_of_not_ge hjq
      have hprev : Γ (j-1) ≤ κ j := by
        have hp := ih (j-1) (by omega) (by omega)
        have hκ := hκmono (j-1) (by omega)
        simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using hp.trans hκ
      have hden : 0 < 1+α j := by linarith [hα j hqj hj]
      have hΓ : Γ j = (Γ (j-1) - c j + κ j * α j) / (1+α j) :=
        (eq_div_iff (ne_of_gt hden)).mpr (hrec j hqj hj)
      rw [hΓ]
      exact InterpolationAlgebra.multiplier_le_weight _ _ _ _ hprev (hc j hj) (hα j hqj hj)

theorem interpolation_multiplier_nonnegative (k q : ℕ) (κ α Γ : ℕ → ℝ)
    (hbase : ∀ j ≤ q, Γ j = κ j) (hκ : ∀ j < k, 0 ≤ κ j)
    (hα : ∀ j, q < j → j < k → 0 ≤ α j)
    (hrec : ∀ j, q < j → j < k → Γ j * (1+α j) = Γ (j-1) + κ j * α j) :
    ∀ j < k, 0 ≤ Γ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjq : j ≤ q
    · rw [hbase j hjq]
      exact hκ j hj
    · have hqj : q < j := Nat.lt_of_not_ge hjq
      have hprev := ih (j-1) (by omega) (by omega)
      have hden : 0 < 1+α j := by linarith [hα j hqj hj]
      have hmul : 0 ≤ Γ j * (1+α j) := by
        rw [hrec j hqj hj]
        exact add_nonneg hprev (mul_nonneg (hκ j hj) (hα j hqj hj))
      exact nonneg_of_mul_nonneg_left hmul hden

/-- The complete telescoping comparison for the differences from an
interpolated sequence. The index `j+1` runs over `1,…,k−1`. -/
theorem weighted_interpolation_of_slopes (k q : ℕ) (hk : 1 ≤ k)
    (d g κ c α Γ : ℕ → ℝ)
    (hstep : ∀ j, 1 ≤ j → j < k → d j + g j ≤ d (j+1))
    (hzero : d 1 = 0) (hend : d k ≤ 0)
    (hprefix : ∀ j, 1 ≤ j → j ≤ q → 0 ≤ d j)
    (hcap : ∀ j, q < j → j < k → g j ≤ α j * d j)
    (hκ : ∀ j < k, 0 ≤ κ j)
    (hκmono : ∀ j, j+1 < k → κ j ≤ κ (j+1))
    (hc : ∀ j < k, 0 ≤ c j) (hα : ∀ j, q < j → j < k → 0 ≤ α j)
    (hbase : ∀ j ≤ q, Γ j = κ j)
    (hrec : ∀ j, q < j → j < k → Γ j * (1+α j) = Γ (j-1) - c j + κ j * α j)
    (hΓ : ∀ j < k, 0 ≤ Γ j) :
    (∑ j ∈ Finset.range (k-1), (κ (j+1)*g (j+1) - c (j+1)*d (j+1))) ≤ 0 := by
  have hΓle := interpolation_multiplier_le_weight k q κ c α Γ hbase hκmono hc hα hrec
  apply InterpolationAlgebra.endpoint_comparison (k-1)
    (fun j => κ (j+1)*g (j+1) - c (j+1)*d (j+1)) Γ (fun j => d (j+1))
  · intro j hj
    have hjk : j+1 < k := by omega
    by_cases hjq : j+1 ≤ q
    · have hγj : Γ j = κ j := hbase j (by omega)
      have hγnext : Γ (j+1) = κ (j+1) := hbase (j+1) hjq
      rw [hγj, hγnext]
      have hd := hprefix (j+1) (by omega) hjq
      have hcprod := mul_nonneg (hc (j+1) hjk) hd
      have hkprod := mul_nonneg (sub_nonneg.mpr (hκmono j hjk)) hd
      have hstepmul := mul_le_mul_of_nonneg_left (hstep (j+1) (by omega) hjk) (hκ (j+1) hjk)
      nlinarith
    · have hqj : q < j+1 := Nat.lt_of_not_ge hjq
      have h := InterpolationAlgebra.local_multiplier_inequality
        (d (j+1)) (d (j+1+1)) (g (j+1)) (κ (j+1)) (c (j+1)) (α (j+1)) (Γ j) (Γ (j+1))
        (hstep (j+1) (by omega) hjk) (hcap (j+1) hqj hjk) (hΓ (j+1) hjk)
        (hΓle (j+1) hjk) (by simpa only [Nat.add_sub_cancel] using hrec (j+1) hqj hjk)
      exact h
  · exact hzero
  · simpa only [Nat.sub_add_cancel hk] using hend
  · exact hΓ (k-1) (by omega)

/-- Weighted interpolation in the original excess/tail variables. -/
theorem weighted_interpolation (k q : ℕ) (hk : 1 ≤ k)
    (e f eStar fStar κ c α Γ : ℕ → ℝ)
    (he0 : e 1 = 0) (hestar0 : eStar 1 = 0)
    (he : ∀ j, 1 ≤ j → j < k → e j + f j ≤ e (j+1))
    (hstar : ∀ j, 1 ≤ j → j < k → eStar (j+1) = eStar j + fStar j)
    (hend : e k ≤ eStar k)
    (hprefix : ∀ j, 1 ≤ j → j ≤ q → 0 ≤ e j ∧ eStar j = 0)
    (hcap : ∀ j, q < j → j < k → f j-fStar j ≤ α j*(e j-eStar j))
    (hκ : ∀ j < k, 0 ≤ κ j)
    (hκmono : ∀ j, j+1 < k → κ j ≤ κ (j+1))
    (hc : ∀ j < k, 0 ≤ c j) (hα : ∀ j, q < j → j < k → 0 ≤ α j)
    (hbase : ∀ j ≤ q, Γ j = κ j)
    (hrec : ∀ j, q < j → j < k → Γ j*(1+α j) = Γ (j-1)-c j+κ j*α j)
    (hΓ : ∀ j < k, 0 ≤ Γ j) :
    (∑ j ∈ Finset.range (k-1), (κ (j+1)*f (j+1)-c (j+1)*e (j+1))) ≤
      ∑ j ∈ Finset.range (k-1), (κ (j+1)*fStar (j+1)-c (j+1)*eStar (j+1)) := by
  let d := fun j => e j-eStar j
  let g := fun j => f j-fStar j
  have h := weighted_interpolation_of_slopes k q hk d g κ c α Γ
    (fun j hj hjk => by dsimp [d,g]; linarith [he j hj hjk, hstar j hj hjk])
    (by simp [d,he0,hestar0]) (sub_nonpos.mpr hend)
    (fun j hj hjq => by dsimp [d]; rw [(hprefix j hj hjq).2,sub_zero]; exact (hprefix j hj hjq).1)
    hcap hκ hκmono hc hα hbase hrec hΓ
  have hid :
      (∑ j ∈ Finset.range (k-1), (κ (j+1)*g (j+1)-c (j+1)*d (j+1))) =
        (∑ j ∈ Finset.range (k-1), (κ (j+1)*f (j+1)-c (j+1)*e (j+1))) -
        (∑ j ∈ Finset.range (k-1), (κ (j+1)*fStar (j+1)-c (j+1)*eStar (j+1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [d,g]
    ring
  rw [hid] at h
  linarith

end SharpTailMatching.Probability
