module

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

/-!
# The unique positive crossing of the two standard tail functions

The sum `(1-x)^k + (k*x)^k` is strictly convex on `[0,1]`.
It equals one at zero, is below one at `1/(2*k^2)`, and is
above one at `1/k`. The intermediate value theorem gives a
positive crossing, and strict convexity excludes a second one.
-/

@[expose] public section

open Set

namespace SharpTailMatching

private theorem candidateSum_strictConvex (k : ℕ) (hk : 2 ≤ k) :
    StrictConvexOn ℝ (Icc 0 1)
      (fun x : ℝ => (1 - x)^k + ((k : ℝ) * x)^k) := by
  have hp := strictConvexOn_pow hk
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hsub : (1 - x) ≠ (1 - y) := by
    intro h
    apply hxy
    linarith
  have h₁ := hp.2 (show 1 - x ∈ Ici (0 : ℝ) by exact sub_nonneg.mpr hx.2)
    (show 1 - y ∈ Ici (0 : ℝ) by exact sub_nonneg.mpr hy.2)
    hsub ha hb hab
  have h₂ := hp.convexOn.2
    (show (k : ℝ) * x ∈ Ici (0 : ℝ) by exact mul_nonneg (Nat.cast_nonneg _) hx.1)
    (show (k : ℝ) * y ∈ Ici (0 : ℝ) by exact mul_nonneg (Nat.cast_nonneg _) hy.1)
    ha.le hb.le hab
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  have hleft : 1 - (a*x+b*y) = a*(1-x)+b*(1-y) := by nlinarith
  have hright : (k : ℝ)*(a*x+b*y) = a*((k : ℝ)*x)+b*((k : ℝ)*y) := by ring
  rw [hleft, hright]
  nlinarith only [h₁, h₂]

/-- For every `k ≥ 2`, the two standard candidate success probabilities
have exactly one crossing in the nontrivial open mean interval. -/
theorem critical_mean_exists_unique (k : ℕ) (hk : 2 ≤ k) :
    ∃! β : ℝ, 0 < β ∧ β < (k : ℝ)⁻¹ ∧
      1 - (1 - β)^k = ((k : ℝ) * β)^k := by
  let c : ℝ := k
  have hc2 : 2 ≤ c := by dsimp [c]; exact_mod_cast hk
  have hcpos : 0 < c := by linarith
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hkpos : 0 < k := by omega
  have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
  have hinvpos : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hinvlt : c⁻¹ < 1 := (inv_lt_one₀ hcpos).2 (by linarith)
  let a : ℝ := 1 / (2*c^2)
  have hapos : 0 < a := by dsimp [a]; positivity
  have halt : a < c⁻¹ := by
    dsimp [a]
    rw [one_div, inv_lt_inv₀ (by positivity) hcpos]
    nlinarith
  have haone : a < 1 := halt.trans hinvlt
  have hca : c*a = 1/(2*c) := by
    dsimp [a]
    field_simp
  have hcale : c*a ≤ 1 := by
    rw [hca]
    apply (div_le_one (by positivity : 0 < 2*c)).2
    linarith
  have hsquare : (c*a)^2 = a/2 := by
    dsimp [a]
    field_simp
  let f : ℝ → ℝ := fun x => (1-x)^k + (c*x)^k
  have hfa : f a < 1 := by
    have h₁ := pow_le_of_le_one (by linarith : 0 ≤ 1-a)
      (by linarith : 1-a ≤ 1) hkne
    have h₂ := pow_le_pow_of_le_one (by positivity : 0 ≤ c*a) hcale hk
    dsimp [f]
    nlinarith only [h₁, h₂, hsquare, hapos]
  have hfb : 1 < f c⁻¹ := by
    have hpos : 0 < (1-c⁻¹)^k := pow_pos (by linarith) _
    dsimp [f]
    rw [mul_inv_cancel₀ hcne, one_pow]
    linarith
  have hcont : Continuous f := by dsimp [f]; fun_prop
  obtain ⟨β, hβinterval, hβeq⟩ :=
    intermediate_value_Icc halt.le hcont.continuousOn ⟨hfa.le, hfb.le⟩
  have hβpos : 0 < β := hapos.trans_le hβinterval.1
  have hβlt : β < c⁻¹ := by
    rcases hβinterval.2.eq_or_lt with h | h
    · exfalso
      rw [h] at hβeq
      linarith
    · exact h
  have hβcross : 1-(1-β)^k = (c*β)^k := by
    dsimp [f] at hβeq
    linarith
  refine ⟨β, ⟨hβpos, hβlt, hβcross⟩, ?_⟩
  intro γ hγ
  have hγeq : f γ = 1 := by
    dsimp [f, c]
    linarith [hγ.2.2]
  have hfconv : StrictConvexOn ℝ (Icc 0 1) f := candidateSum_strictConvex k hk
  have hfzero : f 0 = 1 := by simp [f, hkne]
  have hβmem : β ∈ Icc (0 : ℝ) 1 := ⟨hβpos.le, (hβlt.trans hinvlt).le⟩
  have hγmem : γ ∈ Icc (0 : ℝ) 1 := ⟨hγ.1.le, (hγ.2.1.trans hinvlt).le⟩
  rcases lt_trichotomy γ β with hlt | heq | hgt
  · have h := hfconv.lt_on_openSegment (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      hβmem hβpos.ne (Ioo_subset_openSegment ⟨hγ.1, hlt⟩)
    rw [hfzero, hβeq, hγeq, max_self] at h
    exact (lt_irrefl _ h).elim
  · exact heq
  · have h := hfconv.lt_on_openSegment (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
      hγmem hγ.1.ne (Ioo_subset_openSegment ⟨hβpos, hgt⟩)
    rw [hfzero, hβeq, hγeq, max_self] at h
    exact (lt_irrefl _ h).elim

/-- Before the positive crossing, the unit Bernoulli construction is strictly
better than the small Bernoulli construction. -/
theorem unit_candidate_gt_before_critical (k : ℕ) (hk : 2 ≤ k)
    (β x : ℝ) (hβpos : 0 < β) (hβle : β ≤ 1)
    (hβcross : 1-(1-β)^k = ((k : ℝ)*β)^k)
    (hxpos : 0 < x) (hxlt : x < β) :
    ((k : ℝ)*x)^k < 1-(1-x)^k := by
  have hkne : k ≠ 0 := by omega
  have h := (candidateSum_strictConvex k hk).lt_on_openSegment
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show β ∈ Icc (0 : ℝ) 1 from ⟨hβpos.le, hβle⟩)
    hβpos.ne (Ioo_subset_openSegment ⟨hxpos, hxlt⟩)
  have heq : (1-β)^k + ((k : ℝ)*β)^k = 1 := by linarith
  simp only [sub_zero, one_pow, mul_zero, zero_pow hkne, add_zero, heq, max_self] at h
  linarith

/-- After the positive crossing, the small Bernoulli construction is strictly
better than the unit Bernoulli construction, as long as the mean is at most one. -/
theorem small_candidate_gt_after_critical (k : ℕ) (hk : 2 ≤ k)
    (β x : ℝ) (hβpos : 0 < β)
    (hβcross : 1-(1-β)^k = ((k : ℝ)*β)^k)
    (hβlt : β < x) (hxle : x ≤ 1) :
    1-(1-x)^k < ((k : ℝ)*x)^k := by
  have hkne : k ≠ 0 := by omega
  have h := (candidateSum_strictConvex k hk).lt_on_openSegment
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show x ∈ Icc (0 : ℝ) 1 from ⟨(hβpos.trans hβlt).le, hxle⟩)
    (hβpos.trans hβlt).ne (Ioo_subset_openSegment ⟨hβpos, hβlt⟩)
  have heq : (1-β)^k + ((k : ℝ)*β)^k = 1 := by linarith
  simp only [sub_zero, one_pow, mul_zero, zero_pow hkne, add_zero, heq] at h
  rcases lt_max_iff.mp h with hfalse | hsum
  · exact (lt_irrefl _ hfalse).elim
  · linarith

end SharpTailMatching
