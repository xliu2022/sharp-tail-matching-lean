module

public import Mathlib.Tactic

public section

open scoped BigOperators

namespace SharpTailMatching.ProductAlgebra

/-- The minimum-product chord on the unit cube. This induction performs the
endpoint transfer directly and needs neither a minimizer nor a sorting choice. -/
theorem unit_cube_product_lower (n ℓ : ℕ) (a : Fin n → ℝ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1)
    (hs0 : (ℓ : ℝ) ≤ ∑ i, a i) (hs1 : (∑ i, a i) ≤ (ℓ : ℝ) + 1) :
    q ^ ℓ * (1 - (1 - q) * ((∑ i, a i) - ℓ)) ≤
      ∏ i, (1 - (1 - q) * a i) := by
  induction n generalizing ℓ with
  | zero =>
      have hℓ : ℓ = 0 := by
        have h : (ℓ : ℝ) ≤ 0 := by simpa using hs0
        exact_mod_cast Nat.eq_zero_of_le_zero (by exact_mod_cast h)
      subst ℓ
      simp
  | succ n ih =>
      let s : ℝ := ∑ i : Fin n, a i.succ
      have hsnonneg : 0 ≤ s := Finset.sum_nonneg fun i _ => ha0 i.succ
      have hsum : (∑ i : Fin (n + 1), a i) = a 0 + s := Fin.sum_univ_succ a
      have hf : 0 ≤ 1 - (1 - q) * a 0 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq1) (sub_nonneg.mpr (ha1 0))]
      rw [hsum] at hs0 hs1 ⊢
      rw [Fin.prod_univ_succ]
      by_cases hsℓ : (ℓ : ℝ) ≤ s
      · have hrest := ih ℓ (fun i => a i.succ) (fun i => ha0 i.succ)
          (fun i => ha1 i.succ) hsℓ (by change s ≤ _; linarith [ha0 0])
        have hmul := mul_le_mul_of_nonneg_left hrest hf
        have hid : (1 - (1 - q) * a 0) * (q ^ ℓ * (1 - (1 - q) * (s - ℓ))) -
            q ^ ℓ * (1 - (1 - q) * (a 0 + s - ℓ)) =
            q ^ ℓ * (1 - q) ^ 2 * a 0 * (s - ℓ) := by ring
        have hpos : 0 ≤ q ^ ℓ * (1 - q) ^ 2 * a 0 * (s - ℓ) := by
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _))
            (ha0 0)) (sub_nonneg.mpr hsℓ)
        change (1 - (1 - q) * a 0) * (q ^ ℓ * (1 - (1 - q) * (s - ℓ))) ≤ _ at hmul
        linarith
      · cases ℓ with
        | zero => norm_num at hsℓ; linarith
        | succ ℓ =>
            have hℓ : ((ℓ + 1 : ℕ) : ℝ) = (ℓ : ℝ) + 1 := by norm_num
            rw [hℓ] at hs0 hs1
            have hsupper : s ≤ (ℓ : ℝ) + 1 := by
              have h := le_of_not_ge hsℓ
              simpa only [Nat.cast_add, Nat.cast_one] using h
            have hrest := ih ℓ (fun i => a i.succ) (fun i => ha0 i.succ)
              (fun i => ha1 i.succ) (by change _ ≤ s; linarith [ha1 0]) hsupper
            have hmul := mul_le_mul_of_nonneg_left hrest hf
            have hid : (1 - (1 - q) * a 0) * (q ^ ℓ * (1 - (1 - q) * (s - ℓ))) -
                q ^ (ℓ + 1) * (1 - (1 - q) * (a 0 + s - (ℓ + 1))) =
                q ^ ℓ * (1 - q) ^ 2 * (1 - a 0) * (1 + ℓ - s) := by
              rw [pow_succ]
              ring
            have hpos : 0 ≤ q ^ ℓ * (1 - q) ^ 2 * (1 - a 0) * (1 + ℓ - s) := by
              apply mul_nonneg
              · exact mul_nonneg (mul_nonneg (pow_nonneg hq0 _) (sq_nonneg _))
                  (sub_nonneg.mpr (ha1 0))
              · linarith
            change (1 - (1 - q) * a 0) * (q ^ ℓ * (1 - (1 - q) * (s - ℓ))) ≤ _ at hmul
            norm_num only [Nat.cast_succ] at *
            linarith

theorem bounded_product_lower (n ℓ : ℕ) (z : Fin n → ℝ) {m r : ℝ}
    (hm : 0 ≤ m) (hr : m < r)
    (hz0 : ∀ i, 0 ≤ z i) (hzm : ∀ i, z i ≤ m)
    (hs0 : (ℓ : ℝ) * m ≤ ∑ i, z i)
    (hs1 : (∑ i, z i) ≤ ((ℓ : ℝ) + 1) * m) :
    (1 - m / r) ^ ℓ * (1 - ((∑ i, z i) - ℓ * m) / r) ≤ ∏ i, (1 - z i / r) := by
  have hr0 : 0 < r := hm.trans_lt hr
  by_cases hm0 : m = 0
  · have hz : ∀ i, z i = 0 := fun i => le_antisymm (hm0 ▸ hzm i) (hz0 i)
    simp [hm0, hz]
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    let a : Fin n → ℝ := fun i => z i / m
    let q : ℝ := 1 - m / r
    have hq0 : 0 ≤ q := by dsimp [q]; exact sub_nonneg.mpr ((div_le_one hr0).mpr hr.le)
    have hq1 : q ≤ 1 := by dsimp [q]; linarith [div_nonneg hm hr0.le]
    have ha0 : ∀ i, 0 ≤ a i := fun i => div_nonneg (hz0 i) hm
    have ha1 : ∀ i, a i ≤ 1 := fun i => (div_le_one hmpos).mpr (hzm i)
    have hsum : (∑ i, a i) = (∑ i, z i) / m := by simp only [a, Finset.sum_div]
    have h := unit_cube_product_lower n ℓ a hq0 hq1 ha0 ha1
      (by rw [hsum]; exact (le_div_iff₀ hmpos).mpr hs0)
      (by rw [hsum]; exact (div_le_iff₀ hmpos).mpr hs1)
    have hf (i : Fin n) : 1 - (1 - q) * a i = 1 - z i / r := by
      dsimp [q, a]
      field_simp
      ring
    have hl : q ^ ℓ * (1 - (1 - q) * ((∑ i, a i) - ℓ)) =
        (1 - m / r) ^ ℓ * (1 - ((∑ i, z i) - ℓ * m) / r) := by
      rw [hsum]
      dsimp [q]
      field_simp
      ring
    rw [hl] at h
    simpa only [hf] using h

/-- Algebraic form of Corollary 3.2 in the regime `r > m` where the product
lemma applies. Its probabilistic input is stated explicitly. -/
theorem equal_mean_product_corollary (j ℓ : ℕ) (z : Fin j → ℝ) {m r p : ℝ}
    (hm : 0 ≤ m) (hr : m < r)
    (hz0 : ∀ i, 0 ≤ z i) (hzm : ∀ i, z i ≤ m)
    (hsum : (∑ i, z i) = r - 1 + j * m)
    (hrlo : 1 - ((j : ℝ) - ℓ) * m ≤ r)
    (hrhi : r ≤ 1 - ((j : ℝ) - ℓ - 1) * m)
    (hp : (∏ i, (1 - z i / r)) ≤ p) :
    (1 - m / r) ^ ℓ * (1 - ((j : ℝ) - ℓ) * m) / r ≤ p := by
  have hr0 : 0 < r := hm.trans_lt hr
  have h := bounded_product_lower j ℓ z hm hr hz0 hzm
    (by rw [hsum]; nlinarith) (by rw [hsum]; nlinarith)
  have hid : (1 - m / r) ^ ℓ * (1 - ((∑ i, z i) - ℓ * m) / r) =
      (1 - m / r) ^ ℓ * (1 - ((j : ℝ) - ℓ) * m) / r := by
    rw [hsum]
    field_simp
    ring
  rw [hid] at h
  exact h.trans hp

end SharpTailMatching.ProductAlgebra
