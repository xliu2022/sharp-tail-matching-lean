module

public import SharpTailMatching.BinomialTailBounds

/-! # Exact constants for the binomial-tail remainder -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace SharpTailMatching.TailEstimates

def halfTailBound (n : ℕ) : ℝ :=
  3*tailPrefactor n (1/2)/(1-tailRatio n (1/2))^2

def factorialScale (n : ℕ) : ℝ :=
  (n:ℝ)^2 / ((2:ℝ)^(n+1)*((n+1).factorial:ℝ))

theorem tailRatio_mono {n : ℕ} (hn : 1 ≤ n) {c d : ℝ} (hcd : c ≤ d) :
    tailRatio n c ≤ tailRatio n d := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold tailRatio
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcd (by positivity)) (by positivity)

theorem tail_bound_le_half {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    3*tailPrefactor n c/(1-tailRatio n c)^2 ≤ halfTailBound n := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hratio := tailRatio_mono hn hc1
  have hhalf := (tailRatio_bounds hn (c := 1/2) (by norm_num) le_rfl).2
  have hpref : tailPrefactor n c ≤ tailPrefactor n (1/2) := by
    unfold tailPrefactor
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hc0 hc1 (n+1)) (by positivity)
  unfold halfTailBound
  apply div_le_div₀
  · unfold tailPrefactor; positivity
  · linarith
  · exact sq_pos_of_pos (by linarith)
  · exact (sq_le_sq₀ (by linarith : 0 ≤ 1-tailRatio n (1/2))
      (by linarith : 0 ≤ 1-tailRatio n c)).mpr (by linarith)

theorem factorialScale_succ_le {n : ℕ} (hn : 1 ≤ n) :
    factorialScale (n+1) ≤ factorialScale n := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  let D : ℝ := (2:ℝ)^(n+1)*((n+1).factorial:ℝ)
  have hD : 0 < D := by dsimp [D]; positivity
  have hsucc : factorialScale (n+1) = ((n:ℝ)+1)^2/(2*((n:ℝ)+2)*D) := by
    unfold factorialScale D
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  rw [hsucc]
  change ((n:ℝ)+1)^2/(2*((n:ℝ)+2)*D) ≤ (n:ℝ)^2/D
  apply (div_le_div_iff₀ (by positivity) hD).mpr
  have hnum : ((n:ℝ)+1)^2 ≤ 2*(n:ℝ)^2*((n:ℝ)+2) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n:ℝ)-1) (sq_nonneg (n:ℝ))]
  have hh := mul_le_mul_of_nonneg_right hnum hD.le
  nlinarith only [hh]

theorem factorialScale_le_five {n : ℕ} (hn : 5 ≤ n) : factorialScale n ≤ factorialScale 5 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact (factorialScale_succ_le (by omega)).trans ih

theorem half_tail_scaled_identity {n : ℕ} (hn : 1 ≤ n) :
    halfTailBound n * (n:ℝ)^3 = 3*factorialScale n/(1-tailRatio n (1/2))^2 := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  unfold halfTailBound factorialScale tailPrefactor
  rw [div_pow, one_pow]
  field_simp

theorem half_tail_ratio_le_five {n : ℕ} (hn : 5 ≤ n) : tailRatio n (1/2) ≤ 3/35 := by
  have hn5 : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hid : tailRatio n (1/2) = ((1/(n:ℝ)) + 1/((n:ℝ)+2))/4 := by
    unfold tailRatio
    field_simp
    ring
  have h1 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5) hn5
  have h2 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 7)
    (by linarith : (7:ℝ) ≤ (n:ℝ)+2)
  rw [hid]
  simp only [one_div]
  norm_num at h1 h2
  linarith

theorem half_tail_bound_four : halfTailBound 4 < 1/4000 := by
  norm_num [halfTailBound, tailPrefactor, tailRatio, Nat.factorial]

theorem half_tail_bound_large {n : ℕ} (hn : 5 ≤ n) :
    halfTailBound n < 1/(500*(n:ℝ)^3) := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hscale := factorialScale_le_five hn
  have hratio := half_tail_ratio_le_five hn
  have hden : (32/35:ℝ)^2 ≤ (1-tailRatio n (1/2))^2 :=
    (sq_le_sq₀ (by norm_num) (by linarith)).mpr (by linarith)
  have hbound : 3*factorialScale n/(1-tailRatio n (1/2))^2 ≤
      3*factorialScale 5/(32/35:ℝ)^2 := by
    apply div_le_div₀
    · unfold factorialScale; positivity
    · linarith
    · norm_num
    · exact hden
  have hconst : 3*factorialScale 5/(32/35:ℝ)^2 < 1/500 := by
    norm_num [factorialScale, Nat.factorial]
  have hh := hbound.trans_lt hconst
  rw [← half_tail_scaled_identity (by omega : 1 ≤ n)] at hh
  have hid : 1/(500*(n:ℝ)^3) = (1/500)/(n:ℝ)^3 := by ring
  rw [hid]
  exact (lt_div_iff₀ (by positivity)).mpr hh

theorem normalized_tail_four {k : ℕ} (hk : 1 ≤ k) {c R : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1/2) (hR0 : 0 ≤ R) (hR3 : R < 3) :
    R*tailSeries 4 k c < 1/4000 := by
  exact (normalized_tail_bound (by norm_num : 1 ≤ 4) hk hc0 hc1 hR0 hR3).trans_le
    ((tail_bound_le_half (by norm_num : 1 ≤ 4) hc0.le hc1).trans half_tail_bound_four.le)

theorem normalized_tail_large {n k : ℕ} (hn : 5 ≤ n) (hk : 1 ≤ k) {c R : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1/2) (hR0 : 0 ≤ R) (hR3 : R < 3) :
    R*tailSeries n k c < 1/(500*(n:ℝ)^3) := by
  exact (normalized_tail_bound (by omega : 1 ≤ n) hk hc0 hc1 hR0 hR3).trans_le
    ((tail_bound_le_half (by omega : 1 ≤ n) hc0.le hc1).trans (half_tail_bound_large hn).le)

end SharpTailMatching.TailEstimates
