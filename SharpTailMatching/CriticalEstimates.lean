module

public import SharpTailMatching.ScalarCertificates
public import SharpTailMatching.Probability.CriticalMean
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Quantitative estimates at the positive crossing

The finite Taylor bounds below are proved algebraically by induction. Thus
the fourth-node estimate is connected to the actual crossing equation,
without treating a Taylor remainder sign as an assumption.
-/

@[expose] public section

noncomputable section

open Set

namespace SharpTailMatching.CriticalEstimates

def taylorOne (n u : ℝ) : ℝ := 1 + n * u
def taylorTwo (n u : ℝ) : ℝ := taylorOne n u + n * (n-1) / 2 * u^2
def taylorThree (n u : ℝ) : ℝ := taylorTwo n u + n * (n-1) * (n-2) / 6 * u^3
def taylorFour (n u : ℝ) : ℝ := taylorThree n u + n * (n-1) * (n-2) * (n-3) / 24 * u^4

theorem taylorOne_succ (n u : ℝ) : taylorOne (n+1) u = taylorOne n u + u := by
  unfold taylorOne; ring
theorem taylorTwo_succ (n u : ℝ) : taylorTwo (n+1) u = taylorTwo n u + u * taylorOne n u := by
  unfold taylorTwo taylorOne; ring
theorem taylorThree_succ (n u : ℝ) :
    taylorThree (n+1) u = taylorThree n u + u * taylorTwo n u := by
  unfold taylorThree taylorTwo taylorOne; ring
theorem taylorFour_succ (n u : ℝ) :
    taylorFour (n+1) u = taylorFour n u + u * taylorThree n u := by
  unfold taylorFour taylorThree taylorTwo taylorOne; ring

theorem positive_taylor_bounds (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    taylorOne n u ≤ (1+u)^n ∧ taylorTwo n u ≤ (1+u)^n ∧
    taylorThree n u ≤ (1+u)^n ∧ taylorFour n u ≤ (1+u)^n := by
  induction n with
  | zero => norm_num [taylorFour, taylorThree, taylorTwo, taylorOne]
  | succ n ih =>
      have hpow : 1 ≤ (1+u)^n := one_le_pow₀ (by linarith)
      rw [Nat.cast_succ, taylorOne_succ, taylorTwo_succ, taylorThree_succ,
        taylorFour_succ, pow_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := mul_le_mul_of_nonneg_left hpow hu
        nlinarith [ih.1]
      · have h := mul_le_mul_of_nonneg_left ih.1 hu
        nlinarith [ih.2.1]
      · have h := mul_le_mul_of_nonneg_left ih.2.1 hu
        nlinarith [ih.2.2.1]
      · have h := mul_le_mul_of_nonneg_left ih.2.2.1 hu
        nlinarith [ih.2.2.2]

/-- The first four Bonferroni bounds, including exponents below four. -/
theorem negative_taylor_bounds (n : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    taylorOne n (-u) ≤ (1-u)^n ∧ (1-u)^n ≤ taylorTwo n (-u) ∧
    taylorThree n (-u) ≤ (1-u)^n ∧ (1-u)^n ≤ taylorFour n (-u) := by
  induction n with
  | zero => norm_num [taylorFour, taylorThree, taylorTwo, taylorOne]
  | succ n ih =>
      have hpow : (1-u)^n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      rw [Nat.cast_succ, taylorOne_succ, taylorTwo_succ, taylorThree_succ,
        taylorFour_succ, pow_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · have h := mul_le_mul_of_nonneg_left hpow hu
        nlinarith [ih.1]
      · have h := mul_le_mul_of_nonneg_left ih.1 hu
        nlinarith [ih.2.1]
      · have h := mul_le_mul_of_nonneg_left ih.2.1 hu
        nlinarith [ih.2.2.1]
      · have h := mul_le_mul_of_nonneg_left ih.2.2.1 hu
        nlinarith [ih.2.2.2]

def criticalDifference (k : ℕ) (c : ℝ) : ℝ :=
  (1 + c / k) ^ k - (1 - (1-c) / k) ^ k

theorem fourth_node_taylor_identity {k c : ℝ} (hk : k ≠ 0) :
    taylorFour k (c/k) - taylorFour k (-(1-c)/k) =
      ScalarCertificates.fourthNodeG c k⁻¹ := by
  unfold taylorFour taylorThree taylorTwo taylorOne ScalarCertificates.fourthNodeG
  field_simp
  ring

theorem fourth_node_taylor_lower {k : ℕ} (hk : 1 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ScalarCertificates.fourthNodeG c (k : ℝ)⁻¹ ≤ criticalDifference k c := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hp := (positive_taylor_bounds k (div_nonneg hc0 hkpos.le)).2.2.2
  have hn := (negative_taylor_bounds k
    (div_nonneg (sub_nonneg.mpr hc1) hkpos.le)
    ((div_le_one hkpos).mpr (by linarith))).2.2.2
  have hid := fourth_node_taylor_identity (c := c) hkpos.ne'
  rw [neg_div] at hid
  unfold criticalDifference
  linarith

/-- The fourth-node rational certificate applies to the genuine crossing. -/
theorem fourth_node_gap_at_crossing {k : ℕ} (hk : 5 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) (hcross : criticalDifference k c = 1) :
    ScalarCertificates.fourthNodeT c (k : ℝ)⁻¹ / 4 <
      81/256 - ScalarCertificates.fourthNodeA c (k : ℝ)⁻¹ := by
  have hk5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  apply ScalarCertificates.fourth_node_positive_gap hc0 hc1 (by positivity)
  · simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hk5
  · exact (fourth_node_taylor_lower (by omega) hc0 (by linarith)).trans_eq hcross

theorem criticalDifference_derivative {k : ℕ} (hk : k ≠ 0) (c : ℝ) :
    HasDerivAt (criticalDifference k)
      ((1+c/k)^(k-1) - (1-(1-c)/k)^(k-1)) c := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  convert (((hasDerivAt_const c 1).add ((hasDerivAt_id c).div_const (k : ℝ))).pow k).sub
    (((hasDerivAt_const c 1).sub
      (((hasDerivAt_const c 1).sub (hasDerivAt_id c)).div_const (k : ℝ))).pow k) using 1
  · rfl
  · simp only [id_eq, Pi.add_apply, Pi.sub_apply]
    field_simp [hkR]
    ring

theorem criticalDifference_strictMono {k : ℕ} (hk : 2 ≤ k) :
    StrictMonoOn (criticalDifference k) (Ici 0) := by
  have hk0 : k ≠ 0 := by omega
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro c _
    exact (criticalDifference_derivative hk0 c).continuousAt.continuousWithinAt
  · intro c hc
    rw [(criticalDifference_derivative hk0 c).deriv]
    have hc0 : 0 ≤ c := interior_subset hc
    apply sub_pos.mpr
    apply pow_lt_pow_left₀
    · have hid : (1+c/(k:ℝ)) - (1-(1-c)/(k:ℝ)) = (k:ℝ)⁻¹ := by ring
      linarith [inv_pos.mpr hkpos]
    · have hle : (1-c)/(k:ℝ) ≤ 1 := (div_le_one hkpos).mpr (by linarith)
      linarith
    · omega

theorem criticalDifference_half_ge {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ criticalDifference k (1/2) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have h2 : 2 * (k : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hkpos).mpr hk2
  have hi : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr hkpos.le
  have hG := fourth_node_taylor_lower (k := k) (by omega)
    (c := 1/2) (by norm_num) (by norm_num)
  have hid : ScalarCertificates.fourthNodeG (1/2) (k : ℝ)⁻¹ =
      1 + (1-(k:ℝ)⁻¹) * (1-2*(k:ℝ)⁻¹) / 24 := by
    unfold ScalarCertificates.fourthNodeG; ring
  rw [hid] at hG
  have hh : 0 ≤ (1-(k:ℝ)⁻¹) * (1-2*(k:ℝ)⁻¹) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

theorem criticalDifference_half_gt {k : ℕ} (hk : 3 ≤ k) :
    1 < criticalDifference k (1/2) := by
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have h2 : 2 * (k : ℝ)⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one hkpos).mpr (by linarith)
  have hi : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr hkpos.le
  have hG := fourth_node_taylor_lower (k := k) (by omega)
    (c := 1/2) (by norm_num) (by norm_num)
  have hid : ScalarCertificates.fourthNodeG (1/2) (k : ℝ)⁻¹ =
      1 + (1-(k:ℝ)⁻¹) * (1-2*(k:ℝ)⁻¹) / 24 := by
    unfold ScalarCertificates.fourthNodeG; ring
  rw [hid] at hG
  have hh : 0 < (1-(k:ℝ)⁻¹) * (1-2*(k:ℝ)⁻¹) :=
    mul_pos (by linarith) (by linarith)
  linarith

theorem critical_parameter_le_half {k : ℕ} (hk : 2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) : c ≤ 1/2 := by
  by_contra h
  have hlt := criticalDifference_strictMono hk (show (1/2:ℝ) ∈ Ici 0 by norm_num)
    hc (lt_of_not_ge h)
  have hge := criticalDifference_half_ge hk
  rw [hcross] at hlt
  linarith

theorem critical_parameter_lt_half {k : ℕ} (hk : 3 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) : c < 1/2 := by
  by_contra h
  have hle := (criticalDifference_strictMono (by omega : 2 ≤ k)).monotoneOn
    (show (1/2:ℝ) ∈ Ici 0 by norm_num) hc (le_of_not_gt h)
  have hgt := criticalDifference_half_gt hk
  rw [hcross] at hle
  linarith

theorem critical_parameter_two {c : ℝ} (hcross : criticalDifference 2 c = 1) : c = 1/2 := by
  norm_num [criticalDifference] at hcross
  nlinarith

theorem criticalDifference_of_beta {k : ℕ} (hk : 1 ≤ k) {β : ℝ}
    (hβ : 0 < β) (hcross : 1-(1-β)^k = ((k:ℝ)*β)^k) :
    criticalDifference k (β⁻¹-k) = 1 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hβ0 : β ≠ 0 := hβ.ne'
  have hden : (k:ℝ)*β ≠ 0 := mul_ne_zero hk0 hβ0
  have hA : 1 + (β⁻¹-(k:ℝ))/(k:ℝ) = ((k:ℝ)*β)⁻¹ := by
    field_simp
    ring
  have hB : 1 - (1-(β⁻¹-(k:ℝ)))/(k:ℝ) = (1-β)/((k:ℝ)*β) := by
    field_simp
    ring
  unfold criticalDifference
  rw [hA, hB, inv_pow, div_pow]
  calc
    _ = (1-(1-β)^k) / (((k:ℝ)*β)^k) := by ring
    _ = 1 := by rw [hcross]; exact div_self (pow_ne_zero _ hden)

theorem critical_parameter_from_beta {k : ℕ} (hk : 2 ≤ k) {β : ℝ}
    (hβ : 0 < β) (hβlt : β < (k:ℝ)⁻¹)
    (hcross : 1-(1-β)^k = ((k:ℝ)*β)^k) :
    0 < β⁻¹-k ∧ β⁻¹-k ≤ 1/2 ∧ criticalDifference k (β⁻¹-k) = 1 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hmul : (k:ℝ)*β < 1 := by
    have h := mul_lt_mul_of_pos_left hβlt hkpos
    simpa only [mul_inv_cancel₀ hkpos.ne'] using h
  have hc : 0 < β⁻¹-(k:ℝ) := by
    have h : (k:ℝ) < β⁻¹ := by
      simpa only [one_div] using (lt_div_iff₀ hβ).mpr hmul
    linarith
  have hg := criticalDifference_of_beta (by omega : 1 ≤ k) hβ hcross
  exact ⟨hc, critical_parameter_le_half hk hc.le hg, hg⟩

end SharpTailMatching.CriticalEstimates
