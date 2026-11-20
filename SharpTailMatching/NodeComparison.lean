module

public import SharpTailMatching.BinomialNodes

/-! # Strict comparison of conditional deficit and support at the nodes -/

@[expose] public section

noncomputable section

open Set SharpTailMatching.ScalarCertificates SharpTailMatching.RationalCertificates

namespace SharpTailMatching.CriticalEstimates

def nodeZ (n k : ℕ) (c : ℝ) : ℝ :=
  nodeFailure n k c/(1-1/((k:ℝ)+c))^k - 1

theorem nodeZ_above_comparison {n k : ℕ} (hn : 4 ≤ n) (hnk : n+2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    comparisonValue ((n:ℝ)+1) ((k:ℝ)/((k:ℝ)+c)) < nodeZ n k c := by
  have hk6 : 6 ≤ k := by omega
  have hcLow := critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hcpos : 0 < c := by
    have h : 0 ≤ 2/(25*(k:ℝ)) := by positivity
    linarith
  have hcHalf := critical_parameter_le_half (by omega : 2 ≤ k) hc hcross
  let p := (1-1/((k:ℝ)+c))^k
  let a := (k:ℝ)/((k:ℝ)+c)
  let R := a^(k-1)/p
  have hR : 0 ≤ R ∧ R < 3 := critical_tail_multiplier hk6 hc hcross
  have hH : nodeA n*nodeB n k c*nodeC k c < untruncatedNode n k c/p :=
    rational_node_lower (by omega) (by omega) hc hcHalf
  have hphi : phi n k c = nodeA n*nodeB n k c*nodeC k c - 1 -
      comparisonValue ((n:ℝ)+1) a := by
    unfold phi nodeA nodeB nodeC
    rfl
  have hid : nodeZ n k c = untruncatedNode n k c/p-R*TailEstimates.tailSeries n k c-1 := by
    unfold nodeZ
    rw [nodeFailure_eq_untruncated_sub_tail (by omega) (by omega) hc]
    dsimp [p, R, a]
    ring
  by_cases hn4 : n = 4
  · subst n
    have htail := TailEstimates.normalized_tail_four (by omega : 1 ≤ k) hcpos hcHalf hR.1 hR.2
    have hcert := phi_at_critical_four hk6 hc hcross
    norm_num only [Nat.cast_ofNat] at hphi
    rw [hphi] at hcert
    rw [hid]
    norm_num only [Nat.cast_ofNat] at *
    linarith
  · have hn5 : 5 ≤ n := by omega
    have htail := TailEstimates.normalized_tail_large hn5 (by omega : 1 ≤ k)
      hcpos hcHalf hR.1 hR.2
    have hcert := phi_at_critical_large hn5 hnk hc hcross
    rw [hphi] at hcert
    rw [hid]
    linarith

theorem deficitTest_strictMono {t a : ℝ} (ha : 0 < a) (hat : a < t) :
    StrictMonoOn (deficitTest t a) (Ioi 0) := by
  intro z hz w hw hzw
  have hz0 : 0 < z := hz
  have hw0 : 0 < w := hw
  have hfrac : 19*a/(20*w) ≤ 19*a/(20*z) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hlin := mul_lt_mul_of_pos_left hzw (sub_pos.mpr hat)
  unfold deficitTest
  linarith

theorem node_deficitTest_gap {n k : ℕ} (hn : 4 ≤ n) (hnk : n+2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    3*((k:ℝ)/((k:ℝ)+c))/20 <
      deficitTest ((n:ℝ)+1) ((k:ℝ)/((k:ℝ)+c)) (nodeZ n k c) := by
  have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  let a := (k:ℝ)/((k:ℝ)+c)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hat : a < (n:ℝ)+1 := by linarith
  have ht4 : 4*a < (n:ℝ)+1 := by linarith
  have hcomp : 0 < comparisonValue ((n:ℝ)+1) a := comparisonValue_pos ha hat
  have hz := nodeZ_above_comparison hn hnk hc hcross
  have hm := deficitTest_strictMono ha hat hcomp (hcomp.trans hz) hz
  exact (target_substitution_strict ha ht4).trans hm

/-- The scalar conversion from the binomial node formulas to the desired
support/deficit gap. `T` is the nonnegative binomial excess term. -/
theorem node_moment_gap {k t a p F T z : ℝ}
    (hk : 0 < k) (hp : 0 < p) (hT : 0 ≤ T) (hz : 0 < z)
    (hF : F = p*(1+z)) (hG : 3*a/20 < deficitTest t a z) :
    a/k/5 < ((t-a)*F+T)/(k*p) - (19/20)*(a/k*(1+1/z)) := by
  have hid : k*(((t-a)*F+T)/(k*p) - (19/20)*(a/k*(1+1/z)) - a/k/20) =
      deficitTest t a z + T/p := by
    rw [hF]
    unfold deficitTest
    field_simp
    ring
  have hTp : 0 ≤ T/p := div_nonneg hT hp.le
  have hmul : 3*a/20 <
      k*(((t-a)*F+T)/(k*p) - (19/20)*(a/k*(1+1/z)) - a/k/20) := by
    rw [hid]
    linarith
  have haid : k*(a/k) = a := by field_simp
  nlinarith

end SharpTailMatching.CriticalEstimates
