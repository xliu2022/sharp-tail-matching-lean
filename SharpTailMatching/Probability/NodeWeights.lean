module

public import SharpTailMatching.Probability.Thinning
public import SharpTailMatching.CriticalEstimates
public import SharpTailMatching.CriticalLowerBound
public import Mathlib.Data.Nat.Choose.Cast

/-! # The finite weighted node sums and their critical-parameter values -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability.ComparisonGeometry

def nodeComparisonSum (k : ℕ) (r : ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*r^(k-(j+1))*tailNode k (j+1) t

def nodeFailureValue (t : ℕ) : ℝ := (1-1/(t : ℝ))^t

theorem starComparisonSum (k t : ℕ) (r θ : ℝ) :
    (∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*r^(k-(j+1))*tailStar k (j+1) t θ) =
      (1-θ)*nodeComparisonSum k r t+θ*nodeComparisonSum k r (t+1) := by
  unfold tailStar nodeComparisonSum
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem nodeComparisonSum_reversed (k t : ℕ) (r : ℝ) :
    nodeComparisonSum k r t = ∑ h ∈ Finset.range (k-1),
      (k.choose (h+1) : ℝ)*r^(h+1)*(if t ≤ h+1 then 0 else 1-(1-1/(t : ℝ))^(t-(h+1))) := by
  unfold nodeComparisonSum
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h < k-1 := Finset.mem_range.mp hh
  have hidx : k-1-1-h+1 = k-(h+1) := by omega
  have hhk : h+1 ≤ k := by omega
  rw [hidx,Nat.choose_symm hhk,Nat.sub_sub_self hhk]
  simp only [tailNode,nodeTailNat,nodePowerNat,Nat.sub_sub_self hhk]

theorem nodeComparisonSum_truncated (k t : ℕ) (ht : 1 ≤ t) (htk : t ≤ k) (r : ℝ) :
    nodeComparisonSum k r t = ∑ h ∈ Finset.range (t-1),
      (k.choose (h+1) : ℝ)*r^(h+1)*(1-(1-1/(t : ℝ))^(t-(h+1))) := by
  rw [nodeComparisonSum_reversed]
  let f : ℕ → ℝ := fun h => (k.choose (h+1) : ℝ)*r^(h+1)*
    (if t ≤ h+1 then 0 else 1-(1-1/(t : ℝ))^(t-(h+1)))
  change (∑ h ∈ Finset.range (k-1),f h) = _
  have htrunc : (∑ h ∈ Finset.range (t-1),f h) = ∑ h ∈ Finset.range (k-1),f h := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro h _ hh
    have hge : t-1 ≤ h := by simpa only [Finset.mem_range,not_lt] using hh
    simp only [f,ite_eq_left (show t ≤ h+1 by omega),mul_zero]
  rw [← htrunc]
  apply Finset.sum_congr rfl
  intro h hh
  have hlt : ¬t ≤ h+1 := by have := Finset.mem_range.mp hh; omega
  simp only [f,ite_eq_right hlt]

theorem nodeComparisonSum_one (k : ℕ) (r : ℝ) : nodeComparisonSum k r 1 = 0 := by
  rw [nodeComparisonSum_reversed]
  apply Finset.sum_eq_zero
  intro h _
  simp

theorem nodeFailureValue_one : nodeFailureValue 1 = 0 := by norm_num [nodeFailureValue]

theorem nodeComparisonSum_endpoint (k : ℕ) (hk : 1 ≤ k) (r : ℝ) :
    nodeComparisonSum k r k = (1+r)^k-(1-1/(k : ℝ)+r)^k-1+nodeFailureValue k := by
  let q : ℝ := 1-1/(k : ℝ)
  have hsum : (∑ h ∈ Finset.range (k+1),(k.choose h : ℝ)*r^h*(1-q^(k-h))) =
      (1+r)^k-(q+r)^k := by
    rw [CentralBinomial.add_pow_extended 1 r k (k+1) (by omega),
      CentralBinomial.add_pow_extended q r k (k+1) (by omega),← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h _
    simp only [one_pow]
    ring
  rw [Finset.sum_range_succ] at hsum
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,sub_self,mul_zero,add_zero] at hsum
  have hfirst : (∑ h ∈ Finset.range k,(k.choose h : ℝ)*r^h*(1-q^(k-h))) =
      (1-q^k)+nodeComparisonSum k r k := by
    have hsplit := Finset.sum_range_succ'
      (fun h => (k.choose h : ℝ)*r^h*(1-q^(k-h))) (k-1)
    rw [Nat.sub_add_cancel hk] at hsplit
    rw [hsplit,nodeComparisonSum_truncated k k hk le_rfl r]
    simp only [Nat.choose_zero_right,Nat.cast_one,pow_zero,one_mul,Nat.sub_zero]
    dsimp [q]
    ring
  rw [hfirst] at hsum
  unfold nodeFailureValue
  dsimp [q] at hsum
  linarith

theorem nodeComparisonSum_at_crossing (k : ℕ) (hk : 1 ≤ k) (c : ℝ)
    (hcross : CriticalEstimates.criticalDifference k c = 1) :
    nodeComparisonSum k (c/(k : ℝ)) k = nodeFailureValue k := by
  rw [nodeComparisonSum_endpoint k hk]
  have hid : 1-1/(k : ℝ)+c/(k : ℝ) = 1-(1-c)/(k : ℝ) := by ring
  rw [hid]
  unfold CriticalEstimates.criticalDifference at hcross
  linarith

theorem cast_choose_three (k : ℕ) (hk : 2 ≤ k) :
    (k.choose 3 : ℝ) = (k : ℝ)*((k : ℝ)-1)*((k : ℝ)-2)/6 := by
  have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq k 2)
  norm_num only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_sub hk] at h
  rw [Nat.cast_choose_two] at h
  linarith

theorem nodeComparisonSum_two (k : ℕ) (hk : 2 ≤ k) (c : ℝ) :
    nodeComparisonSum k (c/(k : ℝ)) 2 = c/2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [nodeComparisonSum_truncated k 2 (by omega) hk]
  norm_num [Finset.sum_range_succ]
  field_simp

theorem nodeComparisonSum_three (k : ℕ) (hk : 3 ≤ k) (c : ℝ) :
    nodeComparisonSum k (c/(k : ℝ)) 3 = 5*c/9+(1-(k : ℝ)⁻¹)*c^2/6 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [nodeComparisonSum_truncated k 3 (by omega) hk]
  norm_num [Finset.sum_range_succ,Nat.cast_choose_two]
  field_simp
  ring

theorem nodeComparisonSum_four (k : ℕ) (hk : 4 ≤ k) (c : ℝ) :
    nodeComparisonSum k (c/(k : ℝ)) 4 = ScalarCertificates.fourthNodeA c (k : ℝ)⁻¹ := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [nodeComparisonSum_truncated k 4 (by omega) hk]
  norm_num [Finset.sum_range_succ,Nat.cast_choose_two,cast_choose_three k (by omega),
    ScalarCertificates.fourthNodeA]
  field_simp
  ring

theorem node_four_strict {k : ℕ} (hk : 5 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    nodeComparisonSum k (c/(k : ℝ)) 4 < nodeFailureValue 4 := by
  have hchalf := CriticalEstimates.critical_parameter_le_half (by omega : 2 ≤ k) hc hcross
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hh : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have hhu : (k : ℝ)⁻¹ ≤ 1/5 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5) hkR
  have h1 : 0 ≤ 1-(k : ℝ)⁻¹ := by linarith
  have h2 : 0 ≤ 1-2*(k : ℝ)⁻¹ := by linarith
  have h3 : 0 ≤ 1-3*(k : ℝ)⁻¹ := by linarith
  have h4 : 0 ≤ 1-4*(k : ℝ)⁻¹ := by linarith
  have hden : 0 < 24*(1-c/5) := by linarith
  have hT : 0 ≤ ScalarCertificates.fourthNodeT c (k : ℝ)⁻¹ := by
    unfold ScalarCertificates.fourthNodeT
    positivity
  have hgap := CriticalEstimates.fourth_node_gap_at_crossing hk hc hchalf hcross
  rw [nodeComparisonSum_four k (by omega)]
  norm_num only [nodeFailureValue,Nat.cast_ofNat]
  linarith

theorem ratio_three_lt_four (c h : ℝ) (hc : 5/12 ≤ c) (hh : h ≤ 1/4) :
    15/8*c+9/16*(1-h)*c^2 <
      148/81*c+56/81*(1-h)*c^2+32/243*(1-h)*(1-2*h)*c^3 := by
  have hU : 3/4 ≤ 1-h := by linarith
  have hV : 1/2 ≤ 1-2*h := by linarith
  have hUc : (3/4)*(5/12) ≤ (1-h)*c := mul_le_mul hU hc (by norm_num) (by linarith)
  have hUV : (3/4)*(1/2) ≤ (1-h)*(1-2*h) := mul_le_mul hU hV (by norm_num) (by linarith)
  have hcsq : (5/12 : ℝ)^2 ≤ c^2 := by nlinarith
  have hUVc : ((3/4)*(1/2))*((5/12 : ℝ)^2) ≤ (1-h)*(1-2*h)*c^2 :=
    mul_le_mul hUV hcsq (sq_nonneg _) (by nlinarith)
  have hbracket : 0 < 501*(1-h)*c+512*(1-h)*(1-2*h)*c^2-186 := by nlinarith
  have hpos : 0 < c*(501*(1-h)*c+512*(1-h)*(1-2*h)*c^2-186)/3888 := by
    exact div_pos (mul_pos (by linarith) hbracket) (by norm_num)
  have hid := ScalarCertificates.node_difference_four_three c h
  linarith

theorem node_three_four_scaled {k : ℕ} (hk : 4 ≤ k) {c : ℝ} (hc : 5/12 ≤ c) :
    nodeComparisonSum k (c/(k : ℝ)) 3*(81/256) <
      nodeComparisonSum k (c/(k : ℝ)) 4*(8/27) := by
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hh : (k : ℝ)⁻¹ ≤ 1/4 := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hkR
  have h := ratio_three_lt_four c (k : ℝ)⁻¹ hc hh
  rw [nodeComparisonSum_three k (by omega),nodeComparisonSum_four k hk]
  unfold ScalarCertificates.fourthNodeA
  nlinarith

theorem node_three_strict {k : ℕ} (hk : 4 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    nodeComparisonSum k (c/(k : ℝ)) 3 < nodeFailureValue 3 := by
  have hclower := CriticalEstimates.critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hc5 : 5/12 ≤ c := by
    have hnonneg : 0 ≤ 2/(25*(k : ℝ)) := by positivity
    linarith
  have hfour : nodeComparisonSum k (c/(k : ℝ)) 4 ≤ (81/256 : ℝ) := by
    by_cases hk4 : k = 4
    · subst k
      rw [nodeComparisonSum_at_crossing 4 (by omega) c hcross]
      norm_num [nodeFailureValue]
    · have h := (node_four_strict (by omega : 5 ≤ k) hc hcross).le
      norm_num [nodeFailureValue] at h
      exact h
  have hcomp := node_three_four_scaled hk hc5
  norm_num [nodeFailureValue]
  nlinarith

theorem node_two_strict {k : ℕ} (hk : 3 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    nodeComparisonSum k (c/(k : ℝ)) 2 < nodeFailureValue 2 := by
  have hchalf := CriticalEstimates.critical_parameter_lt_half hk hc hcross
  rw [nodeComparisonSum_two k (by omega)]
  norm_num [nodeFailureValue]
  linarith

theorem initial_node_strict {k s : ℕ} (_hk : 2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (hs : 2 ≤ s) (hs4 : s ≤ 4) (hsk : s < k) :
    nodeComparisonSum k (c/(k : ℝ)) s < nodeFailureValue s := by
  have hsCases : s = 2 ∨ s = 3 ∨ s = 4 := by omega
  rcases hsCases with rfl | rfl | rfl
  · exact node_two_strict (by omega) hc hcross
  · exact node_three_strict (by omega) hc hcross
  · exact node_four_strict (by omega) hc hcross

end SharpTailMatching.Probability.ComparisonGeometry
