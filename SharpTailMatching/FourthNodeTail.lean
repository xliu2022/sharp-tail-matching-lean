module

public import SharpTailMatching.NodeComparison

/-! # The fourth-node binomial tail

The estimate uses the exact first binomial coefficient, followed by a finite
geometric majorant. The zero coefficients beyond the binomial range are
included, so there is no change of index at the upper endpoint.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.TailEstimates

def binomialTerm (k h : ℕ) (c : ℝ) : ℝ :=
  ((k-1).choose h:ℝ)*(c/(k:ℝ))^h

def binomialTail (m k : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, binomialTerm k (m+j) c

theorem binomialTerm_nonneg (k h : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ binomialTerm k h c := by
  unfold binomialTerm
  positivity

theorem binomialTerm_step {k : ℕ} (hk : 1 ≤ k) (h : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ((h:ℝ)+1)*binomialTerm k (h+1) c ≤ c*binomialTerm k h c := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hid : ((k-1).choose (h+1):ℝ)*((h:ℝ)+1) =
      ((k-1).choose h:ℝ)*((k-1-h:ℕ):ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq (k-1) h
  have hsub : ((k-1-h:ℕ):ℝ) ≤ k := by exact_mod_cast (show k-1-h ≤ k by omega)
  have hcoef : ((k-1).choose (h+1):ℝ)*((h:ℝ)+1) ≤ ((k-1).choose h:ℝ)*(k:ℝ) := by
    rw [hid]
    exact mul_le_mul_of_nonneg_left hsub (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ (c/(k:ℝ))^(h+1))
  have heq : (((k-1).choose h:ℝ)*(k:ℝ))*(c/(k:ℝ))^(h+1) =
      c*binomialTerm k h c := by
    unfold binomialTerm
    rw [pow_succ]
    field_simp
  rw [heq] at hmul
  simpa only [binomialTerm, mul_assoc, mul_left_comm, mul_comm] using hmul

theorem binomialTerm_shift_step {k : ℕ} (hk : 1 ≤ k) (m j : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    binomialTerm k (m+(j+1)) c ≤ c/((m:ℝ)+1)*binomialTerm k (m+j) c := by
  have h := binomialTerm_step hk (m+j) hc
  have hnonneg := binomialTerm_nonneg k (m+j+1) hc
  have hm : (m:ℝ)+1 ≤ ((m+j:ℕ):ℝ)+1 := by
    exact_mod_cast (show m+1 ≤ m+j+1 by omega)
  have hleft := mul_le_mul_of_nonneg_right hm hnonneg
  have hsum : m+(j+1) = m+j+1 := by omega
  rw [hsum]
  calc
    _ ≤ (c*binomialTerm k (m+j) c)/((m:ℝ)+1) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith)
    _ = _ := by ring

theorem binomialTerm_geometric {k : ℕ} (hk : 1 ≤ k) (m j : ℕ)
    {c : ℝ} (hc : 0 ≤ c) :
    binomialTerm k (m+j) c ≤ binomialTerm k m c*(c/((m:ℝ)+1))^j := by
  induction j with
  | zero => simp
  | succ j ih =>
      calc
        _ ≤ c/((m:ℝ)+1)*binomialTerm k (m+j) c := binomialTerm_shift_step hk m j hc
        _ ≤ c/((m:ℝ)+1)*(binomialTerm k m c*(c/((m:ℝ)+1))^j) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem geometric_identity (k : ℕ) (r : ℝ) :
    (1-r)*(∑ j ∈ Finset.range k, r^j) = 1-r^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

theorem geometric_bound (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑ j ∈ Finset.range k, r^j) ≤ 1/(1-r) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-r)).mpr
  have h := geometric_identity k r
  nlinarith [pow_nonneg hr0 k]

theorem binomialTail_geometric {k : ℕ} (hk : 1 ≤ k) (m : ℕ)
    {c : ℝ} (hc : 0 ≤ c) (hcm : c < (m:ℝ)+1) :
    binomialTail m k c ≤ binomialTerm k m c/(1-c/((m:ℝ)+1)) := by
  have hr0 : 0 ≤ c/((m:ℝ)+1) := by positivity
  have hr1 : c/((m:ℝ)+1) < 1 := (div_lt_one (by positivity)).mpr hcm
  unfold binomialTail
  calc
    _ ≤ ∑ j ∈ Finset.range k, binomialTerm k m c*(c/((m:ℝ)+1))^j :=
      Finset.sum_le_sum fun j _ => binomialTerm_geometric hk m j hc
    _ = binomialTerm k m c*∑ j ∈ Finset.range k, (c/((m:ℝ)+1))^j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ binomialTerm k m c*(1/(1-c/((m:ℝ)+1))) :=
      mul_le_mul_of_nonneg_left (geometric_bound k hr0 hr1) (binomialTerm_nonneg k m hc)
    _ = _ := by ring

theorem cast_choose_four {k : ℕ} (hk : 5 ≤ k) :
    ((k-1).choose 4:ℝ) = ((k:ℝ)-1)*((k:ℝ)-2)*((k:ℝ)-3)*((k:ℝ)-4)/24 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (k-1) 4
  norm_num only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    Nat.factorial_succ, Nat.factorial_zero, Nat.reduceMul, Nat.mul_one] at h
  have h' : ((k-1-3:ℕ):ℝ)*(((k-1-2:ℕ):ℝ)*(((k-1-1:ℕ):ℝ)*((k-1:ℕ):ℝ))) =
      24*((k-1).choose 4:ℝ) := by exact_mod_cast h
  rw [Nat.cast_sub (by omega : 3 ≤ k-1), Nat.cast_sub (by omega : 2 ≤ k-1),
    Nat.cast_sub (by omega : 1 ≤ k-1), Nat.cast_sub (by omega : 1 ≤ k)] at h'
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at h'
  nlinarith [h']

theorem fourth_binomial_tail_bound {k : ℕ} (hk : 5 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    binomialTail 4 k c ≤ ScalarCertificates.fourthNodeT c (k:ℝ)⁻¹ := by
  have h := binomialTail_geometric (by omega : 1 ≤ k) 4 hc0 (by norm_num; linarith)
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hid : binomialTerm k 4 c/(1-c/(((4:ℕ):ℝ)+1)) =
      ScalarCertificates.fourthNodeT c (k:ℝ)⁻¹ := by
    unfold binomialTerm ScalarCertificates.fourthNodeT
    rw [cast_choose_four hk]
    norm_num only [Nat.cast_ofNat]
    field_simp
  exact h.trans_eq hid

theorem fourth_binomial_tail_strict {k : ℕ} (hk : 5 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    binomialTail 4 k c < 4*(81/256-ScalarCertificates.fourthNodeA c (k:ℝ)⁻¹) := by
  have hc1 := CriticalEstimates.critical_parameter_le_half (by omega : 2 ≤ k) hc0 hcross
  have hbound := fourth_binomial_tail_bound hk hc0 hc1
  have hgap := CriticalEstimates.fourth_node_gap_at_crossing hk hc0 hc1 hcross
  linarith

end SharpTailMatching.TailEstimates

namespace SharpTailMatching.CriticalEstimates

theorem fourth_deficitTest_gap {a z : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : a/(4-a) < z) :
    3*a/20 < ScalarCertificates.deficitTest 4 a z := by
  have hden : 0 < 4-a := by linarith
  have hbase : 0 < a/(4-a) := div_pos ha0 hden
  have hinc := deficitTest_strictMono ha0 (by linarith : a < 4) hbase (hbase.trans hz) hz
  have hid : ScalarCertificates.deficitTest 4 a (a/(4-a)) = (4-a)/20 := by
    unfold ScalarCertificates.deficitTest
    field_simp
    ring
  rw [hid] at hinc
  linarith

end SharpTailMatching.CriticalEstimates
