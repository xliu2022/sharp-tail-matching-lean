module

public import SharpTailMatching.AnalyticNodeBounds
public import SharpTailMatching.TailNumerics

/-! # Binomial formulas for the interpolated comparison nodes -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

open scoped BigOperators

namespace SharpTailMatching.CriticalEstimates

def nodeFailure (n k : ℕ) (c : ℝ) : ℝ :=
  ((k:ℝ)/((k:ℝ)+c))^(k-1) *
    ∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*(c/(k:ℝ))^h*((n:ℝ)/(n+1))^(n-h)

def untruncatedNode (n k : ℕ) (c : ℝ) : ℝ :=
  ((n:ℝ)/(n+1))^n * (1+(c/((k:ℝ)+c))/(n:ℝ))^(k-1)

theorem sum_shift_of_vanishing (f : ℕ → ℝ) {n k : ℕ} (hnk : n+1 ≤ k)
    (hlo : ∀ h, h ≤ n → f h = 0) (hhi : ∀ h, k ≤ h → f h = 0) :
    (∑ h ∈ Finset.range k, f h) = ∑ j ∈ Finset.range k, f (n+1+j) := by
  let m := k-(n+1)
  have hindex : n+1+m = k := Nat.add_sub_of_le hnk
  calc
    _ = ∑ h ∈ Finset.range (n+1+m), f h := by rw [hindex]
    _ = (∑ h ∈ Finset.range (n+1), f h) + ∑ j ∈ Finset.range m, f (n+1+j) :=
      Finset.sum_range_add f (n+1) m
    _ = ∑ j ∈ Finset.range m, f (n+1+j) := by
      have hz : (∑ h ∈ Finset.range (n+1), f h) = 0 :=
        Finset.sum_eq_zero fun h hh => hlo h (by have := Finset.mem_range.mp hh; omega)
      rw [hz, zero_add]
    _ = ∑ j ∈ Finset.range k, f (n+1+j) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.sub_le _ _))
      intro j _ hj
      have hjm : m ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
      exact hhi (n+1+j) (by omega)

theorem divided_power_cancel {q : ℝ} (hq : q ≠ 0) {n h : ℕ} (hh : h ≤ n) :
    q^n/q^h = q^(n-h) := by
  have hid : q^n = q^(n-h)*q^h := by rw [← pow_add, Nat.sub_add_cancel hh]
  rw [hid, mul_div_cancel_right₀ _ (pow_ne_zero _ hq)]

theorem divided_power_above {q : ℝ} (hq : q ≠ 0) (n j : ℕ) :
    q^n/q^(n+1+j) = q⁻¹^(j+1) := by
  have hid : n+1+j = n+(j+1) := by omega
  rw [hid, pow_add, inv_pow]
  field_simp

theorem binomial_generating_node {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) :
    untruncatedNode n k c =
      ((k:ℝ)/((k:ℝ)+c))^(k-1) *
        ∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*(c/(k:ℝ))^h*
          (((n:ℝ)/(n+1))^n/((n:ℝ)/(n+1))^h) := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  let a := (k:ℝ)/((k:ℝ)+c)
  let q := (n:ℝ)/(n+1)
  let z := c/(k:ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hgen : a*(1+z/q) = 1+(c/((k:ℝ)+c))/(n:ℝ) := by
    dsimp [a, q, z]
    field_simp
    ring
  have hsum : (∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*z^h*(q^n/q^h)) =
      q^n*(1+z/q)^(k-1) := by
    have hp := CentralBinomial.add_pow_extended 1 (z/q) (k-1) k (by omega)
    rw [hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    simp only [one_pow, mul_one, div_pow]
    ring
  change untruncatedNode n k c = a^(k-1)*
    ∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*z^h*(q^n/q^h)
  rw [hsum]
  unfold untruncatedNode
  rw [← hgen, mul_pow]
  ring

theorem nodeFailure_eq_untruncated_sub_tail {n k : ℕ} (hn : 1 ≤ n) (hnk : n+1 ≤ k)
    {c : ℝ} (hc : 0 ≤ c) :
    nodeFailure n k c = untruncatedNode n k c -
      ((k:ℝ)/((k:ℝ)+c))^(k-1) * TailEstimates.tailSeries n k c := by
  have hk : 1 ≤ k := by omega
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let a := (k:ℝ)/((k:ℝ)+c)
  let q := (n:ℝ)/(n+1)
  let z := c/(k:ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  let f : ℕ → ℝ := fun h => ((k-1).choose h:ℝ)*z^h*(q^n/q^h-q^(n-h))
  have hlo : ∀ h, h ≤ n → f h = 0 := by
    intro h hh
    dsimp [f]
    rw [divided_power_cancel hq.ne' hh]
    ring
  have hhi : ∀ h, k ≤ h → f h = 0 := by
    intro h hh
    dsimp [f]
    simp [Nat.choose_eq_zero_of_lt (by omega : k-1 < h)]
  have hshift := sum_shift_of_vanishing f hnk hlo hhi
  have hterm (j : ℕ) : f (n+1+j) = TailEstimates.tailTerm n k j c := by
    have hsub : n-(n+1+j) = 0 := by omega
    dsimp [f, z, TailEstimates.tailTerm]
    rw [divided_power_above hq.ne' n j, hsub, pow_zero]
    have hqi : q⁻¹ = ((n:ℝ)+1)/(n:ℝ) := by dsimp [q]; rw [inv_div]
    rw [hqi]
  have hsum : (∑ h ∈ Finset.range k, f h) = TailEstimates.tailSeries n k c := by
    rw [hshift]
    exact Finset.sum_congr rfl fun j _ => hterm j
  have hdiff : untruncatedNode n k c - nodeFailure n k c =
      a^(k-1)*(∑ h ∈ Finset.range k, f h) := by
    rw [binomial_generating_node hn hk hc]
    unfold nodeFailure
    change a^(k-1)*(∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*z^h*(q^n/q^h)) -
      a^(k-1)*(∑ h ∈ Finset.range k, ((k-1).choose h:ℝ)*z^h*q^(n-h)) = _
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    dsimp [f]
    ring
  rw [hsum] at hdiff
  change nodeFailure n k c = untruncatedNode n k c - a^(k-1)*TailEstimates.tailSeries n k c
  linarith

theorem critical_tail_multiplier {k : ℕ} (hk : 6 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    0 ≤ ((k:ℝ)/((k:ℝ)+c))^(k-1)/(1-1/((k:ℝ)+c))^k ∧
      ((k:ℝ)/((k:ℝ)+c))^(k-1)/(1-1/((k:ℝ)+c))^k < 3 := by
  have hk6 : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  obtain ⟨ha0, ha1, hac, hp0, hp1, he⟩ := critical_elementary_bounds hk hc hcross
  have hae : (k:ℝ)*(1/((k:ℝ)+c)) = (k:ℝ)/((k:ℝ)+c) := by ring
  rw [hae] at ha0 ha1
  have hp : 0 < (1-1/((k:ℝ)+c))^k := by linarith
  constructor
  · positivity
  · apply (div_lt_iff₀ hp).mpr
    have hpow : ((k:ℝ)/((k:ℝ)+c))^(k-1) ≤ 1 :=
      pow_le_one₀ (by positivity) ha1.le
    linarith

end SharpTailMatching.CriticalEstimates
