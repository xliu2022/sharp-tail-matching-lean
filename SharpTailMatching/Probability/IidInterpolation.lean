module

public import SharpTailMatching.Probability.PartialSums

/-! # Weighted interpolation of iid tails -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching.Probability

def interpolationMultiplier (q : ℕ) (κ c α : ℕ → ℝ) : ℕ → ℝ
  | 0 => κ 0
  | j+1 => if j+1 ≤ q then κ (j+1) else
      (interpolationMultiplier q κ c α j-c (j+1)+κ (j+1)*α (j+1))/(1+α (j+1))

theorem interpolationMultiplier_base (q : ℕ) (κ c α : ℕ → ℝ) (j : ℕ) (hj : j ≤ q) :
    interpolationMultiplier q κ c α j = κ j := by
  cases j with
  | zero => rfl
  | succ j => simp only [interpolationMultiplier,ite_eq_left hj]

theorem interpolationMultiplier_rec (q : ℕ) (κ c α : ℕ → ℝ) (j : ℕ)
    (hj : q < j) (hα : 0 ≤ α j) :
    interpolationMultiplier q κ c α j*(1+α j) =
      interpolationMultiplier q κ c α (j-1)-c j+κ j*α j := by
  cases j with
  | zero => omega
  | succ j =>
    have hden : 1+α (j+1) ≠ 0 := by linarith
    simp only [interpolationMultiplier,ite_eq_right (Nat.not_le.mpr hj),Nat.add_sub_cancel,
      div_mul_cancel₀ _ hden]

def binomialWeight (k : ℕ) (r : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else (k.choose j : ℝ)*r^(k-j)

theorem binomialWeight_nonneg (k : ℕ) (r : ℝ) (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ binomialWeight k r j := by
  unfold binomialWeight
  split <;> positivity

theorem binomialWeight_monotone (k : ℕ) (_hk : 2 ≤ k) (r : ℝ)
    (hr : 0 ≤ r) (hrk : ((k : ℝ)-1)*r ≤ 2) (j : ℕ) (hjk : j+1 < k) :
    binomialWeight k r j ≤ binomialWeight k r (j+1) := by
  by_cases hj0 : j = 0
  · subst j
    simpa [binomialWeight] using binomialWeight_nonneg k r hr 1
  · have hpow : k-j = (k-(j+1))+1 := by omega
    have hcoeff : (k.choose j : ℝ)*r ≤ (k.choose (j+1) : ℝ) := by
      have hchoose : (k.choose (j+1) : ℝ)*((j : ℝ)+1) =
          (k.choose j : ℝ)*((k : ℝ)-(j : ℝ)) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.choose_succ_right_eq k j)
        simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_sub (show j ≤ k by omega)] using h
      have hjkR : (j : ℝ)+2 ≤ k := by exact_mod_cast (show j+2 ≤ k by omega)
      have hjR : (j : ℝ)+1 ≤ (k : ℝ)-1 := by linarith
      have hjdiff : (2 : ℝ) ≤ (k : ℝ)-(j : ℝ) := by linarith
      have hrj : ((j : ℝ)+1)*r ≤ (k : ℝ)-(j : ℝ) :=
        (mul_le_mul_of_nonneg_right hjR hr).trans (hrk.trans hjdiff)
      have hmul := mul_le_mul_of_nonneg_left hrj (Nat.cast_nonneg (k.choose j) : (0 : ℝ) ≤ _)
      have hjpos : 0 < (j : ℝ)+1 := by positivity
      nlinarith
    simp only [binomialWeight,ite_eq_right hj0,ite_eq_right (show j+1 ≠ 0 by omega),hpow,pow_succ]
    have hmul := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr (k-(j+1)))
    nlinarith

/-- Complete zero-penalty interpolation for the actual iid partial tails.
All supporting-line and excess-recursion premises are discharged here. -/
theorem iid_weighted_interpolation (k t : ℕ) (ht : 0 < t) (htk : t < k)
    (θ : ℝ) (μ : ProbabilityMeasure ℝ≥0)
    (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ)
    (κ : ℕ → ℝ) (hκ : ∀ j < k, 0 ≤ κ j)
    (hκmono : ∀ j, j+1 < k → κ j ≤ κ (j+1)) :
    (∑ j ∈ Finset.range (k-1),κ (j+1)*tailProbability (j+1) μ) ≤
      ∑ j ∈ Finset.range (k-1),κ (j+1)*ComparisonGeometry.tailStar k (j+1) t θ := by
  let q := k-t
  let α : ℕ → ℝ := fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t (t+1 : ℕ)
  let Γ := interpolationMultiplier q κ (fun _ => 0) α
  have hα : ∀ j, q < j → j < k → 0 ≤ α j := by
    intro j hj hjk
    have hlevel : 1 ≤ k-j := by omega
    have hlt : k-j < t := by dsimp [q] at hj; omega
    exact (ComparisonGeometry.chordSlope_pos (k-j : ℕ) t (t+1 : ℕ)
      (by exact_mod_cast hlevel) (by exact_mod_cast hlt) (by exact_mod_cast Nat.lt_succ_self t)).le
  have hbase : ∀ j ≤ q, Γ j = κ j := interpolationMultiplier_base q κ (fun _ => 0) α
  have hrec : ∀ j, q < j → j < k → Γ j*(1+α j) = Γ (j-1)+κ j*α j := by
    intro j hj hjk
    simpa only [sub_zero] using interpolationMultiplier_rec q κ (fun _ => 0) α j hj (hα j hj hjk)
  have hΓ : ∀ j < k, 0 ≤ Γ j :=
    interpolation_multiplier_nonnegative k q κ α Γ hbase hκ hα hrec
  have h := weighted_interpolation k q (by omega)
    (fun j => partialExcess k j μ) (fun j => tailProbability j μ)
    (fun j => ComparisonGeometry.excessStar k j t θ)
    (fun j => ComparisonGeometry.tailStar k j t θ) κ (fun _ => 0) α Γ
    (partialExcess_one k μ hsupp) (ComparisonGeometry.excessStar_one k t (by omega) htk θ)
    (fun j _ _ => partialExcess_rec k j (by omega) μ hsupp hmean)
    (fun j _ hj => ComparisonGeometry.excessStar_rec k j t hj θ)
    (by rw [partialExcess_last,ComparisonGeometry.excessStar_last k t ht θ,hexcess])
    (fun j _ hj => ⟨(partialExcess_bounds k j (by omega) (by dsimp [q] at hj; omega) μ hsupp hmean).1,
      ComparisonGeometry.excessStar_prefix k j t htk.le hj θ⟩)
    (fun j hj hjk => partial_star_slope_bound k j t (by omega) hjk
      (by dsimp [q] at hj; omega) htk θ μ hsupp hmean)
    hκ hκmono (fun _ _ => le_rfl) hα hbase
    (fun j hj hjk => by simpa only [sub_zero] using hrec j hj hjk) hΓ
  simpa only [zero_mul,sub_zero] using h

theorem iid_binomial_interpolation (k t : ℕ) (hk : 2 ≤ k) (ht : 0 < t) (htk : t < k)
    (θ r : ℝ) (hr : 0 ≤ r) (hrk : ((k : ℝ)-1)*r ≤ 2)
    (μ : ProbabilityMeasure ℝ≥0) (hsupp : (μ : Measure ℝ≥0) (Set.Ioi 1) = 0)
    (hmean : mean μ = ENNReal.ofReal (k : ℝ)⁻¹)
    (hexcess : normalizedExcess k μ = ComparisonGeometry.segmentExcess t θ) :
    (∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*r^(k-(j+1))*tailProbability (j+1) μ) ≤
      ∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*r^(k-(j+1))*
        ComparisonGeometry.tailStar k (j+1) t θ := by
  simpa only [binomialWeight,ite_eq_right (Nat.add_one_ne_zero _)] using
    iid_weighted_interpolation k t ht htk θ μ hsupp hmean hexcess (binomialWeight k r)
      (fun j _ => binomialWeight_nonneg k r hr j) (binomialWeight_monotone k hk r hr hrk)

end SharpTailMatching.Probability
