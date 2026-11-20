module

public import SharpTailMatching.Probability.IidInterpolation
public import SharpTailMatching.MultiplierPositivity

/-! # Interpolation with the actual binomial costs -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace SharpTailMatching.Probability

def shortBinomialWeight (k : ℕ) (a r : ℝ) (j : ℕ) : ℝ :=
  a^(k-1)*binomialWeight (k-1) r j

def binomialCost (k : ℕ) (a r : ℝ) (j : ℕ) : ℝ :=
  a^k/(k:ℝ)*binomialWeight k r j

theorem shortBinomialWeight_nonneg (k : ℕ) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ shortBinomialWeight k a r j :=
  mul_nonneg (pow_nonneg ha _) (binomialWeight_nonneg (k-1) r hr j)

theorem shortBinomialWeight_pos {k j : ℕ} (hj : 1 ≤ j) (hjk : j < k)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < shortBinomialWeight k a r j := by
  unfold shortBinomialWeight binomialWeight
  rw [ite_eq_right (by omega : j ≠ 0)]
  have hchoose : (0:ℝ) < (k-1).choose j := by
    exact_mod_cast Nat.choose_pos (by omega : j ≤ k-1)
  positivity

theorem shortBinomialWeight_step {k j : ℕ} (hj : 2 ≤ j) (hjk : j < k) (a r : ℝ) :
    ((k-j:ℕ):ℝ)*shortBinomialWeight k a r (j-1) =
      (j:ℝ)*r*shortBinomialWeight k a r j := by
  have hchoose : ((k-j:ℕ):ℝ)*((k-1).choose (j-1):ℝ) =
      (j:ℝ)*((k-1).choose j:ℝ) := by
    have h := Nat.choose_succ_right_eq (k-1) (j-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j), show k-1-(j-1) = k-j by omega] at h
    have h' : (k-j)*(k-1).choose (j-1) = j*(k-1).choose j := by nlinarith only [h]
    exact_mod_cast h'
  have hpow : k-1-(j-1) = (k-1-j)+1 := by omega
  unfold shortBinomialWeight binomialWeight
  rw [ite_eq_right (by omega : j-1 ≠ 0), ite_eq_right (by omega : j ≠ 0), hpow, pow_succ]
  linear_combination (a^(k-1)*r^(k-1-j)*r)*hchoose

theorem binomialCost_step {k j : ℕ} (hj : 1 ≤ j) (hjk : j < k) (a r : ℝ) :
    ((k-j:ℕ):ℝ)*(k:ℝ)*binomialCost k a r j =
      a*(k:ℝ)*r*shortBinomialWeight k a r j := by
  have hk0 : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hchoose : ((k-j:ℕ):ℝ)*(k.choose j:ℝ) = (k:ℝ)*((k-1).choose j:ℝ) := by
    have h := Nat.choose_mul_succ_eq (k-1) j
    rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at h
    have h' : (k-j)*k.choose j = k*(k-1).choose j := by nlinarith only [h]
    exact_mod_cast h'
  have hpow : k-j = (k-1-j)+1 := by omega
  have hapow : a^k = a^(k-1)*a := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
  unfold shortBinomialWeight binomialCost binomialWeight
  rw [ite_eq_right (by omega : j ≠ 0), ite_eq_right (by omega : j ≠ 0), hpow, pow_succ, hapow]
  field_simp
  rw [← hpow]
  linear_combination (a^(k-1)*a*r^(k-1-j)*r)*hchoose

theorem shortBinomialWeight_ratio {k ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓk : ℓ+1 < k)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    shortBinomialWeight k a (c/(k:ℝ)) (k-ℓ-1)/shortBinomialWeight k a (c/(k:ℝ)) (k-ℓ) =
      c/(ℓ:ℝ)*(1-(ℓ:ℝ)/(k:ℝ)) := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hℓ0 : (0:ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  have hv : 0 < shortBinomialWeight k a (c/(k:ℝ)) (k-ℓ) :=
    shortBinomialWeight_pos (by omega) (by omega) ha (div_pos hc hk0)
  have hstep := shortBinomialWeight_step (by omega : 2 ≤ k-ℓ) (by omega : k-ℓ < k) a (c/(k:ℝ))
  rw [Nat.sub_sub_self (by omega : ℓ ≤ k), Nat.cast_sub (by omega : ℓ ≤ k)] at hstep
  apply (div_eq_iff hv.ne').mpr
  field_simp
  have hmul := congrArg (fun z : ℝ => z*(k:ℝ)) hstep
  field_simp at hmul
  nlinarith only [hmul]

theorem binomialCost_ratio {k ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓk : ℓ < k)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    (k:ℝ)*binomialCost k a (c/(k:ℝ)) (k-ℓ)/shortBinomialWeight k a (c/(k:ℝ)) (k-ℓ) =
      a*c/(ℓ:ℝ) := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hℓ0 : (0:ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  have hv : 0 < shortBinomialWeight k a (c/(k:ℝ)) (k-ℓ) :=
    shortBinomialWeight_pos (by omega) (by omega) ha (div_pos hc hk0)
  have hstep := binomialCost_step (by omega : 1 ≤ k-ℓ) (by omega : k-ℓ < k) a (c/(k:ℝ))
  rw [Nat.sub_sub_self hℓk.le] at hstep
  apply (div_eq_iff hv.ne').mpr
  field_simp
  field_simp at hstep
  nlinarith only [hstep]

theorem cost_multipliers_nonnegative (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (a c : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (hc0 : 0 < c) (hc1 : c < 1/2)
    (hac : 5/12 < a*c) (hrel : (k:ℝ)*(1-a) = a*c) :
    ∀ j < k, 0 ≤ interpolationMultiplier (k-t)
      (fun j => ((t:ℝ)*((t:ℝ)-1)/(2*(k:ℝ)))*shortBinomialWeight k a (c/(k:ℝ)) j)
      (binomialCost k a (c/(k:ℝ)))
      (fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t ((t:ℝ)+1)) j := by
  let L := (t:ℝ)*((t:ℝ)-1)/(2*(k:ℝ))
  let v := shortBinomialWeight k a (c/(k:ℝ))
  let cost := binomialCost k a (c/(k:ℝ))
  let α := fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t ((t:ℝ)+1)
  let Γ := interpolationMultiplier (k-t) (fun j => L*v j) cost α
  let h := fun ℓ => (k:ℝ)*Γ (k-ℓ)/v (k-ℓ)
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
  have hL : 0 ≤ L := by
    have htm : (0:ℝ) ≤ (t:ℝ)-1 := by linarith
    dsimp [L]
    positivity
  have hKL : (k:ℝ)*L = (t:ℝ)*((t:ℝ)-1)/2 := by dsimp [L]; field_simp
  have hv (j : ℕ) (hj : 1 ≤ j) (hjk : j < k) : 0 < v j :=
    shortBinomialWeight_pos hj hjk ha0 (div_pos hc0 hk0)
  have hbase : h t = (t:ℝ)*((t:ℝ)-1)/2 := by
    have hΓ : Γ (k-t) = L*v (k-t) := interpolationMultiplier_base _ _ _ _ _ le_rfl
    dsimp [h]
    rw [hΓ]
    have hv0 := (hv (k-t) (by omega) (by omega)).ne'
    field_simp
    nlinarith only [hKL]
  have hrec : ∀ ℓ, 1 ≤ ℓ → ℓ < t →
      (1+ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1))*h ℓ =
        c/(ℓ:ℝ)*((1-(ℓ:ℝ)/(k:ℝ))*h (ℓ+1)-a)+
          ((t:ℝ)*((t:ℝ)-1)/2)*ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1) := by
    intro ℓ hℓ hℓt
    have hindex : k-ℓ-1 = k-(ℓ+1) := by omega
    have hαeq : α (k-ℓ) = ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1) := by
      dsimp [α]
      rw [Nat.sub_sub_self (by omega : ℓ ≤ k)]
    have hαpos : 0 ≤ α (k-ℓ) := by
      rw [hαeq]
      exact (ComparisonGeometry.chordSlope_pos ℓ t ((t:ℝ)+1)
        (by exact_mod_cast hℓ) (by exact_mod_cast (show ℓ+1 ≤ t by omega)) (by linarith)).le
    have hΓrec := interpolationMultiplier_rec (k-t) (fun j => L*v j) cost α (k-ℓ)
      (by omega) hαpos
    change Γ (k-ℓ)*(1+α (k-ℓ)) = Γ (k-ℓ-1)-cost (k-ℓ)+L*v (k-ℓ)*α (k-ℓ) at hΓrec
    rw [hαeq] at hΓrec
    have hvj := (hv (k-ℓ) (by omega) (by omega)).ne'
    have hvprev := (hv (k-ℓ-1) (by omega) (by omega)).ne'
    have hvratio : v (k-ℓ-1)/v (k-ℓ) = c/(ℓ:ℝ)*(1-(ℓ:ℝ)/(k:ℝ)) :=
      shortBinomialWeight_ratio hℓ (by omega) ha0 hc0
    have hcratio : (k:ℝ)*cost (k-ℓ)/v (k-ℓ) = a*c/(ℓ:ℝ) :=
      binomialCost_ratio hℓ (by omega) ha0 hc0
    calc
      _ = (k:ℝ)/v (k-ℓ)*(Γ (k-ℓ)*(1+ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1))) := by
        dsimp [h]
        ring
      _ = (k:ℝ)/v (k-ℓ)*(Γ (k-ℓ-1)-cost (k-ℓ)+
          L*v (k-ℓ)*ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1)) := by rw [hΓrec]
      _ = ((k:ℝ)*Γ (k-ℓ-1)/v (k-ℓ-1))*(v (k-ℓ-1)/v (k-ℓ))-
          (k:ℝ)*cost (k-ℓ)/v (k-ℓ)+
          ((k:ℝ)*L)*ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1) := by
        field_simp
      _ = h (ℓ+1)*(c/(ℓ:ℝ)*(1-(ℓ:ℝ)/(k:ℝ)))-a*c/(ℓ:ℝ)+
          ((t:ℝ)*((t:ℝ)-1)/2)*ComparisonGeometry.chordSlope ℓ t ((t:ℝ)+1) := by
        rw [hvratio, hcratio, hKL, hindex]
      _ = _ := by ring
  have hpositive := SlopeEstimates.downward_multiplier_positive k t hk ht htk c a hc0 hc1 ha1 hac hrel h hbase hrec
  intro j hj
  change 0 ≤ Γ j
  by_cases hjq : j ≤ k-t
  · rw [show Γ j = L*v j from interpolationMultiplier_base _ _ _ _ _ hjq]
    exact mul_nonneg hL (shortBinomialWeight_nonneg k ha0.le (div_nonneg hc0.le hk0.le) j)
  · have hj1 : 1 ≤ j := by omega
    have hscaled := hpositive (k-j) (by omega) (by omega)
    dsimp [h] at hscaled
    rw [Nat.sub_sub_self hj.le] at hscaled
    have hnum := (lt_div_iff₀ (hv j hj1 hj)).mp hscaled
    have hG : 0 < Γ j := pos_of_mul_pos_right (by simpa using hnum) hk0.le
    exact hG.le

theorem critical_cost_multipliers_nonnegative (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    ∀ j < k, 0 ≤ interpolationMultiplier (k-t)
      (fun j => ((t:ℝ)*((t:ℝ)-1)/(2*(k:ℝ)))*
        shortBinomialWeight k ((k:ℝ)/((k:ℝ)+c)) (c/(k:ℝ)) j)
      (binomialCost k ((k:ℝ)/((k:ℝ)+c)) (c/(k:ℝ)))
      (fun j => ComparisonGeometry.chordSlope (k-j : ℕ) t ((t:ℝ)+1)) j := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hcLow := CriticalEstimates.critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hc0 : 0 < c := by
    have hp : 0 ≤ 2/(25*(k:ℝ)) := by positivity
    linarith
  have hc1 := CriticalEstimates.critical_parameter_lt_half (by omega : 3 ≤ k) hc hcross
  have hb := CriticalEstimates.critical_elementary_bounds hk hc hcross
  simp only [mul_one_div] at hb
  apply cost_multipliers_nonnegative k t hk ht htk ((k:ℝ)/((k:ℝ)+c)) c
    (by positivity) (by exact hb.2.1.le) hc0 hc1 (by exact hb.2.2.1)
  field_simp
  ring

end SharpTailMatching.Probability
