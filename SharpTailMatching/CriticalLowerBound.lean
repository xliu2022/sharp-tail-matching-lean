module

public import SharpTailMatching.CriticalEstimates
public import SharpTailMatching.CentralBinomial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # The explicit lower bound for the critical parameter -/

@[expose] public section

noncomputable section

open Set

namespace SharpTailMatching.CriticalEstimates

theorem log_one_sub_quadratic {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) :
    Real.log (1-η) ≤ -η-η^2/2 := by
  let f : ℝ → ℝ := fun t => Real.log (1-t) + t + t^2/2
  have hd (t : ℝ) (ht : t < 1) : HasDerivAt f (-t^2/(1-t)) t := by
    have ht0 : 1-t ≠ 0 := by linarith
    convert ((((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log ht0).add
      (hasDerivAt_id t)).add (((hasDerivAt_id t).pow 2).div_const 2) using 1
    · rfl
    · simp only [id_eq, Pi.sub_apply]
      field_simp
      ring
  have hm : AntitoneOn f (Iio 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iio _)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      have ht' : t < 1 := by simpa only [interior_Iio, mem_Iio] using ht
      exact (hd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t < 1 := by simpa only [interior_Iio, mem_Iio] using ht
      rw [(hd t ht').deriv]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
        (by linarith)
  have hh := hm (show (0:ℝ) ∈ Iio 1 by norm_num) hη1 hη0
  dsimp [f] at hh
  norm_num at hh
  linarith

theorem central_critical_exp_upper {k : ℕ} (hk : 2 ≤ k) {b : ℝ} (hb : 0 < b) :
    criticalDifference k (1/2 + (k:ℝ)*(b-1)) ≤
      b^(k-1) * Real.exp (((k:ℝ)-1)*((k:ℝ)-2)/(24*(k:ℝ)^2*b^2)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n+2 := ⟨k-2, by omega⟩
  have hkpos : (0:ℝ) < (n+2:ℕ) := by positivity
  have h := CentralBinomial.central_binomial_exp_bound (n+1) hb
    (h := 1/(2*(n+2:ℕ))) (by positivity)
  have hA : 1+(1/2+(n+2:ℕ)*(b-1))/(n+2:ℕ) = b+1/(2*(n+2:ℕ)) := by
    field_simp
    ring
  have hB : 1-(1-(1/2+(n+2:ℕ)*(b-1)))/(n+2:ℕ) = b-1/(2*(n+2:ℕ)) := by
    field_simp
    ring
  have hcoef : (((n+1)*((n+1)-1):ℕ):ℝ) * ((1/(2*(n+2:ℕ)))/b)^2/6 =
      (((n+2:ℕ):ℝ)-1)*(((n+2:ℕ):ℝ)-2)/(24*((n+2:ℕ):ℝ)^2*b^2) := by
    norm_num only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring
  have hpre : 2*(n+1+1:ℕ)*(1/(2*(n+2:ℕ))) = (1:ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring
  rw [hcoef, hpre, one_mul] at h
  simpa only [criticalDifference, hA, hB, show n+1+1 = n+2 by omega,
    show n+2-1 = n+1 by omega] using h

def criticalTestPoint (k : ℕ) : ℝ := 11/24 + 2/(25*(k:ℝ))
def criticalEta (k : ℕ) : ℝ := 1/(24*(k:ℝ)) - 2/(25*(k:ℝ)^2)

theorem criticalEta_bounds {k : ℕ} (hk : 2 ≤ k) :
    0 < criticalEta k ∧ criticalEta k < 1/(24*(k:ℝ)) ∧ criticalEta k < 1 := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hid : criticalEta k = (25*(k:ℝ)-48)/(600*(k:ℝ)^2) := by
    unfold criticalEta
    field_simp
    ring
  have hpos : 0 < criticalEta k := by
    rw [hid]
    exact div_pos (by linarith) (by positivity)
  have hupper : criticalEta k < 1/(24*(k:ℝ)) := by
    unfold criticalEta
    have h : 0 < 2/(25*(k:ℝ)^2) := by positivity
    linarith
  refine ⟨hpos, hupper, hupper.trans ?_⟩
  exact (div_lt_one (by positivity : (0:ℝ) < 24*k)).mpr (by linarith)

theorem critical_test_identity {k : ℕ} (hk : 1 ≤ k) :
    criticalTestPoint k = 1/2 + (k:ℝ)*((1-criticalEta k)-1) := by
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold criticalTestPoint criticalEta
  field_simp
  ring

theorem critical_test_log_negative {k : ℕ} (hk : 2 ≤ k) :
    Real.log (1-criticalEta k) + ((k:ℝ)-2)/(24*(k:ℝ)^2*(1-criticalEta k)^2) < 0 := by
  obtain ⟨hη0, hηupper, hη1⟩ := criticalEta_bounds hk
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  let η := criticalEta k
  let b := 1-η
  have hb : 0 < b := by dsimp [b, η]; linarith
  have hlog := log_one_sub_quadratic hη0.le hη1
  have hscaled := mul_le_mul_of_nonneg_left hlog (sq_nonneg (1-criticalEta k))
  have hscaled' : b^2 * Real.log b ≤ -η+3/2*η^2 := by
    change b^2 * Real.log b ≤ b^2 * (-η-η^2/2) at hscaled
    have hid : b^2 * (-η-η^2/2) = -η+3/2*η^2-η^4/2 := by dsimp [b]; ring
    rw [hid] at hscaled
    nlinarith [sq_nonneg (η^2)]
  have hηsq : η^2 ≤ 1/(576*(k:ℝ)^2) := by
    have hh : (1/(24*(k:ℝ)))^2 = 1/(576*(k:ℝ)^2) := by ring
    rw [← hh]
    exact (sq_le_sq₀ (by exact hη0.le) (by positivity)).mpr hηupper.le
  have hid : -η + (3/2:ℝ)*(1/(576*(k:ℝ)^2)) + ((k:ℝ)-2)/(24*(k:ℝ)^2) =
      -(7/9600)/(k:ℝ)^2 := by
    dsimp [η, criticalEta]
    field_simp
    ring
  have hnum : b^2*Real.log b + ((k:ℝ)-2)/(24*(k:ℝ)^2) < 0 := by
    have hneg : -(7/9600)/(k:ℝ)^2 < 0 :=
      div_neg_of_neg_of_pos (by norm_num) (by positivity)
    nlinarith
  have hprod : b^2 * (Real.log b + ((k:ℝ)-2)/(24*(k:ℝ)^2*b^2)) =
      b^2*Real.log b + ((k:ℝ)-2)/(24*(k:ℝ)^2) := by
    field_simp
  change Real.log b + ((k:ℝ)-2)/(24*(k:ℝ)^2*b^2) < 0
  by_contra hnot
  have hp := mul_nonneg (sq_nonneg b) (le_of_not_gt hnot)
  rw [hprod] at hp
  linarith

theorem critical_test_below_one {k : ℕ} (hk : 2 ≤ k) :
    criticalDifference k (criticalTestPoint k) < 1 := by
  obtain ⟨hη0, hηupper, hη1⟩ := criticalEta_bounds hk
  let b := 1-criticalEta k
  have hb : 0 < b := by dsimp [b]; linarith
  have hupper := central_critical_exp_upper hk hb
  rw [← critical_test_identity (by omega : 1 ≤ k)] at hupper
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hknat : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hexp : b^(k-1) * Real.exp (((k:ℝ)-1)*((k:ℝ)-2)/(24*(k:ℝ)^2*b^2)) =
      Real.exp (((k:ℝ)-1) * (Real.log b + ((k:ℝ)-2)/(24*(k:ℝ)^2*b^2))) := by
    calc
      _ = Real.exp (((k-1:ℕ):ℝ)*Real.log b) *
          Real.exp (((k:ℝ)-1)*((k:ℝ)-2)/(24*(k:ℝ)^2*b^2)) := by
        rw [Real.exp_nat_mul, Real.exp_log hb]
      _ = Real.exp (((k-1:ℕ):ℝ)*Real.log b +
          ((k:ℝ)-1)*((k:ℝ)-2)/(24*(k:ℝ)^2*b^2)) := (Real.exp_add _ _).symm
      _ = _ := by congr 1; rw [hknat]; ring
  rw [hexp] at hupper
  apply hupper.trans_lt
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_pos_of_neg (by linarith) (critical_test_log_negative hk)

/-- The explicit lower bound used in the interpolation and support estimates. -/
theorem critical_parameter_lower {k : ℕ} (hk : 2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    11/24 + 2/(25*(k:ℝ)) < c := by
  have htest : 0 ≤ criticalTestPoint k := by unfold criticalTestPoint; positivity
  by_contra h
  have hmono := (criticalDifference_strictMono hk).monotoneOn hc htest (le_of_not_gt h)
  have hsmall := critical_test_below_one hk
  rw [hcross] at hmono
  linarith

end SharpTailMatching.CriticalEstimates
