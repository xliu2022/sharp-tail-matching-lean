module

public import SharpTailMatching.Probability.NodeWeights
public import SharpTailMatching.CriticalProbabilityEstimates

/-! # The base deficit and its quantitative ratio bound -/

@[expose] public section

noncomputable section

namespace SharpTailMatching.Probability.ComparisonGeometry

theorem zero_nodePower_strictMono :
    StrictMonoOn (nodePower 0) (Set.Ioi 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro t ht
    exact (hasDerivAt_nodePower 0 t ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 1 < t := by simpa only [interior_Ioi, Set.mem_Ioi] using ht
    rw [(hasDerivAt_nodePower 0 t ht').deriv]
    exact mul_pos_of_neg_of_neg (by nlinarith [nodePower_pos 0 t] : -nodePower 0 t < 0)
      (zero_logarithmicRate_neg t ht')

theorem nodeFailureValue_ge_four {t : ℕ} (ht : 4 ≤ t) : 81/256 ≤ nodeFailureValue t := by
  have hmono := zero_nodePower_strictMono.monotoneOn
    (show (4:ℝ) ∈ Set.Ioi 1 by norm_num) (show (t:ℝ) ∈ Set.Ioi 1 by
      have htR : (4:ℝ) ≤ t := by exact_mod_cast ht
      change 1 < (t:ℝ); linarith) (by exact_mod_cast ht)
  have hfour := nodePowerNat_eq_real 0 4 (by omega) (by omega)
  have htval := nodePowerNat_eq_real 0 t (by omega) (by omega)
  norm_num only [Nat.cast_zero, Nat.cast_ofNat] at hfour htval
  rw [← hfour, ← htval] at hmono
  norm_num [nodePowerNat, nodeFailureValue] at hmono ⊢
  exact hmono

theorem base_deficit_numerical {k t c x a p H : ℝ}
    (hk : 0 < k) (ht : 4 ≤ t) (hc : 4/9 < c) (hx : 0 < x)
    (ha : 12/13 < a) (hax : a = k*x) (hp0 : 0 < p) (hp1 : p < 3/8)
    (hH : 81/256 ≤ H) :
    let rb := x*(t+c)*H/p
    let L := t*(t-1)/(2*k)
    x < rb ∧ L*x/(rb-x)^2 < 9/10 := by
  let rb := x*(t+c)*H/p
  let L := t*(t-1)/(2*k)
  let A := (27*t-20)/32
  have hA : 0 < A := by dsimp [A]; linarith
  have ht0 : 0 < t := by linarith
  have htm : 0 < t-1 := by linarith
  have ha0 : 0 < a := by linarith
  have htc : 0 < t+c := by linarith
  have hnum : (t+4/9)*(81/256) < (t+c)*H := by
    have hm := mul_le_mul_of_nonneg_left hH htc.le
    nlinarith
  have hratio : (27*t+12)/32 < (t+c)*H/p := by
    apply (lt_div_iff₀ hp0).mpr
    have hm := mul_lt_mul_of_pos_left hp1 (by linarith : 0 < (27*t+12)/32)
    nlinarith
  have hgap : x*A < rb-x := by
    have hm := mul_lt_mul_of_pos_left hratio hx
    have hid : x*((t+c)*H/p) = rb := by dsimp [rb]; ring
    rw [hid] at hm
    dsimp [A]
    nlinarith only [hm]
  have hr : x < rb := by have hp : 0 < x*A := mul_pos hx hA; linarith
  refine ⟨hr, ?_⟩
  have hLx : 0 < L*x := by dsimp [L]; positivity
  have hsq : (x*A)^2 < (rb-x)^2 := by
    have hp := mul_pos hx hA
    nlinarith [sq_nonneg (rb-x-x*A)]
  have hid : L*x/(x*A)^2 = (t*(t-1)/(2*a))/A^2 := by
    dsimp [L]
    rw [hax]
    field_simp
  have hnum2 : t*(t-1)/(2*a) < 13/24*t*(t-1) := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*a)).mpr
    have hmul := mul_pos (by linarith : 0 < 13*a-12) (mul_pos ht0 htm)
    nlinarith
  have ht27 : 0 < 27*t-20 := by linarith
  have hratid : (13/24*t*(t-1))/A^2 = 1664*t*(t-1)/(3*(27*t-20)^2) := by
    dsimp [A]
    field_simp [ne_of_gt ht27]
    norm_num
  have hpoly := mul_nonneg (by linarith : 0 ≤ t-4) (by linarith : 0 ≤ 251*t-300)
  have hnumeric : 1664*t*(t-1)/(3*(27*t-20)^2) ≤ 104/121 := by
    apply (div_le_iff₀ (by positivity : 0 < 3*(27*t-20)^2)).mpr
    nlinarith only [hpoly]
  calc
    _ < L*x/(x*A)^2 := div_lt_div_of_pos_left hLx (sq_pos_of_pos (mul_pos hx hA)) hsq
    _ = (t*(t-1)/(2*a))/A^2 := hid
    _ < (13/24*t*(t-1))/A^2 := div_lt_div_of_pos_right hnum2 (sq_pos_of_pos hA)
    _ = 1664*t*(t-1)/(3*(27*t-20)^2) := hratid
    _ ≤ 104/121 := hnumeric
    _ < 9/10 := by norm_num

theorem critical_base_deficit_bounds {k t : ℕ} (hk : 6 ≤ k) (ht : 4 ≤ t)
    {c : ℝ} (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let x := 1/((k:ℝ)+c)
    let p0 := (1-x)^k
    let rb := x*((t:ℝ)+c)*nodeFailureValue t/p0
    let L := (t:ℝ)*((t:ℝ)-1)/(2*(k:ℝ))
    x < rb ∧ L*x/(rb-x)^2 < 9/10 := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hb := CriticalEstimates.critical_elementary_bounds hk hc hcross
  have hcLow := CriticalEstimates.critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hc4 : (4:ℝ)/9 < c := by
    have hp : 0 ≤ 2/(25*(k:ℝ)) := by positivity
    linarith
  exact base_deficit_numerical hk0 (by exact_mod_cast ht) hc4 (by positivity)
    hb.1 rfl (by linarith [hb.2.2.2.1]) (hb.2.2.2.2.1.trans hb.2.2.2.2.2)
    (nodeFailureValue_ge_four ht)

end SharpTailMatching.Probability.ComparisonGeometry
