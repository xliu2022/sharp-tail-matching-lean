module

public import SharpTailMatching.RationalCertificates
public import SharpTailMatching.CriticalProbabilityEstimates

/-! # Moving the exact rational certificates to the actual critical parameter -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Set SharpTailMatching.ScalarCertificates SharpTailMatching.RationalCertificates

namespace SharpTailMatching.CriticalEstimates

def comparisonBC (n k c : ℝ) : ℝ :=
  (1+(k-1)*(c/(k+c))/n+(k-1)*(k-2)*(c/(k+c))^2/(2*n^2)) *
    (1+(1/2-c)/k+1/(12*k^2))

def derivativeAlpha (k c : ℝ) : ℝ :=
  (k-1)/(k+c)^2 * (k+1/2-2*c+(1/12-c^2)/k)

def derivativeBeta (k c : ℝ) : ℝ :=
  (k-1)*(k-2)*c/(k+c)^3 * (k+1/2-3*c/2+(1/12-c^2/2)/k)

theorem comparisonBC_derivative {n k c : ℝ} (hn : n ≠ 0) (hk : k ≠ 0)
    (hkc : k+c ≠ 0) :
    HasDerivAt (comparisonBC n k)
      (derivativeAlpha k c / n + derivativeBeta k c / n^2 - 1/k) c := by
  have hz : HasDerivAt (fun u : ℝ => u/(k+u)) (k/(k+c)^2) c := by
    convert (hasDerivAt_id c).div ((hasDerivAt_const c k).add (hasDerivAt_id c)) hkc using 1
    · rfl
    · simp only [id_eq, Pi.add_apply]
      field_simp
      ring
  convert (((hasDerivAt_const c 1).add ((hz.const_mul (k-1)).div_const n)).add
    (((hz.pow 2).const_mul ((k-1)*(k-2))).div_const (2*n^2))).mul
    (((hasDerivAt_const c 1).add
      (((hasDerivAt_const c (1/2)).sub (hasDerivAt_id c)).div_const k)).add_const (1/(12*k^2))) using 1
  · funext u
    dsimp [comparisonBC]
  · dsimp [derivativeAlpha, derivativeBeta]
    field_simp
    ring

theorem derivative_coefficients_pos {k c : ℝ} (hk : 6 ≤ k)
    (hc0 : 11/24 ≤ c) (hc1 : c ≤ 1/2) :
    0 < derivativeAlpha k c ∧ 0 < derivativeBeta k c := by
  have hkpos : 0 < k := by linarith
  have hcpos : 0 < c := by linarith
  have hsq : c^2 ≤ 1/4 := by nlinarith [mul_nonneg hcpos.le (sub_nonneg.mpr hc1)]
  have hkc : k*c ≤ k/2 := by nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hc1)]
  have hA : 0 < k+1/2-2*c+(1/12-c^2)/k := by
    have hprod : k*(k+1/2-2*c+(1/12-c^2)/k) = k^2+k/2-2*k*c+1/12-c^2 := by
      field_simp
      ring
    have hp : 0 < k*(k+1/2-2*c+(1/12-c^2)/k) := by rw [hprod]; nlinarith
    exact (mul_pos_iff_of_pos_left hkpos).mp hp
  have hB : 0 < k+1/2-3*c/2+(1/12-c^2/2)/k := by
    have hprod : k*(k+1/2-3*c/2+(1/12-c^2/2)/k) = k^2+k/2-3*k*c/2+1/12-c^2/2 := by
      field_simp
      ring
    have hp : 0 < k*(k+1/2-3*c/2+(1/12-c^2/2)/k) := by rw [hprod]; nlinarith
    exact (mul_pos_iff_of_pos_left hkpos).mp hp
  constructor
  · exact mul_pos (div_pos (by linarith) (by positivity)) hA
  · exact mul_pos (div_pos
      (mul_pos (mul_pos (by linarith) (by linarith)) hcpos) (by positivity)) hB

theorem comparisonBC_boundary_identity {k c : ℝ} (hk : k ≠ 0)
    (hk2 : k-2 ≠ 0) (hkc : k+c ≠ 0) :
    2*k*(k-2)*(k+c)^3 *
      (derivativeAlpha k c/(k-2) + derivativeBeta k c/(k-2)^2 - 1/k) =
    (3-6*c)*k^3 + (-5/6+14*c-15*c^2)*k^2 +
      (-1/6-5*c/3+21*c^2-5*c^3)*k + c*(7*c^2-1/3) := by
  unfold derivativeAlpha derivativeBeta
  field_simp
  ring

theorem comparisonBC_derivative_pos {n k c : ℝ} (hn : 4 ≤ n) (hnk : n+2 ≤ k)
    (hc0 : 11/24 ≤ c) (hc1 : c ≤ 1/2) :
    0 < derivativeAlpha k c/n + derivativeBeta k c/n^2 - 1/k := by
  have hk : 6 ≤ k := by linarith
  have hnpos : 0 < n := by linarith
  have hkpos : 0 < k := by linarith
  have hkm : 0 < k-2 := by linarith
  have hcpos : 0 < c := by linarith
  obtain ⟨hA, hB⟩ := derivative_coefficients_pos hk hc0 hc1
  have hid := comparisonBC_boundary_identity hkpos.ne' hkm.ne' (by positivity : k+c ≠ 0)
  have hpoly := ScalarCertificates.derivative_boundary_positive hkpos hc0 hc1
  have hboundary : 0 < derivativeAlpha k c/(k-2) + derivativeBeta k c/(k-2)^2 - 1/k := by
    have hmul : 0 < 2*k*(k-2)*(k+c)^3 := by positivity
    exact (mul_pos_iff_of_pos_left hmul).mp (by rw [hid]; exact hpoly)
  have hAmono : derivativeAlpha k c/(k-2) ≤ derivativeAlpha k c/n :=
    div_le_div_of_nonneg_left hA.le hnpos (by linarith)
  have hBmono : derivativeBeta k c/(k-2)^2 ≤ derivativeBeta k c/n^2 :=
    div_le_div_of_nonneg_left hB.le (sq_pos_of_pos hnpos)
      ((sq_le_sq₀ hnpos.le hkm.le).mpr (by linarith))
  linarith

theorem comparisonBC_strictMono {n k : ℝ} (hn : 4 ≤ n) (hnk : n+2 ≤ k) :
    StrictMonoOn (comparisonBC n k) (Icc (11/24) (1/2)) := by
  have hn0 : n ≠ 0 := by linarith
  have hk0 : k ≠ 0 := by linarith
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro c hc
    exact (comparisonBC_derivative hn0 hk0 (by have := hc.1; linarith)).continuousAt.continuousWithinAt
  · intro c hc
    have hc' : c ∈ Icc (11/24) (1/2) := interior_subset hc
    rw [(comparisonBC_derivative hn0 hk0 (by have := hc'.1; linarith)).deriv]
    exact comparisonBC_derivative_pos hn hnk hc'.1 hc'.2

theorem comparisonValue_monotone {t u v : ℝ} (ht : 2 ≤ t)
    (hu0 : 0 ≤ u) (huv : u ≤ v) (hv1 : v ≤ 1) :
    comparisonValue t u ≤ comparisonValue t v := by
  have htpos : 0 < t := by linarith
  have htu : 0 < t-u := by linarith
  have htv : 0 < t-v := by linarith
  have hv0 : 0 ≤ v := hu0.trans huv
  have huv1 : u*v ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr (huv.trans hv1)) hv0]
  have hinner : 0 < 19*t^2+4*t*(u+v)-4*u*v := by
    nlinarith [mul_nonneg htpos.le (add_nonneg hu0 hv0)]
  have hid : comparisonValue t v - comparisonValue t u =
      (v-u)*(19*t^2+4*t*(u+v)-4*u*v)/(20*t*(t-u)*(t-v)) := by
    unfold comparisonValue
    field_simp
    ring
  have hp : 0 ≤ (v-u)*(19*t^2+4*t*(u+v)-4*u*v)/(20*t*(t-u)*(t-v)) := by
    positivity
  linarith

theorem phi_monotone {n k : ℝ} (hn : 4 ≤ n) (hnk : n+2 ≤ k) :
    MonotoneOn (phi n k) (Icc (11/24) (1/2)) := by
  intro c hc d hd hcd
  have hBC := (comparisonBC_strictMono hn hnk).monotoneOn hc hd hcd
  have hkpos : 0 < k := by linarith
  have hkc : 0 < k+c := by have := hc.1; linarith
  have hkd : 0 < k+d := by have := hd.1; linarith
  have hfrac : k/(k+d) ≤ k/(k+c) := div_le_div_of_nonneg_left hkpos.le hkc (by linarith)
  have hupper : k/(k+c) ≤ 1 := (div_le_one hkc).mpr (by have := hc.1; linarith)
  have hcomp := comparisonValue_monotone (by linarith : 2 ≤ n+1)
    (div_nonneg hkpos.le hkd.le) hfrac hupper
  let A : ℝ := 1+3/(6*n+4)+(3/(6*n+4))^2/2+(3/(6*n+4))^3/6
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmul := mul_le_mul_of_nonneg_left hBC hA
  have hphi (u : ℝ) : phi n k u = A*comparisonBC n k u - 1 - comparisonValue (n+1) (k/(k+u)) := by
    unfold phi comparisonBC A
    ring
  rw [hphi, hphi]
  linarith

theorem phi_at_critical_large {n k : ℕ} (hn : 5 ≤ n) (hnk : n+2 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    1/(500*(n:ℝ)^3) < phi n k c := by
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hnkR : (n:ℝ)+2 ≤ k := by exact_mod_cast hnk
  have hcl := critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hc0 : 11/24 ≤ c := by
    have hp : 0 ≤ 2/(25*(k:ℝ)) := by positivity
    linarith
  have hc1 := critical_parameter_le_half (by omega : 2 ≤ k) hc hcross
  exact (RationalCertificates.phi_lower_bound_large hnR hnkR).trans_le
    (phi_monotone (by linarith : (4:ℝ) ≤ n) hnkR (by norm_num) ⟨hc0, hc1⟩ hc0)

theorem phi_at_critical_four {k : ℕ} (hk : 6 ≤ k) {c : ℝ}
    (hc : 0 ≤ c) (hcross : criticalDifference k c = 1) :
    1/4000 < phi 4 k c := by
  have hkR : (6:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hcl := critical_parameter_lower (by omega : 2 ≤ k) hc hcross
  have hfrac : 1/(24*(k:ℝ)) < 2/(25*(k:ℝ)) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hd0 : 11/24 ≤ 11/24+1/(24*(k:ℝ)) := by
    have hp : 0 ≤ 1/(24*(k:ℝ)) := by positivity
    linarith
  have hd1 : 11/24+1/(24*(k:ℝ)) ≤ 1/2 := by
    have hh : 1/(24*(k:ℝ)) ≤ 1/24 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith
  have hdc : 11/24+1/(24*(k:ℝ)) ≤ c := by linarith
  have hc1 := critical_parameter_le_half (by omega : 2 ≤ k) hc hcross
  exact (RationalCertificates.phi_lower_bound_four hkR).trans_le
    (phi_monotone (by norm_num : (4:ℝ) ≤ 4) (by linarith : (4:ℝ)+2 ≤ k)
      ⟨hd0, hd1⟩ ⟨by linarith, hc1⟩ hdc)

end SharpTailMatching.CriticalEstimates
