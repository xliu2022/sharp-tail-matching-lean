module

public import SharpTailMatching.ExclusionAlgebra
public import SharpTailMatching.SupportAlgebra
public import SharpTailMatching.CriticalEstimates

/-! # Scalar estimates for the normalized two-component exclusion

The probability modules supply the identities for actual conditional moments.
This file keeps the rational deductions independent of measure notation.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace SharpTailMatching.ExclusionAlgebra

theorem normalized_support_ranges {θ u α e b : ℝ}
    (hθ : 0 < θ) (hu : 0 < u) (hα0 : 0 ≤ α) (hα1 : α ≤ (1-θ)/6)
    (he0 : 0 ≤ e) (he1 : e < (1-3*u-4*α)/20)
    (hb0 : u ≤ b) (hb1 : b ≤ u+1/16+15*α/16) :
    u < 1/3 ∧ e < 1/20 ∧ u ≤ b ∧ b ≤ u+(7-5*θ)/32 := by
  refine ⟨by linarith, by linarith, hb0, ?_⟩
  linarith

theorem normalized_variance_upper {θ u α e b v q a c : ℝ}
    (hθ : θ < 1) (hu0 : 0 < u) (hu1 : u < 1/3) (hα : 0 ≤ α)
    (he0 : 0 ≤ e) (he1 : e ≤ (1-3*u)/20) (hb : 0 ≤ b)
    (hq : 5/6 < q) (ha : 12/13 < a) (hc : 11/24 ≤ c)
    (hv : v+(63/80)*q*a*(1-θ)*b < (1+(1-c)*u-c*α-e)*e) :
    v+(3/5)*(1-θ)*b < Φ u ∧ Φ u < 19/400 := by
  have hqa : 10/13 < q*a := by
    have hp := mul_pos (by linarith : 0 < q-5/6) (by linarith : 0 < a-12/13)
    nlinarith
  have hcoeff : 3/5 ≤ (63/80)*q*a := by nlinarith
  have hcross := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (by linarith : 0 ≤ 1-θ) hb)
  have hcu := mul_nonneg (by linarith : 0 ≤ c-11/24) hu0.le
  have hcα := mul_nonneg (by linarith : 0 ≤ c) hα
  have hB : 1+(1-c)*u-c*α-e ≤ 1+13*u/24-e := by nlinarith
  have hquad := mul_le_mul_of_nonneg_right hB he0
  have hbound := SupportAlgebra.conditional_variance_upper hu0 hu1 he0 he1
  unfold Φ
  constructor
  · nlinarith only [hv, hcross, hquad, hbound.1]
  · exact hbound.2

theorem upper_count_ranges {a θ lam ν d g γ : ℝ}
    (ha : a < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hlam : 0 < lam) (hν0 : 0 ≤ ν) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hν1 : ν < 3*d/20) (hmass : lam*(1-ν) = a*(1-θ))
    (hg : d*g = lam*ν) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g) :
    0 ≤ g ∧ 0 ≤ γ ∧ γ ≤ g ∧ g < 3*(1-θ)/17 ∧ g < (1-θ)/5 := by
  have hg0 : 0 ≤ g := by
    have hp := mul_nonneg hlam.le hν0
    nlinarith only [hg, hp, hd0]
  have hνsmall : ν < 3/20 := by linarith
  have hmasslt : lam*(1-ν) < 1-θ := by
    rw [hmass]
    have h := mul_lt_mul_of_pos_right ha (by linarith : 0 < 1-θ)
    simpa only [one_mul] using h
  have hlambound : lam < 20*(1-θ)/17 := by
    have hp := mul_pos hlam (by linarith : 0 < 3/20-ν)
    nlinarith
  have hglam : g < 3*lam/20 := by
    have hp := mul_lt_mul_of_pos_left hν1 hlam
    nlinarith only [hp, hg, hd0]
  refine ⟨hg0, hγ0, hγg, by linarith, ?_⟩
  linarith

theorem upper_count_identities {k a θ lam ν d q g ℓ : ℝ}
    (hk : 0 < k) (hd : 0 < d) (hmass : lam*(1-ν) = a*(1-θ))
    (hdval : d = 1-lam*(1-ν)/k) (hqval : q = 1-lam/k)
    (hg : d*g = lam*ν) (hℓ : ℓ = a-lam) :
    q/d = 1-g/k ∧ a*θ = ℓ+d*g := by
  constructor
  · apply (div_eq_iff hd.ne').mpr
    have hdk : k*d = k-lam*(1-ν) := by rw [hdval]; field_simp
    have hqk : k*q = k-lam := by rw [hqval]; field_simp
    apply (mul_left_cancel₀ hk.ne')
    field_simp
    nlinarith only [hdk, hqk, hg]
  · rw [hℓ, hg]
    nlinarith only [hmass]

theorem lower_variance_bounds {k q d V z g Θ : ℝ}
    (hq : 0 < q) (hd : 0 < d) (hqd : q ≤ d) (hV : 0 < V)
    (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ d*g) (hvar : q*V = d*z+Θ)
    (hratio : q/d = 1-g/k) :
    z ≤ V ∧ V ≤ (z+g)/(1-g/k) := by
  constructor
  · by_cases hz : 0 ≤ z
    · have hdz := mul_le_mul_of_nonneg_right hqd hz
      have hmul : q*z ≤ q*V := by linarith
      exact (mul_le_mul_iff_right₀ hq).mp (by nlinarith only [hmul])
    · linarith
  · have hden : 0 < 1-g/k := by rw [← hratio]; positivity
    apply (le_div_iff₀ hden).mpr
    rw [← hratio]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith only [hvar, hΘ1]

theorem lower_tail_mass_factor {k : ℕ} (hk : 1 ≤ k) {x q p ℓ : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hp : 0 < p) (hp0 : p ≤ (1-x)^k)
    (hℓ : 0 < ℓ) (hq : q = 1-x+ℓ/(k:ℝ)) :
    1+ℓ < q^k/p := by
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  let u := ℓ/((k:ℝ)*(1-x))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hbern := (CriticalEstimates.positive_taylor_bounds k hu).1
  change 1+(k:ℝ)*u ≤ (1+u)^k at hbern
  have hul : ℓ < (k:ℝ)*u := by
    have hid : (k:ℝ)*u = ℓ/(1-x) := by dsimp [u]; field_simp
    rw [hid]
    apply (lt_div_iff₀ (by linarith : 0 < 1-x)).mpr
    nlinarith [mul_pos hℓ hx0]
  have hqfactor : q = (1-x)*(1+u) := by
    rw [hq]
    dsimp [u]
    field_simp [ne_of_gt (sub_pos.mpr hx1)]
  have hpow0 : 0 < (1-x)^k := pow_pos (by linarith) _
  have hq0 : 0 ≤ q^k := by rw [hqfactor, mul_pow]; positivity
  have hdiv := div_le_div_of_nonneg_left hq0 hp hp0
  have hid : q^k/(1-x)^k = (1+u)^k := by rw [hqfactor, mul_pow]; field_simp
  rw [hid] at hdiv
  linarith

theorem lower_tail_mass {K0 R γ g ℓ : ℝ}
    (hK : K0 = 1/R-1+γ) (hR : 1+ℓ < 1/R) (hγ : 5*g/8 ≤ γ) :
    ℓ+5*g/8 < K0 := by linarith

theorem lower_variance_four_tail_mass {a c θ u d q V z g ℓ K0 : ℝ}
    (ha : 12/13 < a) (hc0 : 11/24 < c) (hc1 : c ≤ 1/2)
    (hθ : 0 < θ) (hu : 0 < u) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hq : 5/6 < q) (hV : 0 < V) (hg : 0 ≤ g) (hℓ : 0 < ℓ)
    (hθeq : a*θ = ℓ+d*g) (huℓ : a*(c-3/17)*u < ℓ)
    (hz : z ≤ θ+(1-c)*u) (hvar : q*V ≤ d*(z+g))
    (hK : ℓ+5*g/8 < K0) : V < 4*K0 := by
  have hcoef : 1/4 < a*(c-3/17) := by
    have hp := mul_pos (by linarith : 0 < a-12/13) (by linarith : 0 < c-3/17)
    nlinarith
  have hu4 : u < 4*ℓ := by
    have hp := mul_lt_mul_of_pos_right hcoef hu
    nlinarith
  have hθbound : θ < (13/12)*(ℓ+g) := by
    have hp := mul_lt_mul_of_pos_right ha hθ
    have hgd := mul_le_mul_of_nonneg_right hd1 hg
    nlinarith
  have hzu : z+g < (13/4)*ℓ+(25/12)*g := by
    have hcu := mul_lt_mul_of_pos_right (by linarith : 1-c < 13/24) hu
    linarith
  have hqV := mul_lt_mul_of_pos_right hq hV
  have hzpos : 0 < z+g := by
    have hq0 : 0 < q := by linarith
    have hp : 0 < d*(z+g) := (mul_pos hq0 hV).trans_le hvar
    exact pos_of_mul_pos_right hp hd0.le
  have hdprod := mul_le_mul_of_nonneg_right hd1 hzpos.le
  nlinarith only [hvar, hzu, hqV, hdprod, hK, hℓ]

theorem basic_first_moment {V K0 K1 τ : ℝ} (hV : 0 < V) (hτ : 0 < τ)
    (hK0 : V < 4*K0) (hK1 : τ*K0 ≤ K1) : τ/4 < K1/V := by
  apply (lt_div_iff₀ hV).mpr
  have h := mul_lt_mul_of_pos_left hK0 hτ
  nlinarith

end SharpTailMatching.ExclusionAlgebra
