module

public import SharpTailMatching.ExclusionEstimates

/-! # The lower-tail first moment and normalized cubic contradiction -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace SharpTailMatching.ExclusionAlgebra

theorem conditional_first_moment_lower {θ z v g γ dL K1 : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hz : 0 < z)
    (hv0 : 0 ≤ v) (hv1 : v < 1/20) (hg0 : 0 ≤ g) (hg1 : g < (1-θ)/5)
    (hγ0 : 0 ≤ γ) (hγg : γ ≤ g)
    (hcond : (dL-z)^2 ≤ v*γ/(1-γ)) (hK : K1 = (1-γ)*dL) :
    (1-g)*z-1/10 < K1 := by
  have hgsmall : g < 1/5 := by linarith
  have hγ1 : γ < 1 := by linarith
  have hden : 0 < 1-γ := by linarith
  have hcond' := (le_div_iff₀ hden).mp hcond
  have hmul := mul_le_mul_of_nonneg_right hcond' hden.le
  have hvg : v*g < 1/100 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 1/20-v) hg0
    nlinarith
  have hγsq : v*γ*(1-γ) ≤ v*g := by
    have h1 := mul_nonneg (mul_nonneg hv0 hγ0) hγ0
    have h2 := mul_le_mul_of_nonneg_left hγg hv0
    nlinarith
  have hs : ((1-γ)*(dL-z))^2 < 1/100 := by nlinarith only [hmul, hγsq, hvg]
  have hdev : -(1/10) < (1-γ)*(dL-z) := by nlinarith only [hs]
  have hγz := mul_le_mul_of_nonneg_right hγg hz.le
  nlinarith only [hK, hdev, hγz]

theorem strong_first_moment_rational {θ : ℝ} (hθ0 : 1/4 ≤ θ) (hθ1 : θ ≤ 1) :
    3*θ/4 < (((4+θ)/5-1/(8*θ))*(29+θ))/(30*(1+(1-θ)/(4*θ))) := by
  have hθpos : 0 < θ := by linarith
  have hden : 0 < 3*θ+1 := by positivity
  have hid : (((4+θ)/5-1/(8*θ))*(29+θ))/(30*(1+(1-θ)/(4*θ)))-3*θ/4 =
      (8*θ^3-411*θ^2+698*θ-145)/(300*(3*θ+1)) := by
    have hform : 1+(1-θ)/(4*θ) = (3*θ+1)/(4*θ) := by field_simp; ring
    rw [hform]
    field_simp
    ring
  have hpolynomial : 8*θ^3-411*θ^2+698*θ-145 =
      (779*θ-179)/4+(θ-1/4)*(1-θ)*(401-8*θ) := by ring
  have hrem : 0 ≤ (θ-1/4)*(1-θ)*(401-8*θ) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hnum : 0 < 8*θ^3-411*θ^2+698*θ-145 := by rw [hpolynomial]; linarith
  have hpos := div_pos hnum (by positivity : 0 < 300*(3*θ+1))
  linarith

theorem strong_first_moment {k θ z v V g γ dL K1 : ℝ}
    (hk : 6 ≤ k) (hθ0 : 1/4 ≤ θ) (hθ1 : θ < 1) (hz : 4*θ/5 ≤ z)
    (hv0 : 0 ≤ v) (hv1 : v < 1/20) (hV : 0 < V)
    (hg0 : 0 ≤ g) (hg1 : g < (1-θ)/5) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g)
    (hcond : (dL-z)^2 ≤ v*γ/(1-γ)) (hK : K1 = (1-γ)*dL)
    (hvar : V ≤ (z+g)/(1-g/k)) : 3*θ/4 < K1/V := by
  have hθpos : 0 < θ := by linarith
  have hzpos : 0 < z := by linarith
  have hkpos : 0 < k := by linarith
  have hKlow := conditional_first_moment_lower hθpos hθ1 hzpos hv0 hv1 hg0 hg1 hγ0 hγg hcond hK
  let A := (4+θ)/5-1/(8*θ)
  let B := (29+θ)/30
  let C := 1+(1-θ)/(4*θ)
  have hinv : 1/(8*θ) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hA : 0 < A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hAz : A*z < K1 := by
    have hlin : ((4+θ)/5)*z ≤ (1-g)*z :=
      mul_le_mul_of_nonneg_right (by linarith) hzpos.le
    have hfrac : 1/10 ≤ z/(8*θ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    have hid : A*z = ((4+θ)/5)*z-z/(8*θ) := by dsimp [A]; ring
    rw [hid]
    linarith
  have hden : B ≤ 1-g/k := by
    have hfrac : g/k ≤ g/6 := div_le_div_of_nonneg_left hg0 (by norm_num) hk
    dsimp [B]
    linarith
  have hnum : z+g ≤ z*C := by
    have h1 := mul_le_mul_of_nonneg_right hg1.le (by positivity : 0 ≤ 4*θ)
    have h2 := mul_le_mul_of_nonneg_right hz (by linarith : 0 ≤ 1-θ)
    have hgfrac : g ≤ z*(1-θ)/(4*θ) :=
      (le_div_iff₀ (by positivity)).mpr (by nlinarith only [h1, h2])
    have hid : z*C = z+z*(1-θ)/(4*θ) := by dsimp [C]; ring
    rw [hid]
    linarith
  have hVbound : V ≤ z*C/B := hvar.trans
    (div_le_div₀ (mul_nonneg hzpos.le hC.le) hnum hB hden)
  have hF : 0 < A*B/C := by positivity
  have hmul := mul_le_mul_of_nonneg_left hVbound hF.le
  have hid : (A*B/C)*(z*C/B) = A*z := by field_simp
  rw [hid] at hmul
  have hratio : A*B/C < K1/V := (lt_div_iff₀ hV).mpr (hmul.trans_lt hAz)
  have hrat := strong_first_moment_rational hθ0 hθ1.le
  have hform : A*B/C = (((4+θ)/5-1/(8*θ))*(29+θ))/(30*(1+(1-θ)/(4*θ))) := by
    change A*((29+θ)/30)/C = A*(29+θ)/(30*C)
    rw [mul_div_assoc, div_div]
    rw [← mul_div_assoc]
  rw [hform] at hratio
  exact hrat.trans hratio

theorem uniform_first_moment {k θ u c τ z v V g γ dL K0 K1 : ℝ}
    (hk : 6 ≤ k) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : 0 < u) (hc : 0 < c)
    (hτ : τ = 1-θ+c*u) (hz : θ-1/20 < z)
    (hv0 : 0 ≤ v) (hv1 : v < 1/20) (hV : 0 < V)
    (hg0 : 0 ≤ g) (hg1 : g < (1-θ)/5) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g)
    (hcond : (dL-z)^2 ≤ v*γ/(1-γ)) (hK : K1 = (1-γ)*dL)
    (hvar : V ≤ (z+g)/(1-g/k)) (hK0 : V < 4*K0) (hK1 : τ*K0 ≤ K1) :
    3*max θ (1/4)/4 < K1/V := by
  by_cases hθ : θ ≤ 1/4
  · rw [max_eq_right hθ]
    have hτpos : 0 < τ := by rw [hτ]; nlinarith [mul_pos hc hu]
    have hbasic := basic_first_moment hV hτpos hK0 hK1
    have hτ3 : 3/4 < τ := by rw [hτ]; nlinarith [mul_pos hc hu]
    linarith
  · rw [max_eq_left (le_of_not_ge hθ)]
    exact strong_first_moment hk (le_of_not_ge hθ) hθ1 (by linarith) hv0 hv1 hV
      hg0 hg1 hγ0 hγg hcond hK hvar

theorem cubic_denominator_bound {V z b : ℝ} (hV : 0 < V) (hzV : z ≤ V)
    (hb : 0 ≤ b) (hz : z < 4/3) :
    1+(max (z-b) 0)^2/(12*V) < 10/9 := by
  have hmax : 0 ≤ max (z-b) 0 := le_max_right _ _
  by_cases hz0 : z ≤ 0
  · rw [max_eq_right (by linarith : z-b ≤ 0)]
    norm_num
  · have hzpos : 0 < z := lt_of_not_ge hz0
    have hmb : max (z-b) 0 ≤ z := max_le (by linarith) hzpos.le
    have hsquare : (max (z-b) 0)^2 ≤ z*V := by
      have h1 := mul_le_mul hmb hmb hmax hzpos.le
      have h2 := mul_le_mul_of_nonneg_left hzV hzpos.le
      nlinarith only [h1, h2]
    have hfrac : (max (z-b) 0)^2/(12*V) ≤ z/12 :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hsquare])
    linarith

theorem cubic_normalized_lower {θ u b e z τ v V K1 : ℝ}
    (hθ0 : 0 < θ) (hu0 : 0 ≤ u) (hu1 : u < 1/3) (hb0 : 0 ≤ b)
    (hb1 : b ≤ u+(7-5*θ)/32) (he : e < (1-3*u)/20)
    (hsum : τ+z = 1+u-e) (hV : 0 < V) (hzV : z ≤ V) (hz : z < 4/3)
    (hK : 3*max θ (1/4)/4 < K1/V)
    (hcubic : (K1/(3*V))*(τ+z-2*b)^3/(1+(max (z-b) 0)^2/(12*V)) ≤ v) :
    9*max θ (1/4)/40*(19/20+23*u/20-2*b)^3 < v := by
  let σ := max θ (1/4)
  let D := 19/20+23*u/20-2*b
  let den := 1+(max (z-b) 0)^2/(12*V)
  have hσ : 0 < σ := (by norm_num : (0:ℝ) < 1/4).trans_le (le_max_right _ _)
  have hD : 0 < D := by dsimp [D]; linarith
  have hDgap : D < τ+z-2*b := by dsimp [D]; linarith
  have hden0 : 0 < den := by dsimp [den]; positivity
  have hden1 : den < 10/9 := cubic_denominator_bound hV hzV hb0 hz
  have hK3 : σ/4 < K1/(3*V) := by
    have hid : K1/(3*V) = (K1/V)/3 := by ring
    rw [hid]
    change 3*σ/4 < K1/V at hK
    linarith
  have hcube : D^3 < (τ+z-2*b)^3 := pow_lt_pow_left₀ hDgap hD.le (by norm_num)
  have hnum : σ/4*D^3 < (K1/(3*V))*(τ+z-2*b)^3 :=
    mul_lt_mul hK3 hcube.le (pow_pos hD _) (by linarith)
  have hratio : 9*σ/40*D^3 < (K1/(3*V))*(τ+z-2*b)^3/den := by
    apply (lt_div_iff₀ hden0).mpr
    have hcoef := mul_lt_mul_of_pos_left hden1 (by positivity : 0 < 9*σ/40*D^3)
    nlinarith only [hcoef, hnum]
  exact hratio.trans_le hcubic

/-- The complete numerical exclusion from the normalized identities supplied
by the actual upper/lower mixture. No numerical sampling is involved. -/
theorem complete_normalized_exclusion
    {k a c θ u α d e b q v V z τ g γ ℓ Θ dL K0 K1 : ℝ}
    (hk : 6 ≤ k) (ha : 12/13 < a) (hc0 : 11/24 < c) (hc1 : c ≤ 1/2)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : 0 < u)
    (hα0 : 0 ≤ α) (hα1 : α ≤ (1-θ)/6)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (he0 : 0 ≤ e) (he1 : e < (1-3*u-4*α)/20)
    (hb0 : u ≤ b) (hb1 : b ≤ u+1/16+15*α/16) (hq : 5/6 < q)
    (hv0 : 0 ≤ v) (hV : 0 < V)
    (hcov : v+(63/80)*q*a*(1-θ)*b < (1+(1-c)*u-c*α-e)*e)
    (hz : z = θ+(1-c)*u-e) (hτ : τ = 1-θ+c*u)
    (hg0 : 0 ≤ g) (hg1 : g < (1-θ)/5) (hγ0 : 0 ≤ γ) (hγg : γ ≤ g)
    (hℓ : 0 < ℓ) (hθeq : a*θ = ℓ+d*g) (huℓ : a*(c-3/17)*u < ℓ)
    (hratio : q/d = 1-g/k) (hΘ0 : 0 ≤ Θ) (hΘ1 : Θ ≤ d*g)
    (hvar : q*V = d*z+Θ) (hK0 : ℓ+5*g/8 < K0) (hKτ : τ*K0 ≤ K1)
    (hcond : (dL-z)^2 ≤ v*γ/(1-γ)) (hK1 : K1 = (1-γ)*dL)
    (hcubic : (K1/(3*V))*(τ+z-2*b)^3/(1+(max (z-b) 0)^2/(12*V)) ≤ v) : False := by
  have hranges := normalized_support_ranges hθ0 hu hα0 hα1 he0 he1 hb0 hb1
  have hbnonneg : 0 ≤ b := hu.le.trans hb0
  have heSmall : e ≤ (1-3*u)/20 := by linarith
  have hupper := normalized_variance_upper hθ1 hu hranges.1 hα0 he0 heSmall hbnonneg hq ha hc0.le hcov
  have hvsmall : v < 1/20 := by
    have hpos : 0 ≤ (3/5)*(1-θ)*b := by positivity
    linarith [hupper.1, hupper.2]
  have hk0 : 0 < k := by linarith
  have hqd : q ≤ d := by
    apply (div_le_one hd0).mp
    rw [hratio]
    have hgp : 0 ≤ g/k := div_nonneg hg0 hk0.le
    linarith
  have hVbounds := lower_variance_bounds (by linarith : 0 < q) hd0 hqd hV hΘ0 hΘ1 hvar hratio
  have hvarUpper : q*V ≤ d*(z+g) := by nlinarith only [hvar, hΘ1]
  have hK0V := lower_variance_four_tail_mass ha hc0 hc1 hθ0 hu hd0 hd1 hq hV hg0 hℓ
    hθeq huℓ (by rw [hz]; linarith) hvarUpper hK0
  have hzθ : θ-1/20 < z := by
    have hprod := mul_nonneg (by linarith : 0 ≤ 1-c) hu.le
    rw [hz]
    linarith [hranges.2.1]
  have hzbound : z < 4/3 := by
    have hcu := mul_lt_mul_of_pos_right (by linarith : 1-c < 13/24) hu
    rw [hz]
    linarith [hranges.1]
  have hK := uniform_first_moment hk hθ0 hθ1 hu (by linarith : 0 < c) hτ hzθ hv0 hvsmall hV
    hg0 hg1 hγ0 hγg hcond hK1 hVbounds.2 hK0V hKτ
  have hsum : τ+z = 1+u-e := by rw [hτ,hz]; ring
  have hlower := cubic_normalized_lower hθ0 hu.le hranges.1 hbnonneg hranges.2.2.2
    (by linarith : e < (1-3*u)/20) hsum hV hVbounds.1 hzbound hK hcubic
  exact normalized_variance_contradiction hθ0 hθ1 hu.le hranges.1 hbnonneg hranges.2.2.2 hupper.1 hlower

end SharpTailMatching.ExclusionAlgebra
