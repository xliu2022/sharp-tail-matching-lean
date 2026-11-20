module

public import SharpTailMatching.Probability.EnvelopeAlgebra
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Geometry of the comparison nodes

The logarithm bounds used here replace the manuscript's power-series
estimates. They imply positivity and decreasing slopes along the node curve.
-/

@[expose] public section

noncomputable section

open Set Real

namespace SharpTailMatching.Probability.ComparisonGeometry

def nodePower (ℓ t : ℝ) : ℝ := Real.exp ((t-ℓ)*Real.log (1-1/t))
def nodeExcess (ℓ t : ℝ) : ℝ := -ℓ+t*nodePower ℓ t
def nodeTail (ℓ t : ℝ) : ℝ := 1-nodePower ℓ t
def logarithmicRate (ℓ t : ℝ) : ℝ := -Real.log (1-1/t)-(t-ℓ)/(t*(t-1))
def curveSlope (ℓ t : ℝ) : ℝ := logarithmicRate ℓ t/(1-t*logarithmicRate ℓ t)

theorem nodePower_pos (ℓ t : ℝ) : 0 < nodePower ℓ t := Real.exp_pos _

theorem nodePower_eq_rpow (ℓ t : ℝ) (ht : 1 < t) :
    nodePower ℓ t = (1-1/t) ^ (t-ℓ) := by
  have hq : 0 < 1-1/t := sub_pos.mpr ((div_lt_one (by linarith : 0 < t)).mpr ht)
  rw [Real.rpow_def_of_pos hq]
  unfold nodePower
  rw [mul_comm]

theorem hasDerivAt_nodePower (ℓ t : ℝ) (ht : 1 < t) :
    HasDerivAt (nodePower ℓ) (-nodePower ℓ t*logarithmicRate ℓ t) t := by
  have ht0 : t ≠ 0 := by linarith
  have htm : t-1 ≠ 0 := by linarith
  have hq : 1-1/t ≠ 0 := by
    have : 1/t < 1 := (div_lt_one (by linarith : 0 < t)).mpr ht
    linarith
  have hlog := ((hasDerivAt_const t 1).sub ((hasDerivAt_const t 1).div (hasDerivAt_id t) ht0)).log hq
  convert (((hasDerivAt_id t).sub_const ℓ).mul hlog).exp using 1
  · rfl
  · simp only [Pi.mul_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    unfold nodePower logarithmicRate
    field_simp
    ring

theorem hasDerivAt_nodeExcess (ℓ t : ℝ) (ht : 1 < t) :
    HasDerivAt (nodeExcess ℓ) (nodePower ℓ t*(1-t*logarithmicRate ℓ t)) t := by
  convert ((hasDerivAt_const t (-ℓ)).add ((hasDerivAt_id t).mul (hasDerivAt_nodePower ℓ t ht))) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_nodeTail (ℓ t : ℝ) (ht : 1 < t) :
    HasDerivAt (nodeTail ℓ) (nodePower ℓ t*logarithmicRate ℓ t) t := by
  convert (hasDerivAt_const t 1).sub (hasDerivAt_nodePower ℓ t ht) using 1
  · rfl
  · ring

theorem hasDerivAt_logarithmicRate (ℓ t : ℝ) (ht : 1 < t) :
    HasDerivAt (logarithmicRate ℓ) ((ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2)) t := by
  have ht0 : t ≠ 0 := by linarith
  have htm : t-1 ≠ 0 := by linarith
  have hq : 1-1/t ≠ 0 := by
    have : 1/t < 1 := (div_lt_one (by linarith : 0 < t)).mpr ht
    linarith
  have hlog := ((hasDerivAt_const t 1).sub ((hasDerivAt_const t 1).div (hasDerivAt_id t) ht0)).log hq
  have hden := (hasDerivAt_id t).mul ((hasDerivAt_id t).sub_const 1)
  convert hlog.neg.sub (((hasDerivAt_id t).sub_const ℓ).div hden (mul_ne_zero ht0 htm)) using 1
  · rfl
  · simp only [Pi.mul_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    field_simp
    ring

theorem logarithmicRate_bounds (ℓ t : ℝ) (hℓ : 1 ≤ ℓ) (ht : ℓ+1 ≤ t) :
    0 < logarithmicRate ℓ t ∧ logarithmicRate ℓ t < ℓ/(t*(t-1)) ∧
      logarithmicRate ℓ t < 1/t := by
  have ht1 : 1 < t := by linarith
  have ht0 : 0 < t := by linarith
  have htm : 0 < t-1 := by linarith
  have hq0 : 0 < 1-1/t := sub_pos.mpr ((div_lt_one ht0).mpr ht1)
  have hq1 : 1-1/t < 1 := by linarith [one_div_pos.mpr ht0]
  have hlogUpper := Real.log_lt_sub_one_of_pos hq0 (ne_of_lt hq1)
  have hlogLower := Real.log_lt_sub_one_of_pos (inv_pos.mpr hq0)
    (show (1-1/t)⁻¹ ≠ 1 by
      intro h
      have hq := inv_inj.mp (by simpa using h : (1-1/t)⁻¹ = (1 : ℝ)⁻¹)
      exact hq1.ne hq)
  rw [Real.log_inv] at hlogLower
  have hrat : (1-1/t)⁻¹-1 = 1/(t-1) := by field_simp; ring
  rw [hrat] at hlogLower
  have hlow : 1/t-(t-ℓ)/(t*(t-1)) = (ℓ-1)/(t*(t-1)) := by field_simp; ring
  have hupp : 1/(t-1)-(t-ℓ)/(t*(t-1)) = ℓ/(t*(t-1)) := by field_simp; ring
  have hnonneg : 0 ≤ (ℓ-1)/(t*(t-1)) := by positivity
  have hupper : ℓ/(t*(t-1)) ≤ 1/t := by
    apply (div_le_div_iff₀ (mul_pos ht0 htm) ht0).mpr
    nlinarith
  have hg0 : 0 < logarithmicRate ℓ t := by unfold logarithmicRate; linarith
  have hgup : logarithmicRate ℓ t < ℓ/(t*(t-1)) := by unfold logarithmicRate; linarith
  exact ⟨hg0,hgup,hgup.trans_le hupper⟩

theorem logarithmicRate_deriv_add_sq_neg (ℓ t : ℝ) (hℓ : 1 ≤ ℓ) (ht : ℓ+1 ≤ t) :
    (ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2) + (logarithmicRate ℓ t)^2 < 0 := by
  have ht0 : 0 < t := by linarith
  have htm : 0 < t-1 := by linarith
  have hg := logarithmicRate_bounds ℓ t hℓ ht
  have hsquare : (logarithmicRate ℓ t)^2 < (ℓ/(t*(t-1)))^2 := by
    nlinarith [hg.1,hg.2.1]
  have hid : (ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2) + (ℓ/(t*(t-1)))^2 =
      (ℓ^2+ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2) := by field_simp; ring
  have hnum : ℓ^2+ℓ-(2*ℓ-1)*t ≤ 0 := by
    nlinarith [mul_nonneg (show 0 ≤ 2*ℓ-1 by linarith) (sub_nonneg.mpr ht),
      mul_nonneg (show 0 ≤ ℓ-1 by linarith) (show 0 ≤ ℓ+1 by linarith)]
  have hfrac : (ℓ^2+ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum (by positivity)
  linarith

theorem curveSlope_den_pos (ℓ t : ℝ) (hℓ : 1 ≤ ℓ) (ht : ℓ+1 ≤ t) :
    0 < 1-t*logarithmicRate ℓ t := by
  have ht0 : 0 < t := by linarith
  have h := (lt_div_iff₀ ht0).mp (logarithmicRate_bounds ℓ t hℓ ht).2.2
  nlinarith

theorem hasDerivAt_curveSlope (ℓ t : ℝ) (hℓ : 1 ≤ ℓ) (ht : ℓ+1 ≤ t) :
    HasDerivAt (curveSlope ℓ)
      (((ℓ-(2*ℓ-1)*t)/(t^2*(t-1)^2)+(logarithmicRate ℓ t)^2)/(1-t*logarithmicRate ℓ t)^2) t := by
  have ht1 : 1 < t := by linarith
  have hg := hasDerivAt_logarithmicRate ℓ t ht1
  have hden := (hasDerivAt_const t 1).sub ((hasDerivAt_id t).mul hg)
  convert hg.div hden (ne_of_gt (curveSlope_den_pos ℓ t hℓ ht)) using 1
  · rfl
  · simp only [Pi.mul_apply,Pi.sub_apply,id_eq]
    ring

theorem nodeExcess_strictMono (ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    StrictMonoOn (nodeExcess ℓ) (Set.Ici (ℓ+1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    exact (hasDerivAt_nodeExcess ℓ t (by change ℓ+1 ≤ t at ht; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : ℓ+1 ≤ t := interior_subset ht
    rw [(hasDerivAt_nodeExcess ℓ t (by linarith)).deriv]
    exact mul_pos (nodePower_pos ℓ t) (curveSlope_den_pos ℓ t hℓ ht')

theorem nodeTail_strictMono (ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    StrictMonoOn (nodeTail ℓ) (Set.Ici (ℓ+1)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · intro t ht
    exact (hasDerivAt_nodeTail ℓ t (by change ℓ+1 ≤ t at ht; linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : ℓ+1 ≤ t := interior_subset ht
    rw [(hasDerivAt_nodeTail ℓ t (by linarith)).deriv]
    exact mul_pos (nodePower_pos ℓ t) (logarithmicRate_bounds ℓ t hℓ ht').1

theorem curveSlope_strictAnti (ℓ : ℝ) (hℓ : 1 ≤ ℓ) :
    StrictAntiOn (curveSlope ℓ) (Set.Ici (ℓ+1)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro t ht
    exact (hasDerivAt_curveSlope ℓ t hℓ ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : ℓ+1 ≤ t := interior_subset ht
    rw [(hasDerivAt_curveSlope ℓ t hℓ ht').deriv]
    exact div_neg_of_neg_of_pos (logarithmicRate_deriv_add_sq_neg ℓ t hℓ ht')
      (sq_pos_of_pos (curveSlope_den_pos ℓ t hℓ ht'))

def chordSlope (ℓ a b : ℝ) : ℝ :=
  (nodeTail ℓ b-nodeTail ℓ a)/(nodeExcess ℓ b-nodeExcess ℓ a)

theorem chordSlope_pos (ℓ a b : ℝ) (hℓ : 1 ≤ ℓ) (ha : ℓ+1 ≤ a) (hab : a < b) :
    0 < chordSlope ℓ a b := by
  have hb : ℓ+1 ≤ b := ha.trans hab.le
  exact div_pos (sub_pos.mpr (nodeTail_strictMono ℓ hℓ ha hb hab))
    (sub_pos.mpr (nodeExcess_strictMono ℓ hℓ ha hb hab))

theorem chordSlope_eq_curveSlope (ℓ a b : ℝ) (hℓ : 1 ≤ ℓ)
    (ha : ℓ+1 ≤ a) (hab : a < b) :
    ∃ c ∈ Ioo a b, chordSlope ℓ a b = curveSlope ℓ c := by
  have hF : ContinuousOn (nodeTail ℓ) (Icc a b) := by
    intro x hx
    exact (hasDerivAt_nodeTail ℓ x (by linarith [hx.1])).continuousAt.continuousWithinAt
  have hE : ContinuousOn (nodeExcess ℓ) (Icc a b) := by
    intro x hx
    exact (hasDerivAt_nodeExcess ℓ x (by linarith [hx.1])).continuousAt.continuousWithinAt
  obtain ⟨c,hc,heq⟩ := exists_ratio_hasDerivAt_eq_ratio_slope (nodeTail ℓ)
    (fun x => nodePower ℓ x*logarithmicRate ℓ x) hab hF
    (fun x hx => hasDerivAt_nodeTail ℓ x (by linarith [hx.1]))
    (nodeExcess ℓ) (fun x => nodePower ℓ x*(1-x*logarithmicRate ℓ x)) hE
    (fun x hx => hasDerivAt_nodeExcess ℓ x (by linarith [hx.1]))
  refine ⟨c,hc,?_⟩
  have hden : 0 < nodeExcess ℓ b-nodeExcess ℓ a :=
    sub_pos.mpr (nodeExcess_strictMono ℓ hℓ ha (ha.trans hab.le) hab)
  have hcden : 0 < 1-c*logarithmicRate ℓ c :=
    curveSlope_den_pos ℓ c hℓ (ha.trans hc.1.le)
  unfold chordSlope curveSlope
  apply (div_eq_div_iff (ne_of_gt hden) (ne_of_gt hcden)).mpr
  apply (mul_right_cancel₀ (ne_of_gt (nodePower_pos ℓ c)))
  nlinarith [heq]

theorem chordSlope_strict_decreasing (ℓ a b c : ℝ) (hℓ : 1 ≤ ℓ)
    (ha : ℓ+1 ≤ a) (hab : a < b) (hbc : b < c) :
    chordSlope ℓ b c < chordSlope ℓ a b := by
  obtain ⟨x,hx,hxs⟩ := chordSlope_eq_curveSlope ℓ a b hℓ ha hab
  obtain ⟨y,hy,hys⟩ := chordSlope_eq_curveSlope ℓ b c hℓ (ha.trans hab.le) hbc
  rw [hxs,hys]
  exact curveSlope_strictAnti ℓ hℓ (ha.trans hx.1.le)
    (ha.trans (hab.le.trans hy.1.le)) (hx.2.trans hy.1)

def chordLine (ℓ a b x : ℝ) : ℝ :=
  nodeTail ℓ a + chordSlope ℓ a b*(x-nodeExcess ℓ a)

theorem chordLine_left (ℓ a b : ℝ) :
    chordLine ℓ a b (nodeExcess ℓ a) = nodeTail ℓ a := by
  simp [chordLine]

theorem chordLine_right (ℓ a b : ℝ) (hℓ : 1 ≤ ℓ) (ha : ℓ+1 ≤ a) (hab : a < b) :
    chordLine ℓ a b (nodeExcess ℓ b) = nodeTail ℓ b := by
  have hden : nodeExcess ℓ b-nodeExcess ℓ a ≠ 0 :=
    ne_of_gt (sub_pos.mpr (nodeExcess_strictMono ℓ hℓ ha (ha.trans hab.le) hab))
  unfold chordLine chordSlope
  rw [div_mul_cancel₀ _ hden]
  ring

/-- The line through two nodes lies above every node outside their parameter
interval. For adjacent integer parameters these are all the other nodes. -/
theorem node_below_chordLine (ℓ a b c : ℝ) (hℓ : 1 ≤ ℓ)
    (ha : ℓ+1 ≤ a) (hab : a < b) (hc : ℓ+1 ≤ c) (hout : c ≤ a ∨ b ≤ c) :
    nodeTail ℓ c ≤ chordLine ℓ a b (nodeExcess ℓ c) := by
  rcases hout with hca | hbc
  · rcases eq_or_lt_of_le hca with rfl | hca
    · simp [chordLine]
    · have hs := (chordSlope_strict_decreasing ℓ c a b hℓ hc hca hab).le
      have hden : 0 < nodeExcess ℓ a-nodeExcess ℓ c :=
        sub_pos.mpr (nodeExcess_strictMono ℓ hℓ hc ha hca)
      unfold chordSlope at hs
      have hmul := (le_div_iff₀ hden).mp hs
      change nodeTail ℓ c ≤ nodeTail ℓ a +
        ((nodeTail ℓ b-nodeTail ℓ a)/(nodeExcess ℓ b-nodeExcess ℓ a))*
          (nodeExcess ℓ c-nodeExcess ℓ a)
      nlinarith
  · rcases eq_or_lt_of_le hbc with rfl | hbc
    · exact (chordLine_right ℓ a b hℓ ha hab).ge
    · have hs := (chordSlope_strict_decreasing ℓ a b c hℓ ha hab hbc).le
      have hden : 0 < nodeExcess ℓ c-nodeExcess ℓ b :=
        sub_pos.mpr (nodeExcess_strictMono ℓ hℓ (ha.trans hab.le) hc hbc)
      change (nodeTail ℓ c-nodeTail ℓ b)/(nodeExcess ℓ c-nodeExcess ℓ b) ≤
        chordSlope ℓ a b at hs
      have hmul := (div_le_iff₀ hden).mp hs
      have hend := chordLine_right ℓ a b hℓ ha hab
      unfold chordLine at hend ⊢
      nlinarith

theorem zero_logarithmicRate_neg (t : ℝ) (ht : 1 < t) :
    logarithmicRate 0 t < 0 := by
  have ht0 : 0 < t := by linarith
  have htne : t ≠ 0 := ne_of_gt ht0
  have htm : t-1 ≠ 0 := by linarith
  have hq0 : 0 < 1-1/t := sub_pos.mpr ((div_lt_one ht0).mpr ht)
  have hq1 : 1-1/t < 1 := by linarith [one_div_pos.mpr ht0]
  have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr hq0)
    (show (1-1/t)⁻¹ ≠ 1 by
      intro h
      have hq := inv_inj.mp (by simpa using h : (1-1/t)⁻¹ = (1 : ℝ)⁻¹)
      exact hq1.ne hq)
  rw [Real.log_inv] at hlog
  have hid : (1-1/t)⁻¹-1 = (t-0)/(t*(t-1)) := by field_simp; ring
  rw [hid] at hlog
  unfold logarithmicRate
  linarith

theorem zero_nodeExcess_strictMono :
    StrictMonoOn (nodeExcess 0) (Set.Ioi 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro t ht
    exact (hasDerivAt_nodeExcess 0 t ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 1 < t := interior_subset ht
    rw [(hasDerivAt_nodeExcess 0 t ht').deriv]
    have hg := zero_logarithmicRate_neg t ht'
    exact mul_pos (nodePower_pos 0 t) (by nlinarith : 0 < 1-t*logarithmicRate 0 t)

end SharpTailMatching.Probability.ComparisonGeometry
