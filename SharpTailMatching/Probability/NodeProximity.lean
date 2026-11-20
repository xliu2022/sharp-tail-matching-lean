module

public import SharpTailMatching.Probability.WeightedNodes

/-! # Deficit and support comparison at the actual weighted nodes -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability.ComparisonGeometry

def weightedNodeZ (k : ℕ) (a p : ℝ) (t : ℕ) : ℝ :=
  (a^k-shortTailNodeSum k a t)/p

def nodeR (k : ℕ) (a p : ℝ) (t : ℕ) : ℝ :=
  ((1-a)+scaledExcessNodeSum k a t/(k : ℝ))/p

def nodeM (k : ℕ) (a p : ℝ) (t : ℕ) : ℝ :=
  a/(k : ℝ)+(a/(k : ℝ))*p/(a^k-shortTailNodeSum k a t)

theorem weightedNodeZ_relation (k t : ℕ) (a p : ℝ) (hp : p ≠ 0) (hpdef : p = 1-a^k) :
    1-shortTailNodeSum k a t = p*(1+weightedNodeZ k a p t) := by
  unfold weightedNodeZ
  field_simp
  nlinarith only [hpdef]

theorem node_proximity_of_deficitTest (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (a p : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hp : 0 < p) (hpdef : p = 1-a^k)
    (hz : 0 < weightedNodeZ k a p t)
    (hG : 3*a/20 < ScalarCertificates.deficitTest (t : ℝ) a (weightedNodeZ k a p t)) :
    shortTailNodeSum k a t < a^k ∧ a/(k : ℝ)/5 < nodeR k a p t-(19/20)*nodeM k a p t := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hden : a^k-shortTailNodeSum k a t = p*weightedNodeZ k a p t := by
    unfold weightedNodeZ
    field_simp
  have hF := weightedNodeZ_relation k t a p hp.ne' hpdef
  have hmoment := weighted_node_moment_identity k hk a t ht
  have hR : nodeR k a p t =
      (((t : ℝ)-a)*(1-shortTailNodeSum k a t)+binomialExcessRemainder k a t)/((k : ℝ)*p) := by
    rw [← hmoment]
    unfold nodeR
    field_simp
  have hM : nodeM k a p t = a/(k : ℝ)*(1+1/weightedNodeZ k a p t) := by
    unfold nodeM
    rw [hden]
    field_simp
  constructor
  · have hpos := mul_pos hp hz
    linarith
  · rw [hR,hM]
    exact CriticalEstimates.node_moment_gap hkpos hp (binomialExcessRemainder_nonneg k t a ha ha1)
      hz hF hG

theorem critical_weightedNodeZ_eq (k t : ℕ) (hk : 2 ≤ k) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    weightedNodeZ k ((k : ℝ)/((k : ℝ)+c)) ((1-1/((k : ℝ)+c))^k) t =
      CriticalEstimates.nodeZ (t-1) k c := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : 0 < (k : ℝ)+c := by linarith
  have hbase : 0 < 1-1/((k : ℝ)+c) := sub_pos.mpr ((div_lt_one hden).mpr (by linarith))
  have hp : (1-1/((k : ℝ)+c))^k ≠ 0 := ne_of_gt (pow_pos hbase k)
  have hF := shortTailNodeSum_eq_nodeFailure k t (by omega) ht c hc
  have hpdef := critical_failure_identity k (by omega) c hc hcross
  unfold weightedNodeZ CriticalEstimates.nodeZ
  rw [← hF]
  let a := (k : ℝ)/((k : ℝ)+c)
  let p := (1-1/((k : ℝ)+c))^k
  change (a^k-shortTailNodeSum k a t)/p = (1-shortTailNodeSum k a t)/p-1
  calc
    _ = ((1-shortTailNodeSum k a t)-p)/p := by
      congr 1
      change p = 1-a^k at hpdef
      linarith only [hpdef]
    _ = (1-shortTailNodeSum k a t)/p-p/p := sub_div _ _ _
    _ = _ := by rw [div_self hp]

theorem critical_weighted_node_proximity (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    shortTailNodeSum k a t < a^k ∧ a/(k : ℝ)/5 < nodeR k a p t-(19/20)*nodeM k a p t := by
  let a := (k : ℝ)/((k : ℝ)+c)
  let p := (1-1/((k : ℝ)+c))^k
  have hb := CriticalEstimates.critical_elementary_bounds hk hc hcross
  simp only [mul_one_div] at hb
  have ha : 0 < a := by dsimp [a]; linarith [hb.1]
  have ha1 : a < 1 := hb.2.1
  have hp : 0 < p := by dsimp [p]; linarith [hb.2.2.2.1]
  have hpdef : p = 1-a^k := critical_failure_identity k (by omega) c hc hcross
  have hF := weightedNodeZ_relation k t a p hp.ne' hpdef
  have hZ : 0 < weightedNodeZ k a p t ∧
      3*a/20 < ScalarCertificates.deficitTest (t : ℝ) a (weightedNodeZ k a p t) := by
    by_cases ht4 : t = 4
    · subst t
      have hgap := fourth_weighted_node_gap k (by omega) c hc hcross
      change 4*p < (4-a)*(1-shortTailNodeSum k a 4) at hgap
      rw [hF] at hgap
      have hnorm : 4 < (4-a)*(1+weightedNodeZ k a p 4) := by
        apply (mul_lt_mul_iff_right₀ hp).mp
        nlinarith only [hgap]
      have hza : a/(4-a) < weightedNodeZ k a p 4 :=
        (div_lt_iff₀ (by linarith : 0 < 4-a)).mpr (by nlinarith)
      refine ⟨(div_pos ha (by linarith)).trans hza,?_⟩
      simpa only [Nat.cast_ofNat] using CriticalEstimates.fourth_deficitTest_gap ha ha1 hza
    · have ht5 : 5 ≤ t := by omega
      have hzEq := critical_weightedNodeZ_eq k t (by omega) (by omega) c hc hcross
      change weightedNodeZ k a p t = _ at hzEq
      rw [hzEq]
      have htR : (5 : ℝ) ≤ t := by exact_mod_cast ht5
      have htcast : ((t-1 : ℕ) : ℝ)+1 = (t : ℝ) := by rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
      have hcomp := CriticalEstimates.nodeZ_above_comparison (by omega : 4 ≤ t-1)
        (by omega : t-1+2 ≤ k) hc hcross
      have hgap := CriticalEstimates.node_deficitTest_gap (by omega : 4 ≤ t-1)
        (by omega : t-1+2 ≤ k) hc hcross
      rw [htcast] at hcomp hgap
      exact ⟨(ScalarCertificates.comparisonValue_pos ha (by linarith)).trans hcomp,hgap⟩
  exact node_proximity_of_deficitTest k t (by omega) (by omega) a p ha.le ha1.le hp hpdef hZ.1 hZ.2

theorem critical_terminal_node (k : ℕ) (hk : 6 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    shortTailNodeSum k a k < a^k ∧ nodeR k a p k = 1 ∧ nodeM k a p k = 1 := by
  let a := (k : ℝ)/((k : ℝ)+c)
  let p := (1-1/((k : ℝ)+c))^k
  let x := a/(k : ℝ)
  let F := 1-shortTailNodeSum k a k
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hb := CriticalEstimates.critical_elementary_bounds hk hc hcross
  simp only [mul_one_div] at hb
  have ha : 0 < a := by dsimp [a]; linarith [hb.1]
  have ha1 : a < 1 := hb.2.1
  have hp : 0 < p := by dsimp [p]; linarith [hb.2.2.2.1]
  have hx : 0 < x := div_pos ha hkpos
  have hx1 : x < 1 := (div_lt_one hkpos).mpr (by
    have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  have hF : F = (1-x)^(k-1) := shortTailNodeSum_last k (by omega) a
  have hFpos : 0 < F := by rw [hF]; exact pow_pos (sub_pos.mpr hx1) _
  have hbase : 1-1/((k : ℝ)+c) = 1-x := by dsimp [x,a]; field_simp
  have hpF : p = (1-x)*F := by
    rw [hF]
    dsimp [p]
    rw [hbase,← pow_succ',Nat.sub_add_cancel (show 1 ≤ k by omega)]
  have hpdef : p = 1-a^k := critical_failure_identity k (by omega) c hc hcross
  have hden : a^k-shortTailNodeSum k a k = x*F := by
    dsimp [F] at hpF
    nlinarith only [hpF,hpdef]
  have hmoment := weighted_node_moment_identity k (by omega) a k (by omega)
  rw [binomialExcessRemainder_last k (by omega),add_zero] at hmoment
  have hraw : ((k : ℝ)-a)*(1-shortTailNodeSum k a k) = (k : ℝ)*p := by
    rw [hpF]
    dsimp [F,x]
    field_simp
  rw [hraw] at hmoment
  have hRnum : (1-a)+scaledExcessNodeSum k a k/(k : ℝ) = p := by
    apply (mul_right_cancel₀ hkne)
    have hid : ((1-a)+scaledExcessNodeSum k a k/(k : ℝ))*(k : ℝ) =
        (k : ℝ)*(1-a)+scaledExcessNodeSum k a k := by field_simp
    rw [hid]
    simpa only [mul_comm p] using hmoment
  refine ⟨by have hpos := mul_pos hx hFpos; linarith,?_,?_⟩
  · unfold nodeR
    rw [hRnum,div_self hp.ne']
  · change x+x*p/(a^k-shortTailNodeSum k a k) = 1
    rw [hden,hpF]
    field_simp
    ring

theorem critical_all_node_proximity (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t ≤ k)
    (c : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    shortTailNodeSum k a t < a^k ∧ a/(k : ℝ)/5 < nodeR k a p t-(19/20)*nodeM k a p t := by
  by_cases htkEq : t = k
  · subst t
    obtain ⟨hV,hR,hM⟩ := critical_terminal_node k hk c hc hcross
    dsimp at hV hR hM ⊢
    refine ⟨hV,?_⟩
    rw [hR,hM]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have ha1 : (k : ℝ)/((k : ℝ)+c) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith)
    have hx : ((k : ℝ)/((k : ℝ)+c))/(k : ℝ) < 1/4 := by
      apply (div_lt_iff₀ hkpos).mpr
      have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    linarith
  · exact critical_weighted_node_proximity k t hk ht (by omega) c hc hcross

def shortTailStarSum (k : ℕ) (a : ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  (1-θ)*shortTailNodeSum k a t+θ*shortTailNodeSum k a (t+1)

def scaledExcessStarSum (k : ℕ) (a : ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  (1-θ)*scaledExcessNodeSum k a t+θ*scaledExcessNodeSum k a (t+1)

def comparisonR (k : ℕ) (a p : ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  ((1-a)+scaledExcessStarSum k a t θ/(k : ℝ))/p

def comparisonM (k : ℕ) (a p : ℝ) (t : ℕ) (θ : ℝ) : ℝ :=
  a/(k : ℝ)+(a/(k : ℝ))*p/(a^k-shortTailStarSum k a t θ)

theorem reciprocal_affine_bound {u v θ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    1/((1-θ)*u+θ*v) ≤ (1-θ)/u+θ/v := by
  have hw : 0 ≤ 1-θ := sub_nonneg.mpr hθ1
  have hden : 0 < (1-θ)*u+θ*v := by
    by_cases hθeq : θ = 1
    · simpa only [hθeq,sub_self,zero_mul,one_mul,zero_add] using hv
    · have hθlt : θ < 1 := lt_of_le_of_ne hθ1 hθeq
      exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hu) (mul_nonneg hθ hv.le)
  apply (div_le_iff₀ hden).mpr
  have hid : (((1-θ)/u+θ/v)*((1-θ)*u+θ*v)-1)*(u*v) =
      θ*(1-θ)*(u-v)^2 := by
    field_simp
    ring
  have hmul : 0*(u*v) ≤ (((1-θ)/u+θ/v)*((1-θ)*u+θ*v)-1)*(u*v) := by
    rw [zero_mul,hid]
    positivity
  have h := (mul_le_mul_iff_left₀ (mul_pos hu hv)).mp hmul
  linarith

theorem comparisonR_affine (k t : ℕ) (a p θ : ℝ) :
    comparisonR k a p t θ = (1-θ)*nodeR k a p t+θ*nodeR k a p (t+1) := by
  unfold comparisonR scaledExcessStarSum nodeR
  ring

theorem comparisonM_le_affine (k t : ℕ) (a p θ : ℝ)
    (ha : 0 ≤ a) (hp : 0 ≤ p) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hV0 : shortTailNodeSum k a t < a^k)
    (hV1 : shortTailNodeSum k a (t+1) < a^k) :
    comparisonM k a p t θ ≤ (1-θ)*nodeM k a p t+θ*nodeM k a p (t+1) := by
  have h := reciprocal_affine_bound (sub_pos.mpr hV0) (sub_pos.mpr hV1) hθ hθ1
  have hmul := mul_le_mul_of_nonneg_left h (mul_nonneg (div_nonneg ha (Nat.cast_nonneg k)) hp)
  have hden : (1-θ)*(a^k-shortTailNodeSum k a t)+θ*(a^k-shortTailNodeSum k a (t+1)) =
      a^k-shortTailStarSum k a t θ := by unfold shortTailStarSum; ring
  rw [hden] at hmul
  calc
    _ = a/(k : ℝ)+(a/(k : ℝ))*p*(1/(a^k-shortTailStarSum k a t θ)) := by
      unfold comparisonM
      ring
    _ ≤ a/(k : ℝ)+(a/(k : ℝ))*p*((1-θ)/(a^k-shortTailNodeSum k a t)+
        θ/(a^k-shortTailNodeSum k a (t+1))) := add_le_add le_rfl hmul
    _ = _ := by unfold nodeM; ring

theorem critical_interpolated_proximity (k t : ℕ) (hk : 6 ≤ k) (ht : 4 ≤ t) (htk : t < k)
    (c θ : ℝ) (hc : 0 ≤ c) (hcross : CriticalEstimates.criticalDifference k c = 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    shortTailStarSum k a t θ < a^k ∧
      a/(k : ℝ)/5 < comparisonR k a p t θ-(19/20)*comparisonM k a p t θ := by
  let a := (k : ℝ)/((k : ℝ)+c)
  let p := (1-1/((k : ℝ)+c))^k
  obtain ⟨hV0,hgap0⟩ := critical_all_node_proximity k t hk ht htk.le c hc hcross
  obtain ⟨hV1,hgap1⟩ := critical_all_node_proximity k (t+1) hk (by omega) (by omega) c hc hcross
  change shortTailNodeSum k a t < a^k at hV0
  change shortTailNodeSum k a (t+1) < a^k at hV1
  change a/(k : ℝ)/5 < nodeR k a p t-(19/20)*nodeM k a p t at hgap0
  change a/(k : ℝ)/5 < nodeR k a p (t+1)-(19/20)*nodeM k a p (t+1) at hgap1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hp : 0 ≤ p := by
    dsimp [p]
    have hkR : (6 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : 0 < (k : ℝ)+c := by linarith
    exact pow_nonneg (sub_nonneg.mpr ((div_le_one hden).mpr (by linarith))) _
  have hM := comparisonM_le_affine k t a p θ ha hp hθ hθ1 hV0 hV1
  have hconv {u v z : ℝ} (hu : z < u) (hv : z < v) : z < (1-θ)*u+θ*v := by
    by_cases heq : θ = 1
    · simpa only [heq,sub_self,zero_mul,one_mul,zero_add] using hv
    · have hθlt : θ < 1 := lt_of_le_of_ne hθ1 heq
      have h0 := mul_lt_mul_of_pos_left hu (by linarith : 0 < 1-θ)
      have h1 := mul_le_mul_of_nonneg_left hv.le hθ
      nlinarith only [h0,h1]
  constructor
  · have h := hconv (neg_lt_neg hV0) (neg_lt_neg hV1)
    dsimp [shortTailStarSum]
    linarith
  · have h := hconv hgap0 hgap1
    rw [comparisonR_affine]
    linarith

end SharpTailMatching.Probability.ComparisonGeometry
