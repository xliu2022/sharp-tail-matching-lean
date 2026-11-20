module

public import SharpTailMatching.Probability.NodeWeights
public import SharpTailMatching.Probability.BinomialAverage
public import SharpTailMatching.NodeComparison
public import SharpTailMatching.FourthNodeTail

/-! # Exact tail and excess identities at weighted comparison nodes -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability.ComparisonGeometry

def shortTailNodeSum (k : ℕ) (a : ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k,((k-1).choose j : ℝ)*a^j*(1-a)^(k-1-j)*tailNode k j t

def scaledExcessNodeSum (k : ℕ) (a : ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a^j*(1-a)^(k-j)*excessNode k j t

def binomialExcessRemainder (k : ℕ) (a : ℝ) (t : ℕ) : ℝ :=
  binomialAverage (k-1) a (fun h => max ((h : ℝ)-(t : ℝ)+1) 0)

def nodeDeficitKernel (t h : ℕ) : ℝ :=
  (t : ℝ)*(1-1/(t : ℝ))^(t-h)+max ((h : ℝ)-(t : ℝ)) 0

theorem tailNode_complement (k j t : ℕ) :
    1-tailNode k j t = (1-1/(t : ℝ))^(t-(k-j)) := by
  unfold tailNode
  split_ifs with h
  · rw [Nat.sub_eq_zero_of_le h,pow_zero,sub_zero]
  · unfold nodeTailNat nodePowerNat
    ring

theorem shortTailNodeSum_average (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (t : ℕ) :
    shortTailNodeSum k a t = binomialAverage (k-1) a (fun h => tailNode k (k-1-h) t) := by
  rw [binomialAverage_success,Nat.sub_add_cancel hk]
  unfold shortTailNodeSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k-1 := by have := Finset.mem_range.mp hj; omega
  rw [Nat.sub_sub_self hjk]

theorem shortTailNodeSum_failure (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (t : ℕ) :
    1-shortTailNodeSum k a t =
      binomialAverage (k-1) a (fun h => (1-1/(t : ℝ))^(t-1-h)) := by
  rw [shortTailNodeSum_average k hk]
  have hsub := binomialAverage_sub (k-1) a (fun _ => 1) (fun h => tailNode k (k-1-h) t)
  rw [binomialAverage_const] at hsub
  rw [← hsub]
  apply binomialAverage_congr
  intro h hh
  rw [tailNode_complement]
  have hlev : k-(k-1-h) = h+1 := by omega
  rw [hlev]
  congr 1
  omega

theorem excessNode_kernel (k h t : ℕ) (hh : h ≤ k) :
    excessNode k (k-h) t = nodeDeficitKernel t h-(h : ℝ) := by
  unfold excessNode
  rw [Nat.sub_sub_self hh]
  split_ifs with ht
  · have htR : (t : ℝ) ≤ h := by exact_mod_cast ht
    unfold nodeDeficitKernel
    rw [Nat.sub_eq_zero_of_le ht,pow_zero,mul_one,max_eq_left (by linarith)]
    ring
  · have htR : (h : ℝ) < t := by exact_mod_cast (Nat.lt_of_not_ge ht)
    unfold nodeExcessNat nodePowerNat nodeDeficitKernel
    rw [max_eq_right (by linarith)]
    ring

theorem scaledExcessNodeSum_kernel (k : ℕ) (a : ℝ) (t : ℕ) :
    (k : ℝ)*(1-a)+scaledExcessNodeSum k a t = binomialAverage k a (nodeDeficitKernel t) := by
  have hrepr : scaledExcessNodeSum k a t = binomialAverage k a (fun h => excessNode k (k-h) t) := by
    rw [binomialAverage_success]
    unfold scaledExcessNodeSum
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.sub_sub_self (show j ≤ k by have := Finset.mem_range.mp hj; omega)]
  rw [hrepr]
  have hcongr := binomialAverage_congr k a (fun h => excessNode k (k-h) t)
    (fun h => nodeDeficitKernel t h-(h : ℝ)) (fun h hh => excessNode_kernel k h t hh)
  rw [hcongr,binomialAverage_sub,binomialAverage_mean]
  ring

theorem nodeDeficitKernel_step (t : ℕ) (ht : 1 ≤ t) (a : ℝ) (h : ℕ) :
    a*nodeDeficitKernel t h+(1-a)*nodeDeficitKernel t (h+1) =
      ((t : ℝ)-a)*(1-1/(t : ℝ))^(t-1-h)+max ((h : ℝ)-(t : ℝ)+1) 0 := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have htq : (t : ℝ)*(1-1/(t : ℝ)) = (t : ℝ)-1 := by field_simp
  by_cases hle : h+1 ≤ t
  · have hR : (h : ℝ)+1 ≤ t := by exact_mod_cast hle
    have hp1 : t-h = (t-1-h)+1 := by omega
    have hp2 : t-(h+1) = t-1-h := by omega
    unfold nodeDeficitKernel
    rw [Nat.cast_add,Nat.cast_one,max_eq_right (by linarith : (h : ℝ)-(t : ℝ) ≤ 0),
      max_eq_right (by linarith : (h : ℝ)+1-(t : ℝ) ≤ 0),
      max_eq_right (by linarith : (h : ℝ)-(t : ℝ)+1 ≤ 0),hp1,hp2,pow_succ]
    have hmul := congrArg (fun x => x*(1-1/(t : ℝ))^(t-1-h)) htq
    nlinarith [congrArg (fun x => a*x) hmul]
  · have hge : t ≤ h := by omega
    have hR : (t : ℝ) ≤ h := by exact_mod_cast hge
    unfold nodeDeficitKernel
    rw [Nat.sub_eq_zero_of_le hge,Nat.sub_eq_zero_of_le (show t ≤ h+1 by omega),
      Nat.sub_eq_zero_of_le (show t-1 ≤ h by omega),pow_zero,Nat.cast_add,Nat.cast_one]
    rw [max_eq_left (by linarith : 0 ≤ (h : ℝ)-(t : ℝ)),
      max_eq_left (by linarith : 0 ≤ (h : ℝ)+1-(t : ℝ)),
      max_eq_left (by linarith : 0 ≤ (h : ℝ)-(t : ℝ)+1)]
    ring

theorem weighted_node_moment_identity (k : ℕ) (hk : 1 ≤ k) (a : ℝ)
    (t : ℕ) (ht : 1 ≤ t) :
    (k : ℝ)*(1-a)+scaledExcessNodeSum k a t =
      ((t : ℝ)-a)*(1-shortTailNodeSum k a t)+binomialExcessRemainder k a t := by
  rw [scaledExcessNodeSum_kernel]
  have hrec := binomialAverage_succ (k-1) a (nodeDeficitKernel t)
  rw [Nat.sub_add_cancel hk] at hrec
  rw [hrec,← binomialAverage_mul_const,← binomialAverage_mul_const,← binomialAverage_add]
  have hid := binomialAverage_congr (k-1) a
    (fun h => a*nodeDeficitKernel t h+(1-a)*nodeDeficitKernel t (h+1))
    (fun h => ((t : ℝ)-a)*(1-1/(t : ℝ))^(t-1-h)+max ((h : ℝ)-(t : ℝ)+1) 0)
    (fun h _ => nodeDeficitKernel_step t ht a h)
  rw [hid,binomialAverage_add,binomialAverage_mul_const,← shortTailNodeSum_failure k hk]
  rfl

theorem binomialExcessRemainder_nonneg (k t : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ binomialExcessRemainder k a t :=
  binomialAverage_nonneg (k-1) a ha ha1 _ (fun _ _ => le_max_right _ _)

theorem normalized_binomial_sum (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : a ≠ 0)
    (f : ℕ → ℝ) (hf : f 0 = 0) :
    (∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a^j*(1-a)^(k-j)*f j) =
      a^k*(f k+∑ j ∈ Finset.range (k-1),(k.choose (j+1) : ℝ)*((1-a)/a)^(k-(j+1))*f (j+1)) := by
  rw [sum_range_without_endpoints k hk _ (by simp [hf])]
  simp only [Nat.choose_self,Nat.cast_one,one_mul,Nat.sub_self,pow_zero,mul_one]
  rw [mul_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hc := thinning_coefficient k (j+1) (by have := Finset.mem_range.mp hj; omega) a ha
  calc
    _ = (k.choose (j+1) : ℝ)*(a^(j+1)*(1-a)^(k-(j+1)))*f (j+1) := by ring
    _ = _ := by rw [hc]; ring

theorem full_node_failure_formula (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (ha : a ≠ 0)
    (t : ℕ) (htk : t ≤ k) :
    binomialAverage k a (fun h => (1-1/(t : ℝ))^(t-h)) =
      1-a^k*(1-nodeFailureValue t+nodeComparisonSum k ((1-a)/a) t) := by
  have hcongr := binomialAverage_congr k a (fun h => (1-1/(t : ℝ))^(t-h))
    (fun h => 1-tailNode k (k-h) t) (fun h hh => by rw [tailNode_complement,Nat.sub_sub_self hh])
  rw [hcongr,binomialAverage_sub,binomialAverage_const,binomialAverage_success]
  have htail : (∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a^j*(1-a)^(k-j)*tailNode k (k-(k-j)) t) =
      ∑ j ∈ Finset.range (k+1),(k.choose j : ℝ)*a^j*(1-a)^(k-j)*tailNode k j t := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.sub_sub_self (show j ≤ k by have := Finset.mem_range.mp hj; omega)]
  rw [htail,normalized_binomial_sum k hk a ha (fun j => tailNode k j t)
    (by simp [tailNode,htk])]
  have hlast : tailNode k k t = 1-nodeFailureValue t := by
    have h := tailNode_complement k k t
    simp only [Nat.sub_self,Nat.sub_zero] at h
    unfold nodeFailureValue
    linarith
  rw [hlast]
  rfl

theorem binomialAverage_factor (n : ℕ) (a : ℝ) (ha : a ≠ 0) (f : ℕ → ℝ) :
    binomialAverage n a f = a^n*∑ h ∈ Finset.range (n+1),
      (n.choose h : ℝ)*((1-a)/a)^h*f h := by
  unfold binomialAverage binomialWeightReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hhn : h ≤ n := by have := Finset.mem_range.mp hh; omega
  have hc := thinning_coefficient n (n-h) (Nat.sub_le _ _) a ha
  rw [Nat.sub_sub_self hhn] at hc
  calc
    _ = (n.choose h : ℝ)*(a^(n-h)*(1-a)^h)*f h := by ring
    _ = _ := by rw [hc]; ring

theorem shortTailNodeSum_eq_nodeFailure (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t)
    (c : ℝ) (hc : 0 ≤ c) :
    1-shortTailNodeSum k ((k : ℝ)/((k : ℝ)+c)) t = CriticalEstimates.nodeFailure (t-1) k c := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htne : (t : ℝ) ≠ 0 := ne_of_gt htpos
  have ha : (k : ℝ)/((k : ℝ)+c) ≠ 0 := ne_of_gt (by positivity)
  have hr : (1-(k : ℝ)/((k : ℝ)+c))/((k : ℝ)/((k : ℝ)+c)) = c/(k : ℝ) := by
    field_simp
    ring
  have hq : 1-1/(t : ℝ) = ((t-1 : ℕ) : ℝ)/(((t-1 : ℕ) : ℝ)+1) := by
    rw [Nat.cast_sub ht,Nat.cast_one,sub_add_cancel]
    field_simp
  rw [shortTailNodeSum_failure k hk,binomialAverage_factor (k-1) _ ha,hr,Nat.sub_add_cancel hk,hq]
  rfl

theorem nodePowerKernel_step (t : ℕ) (ht : 1 ≤ t) (a : ℝ) (h : ℕ) :
    a*((t : ℝ)*(1-1/(t : ℝ))^(t-h))+
      (1-a)*((t : ℝ)*(1-1/(t : ℝ))^(t-(h+1))) =
      ((t : ℝ)-a)*(1-1/(t : ℝ))^(t-1-h)+a*(if t ≤ h then 1 else 0) := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have htq : (t : ℝ)*(1-1/(t : ℝ)) = (t : ℝ)-1 := by field_simp
  by_cases hle : h+1 ≤ t
  · have hp1 : t-h = (t-1-h)+1 := by omega
    have hp2 : t-(h+1) = t-1-h := by omega
    rw [ite_eq_right (show ¬t ≤ h by omega),mul_zero,add_zero,hp1,hp2,pow_succ]
    have hmul := congrArg (fun x => x*(1-1/(t : ℝ))^(t-1-h)) htq
    nlinarith [congrArg (fun x => a*x) hmul]
  · have hge : t ≤ h := by omega
    rw [ite_eq_left hge,Nat.sub_eq_zero_of_le hge,
      Nat.sub_eq_zero_of_le (show t ≤ h+1 by omega),Nat.sub_eq_zero_of_le (show t-1 ≤ h by omega),pow_zero]
    ring

theorem nodePower_average_step (k : ℕ) (hk : 1 ≤ k) (a : ℝ) (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ)*binomialAverage k a (fun h => (1-1/(t : ℝ))^(t-h)) =
      ((t : ℝ)-a)*(1-shortTailNodeSum k a t)+
        a*binomialAverage (k-1) a (fun h => if t ≤ h then 1 else 0) := by
  rw [← binomialAverage_mul_const]
  have hrec := binomialAverage_succ (k-1) a (fun h => (t : ℝ)*(1-1/(t : ℝ))^(t-h))
  rw [Nat.sub_add_cancel hk] at hrec
  rw [hrec,← binomialAverage_mul_const,← binomialAverage_mul_const,← binomialAverage_add]
  have hid := binomialAverage_congr (k-1) a _ _ (fun h _ => nodePowerKernel_step t ht a h)
  rw [hid,binomialAverage_add,binomialAverage_mul_const,binomialAverage_mul_const,
    ← shortTailNodeSum_failure k hk]

theorem binomial_tail_factor (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) (htk : t ≤ k)
    (a : ℝ) (ha : a ≠ 0) :
    a*binomialAverage (k-1) a (fun h => if t ≤ h then 1 else 0) =
      a^k*∑ j ∈ Finset.range k,((k-1).choose (t+j) : ℝ)*((1-a)/a)^(t+j) := by
  rw [binomialAverage_factor (k-1) a ha,Nat.sub_add_cancel hk]
  let f : ℕ → ℝ := fun h => ((k-1).choose h : ℝ)*((1-a)/a)^h*(if t ≤ h then 1 else 0)
  have hsum := CriticalEstimates.sum_shift_of_vanishing f (n := t-1) (k := k) (by omega)
    (fun h hh => by simp only [f,ite_eq_right (show ¬t ≤ h by omega),mul_zero])
    (fun h hh => by simp [f,Nat.choose_eq_zero_of_lt (show k-1 < h by omega)])
  simp only [Nat.sub_add_cancel ht] at hsum
  change a*(a^(k-1)*∑ h ∈ Finset.range k,f h) = _
  rw [hsum]
  have heq : (∑ j ∈ Finset.range k,f (t+j)) =
      ∑ j ∈ Finset.range k,((k-1).choose (t+j) : ℝ)*((1-a)/a)^(t+j) := by
    apply Finset.sum_congr rfl
    intro j _
    simp [f]
  rw [heq]
  have hp : a*a^(k-1) = a^k := by rw [← pow_succ',Nat.sub_add_cancel hk]
  rw [← mul_assoc,hp]

theorem weighted_node_tail_identity (k t : ℕ) (hk : 1 ≤ k) (ht : 1 ≤ t) (htk : t ≤ k)
    (a p : ℝ) (ha : a ≠ 0) (hp : p = 1-a^k) :
    ((t : ℝ)-a)*(1-shortTailNodeSum k a t)-(t : ℝ)*p =
      a^k*((t : ℝ)*(nodeFailureValue t-nodeComparisonSum k ((1-a)/a) t)-
        ∑ j ∈ Finset.range k,((k-1).choose (t+j) : ℝ)*((1-a)/a)^(t+j)) := by
  have hstep := nodePower_average_step k hk a t ht
  rw [full_node_failure_formula k hk a ha t htk,binomial_tail_factor k t hk ht htk a ha] at hstep
  rw [hp]
  nlinarith only [hstep]

theorem critical_failure_identity (k : ℕ) (hk : 1 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (hcross : CriticalEstimates.criticalDifference k c = 1) :
    (1-1/((k : ℝ)+c))^k = 1-((k : ℝ)/((k : ℝ)+c))^k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  have hden : (k : ℝ)+c ≠ 0 := ne_of_gt (by positivity)
  let a := (k : ℝ)/((k : ℝ)+c)
  have hfirst : a*(1+c/(k : ℝ)) = 1 := by dsimp [a]; field_simp
  have hsecond : a*(1-(1-c)/(k : ℝ)) = 1-1/((k : ℝ)+c) := by dsimp [a]; field_simp; ring
  have h := congrArg (fun z => a^k*z) hcross
  unfold CriticalEstimates.criticalDifference at h
  rw [mul_sub,← mul_pow,← mul_pow,hfirst,hsecond,one_pow,mul_one] at h
  change (1-1/((k : ℝ)+c))^k = 1-a^k
  linarith

theorem fourth_weighted_node_identity (k : ℕ) (hk : 4 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    (4-a)*(1-shortTailNodeSum k a 4)-4*p =
      a^k*(4*(81/256-ScalarCertificates.fourthNodeA c (k : ℝ)⁻¹)-TailEstimates.binomialTail 4 k c) := by
  dsimp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : (k : ℝ)/((k : ℝ)+c) ≠ 0 := ne_of_gt (by positivity)
  have hr : (1-(k : ℝ)/((k : ℝ)+c))/((k : ℝ)/((k : ℝ)+c)) = c/(k : ℝ) := by field_simp; ring
  have h := weighted_node_tail_identity k 4 (by omega) (by omega) hk
    ((k : ℝ)/((k : ℝ)+c)) ((1-1/((k : ℝ)+c))^k) ha
    (critical_failure_identity k (by omega) c hc hcross)
  rw [hr,nodeComparisonSum_four k hk] at h
  norm_num [nodeFailureValue] at h
  simpa only [one_div,TailEstimates.binomialTail,TailEstimates.binomialTerm] using h

theorem fourth_weighted_node_gap (k : ℕ) (hk : 5 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (hcross : CriticalEstimates.criticalDifference k c = 1) :
    let a := (k : ℝ)/((k : ℝ)+c)
    let p := (1-1/((k : ℝ)+c))^k
    4*p < (4-a)*(1-shortTailNodeSum k a 4) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have ha : 0 < (k : ℝ)/((k : ℝ)+c) := by positivity
  have htail := TailEstimates.fourth_binomial_tail_strict hk hc hcross
  have hid := fourth_weighted_node_identity k (by omega) c hc hcross
  have hpos := mul_pos (pow_pos ha k) (sub_pos.mpr htail)
  dsimp at hid ⊢
  linarith

theorem shortTailNodeSum_last (k : ℕ) (hk : 1 ≤ k) (a : ℝ) :
    1-shortTailNodeSum k a k = (1-a/(k : ℝ))^(k-1) := by
  rw [shortTailNodeSum_failure k hk]
  unfold binomialAverage binomialWeightReal
  rw [Nat.sub_add_cancel hk]
  have hsum := CentralBinomial.add_pow_extended (a*(1-1/(k : ℝ))) (1-a) (k-1) k (by omega)
  calc
    _ = ∑ h ∈ Finset.range k,((k-1).choose h : ℝ)*(a*(1-1/(k : ℝ)))^(k-1-h)*(1-a)^h := by
      apply Finset.sum_congr rfl
      intro h _
      rw [mul_pow]
      ring
    _ = (a*(1-1/(k : ℝ))+(1-a))^(k-1) := hsum.symm
    _ = _ := by congr 1; ring

theorem binomialExcessRemainder_last (k : ℕ) (hk : 1 ≤ k) (a : ℝ) :
    binomialExcessRemainder k a k = 0 := by
  unfold binomialExcessRemainder
  have h := binomialAverage_congr (k-1) a (fun h => max ((h : ℝ)-(k : ℝ)+1) 0)
    (fun _ => 0) (by
      intro h hh
      have hhR : (h : ℝ)+1 ≤ k := by exact_mod_cast (show h+1 ≤ k by omega)
      exact max_eq_right (by linarith))
  rw [h,binomialAverage_const]

end SharpTailMatching.Probability.ComparisonGeometry
