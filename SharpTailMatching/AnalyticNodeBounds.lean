module

public import SharpTailMatching.PhiMonotonicity

/-! # Analytic lower bounds for the comparison-node generating function -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

open Set
open scoped BigOperators

namespace SharpTailMatching.CriticalEstimates

def nodeA (n : ℝ) : ℝ :=
  1+3/(6*n+4)+(3/(6*n+4))^2/2+(3/(6*n+4))^3/6

def nodeB (n k c : ℝ) : ℝ :=
  1+(k-1)*(c/(k+c))/n+(k-1)*(k-2)*(c/(k+c))^2/(2*n^2)

def nodeC (k c : ℝ) : ℝ := 1+(1/2-c)/k+1/(12*k^2)

theorem log_one_add_rational_derivative {u : ℝ} (hu : 0 ≤ u) :
    HasDerivAt (fun x : ℝ => x*(6+x)/(6+4*x)-Real.log (1+x))
      (u^3/((1+u)*(2*u+3)^2)) u := by
  have hden : 6+4*u ≠ 0 := by positivity
  have hlog : 1+u ≠ 0 := by positivity
  convert (((hasDerivAt_id u).mul ((hasDerivAt_const u 6).add (hasDerivAt_id u))).div
    ((hasDerivAt_const u 6).add ((hasDerivAt_id u).const_mul 4)) hden).sub
    (((hasDerivAt_const u 1).add (hasDerivAt_id u)).log hlog) using 1
  · rfl
  · simp only [id_eq, Pi.add_apply, Pi.mul_apply]
    field_simp
    ring

theorem log_one_add_rational_lt {u : ℝ} (hu : 0 < u) :
    Real.log (1+u) < u*(6+u)/(6+4*u) := by
  have hm : StrictMonoOn (fun x : ℝ => x*(6+x)/(6+4*x)-Real.log (1+x)) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x hx
      exact (log_one_add_rational_derivative hx).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
      rw [(log_one_add_rational_derivative hx'.le).deriv]
      positivity
  have hh := hm (show (0:ℝ) ∈ Ici 0 by simp) hu.le hu
  norm_num at hh
  linarith

theorem cubic_truncation_lt_exp {τ : ℝ} (hτ : 0 < τ) :
    1+τ+τ^2/2+τ^3/6 < Real.exp τ := by
  have hs := Real.sum_le_exp_of_nonneg hτ.le 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  nlinarith [pow_pos hτ 4]

theorem nodeA_lt_exp_power {n : ℕ} (hn : 1 ≤ n) :
    nodeA n < Real.exp 1 * ((n:ℝ)/(n+1))^n := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  let u := 1/(n:ℝ)
  let q := (n:ℝ)/(n+1)
  let τ := 3/(6*(n:ℝ)+4)
  have hu : 0 < u := by dsimp [u]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hlog := log_one_add_rational_lt hu
  have hqinv : q = (1+u)⁻¹ := by dsimp [q, u]; field_simp
  have hid : 1-(n:ℝ)*(u*(6+u)/(6+4*u)) = τ := by
    dsimp [τ, u]
    field_simp
    ring
  have hexponent : τ < 1+(n:ℝ)*Real.log q := by
    rw [hqinv, Real.log_inv]
    have hh := mul_lt_mul_of_pos_left hlog hnpos
    linarith
  have hA : nodeA n < Real.exp τ := cubic_truncation_lt_exp hτ
  have he := Real.exp_lt_exp.mpr hexponent
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hq] at he
  exact hA.trans he

theorem critical_failure_log_lower {k : ℕ} (hk : 2 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    1+(1/2-c)/(k:ℝ)+1/(12*(k:ℝ)^2) <
      -(k:ℝ)*Real.log (1-1/((k:ℝ)+c)) := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  let e := 1/2-c
  let d := (k:ℝ)+c-1/2
  let u := 1/(2*d)
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  have hdle : d ≤ k := by dsimp [d]; linarith
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    apply (div_lt_one (by positivity)).mpr
    dsimp [d]
    linarith
  have hseries := Real.sum_range_le_log_div hu0.le hu1 3
  norm_num [Finset.sum_range_succ] at hseries
  have hstrict : 2*u+2*u^3/3 < Real.log ((1+u)/(1-u)) := by
    nlinarith [pow_pos hu0 5]
  have hratio : 1-1/((k:ℝ)+c) = ((1+u)/(1-u))⁻¹ := by
    have hkc : (k:ℝ)+c ≠ 0 := by linarith
    rw [inv_div]
    dsimp [u]
    field_simp [hd.ne', hkc]
    dsimp [d]
    ring
  have hid : (k:ℝ)*(2*u+2*u^3/3) = (k:ℝ)/d+(k:ℝ)/(12*d^3) := by
    dsimp [u]
    field_simp
    ring
  have hlog : (k:ℝ)/d+(k:ℝ)/(12*d^3) <
      -(k:ℝ)*Real.log (1-1/((k:ℝ)+c)) := by
    have hh := mul_lt_mul_of_pos_left hstrict hkpos
    rw [hid] at hh
    rw [hratio, Real.log_inv]
    linarith
  have hfirst : 1+e/(k:ℝ) ≤ (k:ℝ)/d := by
    have hident : (k:ℝ)/d-(1+e/(k:ℝ)) = e^2/((k:ℝ)*d) := by
      field_simp [hd.ne', hkpos.ne']
      dsimp [e, d]
      ring
    have hp : 0 ≤ e^2/((k:ℝ)*d) := by positivity
    linarith
  have hsecond : 1/(12*(k:ℝ)^2) ≤ (k:ℝ)/(12*d^3) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh := pow_le_pow_left₀ hd.le hdle 3
    nlinarith
  change 1+e/(k:ℝ)+1/(12*(k:ℝ)^2) < _
  linarith

theorem nodeC_lt_exp_failure_ratio {k : ℕ} (hk : 2 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    nodeC k c < Real.exp (-1) / (1-1/((k:ℝ)+c))^k := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hbase : 0 < 1-1/((k:ℝ)+c) := by
    have hdiv : 1/((k:ℝ)+c) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hlog := critical_failure_log_lower hk hc0 hc1
  have hexp := Real.add_one_le_exp (-1-(k:ℝ)*Real.log (1-1/((k:ℝ)+c)))
  have hratio : Real.exp (-1) / (1-1/((k:ℝ)+c))^k =
      Real.exp (-1-(k:ℝ)*Real.log (1-1/((k:ℝ)+c))) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hbase]
  rw [hratio]
  dsimp [nodeC]
  linarith

theorem nodeB_le_binomial {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) :
    nodeB n k c ≤ (1+(c/((k:ℝ)+c))/(n:ℝ))^(k-1) := by
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  have h := (positive_taylor_bounds (k-1) (u := (c/((k:ℝ)+c))/(n:ℝ))
    (by positivity)).2.1
  have hcast : ((k-1:ℕ):ℝ) = (k:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hid : taylorTwo (k-1:ℕ) ((c/((k:ℝ)+c))/(n:ℝ)) = nodeB n k c := by
    rw [hcast]
    unfold taylorTwo taylorOne nodeB
    ring
  rwa [hid] at h

theorem rational_node_lower {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1/2) :
    nodeA n * nodeB n k c * nodeC k c <
      (((n:ℝ)/(n+1))^n * (1+(c/((k:ℝ)+c))/(n:ℝ))^(k-1)) /
        (1-1/((k:ℝ)+c))^k := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hbase : 0 < 1-1/((k:ℝ)+c) := by
    have hh : 1/((k:ℝ)+c) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hA0 : 0 < nodeA n := by unfold nodeA; positivity
  have hB0 : 0 < nodeB n k c := by
    unfold nodeB
    have h1 : 0 ≤ (k:ℝ)-1 := by linarith
    have h2 : 0 ≤ (k:ℝ)-2 := by linarith
    positivity
  have hC0 : 0 < nodeC k c := by
    unfold nodeC
    have he : 0 ≤ 1/2-c := by linarith
    positivity
  have hA := nodeA_lt_exp_power hn
  have hB := nodeB_le_binomial hn hk hc0
  have hC := nodeC_lt_exp_failure_ratio hk hc0 hc1
  let q : ℝ := (n:ℝ)/(n+1)
  let P : ℝ := (1+(c/((k:ℝ)+c))/(n:ℝ))^(k-1)
  let p : ℝ := (1-1/((k:ℝ)+c))^k
  have hq : 0 < q := by dsimp [q]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  calc
    nodeA n * nodeB n k c * nodeC k c <
        (Real.exp 1*q^n) * nodeB n k c * nodeC k c :=
      mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hA hB0) hC0
    _ ≤ (Real.exp 1*q^n)*P*nodeC k c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by positivity)) hC0.le
    _ < (Real.exp 1*q^n)*P*(Real.exp (-1)/p) :=
      mul_lt_mul_of_pos_left hC (by positivity)
    _ = _ := by
      have hE : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
      change (Real.exp 1*q^n)*P*(Real.exp (-1)/p) = q^n*P/p
      calc
        _ = (Real.exp 1*Real.exp (-1))*(q^n*P/p) := by ring
        _ = _ := by rw [hE, one_mul]

end SharpTailMatching.CriticalEstimates
