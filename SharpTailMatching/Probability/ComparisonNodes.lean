module

public import SharpTailMatching.Probability.CurveGeometry

/-!
# Integer comparison nodes and their power envelopes

The integer definitions include the endpoint `t = 1`, where the logarithmic
parametrization is not used. All geometric assertions follow from the
continuous curve away from that endpoint.
-/

@[expose] public section

noncomputable section

open Set Real

namespace SharpTailMatching.Probability.ComparisonGeometry

def nodePowerNat (ℓ t : ℕ) : ℝ := (1-1/(t : ℝ))^(t-ℓ)
def nodeExcessNat (ℓ t : ℕ) : ℝ := -(ℓ : ℝ)+(t : ℝ)*nodePowerNat ℓ t
def nodeTailNat (ℓ t : ℕ) : ℝ := 1-nodePowerNat ℓ t
def excessNode (k j t : ℕ) : ℝ := if t ≤ k-j then 0 else nodeExcessNat (k-j) t
def tailNode (k j t : ℕ) : ℝ := if t ≤ k-j then 0 else nodeTailNat (k-j) t
def maxExcessNode (t : ℕ) : ℝ := nodeExcessNat 0 t

theorem nodePowerNat_eq_real (ℓ t : ℕ) (hℓt : ℓ ≤ t) (ht : 1 < t) :
    nodePowerNat ℓ t = nodePower (ℓ : ℝ) (t : ℝ) := by
  rw [nodePower_eq_rpow _ _ (by exact_mod_cast ht)]
  rw [← Nat.cast_sub hℓt, Real.rpow_natCast]
  rfl

theorem nodeExcessNat_eq_real (ℓ t : ℕ) (hℓt : ℓ ≤ t) (ht : 1 < t) :
    nodeExcessNat ℓ t = nodeExcess (ℓ : ℝ) (t : ℝ) := by
  simp only [nodeExcessNat,nodeExcess,nodePowerNat_eq_real ℓ t hℓt ht]

theorem nodeTailNat_eq_real (ℓ t : ℕ) (hℓt : ℓ ≤ t) (ht : 1 < t) :
    nodeTailNat ℓ t = nodeTail (ℓ : ℝ) (t : ℝ) := by
  simp only [nodeTailNat,nodeTail,nodePowerNat_eq_real ℓ t hℓt ht]

theorem nodeExcessNat_first (ℓ : ℕ) : nodeExcessNat ℓ (ℓ+1) = 0 := by
  have hden : (ℓ : ℝ)+1 ≠ 0 := by positivity
  simp only [nodeExcessNat,nodePowerNat,Nat.add_sub_cancel_left,pow_one,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem nodeTailNat_first (ℓ : ℕ) : nodeTailNat ℓ (ℓ+1) = 1/((ℓ : ℝ)+1) := by
  simp [nodeTailNat,nodePowerNat]

theorem nodeExcessNat_strictMono (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    StrictMonoOn (nodeExcessNat ℓ) (Set.Ici (ℓ+1)) := by
  intro a ha b hb hab
  change ℓ+1 ≤ a at ha
  change ℓ+1 ≤ b at hb
  rw [nodeExcessNat_eq_real ℓ a (by omega) (by omega),
    nodeExcessNat_eq_real ℓ b (by omega) (by omega)]
  apply nodeExcess_strictMono (ℓ : ℝ) (by exact_mod_cast hℓ)
  · change (ℓ : ℝ)+1 ≤ (a : ℝ)
    exact_mod_cast ha
  · change (ℓ : ℝ)+1 ≤ (b : ℝ)
    exact_mod_cast hb
  · exact_mod_cast hab

theorem nodeExcessNat_nonneg (ℓ t : ℕ) (hℓ : 1 ≤ ℓ) (ht : ℓ+1 ≤ t) :
    0 ≤ nodeExcessNat ℓ t := by
  rw [← nodeExcessNat_first ℓ]
  exact (nodeExcessNat_strictMono ℓ hℓ).monotoneOn (by simp) ht ht

theorem maxExcessNode_one : maxExcessNode 1 = 0 := by
  norm_num [maxExcessNode,nodeExcessNat,nodePowerNat]

theorem maxExcessNode_pos (t : ℕ) (ht : 1 < t) : 0 < maxExcessNode t := by
  have htR : (1 : ℝ) < t := by exact_mod_cast ht
  unfold maxExcessNode nodeExcessNat nodePowerNat
  simp only [Nat.cast_zero,neg_zero,zero_add,Nat.sub_zero]
  exact mul_pos (by positivity) (pow_pos (by
    exact sub_pos.mpr ((div_lt_one (by positivity : 0 < (t : ℝ))).mpr htR)) _)

theorem maxExcessNode_strictMono : StrictMonoOn maxExcessNode (Set.Ici 1) := by
  intro a ha b hb hab
  change 1 ≤ a at ha
  change 1 ≤ b at hb
  by_cases ha1 : a = 1
  · subst a
    rw [maxExcessNode_one]
    exact maxExcessNode_pos b hab
  · have ha2 : 1 < a := by omega
    have hb2 : 1 < b := by omega
    unfold maxExcessNode
    rw [nodeExcessNat_eq_real 0 a (by omega) ha2,
      nodeExcessNat_eq_real 0 b (by omega) hb2]
    norm_num only [Nat.cast_zero]
    apply zero_nodeExcess_strictMono
    · change (1 : ℝ) < a
      exact_mod_cast ha2
    · change (1 : ℝ) < b
      exact_mod_cast hb2
    · exact_mod_cast hab

theorem maxExcessNode_nonneg (t : ℕ) (ht : 1 ≤ t) : 0 ≤ maxExcessNode t := by
  rw [← maxExcessNode_one]
  exact maxExcessNode_strictMono.monotoneOn (by simp) ht ht

theorem failureCurve_at_power (T q : ℝ) (n : ℕ)
    (hT : 0 < T) (hq : 0 ≤ q) (hn : 0 < n) :
    EnvelopeAlgebra.failureCurve T n (T*q^n) = T*q^n*(1-q) := by
  rw [EnvelopeAlgebra.failureCurve_eq_root_form T (T*q^n) n hT
    (mul_nonneg hT.le (pow_nonneg hq _)) hn]
  have hdiv : (T*q^n)/T = q^n := by field_simp
  rw [hdiv,Real.pow_rpow_inv_natCast hq (Nat.ne_zero_of_lt hn)]

theorem failureCurve_node_left (ℓ t : ℕ) (ht : ℓ < t) :
    EnvelopeAlgebra.failureCurve (t : ℝ) (t-ℓ) ((ℓ : ℝ)+nodeExcessNat ℓ t) =
      nodePowerNat ℓ t := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have hq : 0 ≤ 1-1/(t : ℝ) := sub_nonneg.mpr ((div_le_one ht0).mpr ht1)
  have hu : (ℓ : ℝ)+nodeExcessNat ℓ t = (t : ℝ)*(1-1/(t : ℝ))^(t-ℓ) := by
    unfold nodeExcessNat nodePowerNat
    ring
  rw [hu,failureCurve_at_power _ _ _ ht0 hq (by omega)]
  unfold nodePowerNat
  field_simp
  ring

theorem failureCurve_node_right (ℓ t : ℕ) (ht : ℓ < t) :
    EnvelopeAlgebra.failureCurve (t : ℝ) (t-ℓ) ((ℓ : ℝ)+nodeExcessNat ℓ (t+1)) =
      nodePowerNat ℓ (t+1) := by
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
  have ht1 : 0 < (t : ℝ)+1 := by positivity
  have hq : 0 ≤ 1-1/((t : ℝ)+1) :=
    sub_nonneg.mpr ((div_le_one ht1).mpr (by linarith))
  have hn : t+1-ℓ = (t-ℓ)+1 := by omega
  have hqmul : ((t : ℝ)+1)*(1-1/((t : ℝ)+1)) = (t : ℝ) := by field_simp; ring
  have hu : (ℓ : ℝ)+nodeExcessNat ℓ (t+1) =
      (t : ℝ)*(1-1/((t : ℝ)+1))^(t-ℓ) := by
    unfold nodeExcessNat nodePowerNat
    rw [hn,pow_succ,Nat.cast_add,Nat.cast_one]
    calc
      _ = (((t : ℝ)+1)*(1-1/((t : ℝ)+1)))*(1-1/((t : ℝ)+1))^(t-ℓ) := by ring
      _ = _ := by rw [hqmul]
  rw [hu,failureCurve_at_power _ _ _ ht0 hq (by omega)]
  unfold nodePowerNat
  rw [hn,pow_succ,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem successCurve_node_left (ℓ t : ℕ) (ht : ℓ < t) :
    EnvelopeAlgebra.successCurve (t : ℝ) (t-ℓ) ((ℓ : ℝ)+nodeExcessNat ℓ t) =
      nodeTailNat ℓ t := by
  simp only [EnvelopeAlgebra.successCurve,failureCurve_node_left ℓ t ht,nodeTailNat]

theorem successCurve_node_right (ℓ t : ℕ) (ht : ℓ < t) :
    EnvelopeAlgebra.successCurve (t : ℝ) (t-ℓ) ((ℓ : ℝ)+nodeExcessNat ℓ (t+1)) =
      nodeTailNat ℓ (t+1) := by
  simp only [EnvelopeAlgebra.successCurve,failureCurve_node_right ℓ t ht,nodeTailNat]

theorem failureCurve_maxExcess_left (t : ℕ) (ht : 0 < t) :
    EnvelopeAlgebra.failureCurve (t : ℝ) t (maxExcessNode t) = (1-1/(t : ℝ))^t := by
  simpa only [Nat.sub_zero,Nat.cast_zero,zero_add,maxExcessNode,nodePowerNat] using
    failureCurve_node_left 0 t ht

theorem failureCurve_maxExcess_right (t : ℕ) (ht : 0 < t) :
    EnvelopeAlgebra.failureCurve (t : ℝ) t (maxExcessNode (t+1)) =
      (1-1/((t+1 : ℕ) : ℝ))^(t+1) := by
  simpa only [Nat.sub_zero,Nat.cast_zero,zero_add,maxExcessNode,nodePowerNat] using
    failureCurve_node_right 0 t ht

theorem nodeExcessNat_succ_level (ℓ t : ℕ) (ht : ℓ+1 < t) :
    nodeExcessNat ℓ t = nodeExcessNat (ℓ+1) t+nodeTailNat (ℓ+1) t := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  have hexp : t-ℓ = (t-(ℓ+1))+1 := by omega
  have htq : (t : ℝ)*(1-1/(t : ℝ)) = (t : ℝ)-1 := by field_simp
  unfold nodeExcessNat nodeTailNat nodePowerNat
  rw [hexp,pow_succ,Nat.cast_add,Nat.cast_one]
  calc
    _ = -(ℓ : ℝ)+((t : ℝ)*(1-1/(t : ℝ)))*(1-1/(t : ℝ))^(t-(ℓ+1)) := by ring
    _ = _ := by rw [htq]; ring

theorem excessNode_rec (k j t : ℕ) (hj : j < k) :
    excessNode k (j+1) t = excessNode k j t+tailNode k j t := by
  have hlev : k-j = (k-(j+1))+1 := by omega
  by_cases hleft : t ≤ k-(j+1)
  · have hright : t ≤ k-j := by omega
    simp only [excessNode,tailNode,ite_eq_left hleft,ite_eq_left hright,zero_add]
  · by_cases hright : t ≤ k-j
    · have ht : t = (k-(j+1))+1 := by omega
      simp only [excessNode,tailNode,ite_eq_right hleft,ite_eq_left hright,zero_add]
      rw [ht,nodeExcessNat_first]
    · simp only [excessNode,tailNode,ite_eq_right hleft,ite_eq_right hright]
      rw [hlev]
      exact nodeExcessNat_succ_level (k-(j+1)) t (by omega)

theorem excessNode_one (k t : ℕ) (hk : 1 ≤ k) (htk : t ≤ k) :
    excessNode k 1 t = 0 := by
  by_cases ht : t ≤ k-1
  · simp [excessNode,ht]
  · have htk' : t = (k-1)+1 := by omega
    simp only [excessNode,ite_eq_right ht]
    rw [htk',nodeExcessNat_first]

theorem excessNode_last (k t : ℕ) (ht : 0 < t) :
    excessNode k k t = maxExcessNode t := by
  simp [excessNode,maxExcessNode,Nat.not_le.mpr ht]

theorem excessNode_nonneg (k j t : ℕ) (_hjk : j ≤ k) (ht : 1 ≤ t) :
    0 ≤ excessNode k j t := by
  by_cases htℓ : t ≤ k-j
  · simp [excessNode,htℓ]
  · simp only [excessNode,ite_eq_right htℓ]
    by_cases hlevel : k-j = 0
    · rw [hlevel]
      exact maxExcessNode_nonneg t ht
    · exact nodeExcessNat_nonneg (k-j) t (by omega) (by omega)

def excessStar (k j t : ℕ) (θ : ℝ) : ℝ :=
  (1-θ)*excessNode k j t+θ*excessNode k j (t+1)
def tailStar (k j t : ℕ) (θ : ℝ) : ℝ :=
  (1-θ)*tailNode k j t+θ*tailNode k j (t+1)
def segmentExcess (t : ℕ) (θ : ℝ) : ℝ :=
  (1-θ)*maxExcessNode t+θ*maxExcessNode (t+1)

theorem excessStar_rec (k j t : ℕ) (hj : j < k) (θ : ℝ) :
    excessStar k (j+1) t θ = excessStar k j t θ+tailStar k j t θ := by
  unfold excessStar tailStar
  rw [excessNode_rec k j t hj,excessNode_rec k j (t+1) hj]
  ring

theorem excessStar_one (k t : ℕ) (hk : 1 ≤ k) (htk : t < k) (θ : ℝ) :
    excessStar k 1 t θ = 0 := by
  simp only [excessStar,excessNode_one k t hk htk.le,
    excessNode_one k (t+1) hk (by omega),mul_zero,add_zero]

theorem excessStar_last (k t : ℕ) (ht : 0 < t) (θ : ℝ) :
    excessStar k k t θ = segmentExcess t θ := by
  simp only [excessStar,segmentExcess,excessNode_last k t ht,
    excessNode_last k (t+1) (by omega)]

theorem excessNode_eq_zero (k j t : ℕ) (ht : t ≤ k-j+1) :
    excessNode k j t = 0 := by
  by_cases h : t ≤ k-j
  · simp [excessNode,h]
  · have heq : t = k-j+1 := by omega
    simp only [excessNode,ite_eq_right h]
    rw [heq,nodeExcessNat_first]

theorem excessStar_prefix (k j t : ℕ) (htk : t ≤ k) (hj : j ≤ k-t) (θ : ℝ) :
    excessStar k j t θ = 0 := by
  have hlev : t ≤ k-j := by omega
  simp only [excessStar,excessNode_eq_zero k j t (by omega),
    excessNode_eq_zero k j (t+1) (by omega),mul_zero,add_zero]

theorem star_chordLine (k j t : ℕ) (hjk : j < k) (ht : k-j < t) (θ : ℝ) :
    tailStar k j t θ =
      chordLine (k-j : ℕ) t (t+1 : ℕ) (excessStar k j t θ) := by
  have hℓ : 1 ≤ k-j := by omega
  have ht2 : 1 < t := by omega
  have ht' : ¬t ≤ k-j := Nat.not_le.mpr ht
  have hts : ¬t+1 ≤ k-j := by omega
  have ha : (k-j : ℕ) + (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hab : (t : ℝ) < (t+1 : ℕ) := by exact_mod_cast (show t < t+1 by omega)
  have hline := chordLine_right (k-j : ℕ) t (t+1 : ℕ) (by exact_mod_cast hℓ) ha hab
  simp only [tailStar,excessStar,tailNode,excessNode,ite_eq_right ht',ite_eq_right hts,
    nodeTailNat_eq_real (k-j) t ht.le ht2,
    nodeTailNat_eq_real (k-j) (t+1) (by omega) (by omega),
    nodeExcessNat_eq_real (k-j) t ht.le ht2,
    nodeExcessNat_eq_real (k-j) (t+1) (by omega) (by omega)]
  rw [← hline]
  unfold chordLine
  ring

end SharpTailMatching.Probability.ComparisonGeometry
