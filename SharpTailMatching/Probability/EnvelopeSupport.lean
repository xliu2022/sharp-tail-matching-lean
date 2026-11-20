module

public import SharpTailMatching.Probability.ComparisonNodes
public import SharpTailMatching.Probability.ComparisonEnvelopes

/-!
# Supporting lines for the probability envelopes

Instead of introducing a piecewise polygon and its inverse, we prove directly
that every adjacent node chord is a global supporting line for every feasible
excess/tail pair. This is precisely the geometric statement used by weighted
interpolation.
-/

@[expose] public section

noncomputable section

open Set Real

namespace SharpTailMatching.Probability.ComparisonGeometry

theorem exists_adjacent_bracket (E : ℕ → ℝ) (a b : ℕ) (hab : a < b)
    (e : ℝ) (ha : E a ≤ e) (hb : e ≤ E b) :
    ∃ s, a ≤ s ∧ s < b ∧ E s ≤ e ∧ e ≤ E (s+1) := by
  induction b generalizing a with
  | zero => omega
  | succ b ih =>
    by_cases hab' : a < b
    · by_cases hbe : e ≤ E b
      · obtain ⟨s,has,hsb,hse,hes⟩ := ih a hab' ha hbe
        exact ⟨s,has,by omega,hse,hes⟩
      · exact ⟨b,by omega,by omega,(le_of_not_ge hbe),hb⟩
    · have haeq : a = b := by omega
      subst a
      exact ⟨b,le_rfl,by omega,ha,hb⟩

theorem integer_node_below_chordLine (ℓ t s : ℕ)
    (hℓ : 1 ≤ ℓ) (ht : ℓ < t) (hs : ℓ < s) :
    nodeTailNat ℓ s ≤ chordLine (ℓ : ℝ) t (t+1 : ℕ) (nodeExcessNat ℓ s) := by
  rw [nodeTailNat_eq_real ℓ s hs.le (by omega),
    nodeExcessNat_eq_real ℓ s hs.le (by omega)]
  apply node_below_chordLine
  · exact_mod_cast hℓ
  · exact_mod_cast ht
  · exact_mod_cast (show t < t+1 by omega)
  · exact_mod_cast hs
  · by_cases hst : s ≤ t
    · exact Or.inl (by exact_mod_cast hst)
    · exact Or.inr (by exact_mod_cast (show t+1 ≤ s by omega))

/-- Global supporting-line conclusion from the family of power-curve bounds.
The only range condition is the sharp unit-support bound on the excess. -/
theorem envelope_below_chordLine (ℓ k t : ℕ) (hℓ : 1 ≤ ℓ)
    (ht : ℓ < t) (htk : t < k) (e f : ℝ) (he0 : 0 ≤ e)
    (hek : e ≤ nodeExcessNat ℓ k)
    (henvelope : ∀ s, ℓ < s → s < k →
      f ≤ EnvelopeAlgebra.successCurve (s : ℝ) (s-ℓ) ((ℓ : ℝ)+e)) :
    f ≤ chordLine (ℓ : ℝ) t (t+1 : ℕ) e := by
  obtain ⟨s,hs,hsK,hse,hes⟩ := exists_adjacent_bracket (nodeExcessNat ℓ) (ℓ+1) k
    (by omega) e (by simpa only [nodeExcessNat_first] using he0) hek
  have hsℓ : ℓ < s := by omega
  have hE : nodeExcessNat ℓ s < nodeExcessNat ℓ (s+1) :=
    nodeExcessNat_strictMono ℓ hℓ hs (by change ℓ+1 ≤ s+1; omega) (by omega)
  let θ : ℝ := (e-nodeExcessNat ℓ s)/(nodeExcessNat ℓ (s+1)-nodeExcessNat ℓ s)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hse) (sub_pos.mpr hE).le
  have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hE)).mpr (by linarith)
  have heq : (1-θ)*nodeExcessNat ℓ s+θ*nodeExcessNat ℓ (s+1) = e := by
    dsimp [θ]
    field_simp [ne_of_gt (sub_pos.mpr hE)]
    ring
  have huL : 0 ≤ (ℓ : ℝ)+nodeExcessNat ℓ s :=
    add_nonneg (Nat.cast_nonneg ℓ) (nodeExcessNat_nonneg ℓ s hℓ hs)
  have huR : 0 ≤ (ℓ : ℝ)+nodeExcessNat ℓ (s+1) :=
    add_nonneg (Nat.cast_nonneg ℓ) (nodeExcessNat_nonneg ℓ (s+1) hℓ (by omega))
  have hconv := (EnvelopeAlgebra.successCurve_convex (s : ℝ) (s-ℓ)
    (by exact_mod_cast (show 0 < s by omega)) (by omega)).2 huL huR
    (sub_nonneg.mpr hθ1) hθ0 (by ring : 1-θ+θ = 1)
  simp only [smul_eq_mul] at hconv
  have huEq : (1-θ)*((ℓ : ℝ)+nodeExcessNat ℓ s)+
      θ*((ℓ : ℝ)+nodeExcessNat ℓ (s+1)) = (ℓ : ℝ)+e := by
    nlinarith [heq]
  rw [huEq,successCurve_node_left ℓ s hsℓ,successCurve_node_right ℓ s hsℓ] at hconv
  have hleft := integer_node_below_chordLine ℓ t s hℓ ht hsℓ
  have hright := integer_node_below_chordLine ℓ t (s+1) hℓ ht (by omega)
  have hlin := add_le_add (mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr hθ1))
    (mul_le_mul_of_nonneg_left hright hθ0)
  have hline : (1-θ)*chordLine (ℓ : ℝ) t (t+1 : ℕ) (nodeExcessNat ℓ s)+
      θ*chordLine (ℓ : ℝ) t (t+1 : ℕ) (nodeExcessNat ℓ (s+1)) =
      chordLine (ℓ : ℝ) t (t+1 : ℕ) e := by
    unfold chordLine
    rw [← heq]
    ring
  rw [hline] at hlin
  exact (henvelope s hsℓ hsK).trans (hconv.trans hlin)

theorem envelope_star_slope_bound (k j t : ℕ) (hjk : j < k)
    (ht : k-j < t) (htk : t < k) (e f θ : ℝ) (he0 : 0 ≤ e)
    (hek : e ≤ nodeExcessNat (k-j) k)
    (henvelope : ∀ s, k-j < s → s < k →
      f ≤ EnvelopeAlgebra.successCurve (s : ℝ) (s-(k-j)) ((k-j : ℕ)+e)) :
    f-tailStar k j t θ ≤ chordSlope (k-j : ℕ) t (t+1 : ℕ)*(e-excessStar k j t θ) := by
  have hline := envelope_below_chordLine (k-j) k t (by omega) ht htk e f he0 hek henvelope
  rw [star_chordLine k j t hjk ht θ]
  unfold chordLine at hline ⊢
  linarith

end SharpTailMatching.Probability.ComparisonGeometry
