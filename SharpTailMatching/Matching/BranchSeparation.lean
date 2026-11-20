module

public import SharpTailMatching.Matching.BinomialApproximation
public import SharpTailMatching.Matching.ExactAssembly
public import SharpTailMatching.CriticalProbabilityEstimates

/-! # Uniform finite separation of the cover and clique branches -/

@[expose] public section

noncomputable section

open Set

namespace SharpTailMatching.Matching

theorem positive_gap_on_interval {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) (hpos : ∀ x ∈ Icc a b, 0 < f x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Icc a b, δ ≤ f x := by
  obtain ⟨x,hx,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf.continuousOn
  exact ⟨f x,hpos x hx,fun y hy => hmin hy⟩

theorem candidate_branch_gaps (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x ∈ Icc (1/((k:ℝ)+1/4)) (k:ℝ)⁻¹,
        δ ≤ ((k:ℝ)*x)^k-(1-(1-x)^k)) ∧
      (∀ x ∈ Icc (1/(4*(k:ℝ)^3)) (1/((k:ℝ)+1/2)),
        δ ≤ (1-(1-x)^k)-((k:ℝ)*x)^k) := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  obtain ⟨β,⟨hβpos,hβlt,hβcross⟩,_⟩ := critical_mean_exists_unique k (by omega)
  have hc := CriticalEstimates.critical_parameter_from_beta (by omega) hβpos hβlt hβcross
  have hclow := CriticalEstimates.critical_parameter_lower (by omega) hc.1.le hc.2.2
  have hchigh := CriticalEstimates.critical_parameter_lt_half hk hc.1.le hc.2.2
  have hβeq : β = 1/((k:ℝ)+(β⁻¹-k)) := by
    rw [show (k:ℝ)+(β⁻¹-k) = β⁻¹ by ring, one_div, inv_inv]
  have hquarter : 1/4 < β⁻¹-(k:ℝ) := by
    have hpos : 0 < 2/(25*(k:ℝ)) := by positivity
    linarith
  have hβquarter : β < 1/((k:ℝ)+1/4) := by
    rw [hβeq]
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hhalfβ : 1/((k:ℝ)+1/2) < β := by
    rw [hβeq]
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hquarterk : 1/((k:ℝ)+1/4) ≤ (k:ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hkpos (by linarith : (k:ℝ) ≤ (k:ℝ)+1/4)
  have hkone : (k:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hkpos).mpr (by linarith)
  have hK : (k:ℝ)+1/2 ≤ 4*(k:ℝ)^3 := by
    have hsquare : 1 ≤ (k:ℝ)^2 := by nlinarith
    have hcube := mul_le_mul_of_nonneg_left hsquare hkpos.le
    nlinarith
  have hKhalf : 1/(4*(k:ℝ)^3) ≤ 1/((k:ℝ)+1/2) :=
    one_div_le_one_div_of_le (by linarith) hK
  obtain ⟨δ₁,hδ₁,hgap₁⟩ := positive_gap_on_interval hquarterk
    (show Continuous (fun x : ℝ => ((k:ℝ)*x)^k-(1-(1-x)^k)) by fun_prop) (by
      intro x hx
      exact sub_pos.mpr (small_candidate_gt_after_critical k (by omega) β x hβpos hβcross
        (hβquarter.trans_le hx.1) (hx.2.trans hkone)))
  obtain ⟨δ₂,hδ₂,hgap₂⟩ := positive_gap_on_interval hKhalf
    (show Continuous (fun x : ℝ => (1-(1-x)^k)-((k:ℝ)*x)^k) by fun_prop) (by
      intro x hx
      exact sub_pos.mpr (unit_candidate_gt_before_critical k (by omega) β x hβpos
        (hβlt.le.trans hkone) hβcross ((by positivity : (0:ℝ) < 1/(4*(k:ℝ)^3)).trans_le hx.1)
        (hx.2.trans_lt hhalfβ)))
  exact ⟨min δ₁ δ₂,lt_min hδ₁ hδ₂,
    fun x hx => (min_le_left _ _).trans (hgap₁ x hx),
    fun x hx => (min_le_right _ _).trans (hgap₂ x hx)⟩

theorem finite_density_of_count_upper {k n : ℕ} (hn : 0 < n) {h A ε : ℝ}
    (hupper : h ≤ A+ε*(n:ℝ)^k) :
    (k.factorial:ℝ)*h/(n:ℝ)^k ≤
      (k.factorial:ℝ)*A/(n:ℝ)^k+(k.factorial:ℝ)*ε := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hupper (Nat.cast_nonneg k.factorial : (0:ℝ) ≤ k.factorial))
    (pow_nonneg hnR.le k)
  have hid : (k.factorial:ℝ)*(A+ε*(n:ℝ)^k)/(n:ℝ)^k =
      (k.factorial:ℝ)*A/(n:ℝ)^k+(k.factorial:ℝ)*ε := by
    field_simp
  rwa [hid] at hscaled

/-- The genuine finite branch separation used by the two local exactification
lemmas. Its constants depend only on the fixed uniformity. -/
theorem matching_branch_separation (k : ℕ) (hk : 3 ≤ k) : FiniteBranchSeparation k := by
  obtain ⟨δ,hδ,hgapCover,hgapClique⟩ := candidate_branch_gaps k hk
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hfac : (0:ℝ) < k.factorial := Nat.cast_pos.mpr (Nat.factorial_pos k)
  let ε : ℝ := δ/(4*(k.factorial:ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcoef : (k.factorial:ℝ)*ε = δ/4 := by dsimp [ε]; field_simp
  obtain ⟨N,hN⟩ := exists_nat_gt (4*(k:ℝ)^2/δ)
  refine ⟨ε,hε,N+1,?_⟩
  intro s n h hs hn hnK hmax
  have hspos : 0 < s := by omega
  have hsn : s ≤ n := by nlinarith
  have hnpos : 0 < n := hspos.trans_le hsn
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hsR : (0:ℝ) < s := by exact_mod_cast hspos
  have hNn : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hlarge := (div_lt_iff₀ hδ).mp (hN.trans_le hNn)
  have herror : 2*((k:ℝ)^2/(n:ℝ)) < δ/2 := by
    have hfrac : (2*(k:ℝ)^2)/(n:ℝ) < δ/2 :=
      (div_lt_iff₀ hnR).mpr (by nlinarith)
    convert hfrac using 1 <;> ring
  let x : ℝ := (s:ℝ)/(n:ℝ)
  have hx0 : 0 < x := div_pos hsR hnR
  have hx1 : x ≤ (k:ℝ)⁻¹ := by
    change (s:ℝ)/(n:ℝ) ≤ (k:ℝ)⁻¹
    rw [← one_div]
    apply (div_le_div_iff₀ hnR hkpos).mpr
    rw [one_mul]
    exact_mod_cast (show s*k ≤ n by nlinarith)
  have hMle : (coverSize k n s:ℝ) ≤ h :=
    (show (coverSize k n s:ℝ) ≤ (max (coverSize k n s) (cliqueSize k s):ℝ) by
      exact_mod_cast le_max_left (coverSize k n s) (cliqueSize k s)).trans hmax
  have hCle : (cliqueSize k s:ℝ) ≤ h :=
    (show (cliqueSize k s:ℝ) ≤ (max (coverSize k n s) (cliqueSize k s):ℝ) by
      exact_mod_cast le_max_right (coverSize k n s) (cliqueSize k s)).trans hmax
  have hMscale : (k.factorial:ℝ)*(coverSize k n s:ℝ)/(n:ℝ)^k ≤
      (k.factorial:ℝ)*h/(n:ℝ)^k := by gcongr
  have hCscale : (k.factorial:ℝ)*(cliqueSize k s:ℝ)/(n:ℝ)^k ≤
      (k.factorial:ℝ)*h/(n:ℝ)^k := by gcongr
  constructor
  · intro happrox
    by_contra houtside
    have hgap := hgapCover x ⟨?_,hx1⟩
    · have hsmall := clique_density_lower (by omega : 1 ≤ k) hn
      have hunit := cover_density_upper (by omega : 1 ≤ k) hnpos hsn
      have hscaled := finite_density_of_count_upper hnpos happrox
      rw [hcoef] at hscaled
      change 1-(1-x)^k+(k:ℝ)^2/(n:ℝ) ≥
        (k.factorial:ℝ)*(coverSize k n s:ℝ)/(n:ℝ)^k at hunit
      have hmul : (k:ℝ)*(s:ℝ)/(n:ℝ) = (k:ℝ)*x := by dsimp [x]; ring
      rw [hmul] at hsmall
      linarith
    · change 1/((k:ℝ)+1/4) ≤ (s:ℝ)/(n:ℝ)
      apply (div_le_div_iff₀ (by linarith : (0:ℝ) < (k:ℝ)+1/4) hnR).mpr
      have hh := lt_of_not_ge houtside
      nlinarith
  · intro happrox
    by_contra houtside
    have hnKR : (n:ℝ) ≤ 4*(k:ℝ)^3*(s:ℝ) := by exact_mod_cast hnK
    have houtR : ((2*k+1:ℕ):ℝ)*(s:ℝ) < 2*(n:ℝ) := by
      exact_mod_cast (lt_of_not_ge houtside)
    push_cast at houtR
    have hxlower : 1/(4*(k:ℝ)^3) ≤ x := by
      change 1/(4*(k:ℝ)^3) ≤ (s:ℝ)/(n:ℝ)
      apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4*(k:ℝ)^3) hnR).mpr
      nlinarith
    have hxupper : x ≤ 1/((k:ℝ)+1/2) := by
      change (s:ℝ)/(n:ℝ) ≤ 1/((k:ℝ)+1/2)
      apply (div_le_div_iff₀ hnR (by linarith : (0:ℝ) < (k:ℝ)+1/2)).mpr
      nlinarith
    have hgap := hgapClique x ⟨hxlower,hxupper⟩
    have hunit := cover_density_lower (by omega : 1 ≤ k) hnpos hsn
    have hsmall := clique_density_upper (by omega : 1 ≤ k) hn
    have hscaled := finite_density_of_count_upper hnpos happrox
    rw [hcoef] at hscaled
    change 1-(1-x)^k ≤
      (k.factorial:ℝ)*(coverSize k n s:ℝ)/(n:ℝ)^k+(k:ℝ)^2/(n:ℝ) at hunit
    have hmul : (k:ℝ)*(s:ℝ)/(n:ℝ) = (k:ℝ)*x := by dsimp [x]; ring
    rw [hmul] at hsmall
    linarith

end SharpTailMatching.Matching
