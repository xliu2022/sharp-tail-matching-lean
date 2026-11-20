module

public import SharpTailMatching.Probability.FiniteCapping
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing product certificates to limits

The finite loss vectors have a convergent subsequence in a compact box. This
preserves their mean bounds, sum, and failure-probability product inequality.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace SharpTailMatching.Probability

theorem product_certificate_limit {ι : Type*} [Fintype ι]
    (pN rN BN : ℕ → ℝ) (mN : ℕ → ι → ℝ)
    (p r B : ℝ) (m : ι → ℝ) (hr : r ≠ 0)
    (hp : Tendsto pN atTop (𝓝 p)) (hrN : Tendsto rN atTop (𝓝 r))
    (hB : Tendsto BN atTop (𝓝 B)) (hm : ∀ i, Tendsto (fun n => mN n i) atTop (𝓝 (m i)))
    (hcert : ∀ᶠ n in atTop, ∃ z : ι → ℝ,
      (∀ i, 0 ≤ z i ∧ z i ≤ mN n i) ∧ (∑ i, z i = BN n) ∧
        (∏ i, (1 - z i / rN n)) ≤ pN n) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ m i) ∧ (∑ i, z i = B) ∧
      (∏ i, (1 - z i / r)) ≤ p := by
  classical
  let C (n : ℕ) (z : ι → ℝ) : Prop :=
    (∀ i, 0 ≤ z i ∧ z i ≤ mN n i) ∧ (∑ i, z i = BN n) ∧
      (∏ i, (1 - z i / rN n)) ≤ pN n
  let zN (n : ℕ) : ι → ℝ := if h : ∃ z, C n z then Classical.choose h else fun _ => 0
  have hzN : ∀ᶠ n in atTop, C n (zN n) := by
    filter_upwards [hcert] with n hn
    change ∃ z, C n z at hn
    simp only [zN, dite_eq_left hn]
    exact Classical.choose_spec hn
  have hmupper : ∀ᶠ n in atTop, ∀ i, mN n i ≤ m i + 1 := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((tendsto_order.mp (hm i)).2 (m i + 1) (by linarith)).mono (fun _ h => h.le)
  have hbounded : ∀ᶠ n in atTop, zN n ∈ Set.Icc (fun _ => 0) (fun i => m i + 1) := by
    filter_upwards [hzN, hmupper] with n hn hupper
    exact ⟨fun i => (hn.1 i).1, fun i => (hn.1 i).2.trans (hupper i)⟩
  obtain ⟨z, _, φ, hφ, hzlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : ι => (0 : ℝ)) (fun i => m i + 1))).tendsto_subseq'
      hbounded.frequently
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hcertφ : ∀ᶠ n in atTop, C (φ n) (zN (φ n)) := hφtop.eventually hzN
  have hzcoord (i : ι) : Tendsto (fun n => zN (φ n) i) atTop (𝓝 (z i)) :=
    (tendsto_pi_nhds.mp hzlim) i
  refine ⟨z, ?_, ?_, ?_⟩
  · intro i
    constructor
    · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hzcoord i)
        (hcertφ.mono (fun _ hn => (hn.1 i).1))
    · exact le_of_tendsto_of_tendsto (hzcoord i) ((hm i).comp hφtop)
        (hcertφ.mono (fun _ hn => (hn.1 i).2))
  · have hsumlim := tendsto_finsetSum Finset.univ (fun i _ => hzcoord i)
    have hsumB : Tendsto (fun n => ∑ i, zN (φ n) i) atTop (𝓝 B) := by
      apply (hB.comp hφtop).congr'
      exact hcertφ.mono (fun _ hn => hn.2.1.symm)
    exact tendsto_nhds_unique hsumlim hsumB
  · have hprodlim : Tendsto (fun n => ∏ i, (1 - zN (φ n) i / rN (φ n)))
        atTop (𝓝 (∏ i, (1 - z i / r))) := by
      apply tendsto_finsetProd
      intro i _
      exact tendsto_const_nhds.sub ((hzcoord i).div (hrN.comp hφtop) hr)
    exact le_of_tendsto_of_tendsto hprodlim (hp.comp hφtop)
      (hcertφ.mono (fun _ hn => hn.2.2))

end SharpTailMatching.Probability

namespace SharpTailMatching.Probability.FiniteProduct

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem expect_weights_tendsto (wN : ℕ → ι → α → ℝ) (w : ι → α → ℝ)
    (hweight : ∀ i a, Tendsto (fun n => wN n i a) atTop (𝓝 (w i a)))
    (f : (ι → α) → ℝ) :
    Tendsto (fun n => expect (wN n) f) atTop (𝓝 (expect w f)) := by
  unfold expect weight
  apply tendsto_finsetSum
  intro ω _
  apply Filter.Tendsto.mul_const
  apply tendsto_finsetProd
  intro i _
  exact hweight i (ω i)

/-- Zero atom weights are permitted by taking a vanishing positive uniform
mixture on the fixed grid, then applying the proved compactness argument. -/
theorem finite_product_bound_nonnegative {n : ℕ} (w X : ι → Fin (n+1) → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hmono : ∀ i, Monotone (X i)) (hX : ∀ i a, 0 ≤ X i a)
    (hp : 0 < failure w X) (hr : 0 < conditionalDeficit w X)
    (hm : ∀ i, mean w X i < conditionalDeficit w X) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ mean w X i) ∧
      (∑ i, z i = balance w X) ∧
      (∏ i, (1 - z i / conditionalDeficit w X)) ≤ failure w X := by
  let ε : ℕ → ℝ := fun q => 1 / ((q : ℝ) + 1)
  let wN : ℕ → ι → Fin (n+1) → ℝ :=
    fun q i a => (1 - ε q) * w i a + ε q / (n+1 : ℕ)
  have hεpos (q) : 0 < ε q := by dsimp [ε]; positivity
  have hεle (q) : ε q ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) q]
  have hwN (q i a) : 0 < wN q i a := by
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr (hεle q)) (hw i a))
      (div_pos (hεpos q) (by positivity))
  have hwN1 (q i) : ∑ a, wN q i a = 1 := by
    dsimp [wN]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hw1 i, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hweight (i a) : Tendsto (fun q => wN q i a) atTop (𝓝 (w i a)) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hε).mul_const (w i a)).add
      (hε.div_const ((n+1 : ℕ) : ℝ))
    simpa only [zero_div, sub_zero, one_mul, add_zero] using h
  have hplim : Tendsto (fun q => failure (wN q) X) atTop (𝓝 (failure w X)) :=
    expect_weights_tendsto wN w hweight _
  have hdeflim : Tendsto (fun q => positiveDeficit (wN q) X) atTop (𝓝 (positiveDeficit w X)) :=
    expect_weights_tendsto wN w hweight _
  have hrlim : Tendsto (fun q => conditionalDeficit (wN q) X) atTop (𝓝 (conditionalDeficit w X)) :=
    hdeflim.div hplim (ne_of_gt hp)
  have hmlim (i : ι) : Tendsto (fun q => mean (wN q) X i) atTop (𝓝 (mean w X i)) := by
    unfold mean
    apply tendsto_finsetSum
    intro a _
    exact (hweight i a).mul_const (X i a)
  have hBlim : Tendsto (fun q => balance (wN q) X) atTop (𝓝 (balance w X)) :=
    (hrlim.sub_const 1).add (tendsto_finsetSum Finset.univ (fun i _ => hmlim i))
  apply product_certificate_limit
    (fun q => failure (wN q) X) (fun q => conditionalDeficit (wN q) X)
    (fun q => balance (wN q) X) (fun q i => mean (wN q) X i)
    (failure w X) (conditionalDeficit w X) (balance w X) (mean w X)
    (ne_of_gt hr) hplim hrlim hBlim hmlim
  have hposp : ∀ᶠ q in atTop, 0 < failure (wN q) X :=
    tendsto_const_nhds.eventually_lt hplim hp
  have hposr : ∀ᶠ q in atTop, 0 < conditionalDeficit (wN q) X :=
    tendsto_const_nhds.eventually_lt hrlim hr
  have hstrict : ∀ᶠ q in atTop, ∀ i, mean (wN q) X i < conditionalDeficit (wN q) X := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hmlim i).eventually_lt hrlim (hm i)
  filter_upwards [hposp, hposr, hstrict] with q hpq hrq hmq
  exact finite_product_bound (wN q) X (hwN q) (hwN1 q) hmono hX hpq hrq hmq

end SharpTailMatching.Probability.FiniteProduct
