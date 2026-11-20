module

public import SharpTailMatching.Probability.FiniteProduct

/-!
# Selected caps for finite independent distributions

The atom weights remain fixed. Each coordinate is an ordered finite list of
values, and capping preserves this order even when values coalesce.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability.FiniteProduct

def extendLast {n : ℕ} (f : Fin (n+1) → ℝ) (q : ℕ) : ℝ :=
  f ⟨min q n, Nat.lt_succ_of_le (min_le_right _ _)⟩

@[simp] theorem extendLast_coe {n : ℕ} (f : Fin (n+1) → ℝ) (a : Fin (n+1)) :
    extendLast f a = f a := by
  unfold extendLast
  congr 1
  ext
  exact min_eq_left (Nat.le_of_lt_succ a.isLt)

theorem extendLast_monotone {n : ℕ} (f : Fin (n+1) → ℝ) (hf : Monotone f) :
    Monotone (extendLast f) := by
  intro a b hab
  apply hf
  exact min_le_min_right n hab

theorem sum_range_extendLast {n : ℕ} (f : Fin (n+1) → ℝ) :
    (∑ a ∈ Finset.range (n+1), extendLast f a) = ∑ a, f a := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [extendLast_coe]

theorem sum_cap_kernel_nonneg (n q : ℕ) (hqn : q < n)
    (x w : ℕ → ℝ) (K : ℝ → ℝ) (hx : Monotone x)
    (hw : ∀ a ≤ n, 0 ≤ w a)
    (hprefix : 0 ≤ ∑ a ∈ Finset.range (q+1), w a * K (x a))
    (hK : 0 ≤ K (x q)) :
    0 ≤ ∑ a ∈ Finset.range (n+1), w a * K (min (x a) (x q)) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show q+1 ≤ n+1 by omega)]
  have hfirst :
      (∑ a ∈ Finset.range (q+1), w a * K (min (x a) (x q))) =
        ∑ a ∈ Finset.range (q+1), w a * K (x a) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [min_eq_left (hx (by have := Finset.mem_range.mp ha; omega))]
  rw [hfirst]
  apply add_nonneg hprefix
  apply Finset.sum_nonneg
  intro a ha
  have ha' := Finset.mem_Ico.mp ha
  rw [min_eq_right (hx (by omega))]
  exact mul_nonneg (hw a (by omega)) hK

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

/-- A nonconstant ordered coordinate has distinct endpoint values. -/
theorem endpoints_strict_of_nonconstant (x : Fin (n+1) → ℝ) (hx : Monotone x)
    (hnc : ¬ ∃ c : ℝ, x = fun _ => c) : x 0 < x (Fin.last n) := by
  apply lt_of_le_of_ne (hx (Fin.zero_le _))
  intro heq
  apply hnc
  refine ⟨x 0, funext fun a => ?_⟩
  exact le_antisymm ((hx (Fin.le_last a)).trans_eq heq.symm) (hx (Fin.zero_le a))

/-- The covariance/Abel choice supplies an actual cap strictly below the
largest value, with nondecreasing conditional deficit. This statement uses
only the original product weights and finite sums. -/
theorem exists_selected_cap (w X : ι → Fin (n+1) → ℝ)
    (hw : ∀ i a, 0 < w i a) (hX : ∀ i, Monotone (X i)) (r : ℝ)
    (hr : positiveDeficit w X = failure w X * r)
    (hnonconstant : ∃ i, ¬ ∃ c : ℝ, X i = fun _ => c) :
    ∃ (i : ι) (q : Fin (n+1)), X i q < X i (Fin.last n) ∧
      0 ≤ expect w (fun ω => centeredFailure r (total (cap X i (X i q)) ω)) := by
  obtain ⟨i, hnc, hmoment⟩ := exists_nonconstant_coordinate_nonpos_moment
    w X (fun i a => (hw i a).le) r hr hnonconstant
  let xN := extendLast (X i)
  let wN := extendLast (w i)
  let K : ℝ → ℝ := coordinateKernel w X r i
  have hxN : Monotone xN := extendLast_monotone (X i) (hX i)
  have hxstrict : xN 0 < xN n := by
    simpa [xN, extendLast, Fin.last] using endpoints_strict_of_nonconstant (X i) (hX i) hnc
  have hwN (a : ℕ) (_ : a ≤ n) : 0 < wN a := hw i _
  have htotal : (∑ a ∈ Finset.range (n+1), wN a * K (xN a)) = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [wN, xN, extendLast_coe, K]
    rw [← centeredFailure_split, expect_centeredFailure w X r hr]
  have hfirstmoment :
      (∑ a ∈ Finset.range (n+1), xN a * (wN a * K (xN a))) ≤ 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [wN, xN, extendLast_coe, K]
    rwa [← centered_moment_split]
  obtain ⟨q, hqn, hxq, hprefix, _, hK⟩ :=
    exists_cap_index_of_monotone n xN wN (fun a => K (xN a)) hxN hxstrict
      hwN htotal hfirstmoment
  let qF : Fin (n+1) := ⟨q, by omega⟩
  have hxqF : xN q = X i qF := by
    change extendLast (X i) qF = _
    exact extendLast_coe _ _
  refine ⟨i, qF, ?_, ?_⟩
  · simpa [hxqF, xN, extendLast, Fin.last] using hxq
  · rw [cap_centeredFailure_split]
    have hcap := sum_cap_kernel_nonneg n q hqn xN wN K hxN
      (fun a ha => (hwN a ha).le) hprefix hK
    rw [← Fin.sum_univ_eq_sum_range] at hcap
    simpa only [wN, xN, extendLast_coe, hxqF, K] using hcap

omit [Fintype ι] [DecidableEq ι] in
theorem mean_nonneg {α : Type*} [Fintype α] (w X : ι → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hX : ∀ i a, 0 ≤ X i a) (i : ι) :
    0 ≤ mean w X i := by
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (hw i a) (hX i a)

omit [Fintype ι] in
theorem mean_cap_ne {α : Type*} [Fintype α] (w X : ι → α → ℝ)
    (i j : ι) (τ : ℝ) (hji : j ≠ i) :
    mean w (cap X i τ) j = mean w X j := by
  simp only [mean, cap_ne X i τ j hji]

theorem sum_mean_cap {α : Type*} [Fintype α] (w X : ι → α → ℝ)
    (i : ι) (τ : ℝ) :
    (∑ j, mean w (cap X i τ) j) = (∑ j, mean w X j) - meanLoss w X i τ := by
  have hdiff :
      (∑ j, (mean w X j - mean w (cap X i τ) j)) = meanLoss w X i τ := by
    have heq (j : ι) : mean w X j - mean w (cap X i τ) j =
        if j = i then meanLoss w X i τ else 0 := by
      by_cases hji : j = i
      · subst j
        rw [mean_cap]
        simp
      · rw [mean_cap_ne w X i j τ hji]
        simp [hji]
    simp only [heq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_sub_distrib] at hdiff
  linarith

theorem conditionalDeficit_relation {α : Type*} [Fintype α]
    (w X : ι → α → ℝ) (hp : 0 < failure w X) :
    positiveDeficit w X = failure w X * conditionalDeficit w X := by
  unfold conditionalDeficit
  field_simp

def balance {α : Type*} [Fintype α] (w X : ι → α → ℝ) : ℝ :=
  conditionalDeficit w X - 1 + ∑ i, mean w X i

/-- Number of distinct values remaining across all coordinates. -/
def supportRank (X : ι → Fin (n+1) → ℝ) : ℕ :=
  ∑ i, (Finset.univ.image (X i)).card

theorem card_range_cap_lt (x : Fin (n+1) → ℝ) (q : Fin (n+1))
    (hq : x q < x (Fin.last n)) :
    (Finset.univ.image (fun a => min (x a) (x q))).card <
      (Finset.univ.image x).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro y hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hy
    rcases le_total (x a) (x q) with h | h
    · rw [min_eq_left h]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · rw [min_eq_right h]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩
  · intro heq
    have hm : x (Fin.last n) ∈ Finset.univ.image (fun a => min (x a) (x q)) := by
      rw [heq]
      exact Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, rfl⟩
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
    have hle := min_le_right (x a) (x q)
    rw [ha] at hle
    exact hq.not_ge hle

theorem supportRank_cap_lt (X : ι → Fin (n+1) → ℝ) (i : ι) (q : Fin (n+1))
    (hq : X i q < X i (Fin.last n)) :
    supportRank (cap X i (X i q)) < supportRank X := by
  classical
  have hi : (Finset.univ.image (cap X i (X i q) i)).card <
      (Finset.univ.image (X i)).card := by
    simpa only [cap, Function.update_self] using card_range_cap_lt (X i) q hq
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hji : j = i
    · subst j
      exact hi.le
    · rw [cap_ne X i (X i q) j hji]
  · exact ⟨i, Finset.mem_univ i, hi⟩

structure OrderedState (ι : Type*) (n : ℕ) where
  values : ι → Fin (n+1) → ℝ
  monotone : ∀ i, Monotone (values i)
  nonneg : ∀ i a, 0 ≤ values i a

def OrderedState.capped (s : OrderedState ι n) (i : ι) (q : Fin (n+1)) :
    OrderedState ι n where
  values := cap s.values i (s.values i q)
  monotone := by
    intro j a b hab
    by_cases hji : j = i
    · subst j
      simpa only [cap_same] using min_le_min_right (s.values i q) (s.monotone i hab)
    · simpa only [cap_ne s.values i (s.values i q) j hji] using s.monotone j hab
  nonneg := by
    intro j a
    by_cases hji : j = i
    · subst j
      simpa only [cap_same] using le_min (s.nonneg i a) (s.nonneg i q)
    · simpa only [cap_ne s.values i (s.values i q) j hji] using s.nonneg j a

/-- Once every coordinate is constant, positive failure probability forces
failure with probability one and the balance is zero. -/
theorem constant_state_terminal (w X : ι → Fin (n+1) → ℝ)
    (hw1 : ∀ i, ∑ a, w i a = 1) (hp : 0 < failure w X)
    (hconstant : ∀ i, ∃ c : ℝ, X i = fun _ => c) :
    failure w X = 1 ∧ balance w X = 0 := by
  classical
  choose c hc using hconstant
  have htotal (ω : ι → Fin (n+1)) : total X ω = ∑ i, c i := by
    simp only [total, hc]
  have hpval : failure w X = failureIndicator (∑ i, c i) := by
    simp only [failure, htotal, expect_const w hw1]
  have hsum : (∑ i, c i) < 1 := by
    by_contra h
    simp only [hpval, failureIndicator, ite_eq_right h] at hp
    exact lt_irrefl 0 hp
  have hpone : failure w X = 1 := by
    rw [hpval, failureIndicator, ite_eq_left hsum]
  have hdef : positiveDeficit w X = 1 - ∑ i, c i := by
    simp only [positiveDeficit, htotal, expect_const w hw1,
      max_eq_left (by linarith : 0 ≤ 1 - ∑ i, c i)]
  have hm (i : ι) : mean w X i = c i := by
    simp only [mean, hc, ← Finset.sum_mul, hw1 i, one_mul]
  refine ⟨hpone, ?_⟩
  simp only [balance, conditionalDeficit, hpone, hdef, div_one, hm]
  ring

/-- Every nonterminal ordered state admits a cap that decreases its support
rank and satisfies all numerical hypotheses of the product induction. -/
theorem ordered_state_cap_step (w : ι → Fin (n+1) → ℝ)
    (hw : ∀ i a, 0 < w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (s : OrderedState ι n) (hp : 0 < failure w s.values)
    (hr : 0 < conditionalDeficit w s.values)
    (hnc : ∃ i, ¬ ∃ c : ℝ, s.values i = fun _ => c) :
    ∃ (t : OrderedState ι n) (i : ι) (ζ : ℝ),
      supportRank t.values < supportRank s.values ∧
      failure w s.values ≤ failure w t.values ∧
      conditionalDeficit w s.values ≤ conditionalDeficit w t.values ∧ 0 ≤ ζ ∧
      (∀ j, 0 ≤ mean w t.values j) ∧
      (∀ j, mean w t.values j + (if j = i then ζ else 0) ≤ mean w s.values j) ∧
      balance w s.values = balance w t.values + ζ ∧
      failure w t.values * (1 - ζ / conditionalDeficit w s.values) ≤ failure w s.values := by
  obtain ⟨i, q, hq, hcenter⟩ := exists_selected_cap w s.values hw s.monotone
    (conditionalDeficit w s.values) (conditionalDeficit_relation w s.values hp) hnc
  let t := s.capped i q
  have ht : t.values = cap s.values i (s.values i q) := rfl
  have hpp : failure w s.values ≤ failure w t.values := by
    rw [ht]
    exact failure_mono_cap w s.values (fun i a => (hw i a).le) i (s.values i q)
  have hp' : 0 < failure w t.values := hp.trans_le hpp
  have hrr : conditionalDeficit w s.values ≤ conditionalDeficit w t.values := by
    rw [expect_centeredFailure_eq] at hcenter
    change 0 ≤ positiveDeficit w t.values - conditionalDeficit w s.values * failure w t.values
      at hcenter
    rw [conditionalDeficit_relation w t.values hp'] at hcenter
    nlinarith
  let d := meanLoss w s.values i (s.values i q)
  have hexcess :
      failure w t.values * conditionalDeficit w t.values -
        failure w s.values * conditionalDeficit w s.values ≤ failure w t.values * d := by
    rw [← conditionalDeficit_relation w t.values hp',
      ← conditionalDeficit_relation w s.values hp]
    exact positiveDeficit_cap_sub_le w s.values (fun i a => (hw i a).le) hw1 i (s.values i q)
  let ζ := d - (conditionalDeficit w t.values - conditionalDeficit w s.values)
  have hstep := cap_step_estimate (failure w s.values) (failure w t.values)
    (conditionalDeficit w s.values) (conditionalDeficit w t.values) d hp hpp hr hrr hexcess
  change 0 ≤ ζ ∧ ζ ≤ d ∧ _ ∧ _ at hstep
  refine ⟨t, i, ζ, ?_, hpp, hrr, hstep.1, ?_, ?_, ?_, hstep.2.2.2⟩
  · exact supportRank_cap_lt s.values i q hq
  · intro j
    exact mean_nonneg w t.values (fun i a => (hw i a).le) t.nonneg j
  · intro j
    by_cases hji : j = i
    · subst j
      rw [ht, mean_cap, ite_eq_left (Eq.refl i)]
      change mean w s.values i - d + ζ ≤ mean w s.values i
      linarith [hstep.2.1]
    · rw [ht, mean_cap_ne w s.values i j (s.values i q) hji, ite_eq_right hji, add_zero]
  · unfold balance
    rw [ht, sum_mean_cap]
    dsimp [ζ, d]
    rw [ht]
    ring

/-- Product bound for independent nonnegative finite distributions represented
by ordered atom lists with positive weights. All cap choices and termination
are constructed in this theorem; there is no cap-existence hypothesis. -/
theorem finite_product_bound (w X : ι → Fin (n+1) → ℝ)
    (hw : ∀ i a, 0 < w i a) (hw1 : ∀ i, ∑ a, w i a = 1)
    (hmono : ∀ i, Monotone (X i)) (hX : ∀ i a, 0 ≤ X i a)
    (hp : 0 < failure w X) (hr : 0 < conditionalDeficit w X)
    (hm : ∀ i, mean w X i < conditionalDeficit w X) :
    ∃ z : ι → ℝ, (∀ i, 0 ≤ z i ∧ z i ≤ mean w X i) ∧
      (∑ i, z i = balance w X) ∧
      (∏ i, (1 - z i / conditionalDeficit w X)) ≤ failure w X := by
  classical
  let s : OrderedState ι n := ⟨X, hmono, hX⟩
  apply product_bound_of_terminating_caps
    (fun t : OrderedState ι n => supportRank t.values)
    (fun t => failure w t.values) (fun t => conditionalDeficit w t.values)
    (fun t => balance w t.values) (fun t => mean w t.values) _ s hp hr
    (fun i => ⟨mean_nonneg w X (fun i a => (hw i a).le) hX i, hm i⟩)
  intro t hpt hrt _
  by_cases hconstant : ∀ i, ∃ c : ℝ, t.values i = fun _ => c
  · exact Or.inl (constant_state_terminal w t.values hw1 hpt hconstant)
  · right
    push Not at hconstant
    exact ordered_state_cap_step w hw hw1 t hpt hrt (by simpa using hconstant)

end SharpTailMatching.Probability.FiniteProduct
