/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Finite bipartite bounds used by the clique sampling argument. The bound is
proved by a cyclic decomposition into perfect matchings, avoiding any appeal
to an unformalized matching-cover duality theorem.
-/
module

public import SharpTailMatching.Matching.Sparse
public import Mathlib.Algebra.Group.Fin.Basic

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

def IsBipartiteMatching {α β : Type*} (M : Finset (α × β)) : Prop :=
  (M : Set (α × β)).Pairwise fun e f ↦ e.1 ≠ f.1 ∧ e.2 ≠ f.2

def BipartiteMatchingNumberAtMost {α β : Type*} (d : ℕ) (E : Finset (α × β)) : Prop :=
  ∀ M : Finset (α × β), M ⊆ E → IsBipartiteMatching M → M.card ≤ d

theorem exists_maximum_bipartite_matching {α β : Type*} (E : Finset (α × β)) :
    ∃ M : Finset (α × β), M ⊆ E ∧ IsBipartiteMatching M ∧
      BipartiteMatchingNumberAtMost M.card E := by
  classical
  let F := E.powerset.filter IsBipartiteMatching
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [F, IsBipartiteMatching, Set.Pairwise]
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image F Finset.card hF
  have hM' : M ⊆ E ∧ IsBipartiteMatching M := by simpa [F] using hM
  refine ⟨M, hM'.1, hM'.2, ?_⟩
  intro N hNE hN
  exact hmax N (by simp [F, hNE, hN])

section Cyclic

variable {A : Type*} [Fintype A] [DecidableEq A] [AddGroup A]

omit [Fintype A] in
theorem cyclic_fiber_isMatching (E : Finset (A × A)) (π : Equiv.Perm A) (t : A) :
    IsBipartiteMatching (E.filter fun e ↦ π.symm e.2 - e.1 = t) := by
  intro e he f hf hef
  have heq := (Finset.mem_filter.mp he).2
  have hfq := (Finset.mem_filter.mp hf).2
  have hsame : π.symm e.2 - e.1 = π.symm f.2 - f.1 := heq.trans hfq.symm
  constructor
  · intro h
    have h' : π.symm e.2 = π.symm f.2 := by simpa only [h, sub_left_inj] using hsame
    exact hef (Prod.ext h (π.symm.injective h'))
  · intro h
    have h' : e.1 = f.1 := by simpa only [h, sub_right_inj] using hsame
    exact hef (Prod.ext h' h)

theorem cyclic_fibers_card (E : Finset (A × A)) (π : Equiv.Perm A) :
    E.card = ∑ t : A, (E.filter fun e ↦ π.symm e.2 - e.1 = t).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)

theorem bipartite_card_le {E : Finset (A × A)} {d : ℕ}
    (hν : BipartiteMatchingNumberAtMost d E) : E.card ≤ Fintype.card A * d := by
  rw [cyclic_fibers_card E (Equiv.refl A)]
  calc
    (∑ t : A, (E.filter fun e ↦ (Equiv.refl A).symm e.2 - e.1 = t).card) ≤
        ∑ _t : A, d := by
      apply Finset.sum_le_sum
      intro t _
      exact hν _ (Finset.filter_subset _ _) (cyclic_fiber_isMatching E _ t)
    _ = Fintype.card A * d := by simp

def permutationScore (E : Finset (A × A)) (π : Equiv.Perm A) : ℕ :=
  (Finset.univ.filter fun i ↦ (i, π i) ∈ E).card

theorem permutationScore_eq_zero_fiber (E : Finset (A × A)) (π : Equiv.Perm A) :
    permutationScore E π = (E.filter fun e ↦ π.symm e.2 - e.1 = 0).card := by
  apply Finset.card_bij (fun i _ ↦ (i, π i))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, by simp⟩
  · intro i _ j _ h
    exact congrArg Prod.fst h
  · intro e he
    have he' := Finset.mem_filter.mp he
    have hπ : π e.1 = e.2 := by
      have h := sub_eq_zero.mp he'.2
      exact (congrArg π h).symm.trans (by simp)
    refine ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [hπ, Prod.eta] using he'.1
    · exact Prod.ext rfl hπ

/-- Equality in the cyclic bound forces every permutation diagonal to have the
same number of edges. -/
theorem permutationScore_eq_of_bipartite_equality {E : Finset (A × A)} {d : ℕ}
    (hν : BipartiteMatchingNumberAtMost d E) (heq : E.card = Fintype.card A * d)
    (π : Equiv.Perm A) : permutationScore E π = d := by
  rw [permutationScore_eq_zero_fiber]
  have hle : ∀ t ∈ (Finset.univ : Finset A),
      (E.filter fun e ↦ π.symm e.2 - e.1 = t).card ≤ d := by
    intro t _
    exact hν _ (Finset.filter_subset _ _) (cyclic_fiber_isMatching E π t)
  apply (Finset.sum_eq_sum_iff_of_le hle).mp ?_ 0 (Finset.mem_univ _)
  rw [← cyclic_fibers_card E π, heq]
  simp

end Cyclic

section Rectangles

variable {A : Type*} [Fintype A] [DecidableEq A]

def bipartiteEntry (E : Finset (A × A)) (i j : A) : ℕ := if (i, j) ∈ E then 1 else 0

omit [Fintype A] in
@[simp]
theorem bipartiteEntry_eq_one_iff (E : Finset (A × A)) (i j : A) :
    bipartiteEntry E i j = 1 ↔ (i, j) ∈ E := by simp [bipartiteEntry]

theorem permutationScore_eq_sum (E : Finset (A × A)) (π : Equiv.Perm A) :
    permutationScore E π = ∑ i : A, bipartiteEntry E i (π i) := by
  rw [permutationScore, Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

omit [Fintype A] in
theorem exists_perm_map_two {i j a b : A} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ π : Equiv.Perm A, π i = a ∧ π j = b := by
  let σ := Equiv.swap i a
  have hσi : σ i = a := Equiv.swap_apply_left _ _
  have hca : σ j ≠ a := by
    intro h
    exact hij (σ.injective (hσi.trans h.symm))
  refine ⟨σ.trans (Equiv.swap (σ j) b), ?_, ?_⟩
  · rw [Equiv.trans_apply, hσi]
    exact Equiv.swap_apply_of_ne_of_ne hca.symm hab
  · simp only [Equiv.trans_apply, Equiv.swap_apply_left]

theorem sum_split_two (f : A → ℕ) {i j : A} (hij : i ≠ j) :
    (∑ x : A, f x) = f i + f j + ∑ x ∈ (Finset.univ.erase i).erase j, f x := by
  have h₁ := (Finset.univ : Finset A).sum_erase_add f (Finset.mem_univ i)
  have h₂ := (Finset.univ.erase i).sum_erase_add f
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)
  omega

/-- Constant sums on all permutation diagonals imply the four-corner identity. -/
theorem rectangle_identity_of_constant_score {E : Finset (A × A)} {d : ℕ}
    (hconst : ∀ π : Equiv.Perm A, permutationScore E π = d) (i j a b : A) :
    bipartiteEntry E i a + bipartiteEntry E j b =
      bipartiteEntry E i b + bipartiteEntry E j a := by
  by_cases hij : i = j
  · subst j
    omega
  by_cases hab : a = b
  · subst b
    rfl
  obtain ⟨π, hπi, hπj⟩ := exists_perm_map_two hij hab
  let σ := (Equiv.swap i j).trans π
  have hσi : σ i = b := by simp only [σ, Equiv.trans_apply, Equiv.swap_apply_left, hπj]
  have hσj : σ j = a := by simp only [σ, Equiv.trans_apply, Equiv.swap_apply_right, hπi]
  have hrest : (∑ x ∈ (Finset.univ.erase i).erase j, bipartiteEntry E x (π x)) =
      ∑ x ∈ (Finset.univ.erase i).erase j, bipartiteEntry E x (σ x) := by
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxj, hxi⟩ := Finset.mem_erase.mp hx
    have hxi' := (Finset.mem_erase.mp hxi).1
    simp only [σ, Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hxi' hxj]
  have h₁ := sum_split_two (fun x ↦ bipartiteEntry E x (π x)) hij
  have h₂ := sum_split_two (fun x ↦ bipartiteEntry E x (σ x)) hij
  rw [← permutationScore_eq_sum, hconst π, hπi, hπj] at h₁
  rw [← permutationScore_eq_sum, hconst σ, hσi, hσj] at h₂
  omega

/-- A zero-one matrix with constant permutation sums consists of complete rows
or complete columns. This also proves the equality case needed in Section 8. -/
theorem rows_or_columns_of_constant_score {E : Finset (A × A)} {d : ℕ}
    (hconst : ∀ π : Equiv.Perm A, permutationScore E π = d) :
    (∃ S : Finset A, S.card = d ∧ E = S ×ˢ Finset.univ) ∨
      (∃ T : Finset A, T.card = d ∧ E = Finset.univ ×ˢ T) := by
  by_cases hmixed : ∃ i a b : A, (i, a) ∈ E ∧ (i, b) ∉ E
  · obtain ⟨i, a, b, hia, hib⟩ := hmixed
    let T := Finset.univ.filter fun c ↦ (i, c) ∈ E
    have hrows : ∀ r c : A, (r, c) ∈ E ↔ (i, c) ∈ E := by
      intro r c
      have hrect := rectangle_identity_of_constant_score hconst i r a b
      have hra : (r, a) ∈ E := by
        by_contra hnot
        simp only [bipartiteEntry, ite_eq_left hia, ite_eq_right hib, ite_eq_right hnot] at hrect
        omega
      have hrect' := rectangle_identity_of_constant_score hconst i r a c
      have hentry : bipartiteEntry E r c = bipartiteEntry E i c := by
        have hi : bipartiteEntry E i a = 1 := by simp [bipartiteEntry, hia]
        have hr : bipartiteEntry E r a = 1 := by simp [bipartiteEntry, hra]
        omega
      rw [← bipartiteEntry_eq_one_iff E r c, ← bipartiteEntry_eq_one_iff E i c, hentry]
    have hshape : E = Finset.univ ×ˢ T := by
      ext ⟨r, c⟩
      simpa only [Finset.mem_product, Finset.mem_univ, true_and, T,
        Finset.mem_filter] using hrows r c
    have hcard : T.card = d := by
      have hid := hconst (Equiv.refl A)
      rw [hshape] at hid
      simpa [permutationScore] using hid
    exact Or.inr ⟨T, hcard, hshape⟩
  · let S := Finset.univ.filter fun r ↦ ∃ c, (r, c) ∈ E
    have hshape : E = S ×ˢ Finset.univ := by
      ext ⟨r, c⟩
      simp only [Finset.mem_product, Finset.mem_univ, and_true, S,
        Finset.mem_filter, true_and]
      constructor
      · intro h
        exact ⟨c, h⟩
      · rintro ⟨a, ha⟩
        by_contra hc
        exact hmixed ⟨r, a, c, ha, hc⟩
    have hcard : S.card = d := by
      have hid := hconst (Equiv.refl A)
      rw [hshape] at hid
      simpa [permutationScore] using hid
    exact Or.inl ⟨S, hcard, hshape⟩

omit [DecidableEq A] in
theorem partial_set_not_constant_membership {S T : Finset A} {d : ℕ}
    (hS : S.card = d) (hd : 0 < d) (hdA : d < Fintype.card A) (j : A) :
    ¬ (∀ i : A, i ∈ S ↔ j ∈ T) := by
  intro h
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨i', _, hi'⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := S) (t := Finset.univ) (by simpa only [Finset.card_univ, hS] using hdA)
  exact hi' ((h i').mpr ((h i).mp hi))

/-- For extremal bipartite matrices with `0 < d < N`, all but one column
determine the last column. This permits a direct equality proof by completing
any two inside blocks with the same collection of disjoint blocks. -/
theorem rows_columns_column_rigidity {E F : Finset (A × A)} {d : ℕ}
    (hE : (∃ S : Finset A, S.card = d ∧ E = S ×ˢ Finset.univ) ∨
      (∃ S : Finset A, S.card = d ∧ E = Finset.univ ×ˢ S))
    (hF : (∃ T : Finset A, T.card = d ∧ F = T ×ˢ Finset.univ) ∨
      (∃ T : Finset A, T.card = d ∧ F = Finset.univ ×ˢ T))
    (hd : 0 < d) (hdA : d < Fintype.card A) (c : A)
    (hsame : ∀ i j, j ≠ c → ((i, j) ∈ E ↔ (i, j) ∈ F)) :
    ∀ i, (i, c) ∈ E ↔ (i, c) ∈ F := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {c}) (t := Finset.univ) (by simp only [Finset.card_singleton, Finset.card_univ]; omega)
  have hjc : j ≠ c := by simpa only [Finset.mem_singleton] using hj
  rcases hE with ⟨S, hScard, rfl⟩ | ⟨S, hScard, rfl⟩
  · rcases hF with ⟨T, hTcard, rfl⟩ | ⟨T, hTcard, rfl⟩
    · intro i
      simpa only [Finset.mem_product, Finset.mem_univ, and_true] using hsame i j hjc
    · exfalso
      apply partial_set_not_constant_membership hScard hd hdA j
      intro i
      simpa only [Finset.mem_product, Finset.mem_univ, and_true, true_and] using hsame i j hjc
  · rcases hF with ⟨T, hTcard, rfl⟩ | ⟨T, hTcard, rfl⟩
    · exfalso
      apply partial_set_not_constant_membership hTcard hd hdA j
      intro i
      simpa only [Finset.mem_product, Finset.mem_univ, and_true, true_and] using
        (hsame i j hjc).symm
    · have herase : S.erase c = T.erase c := by
        ext a
        by_cases hac : a = c
        · subst a
          simp
        · have h := hsame c a hac
          simp only [Finset.mem_erase]
          apply and_congr_right
          intro _
          simpa only [Finset.mem_product, Finset.mem_univ, true_and] using h
      have hcmem : c ∈ S ↔ c ∈ T := by
        have hcard := congrArg Finset.card herase
        by_cases hcS : c ∈ S <;> by_cases hcT : c ∈ T
        · exact iff_of_true hcS hcT
        · rw [Finset.card_erase_of_mem hcS, Finset.erase_eq_of_notMem hcT, hScard, hTcard] at hcard
          omega
        · rw [Finset.erase_eq_of_notMem hcS, Finset.card_erase_of_mem hcT, hScard, hTcard] at hcard
          omega
        · exact iff_of_false hcS hcT
      intro i
      simpa only [Finset.mem_product, Finset.mem_univ, true_and] using hcmem

end Rectangles

theorem bipartite_equality_rows_or_columns {A : Type*} [Fintype A] [DecidableEq A]
    [AddGroup A] {E : Finset (A × A)} {d : ℕ}
    (hν : BipartiteMatchingNumberAtMost d E) (heq : E.card = Fintype.card A * d) :
    (∃ S : Finset A, S.card = d ∧ E = S ×ˢ Finset.univ) ∨
      (∃ T : Finset A, T.card = d ∧ E = Finset.univ ×ˢ T) :=
  rows_or_columns_of_constant_score (permutationScore_eq_of_bipartite_equality hν heq)

end SharpTailMatching.Matching
