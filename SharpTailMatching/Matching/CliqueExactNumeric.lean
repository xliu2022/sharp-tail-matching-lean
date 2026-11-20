/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The exact local clique theorem with numerical assumptions discharged. The
temporary group structure used for cyclic sampling is transported onto the
finite outside vertex set, and is absent from the theorem statement.
-/
module

public import SharpTailMatching.Matching.CliqueRigidity
public import SharpTailMatching.Matching.CliqueWeights
public import Mathlib.Algebra.Group.TransferInstance

@[expose] public section

namespace SharpTailMatching.Matching

theorem clique_block_capacities {k u N : ℕ} (hk : 2 ≤ k)
    (hN : 20 * (k - 1) ≤ N) (hcapacity : 3 * (k - 1) * N ≤ 2 * u) :
    (k - 1) * (N + 1) ≤ u ∧
      ∀ j ∈ Finset.Icc 2 k, (k - 1) * N + (k - j) * (N / j) ≤ u := by
  have hN₂ : 2 ≤ N := by omega
  have hrN := Nat.mul_le_mul_left (k - 1) hN₂
  constructor
  · nlinarith only [hrN, hcapacity]
  · intro j hj
    obtain ⟨hj₂, hjk⟩ := Finset.mem_Icc.mp hj
    have hdiv : j * (N / j) ≤ N := Nat.mul_div_le N j
    have htwo : 2 * (N / j) ≤ N := (Nat.mul_le_mul_right (N / j) hj₂).trans hdiv
    have hkj : k - j ≤ k - 1 := by omega
    have hmul := Nat.mul_le_mul hkj htwo
    nlinarith only [hmul, hcapacity]

variable {A W : Type*} [DecidableEq A] [DecidableEq W] [Fintype A] [Fintype W]

/-- Exact bound and clique rigidity under explicit integer capacities. No
probabilistic, structural, or numerical conclusion is included as a hypothesis. -/
theorem local_clique_exact_of_capacity {k s : ℕ}
    {H : Finset (Finset (A ⊕ W))}
    (hk : 2 ≤ k) (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H)
    (hN : 20 * (k - 1) ≤ Fintype.card W)
    (hcapacity : 3 * (k - 1) * Fintype.card W ≤ 2 * Fintype.card A)
    (hd : 0 < k * (s + 1) - 1 - Fintype.card A)
    (hdN : k * (s + 1) - 1 - Fintype.card A < Fintype.card W) :
    H.card ≤ (k * (s + 1) - 1).choose k ∧
      (H.card = (k * (s + 1) - 1).choose k ↔
        ∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
          H = cliqueFamily k ((Finset.univ : Finset A).disjSum T)) := by
  classical
  have hNp : 0 < Fintype.card W := by omega
  have : NeZero (Fintype.card W) := ⟨hNp.ne'⟩
  let : AddGroup W := (Fintype.equivFin W).addGroup
  obtain ⟨hcommon, hpack⟩ := clique_block_capacities hk hN hcapacity
  have hweight := cliqueWeightSum_lt_choose hk hN hcapacity
  have hsum : Fintype.card A + (k * (s + 1) - 1 - Fintype.card A) = k * (s + 1) - 1 := by
    omega
  have hbound := clique_bound_and_equality_of_weight hk hu hν hQ (by omega) hd hdN
    hcommon hpack hweight
  simpa only [hsum] using hbound

/-- An explicit eventual threshold for the genuine-clique lemma. The integer
quotient is exactly `floor((k - 1/6)s)`. -/
theorem local_clique_range_capacities {k s u N : ℕ}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ u + N)
    (hupper : 2 * (u + N) ≤ (2 * k + 1) * s)
    (hu : u = ((6 * k - 1) * s) / 6) :
    20 * (k - 1) ≤ N ∧ 3 * (k - 1) * N ≤ 2 * u ∧
      0 < k * (s + 1) - 1 - u ∧ k * (s + 1) - 1 - u < N := by
  have hk₁ : k - 1 + 1 = k := by omega
  have hk₆ : 6 * k - 1 + 1 = 6 * k := by omega
  have hfloor₁ : 6 * u ≤ (6 * k - 1) * s := by
    rw [hu]
    exact Nat.mul_div_le _ _
  have hfloor₂ : (6 * k - 1) * s < 6 * (u + 1) := by
    rw [hu]
    exact Nat.lt_mul_div_succ _ (by omega)
  have hN : 20 * (k - 1) ≤ N := by
    nlinarith only [hs, hlower, hfloor₁, hk₁, hk₆]
  have hNupper : 3 * N ≤ 2 * s + 3 := by
    nlinarith only [hupper, hfloor₂, hk₆]
  have hcapacity : 3 * (k - 1) * N ≤ 2 * u := by
    have hmul := Nat.mul_le_mul_left (k - 1) hNupper
    nlinarith only [hmul, hfloor₂, hs, hk₁, hk₆]
  have hd : 0 < k * (s + 1) - 1 - u := by
    have hstrict : u + 1 < k * (s + 1) := by
      nlinarith only [hfloor₁, hs, hk, hk₆]
    omega
  have hdN : k * (s + 1) - 1 - u < N := by omega
  exact ⟨hN, hcapacity, hd, hdN⟩

/-- Manuscript Lemma 8.3, including its equality characterization, on an
explicit inside/outside partition. The uniform threshold `120k` is sufficient. -/
theorem local_clique_exact_sum {k s : ℕ} {H : Finset (Finset (A ⊕ W))}
    (hk : 3 ≤ k) (hs : 120 * k ≤ s)
    (hlower : k * (s + 1) ≤ Fintype.card A + Fintype.card W)
    (hupper : 2 * (Fintype.card A + Fintype.card W) ≤ (2 * k + 1) * s)
    (hcardA : Fintype.card A = ((6 * k - 1) * s) / 6)
    (hu : IsUniform k H) (hν : MatchingNumberAtMost s H)
    (hQ : cliqueFamily k ((Finset.univ : Finset A).map Function.Embedding.inl) ⊆ H) :
    H.card ≤ (k * (s + 1) - 1).choose k ∧
      (H.card = (k * (s + 1) - 1).choose k ↔
        ∃ T : Finset W, T.card = k * (s + 1) - 1 - Fintype.card A ∧
          H = cliqueFamily k ((Finset.univ : Finset A).disjSum T)) := by
  obtain ⟨hN, hcapacity, hd, hdN⟩ := local_clique_range_capacities hk hs hlower hupper hcardA
  exact local_clique_exact_of_capacity (by omega) hu hν hQ hN hcapacity hd hdN

end SharpTailMatching.Matching
