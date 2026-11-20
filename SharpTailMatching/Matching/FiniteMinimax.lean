/-
Copyright (c) 2026 Xizhi Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

A finite matrix minimax theorem derived from Mathlib's proved Sion theorem.
This is the analytic foundation for finite fractional matching-cover duality.
-/
module

public import Mathlib.Topology.Sion
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

open scoped BigOperators

namespace SharpTailMatching.Matching

def probabilitySimplex (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}

theorem probabilitySimplex_single {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    Pi.single i 1 ∈ probabilitySimplex I := by
  constructor
  · intro j
    by_cases hij : j = i <;> simp [hij]
  · simp

theorem probabilitySimplex_nonempty (I : Type*) [Fintype I] [Nonempty I] :
    (probabilitySimplex I).Nonempty := by
  classical
  exact ⟨_, probabilitySimplex_single (Classical.arbitrary I)⟩

theorem probabilitySimplex_convex (I : Type*) [Fintype I] : Convex ℝ (probabilitySimplex I) := by
  intro p hp q hq a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hp.1 i)) (mul_nonneg hb (hq.1 i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.2, hq.2, mul_one, hab]

theorem probabilitySimplex_isClosed (I : Type*) [Fintype I] : IsClosed (probabilitySimplex I) := by
  have heq : probabilitySimplex I =
      (⋂ i : I, {p : I → ℝ | 0 ≤ p i}) ∩ {p : I → ℝ | ∑ i, p i = 1} := by
    ext p
    simp only [probabilitySimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (isClosed_iInter fun i ↦ isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (by fun_prop) continuous_const)

theorem probabilitySimplex_isCompact (I : Type*) [Fintype I] : IsCompact (probabilitySimplex I) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : I → ℝ) 1)).of_isClosed_subset
    (probabilitySimplex_isClosed I)
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro i
  change p i ≤ (1 : ℝ)
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset I)) ↦ hp.1 j)
    (Finset.mem_univ i)
  simpa only [hp.2] using h

noncomputable def matrixPayoff {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℝ) (p : I → ℝ) (q : J → ℝ) : ℝ :=
  ∑ i, p i * ∑ j, a i j * q j

noncomputable def matrixPayoffLeft {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℝ) (q : J → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun p := matrixPayoff a p q
  map_add' p p' := by simp [matrixPayoff, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [matrixPayoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, ← Finset.mul_sum]

noncomputable def matrixPayoffRight {I J : Type*} [Fintype I] [Fintype J]
    (a : I → J → ℝ) (p : I → ℝ) : (J → ℝ) →ₗ[ℝ] ℝ where
  toFun q := matrixPayoff a p q
  map_add' q q' := by simp [matrixPayoff, mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [matrixPayoff, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm _ c, ← Finset.mul_sum, mul_left_comm _ c]
    rw [← Finset.mul_sum]

theorem matrixPayoff_single_left {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (a : I → J → ℝ) (q : J → ℝ) (i : I) :
    matrixPayoff a (Pi.single i 1) q = ∑ j, a i j * q j := by
  simp [matrixPayoff, Pi.single_apply]

theorem matrixPayoff_single_right {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (a : I → J → ℝ) (p : I → ℝ) (j : J) :
    matrixPayoff a p (Pi.single j 1) = ∑ i, p i * a i j := by
  simp [matrixPayoff, Pi.single_apply]

/-- Finite minimax in the form needed for packing-cover duality. The two
probability vectors are actual optimizers, not assumed optimal solutions. -/
theorem exists_matrix_minimax {I J : Type*} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (a : I → J → ℝ) :
    ∃ p ∈ probabilitySimplex I, ∃ q ∈ probabilitySimplex J,
      (∀ j, (∑ i, p i * a i j) ≤ matrixPayoff a p q) ∧
      ∀ i, matrixPayoff a p q ≤ ∑ j, a i j * q j := by
  classical
  have hleft : ∀ q ∈ probabilitySimplex J,
      LowerSemicontinuousOn (fun p ↦ matrixPayoff a p q) (probabilitySimplex I) := by
    intro q _
    exact (show Continuous (fun p ↦ matrixPayoff a p q) by
      unfold matrixPayoff; fun_prop).continuousOn.lowerSemicontinuousOn
  have hright : ∀ p ∈ probabilitySimplex I,
      UpperSemicontinuousOn (fun q ↦ matrixPayoff a p q) (probabilitySimplex J) := by
    intro p _
    exact (show Continuous (fun q ↦ matrixPayoff a p q) by
      unfold matrixPayoff; fun_prop).continuousOn.upperSemicontinuousOn
  obtain ⟨p, hp, q, hq, h⟩ := Sion.exists_isSaddlePointOn
    (probabilitySimplex_nonempty I) (probabilitySimplex_convex I) (probabilitySimplex_isCompact I)
    hleft (fun q _ ↦ ((matrixPayoffLeft a q).convexOn (probabilitySimplex_convex I)).quasiconvexOn)
    (probabilitySimplex_convex J) (probabilitySimplex_nonempty J) (probabilitySimplex_isCompact J)
    hright (fun p _ ↦ ((matrixPayoffRight a p).concaveOn (probabilitySimplex_convex J)).quasiconcaveOn)
  refine ⟨p, hp, q, hq, ?_, ?_⟩
  · intro j
    simpa only [matrixPayoff_single_right] using h p hp (Pi.single j 1) (probabilitySimplex_single j)
  · intro i
    simpa only [matrixPayoff_single_left] using h (Pi.single i 1) (probabilitySimplex_single i) q hq

end SharpTailMatching.Matching
