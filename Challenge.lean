module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Sharp i.i.d. tails and large hypergraph matchings

This independent statement surface records the complete intended main results of
Chi--Sun--Wang, following Theorems 1.1 (matching) and 1.2 (probability) of the
supplied expanded proof. The `sorry` terms below are deliberate Challenge holes;
they are not proofs and do not establish completion of the formalization.

The distribution is an arbitrary Borel probability measure on `ℝ≥0`, with no
finite-support assumption. Its mean is a nonnegative extended integral, so an
infinite expectation cannot satisfy a finite-mean hypothesis. The probability
event uses the finite product of the same measure, encoding independence and
identical distribution directly. All equality classes, including boundary
parameters, are stated below.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace SharpTailMatching

/-- The nonnegative extended expectation of a law on the nonnegative reals. -/
def mean (μ : ProbabilityMeasure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ t : ℝ≥0, (t : ℝ≥0∞) ∂(μ : Measure ℝ≥0)

/-- The probability that the sum of `k` independent samples from `μ` is at least
one. The product measure is a probability measure, so `toReal` loses no mass. -/
def tailProbability (k : ℕ) (μ : ProbabilityMeasure ℝ≥0) : ℝ :=
  ((Measure.pi (fun _ : Fin k => (μ : Measure ℝ≥0)))
    {z : Fin k → ℝ≥0 | 1 ≤ ∑ i, z i}).toReal

/-- The measure `(1-x) δ₀ + x δ₁`. It is a probability measure for `0 ≤ x ≤ 1`,
which is the range in every theorem that identifies an extremizer with it. -/
def unitBernoulliMeasure (x : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1 - x) • Measure.dirac 0 +
    ENNReal.ofReal x • Measure.dirac 1

/-- The measure `(1-kx) δ₀ + kx δ_(1/k)`. It is a probability measure for positive
`k` and `0 ≤ x ≤ 1/k`, the range used in the equality theorem. -/
def smallBernoulliMeasure (k : ℕ) (x : ℝ) : Measure ℝ≥0 :=
  ENNReal.ofReal (1 - (k : ℝ) * x) • Measure.dirac 0 +
    ENNReal.ofReal ((k : ℝ) * x) • Measure.dirac ((k : ℝ≥0)⁻¹)

/-- The claimed optimal success probability, with value one once the allowed
mean is at least `1/k`. Theorems below assume `k ≥ 1` and `x ≥ 0`. -/
def sharpTailValue (k : ℕ) (x : ℝ) : ℝ :=
  if x ≤ (k : ℝ)⁻¹ then
    max (1 - (1 - x) ^ k) (((k : ℝ) * x) ^ k)
  else 1

/-- Every feasible law satisfies the sharp upper bound. -/
theorem sharp_tail_bound (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ ≤ sharpTailValue k x := by
  sorry

/-- The sharp upper bound is attained for every permitted parameter. Together
with `sharp_tail_bound`, this states the exact optimization value without any
convention about the supremum of an empty or unbounded set. -/
theorem sharp_tail_attained (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : 0 ≤ x) :
    ∃ μ : ProbabilityMeasure ℝ≥0,
      mean μ ≤ ENNReal.ofReal x ∧ tailProbability k μ = sharpTailValue k x := by
  sorry

/-- For `k ≥ 2` there is exactly one positive crossing below `1/k`. -/
theorem critical_mean_exists_unique (k : ℕ) (hk : 2 ≤ k) :
    ∃! β : ℝ, 0 < β ∧ β < (k : ℝ)⁻¹ ∧
      1 - (1 - β) ^ k = ((k : ℝ) * β) ^ k := by
  sorry

/-- The complete maximizing-law classification in the nontrivial interval.
Below the crossing only the unit Bernoulli law maximizes; above it only the
small Bernoulli law maximizes; at the crossing precisely these two do. The
endpoint `x = 1/k` is included and gives the point mass at `1/k`. -/
theorem sharp_tail_equality (k : ℕ) (hk : 2 ≤ k)
    (β : ℝ) (hβpos : 0 < β) (hβlt : β < (k : ℝ)⁻¹)
    (hβcross : 1 - (1 - β) ^ k = ((k : ℝ) * β) ^ k)
    (x : ℝ) (hx : 0 < x) (hxle : x ≤ (k : ℝ)⁻¹)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability k μ = sharpTailValue k x ↔
      (x < β ∧ (μ : Measure ℝ≥0) = unitBernoulliMeasure x) ∨
      (x = β ∧ ((μ : Measure ℝ≥0) = unitBernoulliMeasure x ∨
        (μ : Measure ℝ≥0) = smallBernoulliMeasure k x)) ∨
      (β < x ∧ (μ : Measure ℝ≥0) = smallBernoulliMeasure k x) := by
  sorry

/-- At zero allowed mean the only feasible law is the point mass at zero. -/
theorem zero_mean_iff (μ : ProbabilityMeasure ℝ≥0) :
    mean μ = 0 ↔ (μ : Measure ℝ≥0) = Measure.dirac 0 := by
  sorry

/-- For one sample and allowed mean at most one, the unique maximizer is the
unit Bernoulli law. This includes both `x = 0` and `x = 1`. -/
theorem one_sample_equality (x : ℝ) (hx : 0 ≤ x) (hxle : x ≤ 1)
    (μ : ProbabilityMeasure ℝ≥0) (hmean : mean μ ≤ ENNReal.ofReal x) :
    tailProbability 1 μ = sharpTailValue 1 x ↔
      (μ : Measure ℝ≥0) = unitBernoulliMeasure x := by
  sorry

/-- The success probability is one exactly when a sample is at least `1/k`
almost surely. This supplies all maximizing laws above the mean threshold and
also applies to distributions with infinite mean. -/
theorem tail_eq_one_iff (k : ℕ) (hk : 1 ≤ k) (μ : ProbabilityMeasure ℝ≥0) :
    tailProbability k μ = 1 ↔
      (μ : Measure ℝ≥0) (Set.Iio ((k : ℝ≥0)⁻¹)) = 0 := by
  sorry

/-- Every edge of `H` has exactly `k` vertices. Vertex labels range over `Fin n`;
isolated vertices are included in this fixed ambient vertex set. -/
def IsUniform (k : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = k

/-- Every pairwise disjoint subfamily of edges has cardinality at most `s`.
This is exactly the ordinary integer matching-number bound. -/
def MatchingNumberAtMost (s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∀ M : Finset (Finset (Fin n)), M ⊆ H →
    (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) → M.card ≤ s

/-- The number of `k`-sets meeting a fixed `s`-set, in the parameter range
`s ≤ n` appearing in the matching theorems. -/
def coverSize (k n s : ℕ) : ℕ :=
  Nat.choose n k - Nat.choose (n - s) k

/-- The number of edges in a complete `k`-graph on `k(s+1)-1` vertices. -/
def cliqueSize (k s : ℕ) : ℕ :=
  Nat.choose (k * (s + 1) - 1) k

/-- `H` consists of all `k`-sets meeting one fixed `s`-set. -/
def IsCompleteCover (k s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = s ∧
    ∀ e : Finset (Fin n), e ∈ H ↔ e.card = k ∧ ¬ Disjoint e S

/-- `H` consists of all `k`-sets in one fixed set of size `k(s+1)-1`;
all remaining vertices are isolated. -/
def IsStandardClique (k s : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ∃ Q : Finset (Fin n), Q.card = k * (s + 1) - 1 ∧
    ∀ e : Finset (Fin n), e ∈ H ↔ e.card = k ∧ e ⊆ Q

/-- The exact Erdős matching bound, for each fixed uniformity and every
sufficiently large matching parameter, uniformly for all `n ≥ k(s+1)`. No
fractional-cover hypothesis or probability theorem is assumed. -/
theorem large_matching_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ s₀ : ℕ, ∀ s n : ℕ, s₀ ≤ s → k * (s + 1) ≤ n →
      ∀ H : Finset (Finset (Fin n)), IsUniform k H → MatchingNumberAtMost s H →
        H.card ≤ max (coverSize k n s) (cliqueSize k s) := by
  sorry

/-- The exact equality classification. A standard construction is extremal
precisely when its own size equals the larger of the two candidate sizes. -/
theorem large_matching_equality (k : ℕ) (hk : 3 ≤ k) :
    ∃ s₀ : ℕ, ∀ s n : ℕ, s₀ ≤ s → k * (s + 1) ≤ n →
      ∀ H : Finset (Finset (Fin n)), IsUniform k H → MatchingNumberAtMost s H →
        (H.card = max (coverSize k n s) (cliqueSize k s) ↔
          (IsCompleteCover k s H ∧ cliqueSize k s ≤ coverSize k n s) ∨
          (IsStandardClique k s H ∧ coverSize k n s ≤ cliqueSize k s)) := by
  sorry

end SharpTailMatching
