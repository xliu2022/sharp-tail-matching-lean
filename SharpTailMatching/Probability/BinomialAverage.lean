module

public import SharpTailMatching.CentralBinomial

/-! # Finite binomial averages as scalar sums -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace SharpTailMatching.Probability

def binomialWeightReal (n : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ)*a^(n-j)*(1-a)^j

def binomialAverage (n : ℕ) (a : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1),binomialWeightReal n a j*f j

theorem binomialWeightReal_zero_of_lt (n j : ℕ) (hj : n < j) (a : ℝ) :
    binomialWeightReal n a j = 0 := by simp [binomialWeightReal,Nat.choose_eq_zero_of_lt hj]

theorem binomialWeightReal_succ_zero (n : ℕ) (a : ℝ) :
    binomialWeightReal (n+1) a 0 = a*binomialWeightReal n a 0 := by
  simp [binomialWeightReal,pow_succ,mul_comm]

theorem binomialWeightReal_succ (n j : ℕ) (hj : j ≤ n) (a : ℝ) :
    binomialWeightReal (n+1) a (j+1) =
      a*binomialWeightReal n a (j+1)+(1-a)*binomialWeightReal n a j := by
  by_cases heq : j = n
  · subst j
    simp [binomialWeightReal,pow_succ,mul_comm]
  · have hlt : j < n := by omega
    have hpow : n-j = (n-(j+1))+1 := by omega
    unfold binomialWeightReal
    rw [Nat.choose_succ_succ',Nat.cast_add,Nat.add_sub_add_right,pow_succ]
    rw [hpow,pow_succ]
    ring

theorem binomialAverage_succ (n : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    binomialAverage (n+1) a f =
      a*binomialAverage n a f+(1-a)*binomialAverage n a (fun j => f (j+1)) := by
  have hshift : (∑ j ∈ Finset.range (n+1),binomialWeightReal n a (j+1)*f (j+1)) =
      (∑ j ∈ Finset.range n,binomialWeightReal n a (j+1)*f (j+1)) := by
    rw [Finset.sum_range_succ,binomialWeightReal_zero_of_lt n (n+1) (by omega),zero_mul,add_zero]
  have hbase : (∑ j ∈ Finset.range n,binomialWeightReal n a (j+1)*f (j+1))+
      binomialWeightReal n a 0*f 0 = binomialAverage n a f :=
    (Finset.sum_range_succ' (fun j => binomialWeightReal n a j*f j) n).symm
  unfold binomialAverage at ⊢
  rw [Finset.sum_range_succ',binomialWeightReal_succ_zero]
  have hsum : (∑ j ∈ Finset.range (n+1),binomialWeightReal (n+1) a (j+1)*f (j+1)) =
      a*(∑ j ∈ Finset.range (n+1),binomialWeightReal n a (j+1)*f (j+1))+
      (1-a)*(∑ j ∈ Finset.range (n+1),binomialWeightReal n a j*f (j+1)) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [binomialWeightReal_succ n j (by have := Finset.mem_range.mp hj; omega)]
    ring
  rw [hsum,hshift]
  change _ = a*binomialAverage n a f+(1-a)*binomialAverage n a (fun j => f (j+1))
  rw [← hbase]
  unfold binomialAverage
  ring

theorem binomialAverage_const (n : ℕ) (a c : ℝ) : binomialAverage n a (fun _ => c) = c := by
  unfold binomialAverage binomialWeightReal
  rw [← Finset.sum_mul,← CentralBinomial.add_pow_extended a (1-a) n (n+1) (by omega)]
  have h : a+(1-a) = 1 := by ring
  rw [h,one_pow,one_mul]

theorem binomialAverage_add (n : ℕ) (a : ℝ) (f g : ℕ → ℝ) :
    binomialAverage n a (fun j => f j+g j) = binomialAverage n a f+binomialAverage n a g := by
  simp only [binomialAverage,mul_add,Finset.sum_add_distrib]

theorem binomialAverage_sub (n : ℕ) (a : ℝ) (f g : ℕ → ℝ) :
    binomialAverage n a (fun j => f j-g j) = binomialAverage n a f-binomialAverage n a g := by
  simp only [binomialAverage,mul_sub,Finset.sum_sub_distrib]

theorem binomialAverage_mul_const (n : ℕ) (a : ℝ) (f : ℕ → ℝ) (c : ℝ) :
    binomialAverage n a (fun j => c*f j) = c*binomialAverage n a f := by
  unfold binomialAverage
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem binomialAverage_mean (n : ℕ) (a : ℝ) : binomialAverage n a (fun j => (j : ℝ)) = n*(1-a) := by
  induction n with
  | zero => simp [binomialAverage,binomialWeightReal]
  | succ n ih =>
    rw [binomialAverage_succ]
    have hshift : binomialAverage n a (fun j => ((j+1 : ℕ) : ℝ)) =
        binomialAverage n a (fun j => (j : ℝ))+1 := by
      simp only [Nat.cast_add,Nat.cast_one,binomialAverage_add,binomialAverage_const]
    rw [hshift,ih,Nat.cast_add,Nat.cast_one]
    ring

theorem binomialAverage_success (n : ℕ) (a : ℝ) (f : ℕ → ℝ) :
    binomialAverage n a f = ∑ j ∈ Finset.range (n+1),
      (n.choose j : ℝ)*a^j*(1-a)^(n-j)*f (n-j) := by
  unfold binomialAverage binomialWeightReal
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hidx : n+1-1-j = n-j := by omega
  rw [hidx,Nat.choose_symm hjn,Nat.sub_sub_self hjn]

theorem binomialAverage_nonneg (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (f : ℕ → ℝ) (hf : ∀ j ≤ n,0 ≤ f j) : 0 ≤ binomialAverage n a f := by
  apply Finset.sum_nonneg
  intro j hj
  have hfj := hf j (by have := Finset.mem_range.mp hj; omega)
  unfold binomialWeightReal
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ha _))
    (pow_nonneg (sub_nonneg.mpr ha1) _)) hfj

theorem binomialAverage_congr (n : ℕ) (a : ℝ) (f g : ℕ → ℝ)
    (hfg : ∀ j ≤ n,f j = g j) : binomialAverage n a f = binomialAverage n a g := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfg j (by have := Finset.mem_range.mp hj; omega)]

end SharpTailMatching.Probability
