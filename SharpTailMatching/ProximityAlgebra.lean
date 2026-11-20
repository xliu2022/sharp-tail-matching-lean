module

public import Mathlib.Tactic

/-! # The rational comparison step for the conditional deficit -/

@[expose] public section

namespace SharpTailMatching.ComparisonAlgebra

theorem mean_deficit_proximity {x rb r M rs Ms L : ℝ}
    (hx : 0 < x) (hL : 0 ≤ L) (hxb : x < rb) (hbr : rb ≤ r)
    (hrM : r ≤ M) (hMM : M ≤ Ms)
    (hbase : L*x/(rb-x)^2 < 9/10)
    (hcomparison : rs+L*Ms/(Ms-x) ≤ r+L*M/(M-x))
    (hnode : x/5 < rs-(19/20)*Ms) :
    0 ≤ M-r ∧ M-r < (M-4*x)/20 ∧ 3*x < M-x := by
  have hxbM : rb ≤ M := hbr.trans hrM
  have hxM : x < M := hxb.trans_le hxbM
  have hxMs : x < Ms := hxM.trans_le hMM
  have hb : 0 < rb-x := sub_pos.mpr hxb
  have hD : 0 < M-x := sub_pos.mpr hxM
  have hDs : 0 < Ms-x := sub_pos.mpr hxMs
  have hproduct : (rb-x)^2 ≤ (M-x)*(Ms-x) := by
    rw [pow_two]
    exact mul_le_mul (by linarith) (by linarith) hb.le hD.le
  have hratio : L*x/((M-x)*(Ms-x)) ≤ 9/10 := by
    exact (div_le_div_of_nonneg_left (mul_nonneg hL hx.le) (sq_pos_of_pos hb) hproduct).trans hbase.le
  have hid : L*M/(M-x)-L*Ms/(Ms-x) =
      (L*x/((M-x)*(Ms-x)))*(Ms-M) := by
    field_simp
    ring
  have hdiff : rs-r ≤ (L*x/((M-x)*(Ms-x)))*(Ms-M) := by
    linarith only [hcomparison, hid]
  have hratmul := mul_le_mul_of_nonneg_right hratio (sub_nonneg.mpr hMM)
  have hgap : M-r < (M-4*x)/20 := by
    nlinarith only [hdiff, hratmul, hnode, hMM]
  exact ⟨sub_nonneg.mpr hrM, hgap, by linarith⟩

end SharpTailMatching.ComparisonAlgebra
