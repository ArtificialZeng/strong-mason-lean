import Submission.PolynomialHessian
import Submission.PolynomialPositivity

set_option autoImplicit false

/-! The actual positive witness for homogeneous polynomial Hessians. A zero
partial derivative is handled by the zero bilinear form, separately from every
strict-positivity statement. -/

namespace StrongMasonAudit

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp]
theorem hessianBilin_zero (w : ι → ℝ) :
    hessianBilin (0 : MvPolynomial ι ℝ) w = 0 := by
  have hz : formalHessian (0 : MvPolynomial ι ℝ) w = 0 := by
    ext i j
    simp [formalHessian]
  simp [hessianBilin, hz]

/-- A nonzero homogeneous polynomial of degree at least two, with nonnegative
coefficients, has the positive vector itself as a positive Hessian witness. -/
theorem hessianBilin_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < hessianBilin p w w w := by
  rw [hessianBilin_witness_euler hhom]
  have hd0 : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have hd1 : 0 < d - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hd)
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hd0) (Nat.cast_pos.mpr hd1))
    (eval_pos_of_nonnegativeCoefficients hp hp0 hw)

theorem hessianBilin_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    0 < hessianBilin p w w w ↔ p ≠ 0 := by
  constructor
  · intro h hp0
    simp [hp0] at h
  · exact fun hp0 => hessianBilin_pos_of_nonnegativeCoefficients hhom hd hp hp0 hw

/-- The positive-witness hypothesis required for every nonzero first
derivative in the homogeneous common-kernel argument. -/
theorem hessianBilin_pderiv_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (i : ι) (hi : pderiv i p ≠ 0)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < hessianBilin (pderiv i p) w w w := by
  exact hessianBilin_pos_of_nonnegativeCoefficients hhom.pderiv
    (Nat.le_sub_of_add_le hd) (hp.pderiv i) hi hw

/-- An inactive derivative contributes the zero form; every active derivative
has a strict positive witness. This disjunction does not discard inactive
variables from the index type. -/
theorem hessianBilin_pderiv_zero_or_pos
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) (i : ι) :
    hessianBilin (pderiv i p) w = 0 ∨
      0 < hessianBilin (pderiv i p) w w w := by
  by_cases hi : pderiv i p = 0
  · left
    simp [hi]
  · right
    exact hessianBilin_pderiv_pos_of_nonnegativeCoefficients hhom hd hp i hi hw

#print axioms hessianBilin_zero
#print axioms hessianBilin_pos_of_nonnegativeCoefficients
#print axioms hessianBilin_pos_iff_of_nonnegativeCoefficients
#print axioms hessianBilin_pderiv_pos_of_nonnegativeCoefficients
#print axioms hessianBilin_pderiv_zero_or_pos

end StrongMasonAudit
