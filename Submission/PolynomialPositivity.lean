import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Coefficient positivity at positive evaluation vectors. The nonzero
hypotheses below are explicit: a zero partial derivative has zero evaluation.
No homogeneity or finiteness of the variable type is needed for these facts. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-- Every coefficient of a real multivariate polynomial is nonnegative. -/
def NonnegativeCoefficients (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m, 0 ≤ coeff m p

theorem eval_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : 0 ≤ eval w p := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)

/-- A nonzero polynomial with nonnegative coefficients is strictly positive
at every vector whose coordinates are strictly positive. -/
theorem eval_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < eval w p := by
  classical
  rw [eval_eq]
  apply Finset.sum_pos
  · intro m hm
    exact mul_pos (lt_of_le_of_ne (hp m) (Ne.symm (mem_support_iff.mp hm)))
      (Finset.prod_pos fun i _ => pow_pos (hw i) _)
  · exact support_nonempty.mpr hp0

theorem eval_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < eval w p ↔ p ≠ 0 := by
  constructor
  · intro h hp0
    simp [hp0] at h
  · exact fun hp0 => eval_pos_of_nonnegativeCoefficients hp hp0 hw

theorem eval_eq_zero_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : eval w p = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp0
    have := eval_pos_of_nonnegativeCoefficients hp hp0 hw
    exact (ne_of_gt this) h
  · intro h
    simp [h]

/-- Formal partial differentiation preserves coefficient nonnegativity. -/
theorem NonnegativeCoefficients.pderiv
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (i : ι) :
    NonnegativeCoefficients (pderiv i p) := by
  intro m
  rw [coeff_pderiv]
  exact mul_nonneg (hp _) (by positivity)

theorem eval_pderiv_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    (i : ι) (hi : pderiv i p ≠ 0)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) : 0 < eval w (pderiv i p) :=
  eval_pos_of_nonnegativeCoefficients (hp.pderiv i) hi hw

theorem eval_pderiv_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (i : ι)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < eval w (pderiv i p) ↔ pderiv i p ≠ 0 :=
  eval_pos_iff_of_nonnegativeCoefficients (hp.pderiv i) hw

section EulerWitness

variable [Fintype ι]

private theorem homogeneous_euler_eval_for_positivity
    {p : MvPolynomial ι ℝ} {n : ℕ} (hp : p.IsHomogeneous n) (w : ι → ℝ) :
    ∑ i, w i * eval w (pderiv i p) = (n : ℝ) * eval w p := by
  have h := congrArg (eval w) hp.sum_X_mul_pderiv
  simpa using h

/-- Evaluated Euler's identity applied twice, in the order of the formal
partial derivatives. This identity also holds for zero polynomials and degrees
zero or one; strict positivity below requires degree at least two. -/
theorem homogeneous_second_euler_eval
    {p : MvPolynomial ι ℝ} {n : ℕ} (hp : p.IsHomogeneous n) (w : ι → ℝ) :
    (∑ j, w j * (∑ i, w i * eval w (pderiv i (pderiv j p)))) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * eval w p := by
  calc
    _ = ∑ j, w j * (((n - 1 : ℕ) : ℝ) * eval w (pderiv j p)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [homogeneous_euler_eval_for_positivity hp.pderiv]
    _ = ((n - 1 : ℕ) : ℝ) * (∑ j, w j * eval w (pderiv j p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * eval w p := by
      rw [homogeneous_euler_eval_for_positivity hp]
      ring

/-- The Euler quadratic witness is strictly positive for a nonzero homogeneous
polynomial of degree at least two with nonnegative coefficients. -/
theorem homogeneous_second_euler_pos
    {p : MvPolynomial ι ℝ} {n : ℕ} (hhom : p.IsHomogeneous n)
    (hn : 2 ≤ n) (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    0 < ∑ j, w j * (∑ i, w i * eval w (pderiv i (pderiv j p))) := by
  rw [homogeneous_second_euler_eval hhom]
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn1 : 0 < n - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hn0) (Nat.cast_pos.mpr hn1))
    (eval_pos_of_nonnegativeCoefficients hp hp0 hw)

end EulerWitness

#print axioms eval_nonneg_of_nonnegativeCoefficients
#print axioms eval_pos_of_nonnegativeCoefficients
#print axioms eval_pos_iff_of_nonnegativeCoefficients
#print axioms eval_eq_zero_iff_of_nonnegativeCoefficients
#print axioms NonnegativeCoefficients.pderiv
#print axioms eval_pderiv_pos_of_nonnegativeCoefficients
#print axioms eval_pderiv_pos_iff_of_nonnegativeCoefficients
#print axioms homogeneous_second_euler_eval
#print axioms homogeneous_second_euler_pos

end StrongMasonAudit
