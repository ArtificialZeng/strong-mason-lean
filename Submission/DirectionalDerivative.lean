import Submission.PolynomialHessian
import Submission.PolynomialPositivity
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Formal differentiation in a constant real direction. -/
noncomputable def directionalDerivative (v : ι → ℝ) (p : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ := ∑ i, v i • pderiv i p

@[simp] theorem directionalDerivative_add (v : ι → ℝ) (p q : MvPolynomial ι ℝ) :
    directionalDerivative v (p + q) =
      directionalDerivative v p + directionalDerivative v q := by
  simp [directionalDerivative, smul_add, Finset.sum_add_distrib]

@[simp] theorem pderiv_directionalDerivative
    (v : ι → ℝ) (p : MvPolynomial ι ℝ) (j : ι) :
    pderiv j (directionalDerivative v p) = directionalDerivative v (pderiv j p) := by
  simp only [directionalDerivative, map_sum, Derivation.map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_commutation p j i]

@[simp] theorem eval_directionalDerivative
    (v : ι → ℝ) (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    eval w (directionalDerivative v p) = ∑ i, v i * eval w (pderiv i p) := by
  simp [directionalDerivative, smul_eq_C_mul]

theorem directionalDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (v : ι → ℝ) :
    (directionalDerivative v p).IsHomogeneous (d - 1) := by
  change directionalDerivative v p ∈ homogeneousSubmodule ι ℝ (d - 1)
  exact (homogeneousSubmodule ι ℝ (d - 1)).sum_mem (fun i _ =>
    (homogeneousSubmodule ι ℝ (d - 1)).smul_mem (v i) (hp.pderiv (i := i)))

theorem NonnegativeCoefficients.directionalDerivative
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    NonnegativeCoefficients (directionalDerivative v p) := by
  intro m
  unfold StrongMasonAudit.directionalDerivative
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) ((hp.pderiv i) m))

/-- The evaluated gradient, as a linear functional on displacement vectors. -/
noncomputable def gradientFunctional (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, eval w (pderiv i p) • LinearMap.proj i

@[simp] theorem gradientFunctional_apply
    (p : MvPolynomial ι ℝ) (w z : ι → ℝ) :
    gradientFunctional p w z = ∑ i, z i * eval w (pderiv i p) := by
  simp [gradientFunctional, mul_comm]

variable [DecidableEq ι]

/-- Differentiating in a direction and taking the gradient gives the
corresponding row functional of the Hessian. -/
theorem hessianBilin_row_eq_gradient_directionalDerivative
    (p : MvPolynomial ι ℝ) (w v : ι → ℝ) :
    hessianBilin p w v = gradientFunctional (directionalDerivative v p) w := by
  apply LinearMap.ext
  intro z
  simp only [hessianBilin, Matrix.toBilin'_apply, gradientFunctional_apply,
    pderiv_directionalDerivative, eval_directionalDerivative]
  change (∑ i, ∑ j, v i * formalHessian p w i j * z j) =
    ∑ j, z j * (∑ i, v i * formalHessian p w i j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hessianBilin_directionalDerivative
    (p : MvPolynomial ι ℝ) (w v : ι → ℝ) :
    hessianBilin (directionalDerivative v p) w =
      ∑ i, v i • hessianBilin (pderiv i p) w := by
  have hm : formalHessian (directionalDerivative v p) w =
      ∑ i, v i • formalHessian (pderiv i p) w := by
    ext j k
    simp [formalHessian, directionalDerivative, smul_eq_C_mul, Matrix.sum_apply]
  have hb := congrArg
    (Matrix.toBilin' : Matrix ι ι ℝ ≃ₗ[ℝ] LinearMap.BilinForm ℝ (ι → ℝ)) hm
  simpa [hessianBilin] using hb

@[simp] theorem hessianBilin_add (p q : MvPolynomial ι ℝ) (w : ι → ℝ) :
    hessianBilin (p + q) w = hessianBilin p w + hessianBilin q w := by
  have hm : formalHessian (p + q) w = formalHessian p w + formalHessian q w := by
    ext i j
    simp [formalHessian]
  unfold hessianBilin
  rw [hm, map_add]

omit [Fintype ι] [DecidableEq ι] in
theorem formalHessian_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (i j : ι) :
    0 ≤ formalHessian p w i j :=
  eval_nonneg_of_nonnegativeCoefficients ((hp.pderiv j).pderiv i) hw

theorem hessianBilin_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w x y : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    0 ≤ hessianBilin p w x y := by
  simp only [hessianBilin, Matrix.toBilin'_apply]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hx i)
      (formalHessian_nonneg_of_nonnegativeCoefficients hp hw i j)) (hy j)))

omit [DecidableEq ι] in
/-- A positive-degree nonzero homogeneous polynomial with nonnegative
coefficients has nonzero gradient at every strictly positive point. -/
theorem gradientFunctional_ne_zero_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (hd : 1 ≤ d)
    (hcoeff : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : gradientFunctional p w ≠ 0 := by
  have hpos : 0 < gradientFunctional p w w := by
    rw [gradientFunctional_apply, homogeneous_euler_eval hp]
    exact mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd))
      (eval_pos_of_nonnegativeCoefficients hcoeff hp0 hw)
  intro hz
  exact (ne_of_gt hpos) (by rw [hz]; rfl)

#print axioms directionalDerivative_add
#print axioms pderiv_directionalDerivative
#print axioms eval_directionalDerivative
#print axioms directionalDerivative_isHomogeneous
#print axioms NonnegativeCoefficients.directionalDerivative
#print axioms gradientFunctional_apply
#print axioms hessianBilin_row_eq_gradient_directionalDerivative
#print axioms hessianBilin_directionalDerivative
#print axioms hessianBilin_add
#print axioms formalHessian_nonneg_of_nonnegativeCoefficients
#print axioms hessianBilin_nonneg_of_nonnegativeCoefficients
#print axioms gradientFunctional_ne_zero_of_nonnegativeCoefficients

end StrongMasonAudit
