import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! Formal polynomial Hessians and the Euler identities used in the
common-kernel argument. This module does not assert log-concavity. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators Matrix

variable {ι : Type*}

theorem pderiv_commutation (p : MvPolynomial ι ℝ) (i j : ι) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases h : i = j
  · subst j
    rfl
  · ext m
    simp [coeff_pderiv, Finsupp.add_apply, h, Ne.symm h,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

noncomputable def formalHessian (p : MvPolynomial ι ℝ) (w : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => eval w (pderiv i (pderiv j p))

theorem formalHessian_symm (p : MvPolynomial ι ℝ) (w : ι → ℝ) (i j : ι) :
    formalHessian p w i j = formalHessian p w j i := by
  unfold formalHessian
  rw [pderiv_commutation p i j]

variable [Fintype ι]

theorem homogeneous_euler_eval {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ι → ℝ) :
    ∑ i, w i * eval w (pderiv i p) = (d : ℝ) * eval w p := by
  have h := congrArg (eval w) hp.sum_X_mul_pderiv
  simpa using h

theorem formalHessian_euler_entry {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ι → ℝ) (i j : ι) :
    ∑ k, w k * formalHessian (pderiv k p) w i j =
      ((d - 2 : ℕ) : ℝ) * formalHessian p w i j := by
  have h := homogeneous_euler_eval
    ((hp.pderiv (i := j)).pderiv (i := i)) w
  have hswap (k : ι) :
      pderiv k (pderiv i (pderiv j p)) =
        pderiv i (pderiv j (pderiv k p)) := by
    rw [pderiv_commutation (pderiv j p) k i, pderiv_commutation p k j]
  simp_rw [hswap] at h
  unfold formalHessian
  simpa only [Nat.sub_sub] using h

theorem formalHessian_euler_row {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ι → ℝ) (i j : ι) :
    ∑ k, w k * formalHessian (pderiv i p) w k j =
      ((d - 2 : ℕ) : ℝ) * formalHessian p w i j := by
  have h := homogeneous_euler_eval
    ((hp.pderiv (i := j)).pderiv (i := i)) w
  have hswap : pderiv j (pderiv i p) = pderiv i (pderiv j p) :=
    pderiv_commutation p j i
  simp only [formalHessian, hswap]
  simpa only [Nat.sub_sub] using h

theorem formalHessian_gradient {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ι → ℝ) (j : ι) :
    ∑ i, w i * formalHessian p w i j =
      ((d - 1 : ℕ) : ℝ) * eval w (pderiv j p) := by
  exact homogeneous_euler_eval (hp.pderiv (i := j)) w

variable [DecidableEq ι]

noncomputable def hessianBilin (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    LinearMap.BilinForm ℝ (ι → ℝ) := (formalHessian p w).toBilin'

theorem hessianBilin_isSymm (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    (hessianBilin p w).IsSymm := by
  change ((formalHessian p w).toBilin').IsSymm
  apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
  exact Matrix.IsSymm.ext (fun i j => formalHessian_symm p w j i)

theorem hessianBilin_ker_eq_matrix_ker (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    LinearMap.ker (hessianBilin p w) =
      LinearMap.ker ((formalHessian p w).toLin') := by
  classical
  ext z
  simp only [LinearMap.mem_ker]
  constructor
  · intro hz
    funext i
    have hzero : hessianBilin p w (Pi.single i 1) z = 0 := by
      rw [(hessianBilin_isSymm p w).eq _ _, hz, LinearMap.zero_apply]
    simpa [hessianBilin, Matrix.toBilin'_apply, Pi.single_apply,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hzero
  · intro hz
    change formalHessian p w *ᵥ z = 0 at hz
    apply LinearMap.ext
    intro y
    change hessianBilin p w z y = 0
    rw [(hessianBilin_isSymm p w).eq z y]
    simp only [hessianBilin, Matrix.toBilin'_apply', hz, dotProduct_zero]

theorem hessianBilin_euler {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w x y : ι → ℝ) :
    ((d - 2 : ℕ) : ℝ) * hessianBilin p w x y =
      ∑ k, w k * hessianBilin (pderiv k p) w x y := by
  classical
  have hmat : ((d - 2 : ℕ) : ℝ) • formalHessian p w =
      ∑ k, w k • formalHessian (pderiv k p) w := by
    ext i j
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using
      (formalHessian_euler_entry hp w i j).symm
  have hb := congrArg
    (Matrix.toBilin' : Matrix ι ι ℝ ≃ₗ[ℝ] LinearMap.BilinForm ℝ (ι → ℝ)) hmat
  have heval := congrArg (fun B : LinearMap.BilinForm ℝ (ι → ℝ) => B x y) hb
  simpa [hessianBilin] using heval

theorem hessianBilin_euler_row {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w z : ι → ℝ) (i : ι) :
    hessianBilin (pderiv i p) w w z =
      ((d - 2 : ℕ) : ℝ) * hessianBilin p w (Pi.single i 1) z := by
  classical
  simp only [hessianBilin, Matrix.toBilin'_apply]
  calc
    (∑ k, ∑ j, w k * formalHessian (pderiv i p) w k j * z j) =
        ∑ j, (∑ k, w k * formalHessian (pderiv i p) w k j) * z j := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = ∑ j, (((d - 2 : ℕ) : ℝ) * formalHessian p w i j) * z j := by
      simp_rw [formalHessian_euler_row hp w i]
    _ = _ := by
      simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

theorem hessianBilin_witness_euler {p : MvPolynomial ι ℝ} {d : ℕ}
    (hp : p.IsHomogeneous d) (w : ι → ℝ) :
    hessianBilin p w w w =
      (d : ℝ) * ((d - 1 : ℕ) : ℝ) * eval w p := by
  simp only [hessianBilin, Matrix.toBilin'_apply]
  calc
    (∑ i, ∑ j, w i * formalHessian p w i j * w j) =
        ∑ j, (∑ i, w i * formalHessian p w i j) * w j := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ = ∑ j, (((d - 1 : ℕ) : ℝ) * eval w (pderiv j p)) * w j := by
      simp_rw [formalHessian_gradient hp w]
    _ = ((d - 1 : ℕ) : ℝ) * (∑ j, w j * eval w (pderiv j p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [homogeneous_euler_eval hp w]
      ring

#print axioms hessianBilin_euler
#print axioms hessianBilin_euler_row
#print axioms hessianBilin_witness_euler
#print axioms hessianBilin_ker_eq_matrix_ker

end StrongMasonAudit
