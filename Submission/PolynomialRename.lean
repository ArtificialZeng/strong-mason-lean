import Submission.CompleteLogConcavity
import Submission.DirectionalDerivative
import Mathlib.Algebra.MvPolynomial.Rename

set_option autoImplicit false

/-!
Chain rules for arbitrary variable renaming, including maps which merge
variables. Directions are pulled back by composition with the renaming map.
-/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

@[simp] theorem directionalDerivative_C (v : ι → ℝ) (r : ℝ) :
    directionalDerivative v (C r) = 0 := by
  simp [directionalDerivative]

@[simp] theorem directionalDerivative_X (v : ι → ℝ) (i : ι) :
    directionalDerivative v (X i) = C (v i) := by
  classical
  simp [directionalDerivative, pderiv_X, Pi.single_apply, smul_eq_C_mul]

/-- The constant-direction formal derivative obeys the product rule. -/
theorem directionalDerivative_mul (v : ι → ℝ) (p q : MvPolynomial ι ℝ) :
    directionalDerivative v (p * q) =
      directionalDerivative v p * q + p * directionalDerivative v q := by
  simp only [directionalDerivative, pderiv_mul, smul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

/-- Directional chain rule for any map of variables; injectivity is not
required, so variables may be merged. -/
theorem directionalDerivative_rename (f : ι → κ) (v : κ → ℝ)
    (p : MvPolynomial ι ℝ) :
    directionalDerivative v (rename f p) =
      rename f (directionalDerivative (fun i => v (f i)) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, directionalDerivative_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, rename_X, directionalDerivative_mul, directionalDerivative_X,
      hp, map_add, rename_C]

/-- Iterated directional derivatives satisfy the same variable-merging chain
rule, with every direction in the list pulled back. -/
theorem iteratedDirectionalDerivative_rename (f : ι → κ)
    (vs : List (κ → ℝ)) (p : MvPolynomial ι ℝ) :
    iteratedDirectionalDerivative vs (rename f p) =
      rename f (iteratedDirectionalDerivative
        (vs.map (fun v i => v (f i))) p) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [iteratedDirectionalDerivative, List.map_cons, ih,
      directionalDerivative_rename]

variable [DecidableEq ι] [DecidableEq κ]

/-- A Hessian pairing is the evaluated second directional derivative. -/
theorem hessianBilin_eq_eval_directionalDerivative
    (p : MvPolynomial ι ℝ) (w u v : ι → ℝ) :
    hessianBilin p w u v =
      eval w (directionalDerivative v (directionalDerivative u p)) := by
  rw [hessianBilin_row_eq_gradient_directionalDerivative, gradientFunctional_apply,
    eval_directionalDerivative]

/-- Exact Hessian pullback identity for arbitrary variable merging. -/
theorem hessianBilin_rename (f : ι → κ) (p : MvPolynomial ι ℝ)
    (w u v : κ → ℝ) :
    hessianBilin (rename f p) w u v =
      hessianBilin p (fun i => w (f i))
        (fun i => u (f i)) (fun i => v (f i)) := by
  rw [hessianBilin_eq_eval_directionalDerivative,
    directionalDerivative_rename, directionalDerivative_rename, eval_rename,
    hessianBilin_eq_eval_directionalDerivative]
  rfl

#print axioms directionalDerivative_C
#print axioms directionalDerivative_X
#print axioms directionalDerivative_mul
#print axioms directionalDerivative_rename
#print axioms iteratedDirectionalDerivative_rename
#print axioms hessianBilin_eq_eval_directionalDerivative
#print axioms hessianBilin_rename

end StrongMasonAudit
