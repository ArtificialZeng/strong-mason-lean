import Submission.MatroidSignature
import Submission.PolynomialRename
import Submission.BinarySpecialization
import Submission.HessianInequality

set_option autoImplicit false

/-! The actual binary specialization inherits the two-direction Hessian bound. -/

namespace StrongMasonAudit

variable {α : Type*} [Fintype α]

theorem independencePolynomial_binary_hessian_inequality
    (M : Matroid α) [M.Finite] (hn : 2 ≤ M.E.ncard)
    (vs : List (Bool → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : Bool → ℝ) (hw : ∀ i, 0 ≤ w i)
    (u v : Bool → ℝ) (hu : ∀ i, 0 ≤ u i) :
    hessianBilin (iteratedDirectionalDerivative vs
      (MvPolynomial.rename binaryVariable (independencePolynomial M))) w u u *
      hessianBilin (iteratedDirectionalDerivative vs
        (MvPolynomial.rename binaryVariable (independencePolynomial M))) w v v ≤
    (hessianBilin (iteratedDirectionalDerivative vs
      (MvPolynomial.rename binaryVariable (independencePolynomial M))) w u v) ^ 2 := by
  classical
  let us : List (Option α → ℝ) :=
    vs.map (fun v i => v (binaryVariable i))
  have hus : ∀ v ∈ us, ∀ i, 0 ≤ v i := by
    intro v hvus i
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hvus
    exact hv t ht (binaryVariable i)
  simp only [iteratedDirectionalDerivative_rename, hessianBilin_rename]
  apply hessianBilin_diagonal_mul_le_cross_sq
    ((independencePolynomial_nonnegative M).iteratedDirectionalDerivative us hus)
    (fun i => hw (binaryVariable i))
    (independencePolynomial_complete_hessian_sigPos_le_one M hn us hus
      (fun i => w (binaryVariable i)) (fun i => hw (binaryVariable i)))
    (fun i => u (binaryVariable i)) (fun i => v (binaryVariable i))
    (fun i => hu (binaryVariable i))

#print axioms independencePolynomial_binary_hessian_inequality

end StrongMasonAudit
