import Submission.MatroidDerivative
import Submission.CompleteLogConcavity
import Submission.MatroidQuadraticPolynomial

set_option autoImplicit false

/-! Actual matroid independent-set polynomials satisfy the coordinate-quadratic
criterion. The matroid changes by honest contraction under nonloop derivatives. -/

namespace StrongMasonAudit

open MvPolynomial Classical
open scoped BigOperators Matroid

variable {α : Type*}

@[simp] theorem iteratedPartialDerivative_zero_matroid (is : List (Option α)) :
    iteratedPartialDerivative is (0 : MvPolynomial (Option α) ℝ) = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [iteratedPartialDerivative, ih, map_zero]

/-- Every coordinate derivative of the actual independent-set polynomial that
retains degree at least two has connected partial support. -/
theorem iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_connected
    (is : List (Option α)) (M : Matroid α) [M.Finite] (a : ℕ)
    (ha : a + is.length + 2 ≤ M.E.ncard) :
    ConnectedPartialSupport
      (iteratedPartialDerivative is (homogenizingDerivative a (independencePolynomial M))) := by
  induction is generalizing M a with
  | nil =>
    right
    refine ⟨independenceActiveVariables M, ⟨none, none_mem_independenceActiveVariables M⟩,
      ?_, ?_⟩
    · exact pderiv_homogenizingDerivative_eq_zero_of_not_active M a
    · exact homogenizingDerivative_independencePolynomial_connected M a (by simpa using ha)
  | cons i is ih =>
    simp only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative]
    cases i with
    | none =>
      rw [← homogenizingDerivative_succ]
      apply ih M (a + 1)
      simp only [List.length_cons] at ha
      omega
    | some e =>
      by_cases he : M.IsNonloop e
      · rw [pderiv_some_homogenizingDerivative_eq_contract M a he]
        apply ih (M ／ {e}) a
        simp only [Matroid.contract_ground, Set.ncard_sdiff_singleton_of_mem he.mem_ground]
        simp only [List.length_cons] at ha
        omega
      · rw [pderiv_some_homogenizingDerivative_eq_zero_of_not_nonloop M a he,
          iteratedPartialDerivative_zero_matroid]
        exact Or.inl rfl

section FiniteAmbient

variable [Fintype α]

/-- Every actual terminal quadratic coordinate derivative has positive index
at most one. Repeated nonloop derivatives are reduced by matroid contraction. -/
theorem iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_sigPos_le_one
    (is : List (Option α)) (M : Matroid α) [M.Finite] (a : ℕ)
    (ha : a + is.length + 2 = M.E.ncard) (w : Option α → ℝ) :
    sigPos (hessianBilin
      (iteratedPartialDerivative is (homogenizingDerivative a (independencePolynomial M)))
      w).toQuadraticMap ≤ 1 := by
  induction is generalizing M a with
  | nil =>
    have hn : 2 ≤ M.E.ncard := by simp only [List.length_nil] at ha; omega
    have hna : a = M.E.ncard - 2 := by simp only [List.length_nil] at ha; omega
    simpa only [iteratedPartialDerivative, hna] using
      hessianBilin_homogenizingDerivative_independencePolynomial_sigPos_le_one M hn w
  | cons i is ih =>
    simp only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative]
    cases i with
    | none =>
      rw [← homogenizingDerivative_succ]
      apply ih M (a + 1)
      simp only [List.length_cons] at ha
      omega
    | some e =>
      by_cases he : M.IsNonloop e
      · rw [pderiv_some_homogenizingDerivative_eq_contract M a he]
        apply ih (M ／ {e}) a
        simp only [Matroid.contract_ground, Set.ncard_sdiff_singleton_of_mem he.mem_ground]
        simp only [List.length_cons] at ha
        omega
      · rw [pderiv_some_homogenizingDerivative_eq_zero_of_not_nonloop M a he,
          iteratedPartialDerivative_zero_matroid, hessianBilin_zero, sigPos_zero_bilinForm]
        exact Nat.zero_le 1

/-- Arbitrary nonnegative directional derivatives of the actual matroid
polynomial have Hessian positive index at most one, including boundary points. -/
theorem homogenizingDerivative_independencePolynomial_complete_hessian_sigPos_le_one
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a + 2 ≤ M.E.ncard)
    (vs : List (Option α → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : Option α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs
      (homogenizingDerivative a (independencePolynomial M))) w).toQuadraticMap ≤ 1 := by
  apply complete_hessian_sigPos_le_one
    (homogenizingDerivative_independencePolynomial_homogeneous M a) (by omega)
    (homogenizingDerivative_independencePolynomial_nonnegative M a) ?_ ?_ vs hv w hw
  · intro is his
    exact iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_connected
      is M a (by omega)
  · intro is his z hz
    exact iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_sigPos_le_one
      is M a (by omega) z

/-- The full Hessian positive-index conclusion for the actual finite-ground
independent-set polynomial, with no assumptions on coordinate or direction support. -/
theorem independencePolynomial_complete_hessian_sigPos_le_one
    (M : Matroid α) [M.Finite] (hn : 2 ≤ M.E.ncard)
    (vs : List (Option α → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : Option α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs (independencePolynomial M))
      w).toQuadraticMap ≤ 1 := by
  simpa only [homogenizingDerivative_zero] using
    homogenizingDerivative_independencePolynomial_complete_hessian_sigPos_le_one
      M 0 (by simpa using hn) vs hv w hw

end FiniteAmbient

#print axioms iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_connected
#print axioms iteratedPartialDerivative_homogenizingDerivative_independencePolynomial_sigPos_le_one
#print axioms homogenizingDerivative_independencePolynomial_complete_hessian_sigPos_le_one
#print axioms independencePolynomial_complete_hessian_sigPos_le_one

end StrongMasonAudit
