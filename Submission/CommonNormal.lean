import Submission.BoundaryHyperplane
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
Positive-index bounds from nonpositivity on a common hyperplane, and the
common-normal addition criterion used for connected Hessian sums.
-/

namespace StrongMasonAudit

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

/-- A quadratic form nonpositive on the kernel of a nonzero functional has
positive index at most one. -/
theorem sigPos_le_one_of_nonpos_on_kernel
    (Q : QuadraticForm ℝ V) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hneg : ∀ x, ℓ x = 0 → Q x ≤ 0) : sigPos Q ≤ 1 := by
  have hs := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q) (V := LinearMap.ker ℓ) (fun x hx => hneg x hx)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
  rw [← hdim] at hs
  have h : sigPos Q + Module.finrank ℝ (LinearMap.ker ℓ) ≤
      1 + Module.finrank ℝ (LinearMap.ker ℓ) := by
    simpa only [add_comm] using hs
  exact Nat.le_of_add_le_add_right h

/-- Nonnegative weighted sums preserve nonpositivity on a common hyperplane,
and consequently have positive index at most one. -/
theorem sigPos_sum_le_one_of_nonpos_on_kernel
    {ι : Type*} [Fintype ι]
    (B : ι → LinearMap.BilinForm ℝ V) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hneg : ∀ i x, ℓ x = 0 → B i x x ≤ 0) :
    sigPos (∑ i, a i • B i).toQuadraticMap ≤ 1 := by
  apply sigPos_le_one_of_nonpos_on_kernel _ ℓ hℓ
  intro x hx
  change (∑ i, a i • B i) x x ≤ 0
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_nonpos (fun i _ =>
    mul_nonpos_of_nonneg_of_nonpos (ha i) (hneg i x hx))

/-- Two forms of positive index at most one have a sum of positive index at
most one if nonnegative witness vectors give the same nonzero normal.
The witnesses are allowed to be isotropic for their respective forms. -/
theorem sigPos_add_le_one_of_common_normal
    (B C : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (hC : C.IsSymm)
    (hsigB : sigPos B.toQuadraticMap ≤ 1)
    (hsigC : sigPos C.toQuadraticMap ≤ 1)
    (b c : V) (hbb : 0 ≤ B b b) (hcc : 0 ≤ C c c)
    (hnormal : B b = C c) (hnonzero : B b ≠ 0) :
    sigPos (B + C).toQuadraticMap ≤ 1 := by
  have hnegB := nonposOnOrthogonal_of_sigPos_le_one_of_nonneg
    B hB hsigB b hbb hnonzero
  have hCrow : C c ≠ 0 := by rwa [← hnormal]
  have hnegC := nonposOnOrthogonal_of_sigPos_le_one_of_nonneg
    C hC hsigC c hcc hCrow
  apply sigPos_le_one_of_nonpos_on_kernel _ (B b) hnonzero
  intro x hx
  have hCx : C c x = 0 := by rw [← hnormal]; exact hx
  change B x x + C x x ≤ 0
  exact add_nonpos (hnegB x hx) (hnegC x hCx)

/-- The weighted finite-family common-normal criterion. -/
theorem sigPos_sum_le_one_of_common_normal
    {ι : Type*} [Fintype ι]
    (B : ι → LinearMap.BilinForm ℝ V) (hB : ∀ i, (B i).IsSymm)
    (hsig : ∀ i, sigPos (B i).toQuadraticMap ≤ 1)
    (b : ι → V) (hbb : ∀ i, 0 ≤ B i (b i) (b i))
    (ℓ : V →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hnormal : ∀ i, B i (b i) = ℓ)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    sigPos (∑ i, a i • B i).toQuadraticMap ≤ 1 := by
  apply sigPos_sum_le_one_of_nonpos_on_kernel B a ha ℓ hℓ
  intro i x hx
  have hrow : B i (b i) ≠ 0 := by rw [hnormal i]; exact hℓ
  apply nonposOnOrthogonal_of_sigPos_le_one_of_nonneg
    (B i) (hB i) (hsig i) (b i) (hbb i) hrow x
  rw [hnormal i]
  exact hx

#print axioms sigPos_le_one_of_nonpos_on_kernel
#print axioms sigPos_sum_le_one_of_nonpos_on_kernel
#print axioms sigPos_add_le_one_of_common_normal
#print axioms sigPos_sum_le_one_of_common_normal

end StrongMasonAudit
