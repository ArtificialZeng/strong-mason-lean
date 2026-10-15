import Submission.DirectionalDerivative
import Submission.SignatureBridge

set_option autoImplicit false

/-! The two-direction inequality used to extract normalized coefficient bounds. -/

namespace StrongMasonAudit

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Every two-direction principal minor is nonpositive when one diagonal is
nonnegative and the positive index is at most one. The zero diagonal case is
included and requires no limiting argument. -/
theorem bilin_diagonal_mul_le_cross_sq
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hsig : sigPos B.toQuadraticMap ≤ 1) (u v : V) (hu : 0 ≤ B u u) :
    B u u * B v v ≤ (B u v) ^ 2 := by
  by_cases hpos : 0 < B u u
  · exact reverse_cauchy_schwarz B hB u hpos
      (nonposOnOrthogonal_of_sigPos_le_one B hB hsig u hpos) v
  · have hzero : B u u = 0 := le_antisymm (le_of_not_gt hpos) hu
    simpa only [hzero, zero_mul] using sq_nonneg (B u v)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual Hessian satisfies the coefficient-extraction inequality in any
two nonnegative directions, also at boundary evaluation points. -/
theorem hessianBilin_diagonal_mul_le_cross_sq
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hsig : sigPos (hessianBilin p w).toQuadraticMap ≤ 1)
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    hessianBilin p w u u * hessianBilin p w v v ≤
      (hessianBilin p w u v) ^ 2 :=
  bilin_diagonal_mul_le_cross_sq (hessianBilin p w) (hessianBilin_isSymm p w)
    hsig u v (hessianBilin_nonneg_of_nonnegativeCoefficients hp hw hu hu)

#print axioms bilin_diagonal_mul_le_cross_sq
#print axioms hessianBilin_diagonal_mul_le_cross_sq

end StrongMasonAudit
