import Submission.SignatureBridge
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
The orthogonal-hyperplane criterion at a possibly isotropic boundary vector.
The nonzero functional hypothesis excludes vectors in the full radical.
-/

namespace StrongMasonAudit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

/-- A form of positive index at most one is nonpositive on the orthogonal
hyperplane of a nonnegative vector whose associated functional is nonzero.
The boundary case `B b b = 0` is included. -/
theorem nonposOnOrthogonal_of_sigPos_le_one_of_nonneg
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hsig : sigPos B.toQuadraticMap ≤ 1)
    (b : V) (hbb : 0 ≤ B b b) (hrow : B b ≠ 0) :
    NonposOnOrthogonal B b := by
  intro x horth
  by_contra hnonpos
  have hxpos : 0 < B x x := lt_of_not_ge hnonpos
  have hneg := nonposOnOrthogonal_of_sigPos_le_one B hB hsig x hxpos
  have hxb : B x b = 0 := by rw [hB.eq x b, horth]
  have hbeq : B b b = 0 := le_antisymm (hneg b hxb) hbb
  have hrad := isotropic_mem_radical B hB x hxpos hneg b hxb hbeq
  apply hrow
  ext y
  exact hrad y

#print axioms nonposOnOrthogonal_of_sigPos_le_one_of_nonneg

end StrongMasonAudit
