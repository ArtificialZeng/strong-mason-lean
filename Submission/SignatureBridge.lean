import Submission.CommonKernel
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
The signature hypothesis used in the Hessian common-kernel argument.
The positive signature here is Mathlib's maximal dimension of a subspace on
which the diagonal quadratic form is positive definite. Degeneracy is allowed.
-/

namespace StrongMasonAudit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

/-- A symmetric real bilinear form of positive index at most one is nonpositive
on the orthogonal hyperplane of every positive vector. -/
theorem nonposOnOrthogonal_of_sigPos_le_one
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (hsig : sigPos B.toQuadraticMap ≤ 1)
    (w : V) (hpos : 0 < B w w) : NonposOnOrthogonal B w := by
  classical
  intro x horth
  by_contra hnonpos
  have hxpos : 0 < B x x := lt_of_not_ge hnonpos
  let S := Submodule.span ℝ ({w, x} : Set V)
  have hpd : (B.toQuadraticMap.restrict S).PosDef := by
    intro y hy
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp y.property
    have habnz : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      push Not at h
      apply hy
      apply Subtype.ext
      simpa [h.1, h.2] using hab.symm
    change 0 < B (y : V) (y : V)
    rw [← hab]
    have hcalc : B (a • w + b • x) (a • w + b • x) =
        a ^ 2 * B w w + b ^ 2 * B x x := by
      simp only [B.add_left, B.add_right, B.smul_left, B.smul_right]
      rw [hB.eq x w, horth]
      ring
    rw [hcalc]
    rcases habnz with ha | hb
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sq_pos_of_ne_zero ha) hpos)
        (mul_nonneg (sq_nonneg b) hxpos.le)
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sq_nonneg a) hpos.le)
        (mul_pos (sq_pos_of_ne_zero hb) hxpos)
  have hlin : LinearIndependent ℝ ![w, x] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have ha : a * B w w = 0 := by
      have h := congrArg (B w) hab
      simpa only [B.add_right, B.smul_right, horth, mul_zero, add_zero,
        B.zero_right] using h
    have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_right (ne_of_gt hpos)
    have hb : b * B x x = 0 := by
      have h := congrArg (B x) hab
      simpa only [ha0, zero_smul, zero_add, B.smul_right, B.zero_right] using h
    exact ⟨ha0, (mul_eq_zero.mp hb).resolve_right (ne_of_gt hxpos)⟩
  have hdim : Module.finrank ℝ S = 2 := by
    let e : S ≃ₗ[ℝ] Submodule.span ℝ (Set.range ![w, x]) :=
      LinearEquiv.ofEq _ _ (by
        dsimp only [S]
        rw [Matrix.range_cons_cons_empty])
    exact e.finrank_eq.trans (by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hlin)
  have htwo : 2 ≤ sigPos B.toQuadraticMap := by
    simpa only [hdim] using le_sigPos_of_posDef B.toQuadraticMap hpd
  exact (by decide : ¬ (2 : ℕ) ≤ 1) (htwo.trans hsig)

/-- The common-kernel theorem with the orthogonal-hyperplane condition supplied
by the positive-index hypothesis. The Euler identities and positive witnesses
remain explicit hypotheses for the polynomial bridge. -/
theorem common_kernel_eq_of_sigPos_le_one
    {ι : Type*} [Fintype ι]
    (H : LinearMap.BilinForm ℝ V) (hH : H.IsSymm)
    (B : ι → LinearMap.BilinForm ℝ V) (hB : ∀ i, (B i).IsSymm)
    (w : V) (e : ι → V) (a : ι → ℝ) (c : ℝ)
    (hc : c ≠ 0) (ha : ∀ i, 0 < a i)
    (hpos : ∀ i, 0 < B i w w)
    (hsig : ∀ i, sigPos (B i).toQuadraticMap ≤ 1)
    (hEuler : ∀ x y, c * H x y = ∑ i, a i * B i x y)
    (hEulerRow : ∀ i z, B i w z = c * H (e i) z) :
    LinearMap.ker H = ⨅ i, LinearMap.ker (B i) := by
  exact common_kernel_eq H hH B hB w e a c hc ha hpos
    (fun i => nonposOnOrthogonal_of_sigPos_le_one (B i) (hB i) (hsig i) w (hpos i))
    hEuler hEulerRow

#print axioms nonposOnOrthogonal_of_sigPos_le_one
#print axioms common_kernel_eq_of_sigPos_le_one

end StrongMasonAudit
