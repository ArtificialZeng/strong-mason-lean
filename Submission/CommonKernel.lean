import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
An abstract algebraic core of Brändén--Huh (arXiv:1811.01696v2), Lemma 5.
This file deliberately does not claim the full polynomial lemma: the signature
condition and the polynomial Euler identities are explicit hypotheses below.
-/

namespace StrongMasonAudit

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Nonpositivity on the orthogonal hyperplane of a positive witness. -/
def NonposOnOrthogonal (B : LinearMap.BilinForm ℝ V) (w : V) : Prop :=
  ∀ x, B w x = 0 → B x x ≤ 0

/-- Membership in the left radical of a bilinear form. -/
def InRadical (B : LinearMap.BilinForm ℝ V) (z : V) : Prop :=
  ∀ x, B z x = 0

/-- The elementary projection proof of reverse Cauchy--Schwarz. -/
theorem reverse_cauchy_schwarz
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (w : V)
    (hpos : 0 < B w w) (hneg : NonposOnOrthogonal B w) (x : V) :
    B w w * B x x ≤ (B w x) ^ 2 := by
  let y := (B w w) • x - (B w x) • w
  have hy : B w y = 0 := by
    dsimp [y]
    rw [B.sub_right, B.smul_right, B.smul_right]
    ring
  have hcalc : B y y = B w w * (B w w * B x x - (B w x) ^ 2) := by
    dsimp [y]
    simp only [B.sub_left, B.sub_right, B.smul_left, B.smul_right]
    rw [hB.eq x w]
    ring
  have hscaled : B w w * (B w w * B x x - (B w x) ^ 2) ≤ B w w * 0 := by
    simpa only [hcalc, mul_zero] using hneg y hy
  have hdiff := (mul_le_mul_iff_right₀ hpos).mp hscaled
  linarith

private theorem linear_nonpos_forall_slope_zero (p q : ℝ)
    (h : ∀ t : ℝ, p + t * q ≤ 0) : q = 0 := by
  by_contra hq
  have ht := h ((1 - p) / q)
  have heq : p + (1 - p) / q * q = 1 := by
    rw [div_mul_cancel₀ _ hq]
    ring
  linarith

/-- An isotropic vector on the nonpositive orthogonal hyperplane lies in the
whole radical, including in degenerate cases. This is the equality case needed
in the common-kernel argument. -/
theorem isotropic_mem_radical
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm) (w : V)
    (hpos : 0 < B w w) (hneg : NonposOnOrthogonal B w)
    (z : V) (horth : B w z = 0) (hiso : B z z = 0) :
    InRadical B z := by
  have hcross : ∀ y, B w y = 0 → B z y = 0 := by
    intro y hy
    have hline : ∀ t : ℝ, B y y + t * (2 * B z y) ≤ 0 := by
      intro t
      have hp : B w (y + t • z) = 0 := by
        rw [B.add_right, B.smul_right, hy, horth]
        ring
      have hq := hneg (y + t • z) hp
      have hcalc : B (y + t • z) (y + t • z) =
          B y y + t * (2 * B z y) := by
        simp only [B.add_left, B.add_right, B.smul_left, B.smul_right]
        rw [hB.eq y z, hiso]
        ring
      rwa [hcalc] at hq
    have := linear_nonpos_forall_slope_zero (B y y) (2 * B z y) hline
    linarith
  intro x
  let y := (B w w) • x - (B w x) • w
  have hy : B w y = 0 := by
    dsimp [y]
    rw [B.sub_right, B.smul_right, B.smul_right]
    ring
  have hz := hcross y hy
  have hzw : B z w = 0 := by rw [hB.eq z w, horth]
  dsimp [y] at hz
  rw [B.sub_right, B.smul_right, B.smul_right, hzw, mul_zero, sub_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpos)

/-- Abstract common-kernel theorem. In the intended application:
`c = d - 2`, `H` is the Hessian of a degree-`d` homogeneous polynomial,
`B i` is the Hessian of its `i`th partial derivative, `a i = w i`, and
`e i` is the `i`th coordinate vector. Both Euler identities are exposed.

The positive-witness and orthogonal-nonpositivity hypotheses are essential;
the published polynomial statement needs a coefficient-positivity assumption
to justify the positive witness used in its proof. -/
theorem common_kernel
    {ι : Type*} [Fintype ι]
    (H : LinearMap.BilinForm ℝ V) (hH : H.IsSymm)
    (B : ι → LinearMap.BilinForm ℝ V) (hB : ∀ i, (B i).IsSymm)
    (w : V) (e : ι → V) (a : ι → ℝ) (c : ℝ)
    (hc : c ≠ 0) (ha : ∀ i, 0 < a i)
    (hpos : ∀ i, 0 < B i w w)
    (hneg : ∀ i, NonposOnOrthogonal (B i) w)
    (hEuler : ∀ x y, c * H x y = ∑ i, a i * B i x y)
    (hEulerRow : ∀ i z, B i w z = c * H (e i) z)
    (z : V) : InRadical H z ↔ ∀ i, InRadical (B i) z := by
  classical
  constructor
  · intro hz
    have horth : ∀ i, B i w z = 0 := by
      intro i
      rw [hEulerRow i z, hH.eq (e i) z, hz (e i), mul_zero]
    have hnonpos : ∀ i, a i * B i z z ≤ 0 := by
      intro i
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (ha i)) (hneg i z (horth i))
    have hsum : (∑ i, a i * B i z z) = 0 := by
      rw [← hEuler z z, hz z, mul_zero]
    have heach : ∀ i, a i * B i z z = 0 := by
      have hs := (Finset.sum_eq_zero_iff_of_nonpos
        (s := Finset.univ) (fun i _ => hnonpos i)).mp hsum
      intro i
      exact hs i (Finset.mem_univ i)
    intro i
    have hiso : B i z z = 0 :=
      (mul_eq_zero.mp (heach i)).resolve_left (ne_of_gt (ha i))
    exact isotropic_mem_radical (B i) (hB i) w (hpos i) (hneg i) z (horth i) hiso
  · intro hz x
    have hzero : c * H z x = 0 := by
      rw [hEuler z x]
      apply Finset.sum_eq_zero
      intro i _
      rw [hz i x, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_left hc

/-- The same algebraic result expressed as equality of linear-map kernels. -/
theorem common_kernel_eq
    {ι : Type*} [Fintype ι]
    (H : LinearMap.BilinForm ℝ V) (hH : H.IsSymm)
    (B : ι → LinearMap.BilinForm ℝ V) (hB : ∀ i, (B i).IsSymm)
    (w : V) (e : ι → V) (a : ι → ℝ) (c : ℝ)
    (hc : c ≠ 0) (ha : ∀ i, 0 < a i)
    (hpos : ∀ i, 0 < B i w w)
    (hneg : ∀ i, NonposOnOrthogonal (B i) w)
    (hEuler : ∀ x y, c * H x y = ∑ i, a i * B i x y)
    (hEulerRow : ∀ i z, B i w z = c * H (e i) z) :
    LinearMap.ker H = ⨅ i, LinearMap.ker (B i) := by
  ext z
  simpa only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.ext_iff,
    LinearMap.zero_apply, InRadical] using
      common_kernel H hH B hB w e a c hc ha hpos hneg hEuler hEulerRow z

#print axioms reverse_cauchy_schwarz
#print axioms isotropic_mem_radical
#print axioms common_kernel
#print axioms common_kernel_eq

end StrongMasonAudit
