import Submission.CommonNormal
import Submission.DirectionalDerivative
import Submission.HessianPositivity
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.DenselyOrdered

set_option autoImplicit false

/-!
Pointwise closure of the one-positive-direction condition at a limit form
with a positive witness. Applied to homogeneous nonnegative polynomials, this
extends the directional Hessian bound from positive to nonnegative directions.
-/

namespace StrongMasonAudit

open Filter MvPolynomial
open scoped BigOperators Topology

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- An everywhere nonpositive quadratic form has no positive directions. -/
theorem sigPos_eq_zero_of_nonpos (Q : QuadraticForm ℝ V) (hneg : ∀ x, Q x ≤ 0) :
    sigPos Q = 0 := by
  have hs := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := Q) (V := (⊤ : Submodule ℝ V)) (fun x _ => hneg x)
  rw [finrank_top] at hs
  have hz : sigPos Q ≤ 0 :=
    Nat.le_of_add_le_add_right (by simpa only [zero_add] using hs)
  exact Nat.eq_zero_of_le_zero hz

/-- The zero bilinear form has no positive directions. -/
theorem sigPos_zero_bilinForm : sigPos (0 : LinearMap.BilinForm ℝ V).toQuadraticMap = 0 :=
  sigPos_eq_zero_of_nonpos _ (fun _ => le_rfl)

/-- The positive-index bound is closed under pointwise scalar limits whenever
the limit has a positive witness. No topology on the vector space is needed. -/
theorem sigPos_le_one_of_tendsto_of_positive_witness
    {α : Type*} (B : α → LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ V)
    (l : Filter α) [NeBot l]
    (hB : ∀ᶠ a in l, (B a).IsSymm)
    (hsig : ∀ᶠ a in l, sigPos (B a).toQuadraticMap ≤ 1)
    (hlim : ∀ x y, Tendsto (fun a => B a x y) l (𝓝 (C x y)))
    (w : V) (hpos : 0 < C w w) : sigPos C.toQuadraticMap ≤ 1 := by
  have heventpos : ∀ᶠ a in l, 0 < B a w w :=
    (hlim w w).eventually (eventually_gt_nhds hpos)
  have hrev (x : V) : C w w * C x x ≤ (C w x) ^ 2 := by
    have hevent : ∀ᶠ a in l, B a w w * B a x x ≤ (B a w x) ^ 2 :=
      ((hB.and hsig).and heventpos).mono (fun a ha =>
        reverse_cauchy_schwarz (B a) ha.1.1 w ha.2
          (nonposOnOrthogonal_of_sigPos_le_one (B a) ha.1.1 ha.1.2 w ha.2) x)
    exact le_of_tendsto_of_tendsto
      ((hlim w w).mul (hlim x x)) ((hlim w x).pow 2) hevent
  have hrow : C w ≠ 0 := by
    intro hz
    have hww : C w w = 0 := by rw [hz, LinearMap.zero_apply]
    exact (ne_of_gt hpos) hww
  apply sigPos_le_one_of_nonpos_on_kernel C.toQuadraticMap (C w) hrow
  intro x hx
  have hscaled : C w w * C x x ≤ C w w * 0 := by
    simpa only [hx, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hrev x
  exact (mul_le_mul_iff_right₀ hpos).mp hscaled

/-- The positive-index bound is closed under arbitrary pointwise scalar
limits. The case with no positive witness has positive index zero. -/
theorem sigPos_le_one_of_tendsto
    {α : Type*} (B : α → LinearMap.BilinForm ℝ V) (C : LinearMap.BilinForm ℝ V)
    (l : Filter α) [NeBot l]
    (hB : ∀ᶠ a in l, (B a).IsSymm)
    (hsig : ∀ᶠ a in l, sigPos (B a).toQuadraticMap ≤ 1)
    (hlim : ∀ x y, Tendsto (fun a => B a x y) l (𝓝 (C x y))) :
    sigPos C.toQuadraticMap ≤ 1 := by
  by_cases hpos : ∃ w, 0 < C w w
  · obtain ⟨w, hw⟩ := hpos
    exact sigPos_le_one_of_tendsto_of_positive_witness B C l hB hsig hlim w hw
  · have hneg (x : V) : C.toQuadraticMap x ≤ 0 :=
      le_of_not_gt (fun hx => hpos ⟨x, hx⟩)
    rw [sigPos_eq_zero_of_nonpos C.toQuadraticMap hneg]
    exact Nat.zero_le 1

section Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite-coordinate limits of directions give pointwise scalar limits of
the Hessian of the directional derivative. -/
theorem tendsto_hessianBilin_directionalDerivative
    {α : Type*} {l : Filter α} {v : α → ι → ℝ} {v₀ : ι → ℝ}
    (hv : ∀ i, Tendsto (fun a => v a i) l (𝓝 (v₀ i)))
    (p : MvPolynomial ι ℝ) (w x y : ι → ℝ) :
    Tendsto (fun a => hessianBilin (directionalDerivative (v a) p) w x y) l
      (𝓝 (hessianBilin (directionalDerivative v₀ p) w x y)) := by
  have hs := tendsto_finsetSum Finset.univ (fun i _ =>
    (hv i).mul (tendsto_const_nhds (x := hessianBilin (pderiv i p) w x y)))
  simpa only [hessianBilin_directionalDerivative, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul] using hs

/-- A directional Hessian bound on all positive directions extends to all
nonnegative directions by finite-coordinate continuity. -/
theorem directionalDerivative_sigPos_le_one_of_positive_bound
    (p : MvPolynomial ι ℝ) (w : ι → ℝ)
    (hpositive : ∀ v : ι → ℝ, (∀ i, 0 < v i) →
      sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1 := by
  let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
    hessianBilin (directionalDerivative (fun i => v i + ε) p) w
  apply sigPos_le_one_of_tendsto B (hessianBilin (directionalDerivative v p) w)
    (𝓝[>] (0 : ℝ))
  · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
  · exact Filter.Eventually.mono
      (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
      (fun ε hε => hpositive (fun i => v i + ε)
        (fun i => add_pos_of_nonneg_of_pos (hv i) hε))
  · intro x y
    apply tendsto_hessianBilin_directionalDerivative
    intro i
    have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [add_zero] using (tendsto_const_nhds (x := v i)).add heps

/-- For homogeneous polynomials of degree at least three with nonnegative
coefficients, a directional Hessian bound for every strictly positive direction
extends to every nonnegative direction, including zero derivative polynomials. -/
theorem directionalDerivative_sigPos_le_one_of_positive_directions
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (hd : 3 ≤ d)
    (hcoeff : NonnegativeCoefficients p) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hpositive : ∀ v : ι → ℝ, (∀ i, 0 < v i) →
      sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1 := by
  by_cases hzero : directionalDerivative v p = 0
  · rw [hzero, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
      hessianBilin (directionalDerivative (fun i => v i + ε) p) w
    apply sigPos_le_one_of_tendsto_of_positive_witness B
      (hessianBilin (directionalDerivative v p) w) (𝓝[>] (0 : ℝ))
    · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
    · exact Filter.Eventually.mono
        (self_mem_nhdsWithin : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
        (fun ε hε => hpositive (fun i => v i + ε)
          (fun i => add_pos_of_nonneg_of_pos (hv i) hε))
    · intro x y
      apply tendsto_hessianBilin_directionalDerivative
      intro i
      have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [add_zero] using
        (tendsto_const_nhds (x := v i)).add heps
    · exact hessianBilin_pos_of_nonnegativeCoefficients
        (directionalDerivative_isHomogeneous hp v) (Nat.le_sub_of_add_le hd)
        (hcoeff.directionalDerivative hv) hzero hw

end Polynomial

#print axioms sigPos_eq_zero_of_nonpos
#print axioms sigPos_zero_bilinForm
#print axioms sigPos_le_one_of_tendsto_of_positive_witness
#print axioms sigPos_le_one_of_tendsto
#print axioms tendsto_hessianBilin_directionalDerivative
#print axioms directionalDerivative_sigPos_le_one_of_positive_bound
#print axioms directionalDerivative_sigPos_le_one_of_positive_directions

end StrongMasonAudit
