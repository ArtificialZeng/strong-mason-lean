/- Single-file packaging variant of the exact 25-file proof at
   ArtificialZeng/strong-mason-lean commit 6a5302e473de4bee11d7c9b3247970d118f308ad.
   Only imports and file-local section boundaries are changed. -/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Tactic.Ring
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Set.PowersetCard
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Combinatorics.Matroid.Map
import Mathlib

-- The original package sets this option for every source module.
set_option autoImplicit false

/- BEGIN ORIGINAL MODULE: Submission.PolynomialPositivity -/
section SingleFileModule01





set_option autoImplicit false

/-! Coefficient positivity at positive evaluation vectors. The nonzero
hypotheses below are explicit: a zero partial derivative has zero evaluation.
No homogeneity or finiteness of the variable type is needed for these facts. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

/-- Every coefficient of a real multivariate polynomial is nonnegative. -/
def NonnegativeCoefficients (p : MvPolynomial ι ℝ) : Prop :=
  ∀ m, 0 ≤ MvPolynomial.lcoeff ℝ m p

theorem eval_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) : 0 ≤ eval w p := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (hp m) (Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _)

/-- A nonzero polynomial with nonnegative coefficients is strictly positive
at every vector whose coordinates are strictly positive. -/
theorem eval_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < eval w p := by
  classical
  rw [eval_eq]
  apply Finset.sum_pos
  · intro m hm
    exact mul_pos (lt_of_le_of_ne (hp m) (Ne.symm (mem_support_iff.mp hm)))
      (Finset.prod_pos fun i _ => pow_pos (hw i) _)
  · exact support_nonempty.mpr hp0

theorem eval_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < eval w p ↔ p ≠ 0 := by
  constructor
  · intro h hp0
    simp [hp0] at h
  · exact fun hp0 => eval_pos_of_nonnegativeCoefficients hp hp0 hw

theorem eval_eq_zero_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : eval w p = 0 ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp0
    have := eval_pos_of_nonnegativeCoefficients hp hp0 hw
    exact (ne_of_gt this) h
  · intro h
    simp [h]

/-- Formal partial differentiation preserves coefficient nonnegativity. -/
theorem NonnegativeCoefficients.pderiv
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (i : ι) :
    NonnegativeCoefficients (pderiv i p) := by
  intro m
  simp only [MvPolynomial.lcoeff_apply]
  rw [coeff_pderiv]
  exact mul_nonneg (hp _) (by positivity)

theorem eval_pderiv_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    (i : ι) (hi : pderiv i p ≠ 0)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) : 0 < eval w (pderiv i p) :=
  eval_pos_of_nonnegativeCoefficients (hp.pderiv i) hi hw

theorem eval_pderiv_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p) (i : ι)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < eval w (pderiv i p) ↔ pderiv i p ≠ 0 :=
  eval_pos_iff_of_nonnegativeCoefficients (hp.pderiv i) hw

section EulerWitness

variable [Fintype ι]

private theorem homogeneous_euler_eval_for_positivity
    {p : MvPolynomial ι ℝ} {n : ℕ} (hp : p.IsHomogeneous n) (w : ι → ℝ) :
    ∑ i, w i * eval w (pderiv i p) = (n : ℝ) * eval w p := by
  have h := congrArg (eval w) hp.sum_X_mul_pderiv
  simpa using h

/-- Evaluated Euler's identity applied twice, in the order of the formal
partial derivatives. This identity also holds for zero polynomials and degrees
zero or one; strict positivity below requires degree at least two. -/
theorem homogeneous_second_euler_eval
    {p : MvPolynomial ι ℝ} {n : ℕ} (hp : p.IsHomogeneous n) (w : ι → ℝ) :
    (∑ j, w j * (∑ i, w i * eval w (pderiv i (pderiv j p)))) =
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) * eval w p := by
  calc
    _ = ∑ j, w j * (((n - 1 : ℕ) : ℝ) * eval w (pderiv j p)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [homogeneous_euler_eval_for_positivity hp.pderiv]
    _ = ((n - 1 : ℕ) : ℝ) * (∑ j, w j * eval w (pderiv j p)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * eval w p := by
      rw [homogeneous_euler_eval_for_positivity hp]
      ring

/-- The Euler quadratic witness is strictly positive for a nonzero homogeneous
polynomial of degree at least two with nonnegative coefficients. -/
theorem homogeneous_second_euler_pos
    {p : MvPolynomial ι ℝ} {n : ℕ} (hhom : p.IsHomogeneous n)
    (hn : 2 ≤ n) (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    0 < ∑ j, w j * (∑ i, w i * eval w (pderiv i (pderiv j p))) := by
  rw [homogeneous_second_euler_eval hhom]
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hn1 : 0 < n - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hn0) (Nat.cast_pos.mpr hn1))
    (eval_pos_of_nonnegativeCoefficients hp hp0 hw)

end EulerWitness

#print axioms eval_nonneg_of_nonnegativeCoefficients
#print axioms eval_pos_of_nonnegativeCoefficients
#print axioms eval_pos_iff_of_nonnegativeCoefficients
#print axioms eval_eq_zero_iff_of_nonnegativeCoefficients
#print axioms NonnegativeCoefficients.pderiv
#print axioms eval_pderiv_pos_of_nonnegativeCoefficients
#print axioms eval_pderiv_pos_iff_of_nonnegativeCoefficients
#print axioms homogeneous_second_euler_eval
#print axioms homogeneous_second_euler_pos

end StrongMasonAudit

end SingleFileModule01
/- END ORIGINAL MODULE: Submission.PolynomialPositivity -/

/- BEGIN ORIGINAL MODULE: Submission.IndependentSetPolynomial -/
section SingleFileModule02



set_option autoImplicit false

/-! The actual finite independent-set family and its homogenized enumerator.
The ambient type is arbitrary; only the matroid ground set is finite. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators
open Classical

variable {α : Type*}

noncomputable def independentFinsets (M : Matroid α) [M.Finite] :
    Finset (Finset α) := by
  classical
  exact M.ground_finite.toFinset.powerset.filter (fun I => M.Indep (I : Set α))

@[simp] theorem mem_independentFinsets (M : Matroid α) [M.Finite] (I : Finset α) :
    I ∈ independentFinsets M ↔ M.Indep (I : Set α) := by
  classical
  simp only [independentFinsets, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro hI
    refine ⟨?_, hI⟩
    intro x hx
    exact M.ground_finite.mem_toFinset.mpr (hI.subset_ground hx)

theorem independentFinsets_card_le (M : Matroid α) [M.Finite]
    {I : Finset α} (hI : I ∈ independentFinsets M) : I.card ≤ M.E.ncard := by
  classical
  have hsubset : I ⊆ M.ground_finite.toFinset := by
    intro x hx
    exact M.ground_finite.mem_toFinset.mpr
      (((mem_independentFinsets M I).mp hI).subset_ground hx)
  exact (Finset.card_le_card hsubset).trans_eq
    (Set.ncard_eq_toFinset_card M.E M.ground_finite).symm

/-- This is exactly the set appearing in the challenge's count definition. -/
theorem independentSetCount_finset_bridge (M : Matroid α) [M.Finite] (k : ℕ) :
    {I ∈ Set.powersetCard α k | M.Indep I}.ncard =
      ((independentFinsets M).filter (fun I => I.card = k)).card := by
  classical
  have hsets : {I ∈ Set.powersetCard α k | M.Indep I} =
      (((independentFinsets M).filter (fun I => I.card = k)) : Set (Finset α)) := by
    ext I
    simp only [Set.mem_setOf_eq, Set.powersetCard.mem_iff, Finset.mem_coe,
      Finset.mem_filter, mem_independentFinsets]
    exact and_comm
  rw [hsets, Set.ncard_coe_finset]

theorem independentFinsets_sum_by_card {R : Type*} [AddCommMonoid R]
    (M : Matroid α) [M.Finite] (f : ℕ → R) :
    ∑ I ∈ independentFinsets M, f I.card =
      ∑ k ∈ Finset.range (M.E.ncard + 1),
        ((independentFinsets M).filter (fun I => I.card = k)).card • f k := by
  classical
  trans ∑ k ∈ Finset.range (M.E.ncard + 1),
    ∑ I ∈ (independentFinsets M).filter (fun I => I.card = k), f I.card
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro I hI
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (independentFinsets_card_le M hI))
  · apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro I hI
    rw [(Finset.mem_filter.mp hI).2]

noncomputable def independentExponent (n : ℕ) (I : Finset α) : Option α →₀ ℕ := by
  classical
  exact Finsupp.single none (n - I.card) + ∑ i ∈ I, Finsupp.single (some i) 1

@[simp] theorem independentExponent_none (n : ℕ) (I : Finset α) :
    independentExponent n I none = n - I.card := by
  classical
  simp [independentExponent, Finset.sum_apply]

@[simp] theorem independentExponent_some (n : ℕ) (I : Finset α) (i : α) :
    independentExponent n I (some i) = if i ∈ I then 1 else 0 := by
  classical
  simp [independentExponent, Finset.sum_apply, Finsupp.single_apply]

theorem independentExponent_injective (n : ℕ) :
    Function.Injective (independentExponent n : Finset α → Option α →₀ ℕ) := by
  classical
  intro I J h
  apply Finset.ext
  intro i
  have hi := congrArg (fun e : Option α →₀ ℕ => e (some i)) h
  simp only [independentExponent_some] at hi
  by_cases hI : i ∈ I <;> by_cases hJ : i ∈ J <;> simp_all

noncomputable def independentMonomial (n : ℕ) (I : Finset α) :
    MvPolynomial (Option α) ℝ := monomial (independentExponent n I) 1

theorem independentMonomial_homogeneous {n : ℕ} (I : Finset α) (hI : I.card ≤ n) :
    (independentMonomial n I).IsHomogeneous n := by
  classical
  apply isHomogeneous_monomial
  simp only [independentExponent, map_add, map_sum, Finsupp.degree_single,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  exact Nat.sub_add_cancel hI

theorem independentMonomial_nonnegative (n : ℕ) (I : Finset α) :
    NonnegativeCoefficients (independentMonomial n I) := by
  classical
  intro m
  simp only [MvPolynomial.lcoeff_apply, independentMonomial, coeff_monomial]
  split_ifs <;> norm_num

theorem independentMonomial_eq_product (n : ℕ) (I : Finset α) :
    independentMonomial n I =
      X none ^ (n - I.card) * ∏ i ∈ I, X (some i) := by
  classical
  unfold independentMonomial independentExponent
  rw [← one_mul (1 : ℝ), ← monomial_mul]
  rw [← X_pow_eq_monomial, monomial_sum_one]
  rfl

noncomputable def independencePolynomial (M : Matroid α) [M.Finite] :
    MvPolynomial (Option α) ℝ :=
  ∑ I ∈ independentFinsets M, independentMonomial M.E.ncard I

theorem independencePolynomial_homogeneous (M : Matroid α) [M.Finite] :
    (independencePolynomial M).IsHomogeneous M.E.ncard := by
  classical
  exact IsHomogeneous.sum _ _ _ fun I hI =>
    independentMonomial_homogeneous I (independentFinsets_card_le M hI)

theorem independencePolynomial_nonnegative (M : Matroid α) [M.Finite] :
    NonnegativeCoefficients (independencePolynomial M) := by
  classical
  intro m
  simp only [MvPolynomial.lcoeff_apply, independencePolynomial, coeff_sum]
  exact Finset.sum_nonneg fun I _ => independentMonomial_nonnegative M.E.ncard I m

@[simp] theorem coeff_independencePolynomial_exponent (M : Matroid α) [M.Finite]
    (I : Finset α) :
    MvPolynomial.lcoeff ℝ (independentExponent M.E.ncard I) (independencePolynomial M) =
      if M.Indep (I : Set α) then 1 else 0 := by
  classical
  simp only [MvPolynomial.lcoeff_apply, independencePolynomial, coeff_sum, independentMonomial, coeff_monomial]
  have hexp (J : Finset α) :
      independentExponent M.E.ncard J = independentExponent M.E.ncard I ↔ J = I :=
    (independentExponent_injective M.E.ncard).eq_iff
  simp only [hexp]
  simp [mem_independentFinsets]

theorem independencePolynomial_binary_eval (M : Matroid α) [M.Finite] (y z : ℝ) :
    eval (fun o : Option α => o.elim y (fun _ => z)) (independencePolynomial M) =
      ∑ I ∈ independentFinsets M, y ^ (M.E.ncard - I.card) * z ^ I.card := by
  classical
  simp [independencePolynomial, independentMonomial_eq_product, eval_mul, eval_pow]

/-- The normalized count sequence is the actual binary specialization's
coefficient sequence, rather than an auxiliary assumed enumeration. -/
theorem independencePolynomial_binary_eval_counts
    (M : Matroid α) [M.Finite] (y z : ℝ) :
    eval (fun o : Option α => o.elim y (fun _ => z)) (independencePolynomial M) =
      ∑ k ∈ Finset.range (M.E.ncard + 1),
        ({I ∈ Set.powersetCard α k | M.Indep I}.ncard : ℝ) *
          y ^ (M.E.ncard - k) * z ^ k := by
  rw [independencePolynomial_binary_eval]
  simpa only [nsmul_eq_mul, mul_assoc, independentSetCount_finset_bridge] using
    independentFinsets_sum_by_card M
      (fun k : ℕ => y ^ (M.E.ncard - k) * z ^ k)

@[simp] theorem empty_mem_independentFinsets (M : Matroid α) [M.Finite] :
    (∅ : Finset α) ∈ independentFinsets M := by
  apply (mem_independentFinsets M ∅).mpr
  simpa only [Finset.coe_empty] using M.empty_indep

theorem independencePolynomial_eval_one (M : Matroid α) [M.Finite] :
    eval (fun _ => (1 : ℝ)) (independencePolynomial M) =
      ((independentFinsets M).card : ℝ) := by
  classical
  have hfun : (fun o : Option α => o.elim (1 : ℝ) (fun _ => 1)) =
      (fun _ => 1) := by
    funext o
    cases o <;> rfl
  simpa only [hfun, one_pow, one_mul, Finset.sum_const, nsmul_eq_mul,
    mul_one] using independencePolynomial_binary_eval M 1 1

theorem independencePolynomial_ne_zero (M : Matroid α) [M.Finite] :
    independencePolynomial M ≠ 0 := by
  intro hz
  have h := independencePolynomial_eval_one M
  rw [hz, map_zero] at h
  have hc : 0 < (independentFinsets M).card :=
    Finset.card_pos.mpr ⟨∅, empty_mem_independentFinsets M⟩
  exact (ne_of_gt (Nat.cast_pos.mpr hc : (0 : ℝ) < _)) h.symm

#print axioms independentSetCount_finset_bridge
#print axioms independentExponent_injective
#print axioms coeff_independencePolynomial_exponent
#print axioms independencePolynomial_homogeneous
#print axioms independencePolynomial_nonnegative
#print axioms independencePolynomial_binary_eval
#print axioms independencePolynomial_binary_eval_counts
#print axioms independencePolynomial_ne_zero

end StrongMasonAudit

end SingleFileModule02
/- END ORIGINAL MODULE: Submission.IndependentSetPolynomial -/

/- BEGIN ORIGINAL MODULE: Submission.PolynomialHessian -/
section SingleFileModule03





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

end SingleFileModule03
/- END ORIGINAL MODULE: Submission.PolynomialHessian -/

/- BEGIN ORIGINAL MODULE: Submission.MatroidDerivative -/
section SingleFileModule04



set_option autoImplicit false

/-! Actual coordinate derivatives of the finite-ground independent-set enumerator.
All statements in the first sections allow an arbitrary ambient type. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators Matroid

open Classical

variable {α : Type*}

 theorem independentExponent_erase {n : ℕ} {I : Finset α} {e : α}
    (he : e ∈ I) (hI : I.card ≤ n) :
    independentExponent (n - 1) (I.erase e) =
      independentExponent n I - Finsupp.single (some e) 1 := by
  classical
  ext o
  cases o with
  | none =>
    simp only [independentExponent_none, Finsupp.tsub_apply,
      Finsupp.single_apply, Option.some_ne_none, if_false, tsub_zero,
      Finset.card_erase_of_mem he]
    have hc : 0 < I.card := Finset.card_pos.mpr ⟨e, he⟩
    omega
  | some j =>
    by_cases hje : j = e
    · subst j
      simp [independentExponent_some, he]
    · simp [independentExponent_some, hje]

 theorem pderiv_some_independentMonomial {n : ℕ} (I : Finset α) (e : α)
    (hI : I.card ≤ n) :
    pderiv (some e) (independentMonomial n I) =
      if e ∈ I then independentMonomial (n - 1) (I.erase e) else 0 := by
  classical
  unfold independentMonomial
  rw [pderiv_monomial]
  by_cases he : e ∈ I
  · rw [if_pos he, independentExponent_erase he hI]
    simp [independentExponent_some, he]
  · simp [independentExponent_some, he]

 theorem pderiv_some_independencePolynomial (M : Matroid α) [M.Finite] (e : α) :
    pderiv (some e) (independencePolynomial M) =
      ∑ I ∈ (independentFinsets M).filter (fun I => e ∈ I),
        independentMonomial (M.E.ncard - 1) (I.erase e) := by
  classical
  simp only [independencePolynomial, map_sum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  exact pderiv_some_independentMonomial I e (independentFinsets_card_le M hI)

 theorem pderiv_some_twice_independentMonomial {n : ℕ} (I : Finset α) (e : α)
    (hI : I.card ≤ n) :
    pderiv (some e) (pderiv (some e) (independentMonomial n I)) = 0 := by
  classical
  rw [pderiv_some_independentMonomial I e hI]
  by_cases he : e ∈ I
  · rw [if_pos he, pderiv_some_independentMonomial]
    · simp
    · rw [Finset.card_erase_of_mem he]
      omega
  · simp [he]

 theorem pderiv_some_twice_independencePolynomial (M : Matroid α) [M.Finite] (e : α) :
    pderiv (some e) (pderiv (some e) (independencePolynomial M)) = 0 := by
  classical
  simp only [independencePolynomial, map_sum]
  apply Finset.sum_eq_zero
  intro I hI
  exact pderiv_some_twice_independentMonomial I e (independentFinsets_card_le M hI)

theorem mem_independentFinsets_contractElem_iff (M : Matroid α) [M.Finite]
    {e : α} (he : M.IsNonloop e) (I : Finset α) :
    I ∈ independentFinsets (M ／ {e}) ↔ e ∉ I ∧ M.Indep (↑(insert e I) : Set α) := by
  simp only [mem_independentFinsets, he.contractElem_indep_iff, Finset.mem_coe,
    Finset.coe_insert]

/-- Differentiating in a nonloop coordinate gives the actual polynomial of the
single-element contraction, with its true ground cardinality. -/
theorem pderiv_some_independencePolynomial_eq_contract (M : Matroid α) [M.Finite]
    {e : α} (he : M.IsNonloop e) :
    pderiv (some e) (independencePolynomial M) =
      independencePolynomial (M ／ {e}) := by
  classical
  rw [pderiv_some_independencePolynomial, independencePolynomial]
  have hcard : (M ／ {e}).E.ncard = M.E.ncard - 1 := by
    simp [he.mem_ground]
  rw [hcard]
  apply Finset.sum_bij (fun I _ => I.erase e)
  · intro I hI
    rcases Finset.mem_filter.mp hI with ⟨hI, heI⟩
    rw [mem_independentFinsets_contractElem_iff M he]
    refine ⟨Finset.notMem_erase e I, ?_⟩
    simpa only [Finset.insert_erase heI] using (mem_independentFinsets M I).mp hI
  · intro I hI J hJ hIJ
    have heI := (Finset.mem_filter.mp hI).2
    have heJ := (Finset.mem_filter.mp hJ).2
    have h := congrArg (fun I : Finset α => insert e I) hIJ
    simpa only [Finset.insert_erase heI, Finset.insert_erase heJ] using h
  · intro J hJ
    rcases (mem_independentFinsets_contractElem_iff M he J).mp hJ with ⟨heJ, hJ⟩
    refine ⟨insert e J, ?_, Finset.erase_insert heJ⟩
    simp only [Finset.mem_filter, mem_independentFinsets, Finset.mem_insert_self,
      and_true]
    exact hJ
  · intro I hI
    rfl

/-- Iterated differentiation in the homogenizing coordinate. -/
noncomputable def homogenizingDerivative (a : ℕ) (p : MvPolynomial (Option α) ℝ) :
    MvPolynomial (Option α) ℝ := (pderiv none)^[a] p

@[simp] theorem homogenizingDerivative_zero (p : MvPolynomial (Option α) ℝ) :
    homogenizingDerivative 0 p = p := rfl

@[simp] theorem homogenizingDerivative_succ (a : ℕ) (p : MvPolynomial (Option α) ℝ) :
    homogenizingDerivative (a + 1) p = pderiv none (homogenizingDerivative a p) :=
  Function.iterate_succ_apply' _ _ _

 theorem independentExponent_sub_none (n : ℕ) (I : Finset α) :
    independentExponent n I - Finsupp.single none 1 = independentExponent (n - 1) I := by
  classical
  ext o
  cases o with
  | none => simp only [Finsupp.tsub_apply, independentExponent_none, Finsupp.single_eq_same]; omega
  | some e => simp [independentExponent_some]

 theorem pderiv_none_independentMonomial (n : ℕ) (I : Finset α) :
    pderiv none (independentMonomial n I) =
      (n - I.card) • independentMonomial (n - 1) I := by
  classical
  simp only [independentMonomial, pderiv_monomial, independentExponent_none,
    independentExponent_sub_none, smul_monomial, nsmul_eq_mul, one_mul, mul_one]

 theorem homogenizingDerivative_independentMonomial (a n : ℕ) (I : Finset α) :
    homogenizingDerivative a (independentMonomial n I) =
      (n - I.card).descFactorial a • independentMonomial (n - a) I := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [homogenizingDerivative_succ, ih, map_nsmul,
      pderiv_none_independentMonomial, smul_smul, Nat.descFactorial_succ]
    have hsub : n - a - 1 = n - (a + 1) := by omega
    have hcoeff : n - a - I.card = n - I.card - a := by omega
    rw [hsub, hcoeff, Nat.mul_comm]

 theorem homogenizingDerivative_sum {β : Type*} (a : ℕ) (s : Finset β)
    (p : β → MvPolynomial (Option α) ℝ) :
    homogenizingDerivative a (∑ b ∈ s, p b) =
      ∑ b ∈ s, homogenizingDerivative a (p b) := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [homogenizingDerivative_succ, ih, map_sum]

 theorem homogenizingDerivative_independencePolynomial (M : Matroid α) [M.Finite] (a : ℕ) :
    homogenizingDerivative a (independencePolynomial M) =
      ∑ I ∈ independentFinsets M,
        (M.E.ncard - I.card).descFactorial a • independentMonomial (M.E.ncard - a) I := by
  rw [independencePolynomial, homogenizingDerivative_sum]
  simp only [homogenizingDerivative_independentMonomial]

@[simp] theorem coeff_homogenizingDerivative_exponent (M : Matroid α) [M.Finite]
    (a : ℕ) (I : Finset α) :
    MvPolynomial.lcoeff ℝ (independentExponent (M.E.ncard - a) I)
      (homogenizingDerivative a (independencePolynomial M)) =
      if M.Indep (I : Set α) then ((M.E.ncard - I.card).descFactorial a : ℝ) else 0 := by
  classical
  rw [homogenizingDerivative_independencePolynomial]
  simp only [MvPolynomial.lcoeff_apply, coeff_sum, independentMonomial, coeff_smul, coeff_monomial]
  have hexp (J : Finset α) :
      independentExponent (M.E.ncard - a) J = independentExponent (M.E.ncard - a) I ↔ J = I :=
    (independentExponent_injective (M.E.ncard - a)).eq_iff
  simp only [hexp]
  simp [mem_independentFinsets]

 theorem homogenizingDerivative_independencePolynomial_ne_zero
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a ≤ M.E.ncard) :
    homogenizingDerivative a (independencePolynomial M) ≠ 0 := by
  intro hz
  have h := coeff_homogenizingDerivative_exponent M a ∅
  rw [hz, map_zero] at h
  have hpos : (0 : ℝ) < (M.E.ncard.descFactorial a : ℝ) :=
    Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr ha)
  have hi : M.Indep (↑(∅ : Finset α) : Set α) := by simp only [Finset.coe_empty]; exact M.empty_indep
  simp only [hi, if_true, Finset.card_empty, Nat.sub_zero] at h
  exact (ne_of_gt hpos) h.symm

@[simp] theorem homogenizingDerivative_map_zero (a : ℕ) :
    homogenizingDerivative a (0 : MvPolynomial (Option α) ℝ) = 0 := by
  induction a with
  | zero => rfl
  | succ a ih => simp [homogenizingDerivative_succ, ih]

 theorem pderiv_homogenizingDerivative (a : ℕ) (p : MvPolynomial (Option α) ℝ)
    (i : Option α) :
    pderiv i (homogenizingDerivative a p) = homogenizingDerivative a (pderiv i p) := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [homogenizingDerivative_succ, pderiv_commutation, ih,
      homogenizingDerivative_succ]

 theorem homogenizingDerivative_independencePolynomial_homogeneous
    (M : Matroid α) [M.Finite] (a : ℕ) :
    (homogenizingDerivative a (independencePolynomial M)).IsHomogeneous (M.E.ncard - a) := by
  induction a with
  | zero => exact independencePolynomial_homogeneous M
  | succ a ih =>
    rw [homogenizingDerivative_succ]
    convert ih.pderiv using 1 <;> omega

 theorem homogenizingDerivative_independencePolynomial_nonnegative
    (M : Matroid α) [M.Finite] (a : ℕ) :
    NonnegativeCoefficients (homogenizingDerivative a (independencePolynomial M)) := by
  induction a with
  | zero => exact independencePolynomial_nonnegative M
  | succ a ih => simpa only [homogenizingDerivative_succ] using ih.pderiv none

 theorem pderiv_some_independencePolynomial_eq_zero_of_not_nonloop
    (M : Matroid α) [M.Finite] {e : α} (he : ¬M.IsNonloop e) :
    pderiv (some e) (independencePolynomial M) = 0 := by
  rw [pderiv_some_independencePolynomial]
  apply Finset.sum_eq_zero
  intro I hI
  rcases Finset.mem_filter.mp hI with ⟨hI, heI⟩
  exact (he (((mem_independentFinsets M I).mp hI).isNonloop_of_mem heI)).elim

 theorem pderiv_some_homogenizingDerivative_eq_contract
    (M : Matroid α) [M.Finite] (a : ℕ) {e : α} (he : M.IsNonloop e) :
    pderiv (some e) (homogenizingDerivative a (independencePolynomial M)) =
      homogenizingDerivative a (independencePolynomial (M ／ {e})) := by
  rw [pderiv_homogenizingDerivative, pderiv_some_independencePolynomial_eq_contract M he]

 theorem pderiv_some_homogenizingDerivative_eq_zero_of_not_nonloop
    (M : Matroid α) [M.Finite] (a : ℕ) {e : α} (he : ¬M.IsNonloop e) :
    pderiv (some e) (homogenizingDerivative a (independencePolynomial M)) = 0 := by
  rw [pderiv_homogenizingDerivative,
    pderiv_some_independencePolynomial_eq_zero_of_not_nonloop M he,
    homogenizingDerivative_map_zero]

/-- The finite active coordinate set includes the homogenizing coordinate and
exactly the nonloops. Its definition does not require a finite ambient type. -/
noncomputable def independenceActiveVariables (M : Matroid α) [M.Finite] : Finset (Option α) :=
  insert none ((M.ground_finite.toFinset.filter M.IsNonloop).image some)

@[simp] theorem none_mem_independenceActiveVariables (M : Matroid α) [M.Finite] :
    none ∈ independenceActiveVariables M := by simp [independenceActiveVariables]

@[simp] theorem some_mem_independenceActiveVariables (M : Matroid α) [M.Finite] (e : α) :
    some e ∈ independenceActiveVariables M ↔ M.IsNonloop e := by
  simp only [independenceActiveVariables, Finset.mem_insert, Option.some_ne_none,
    false_or, Finset.mem_image, Finset.mem_filter, M.ground_finite.mem_toFinset,
    Option.some.injEq, exists_eq_right]
  exact and_iff_right_of_imp (fun h => h.mem_ground)

 theorem pderiv_some_homogenizingDerivative_ne_zero
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a < M.E.ncard)
    {e : α} (he : M.IsNonloop e) :
    pderiv (some e) (homogenizingDerivative a (independencePolynomial M)) ≠ 0 := by
  rw [pderiv_some_homogenizingDerivative_eq_contract M a he]
  apply homogenizingDerivative_independencePolynomial_ne_zero
  simp only [Matroid.contract_ground, Set.ncard_sdiff_singleton_of_mem he.mem_ground]
  omega

 theorem pderiv_none_some_homogenizingDerivative_ne_zero
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a + 2 ≤ M.E.ncard)
    {e : α} (he : M.IsNonloop e) :
    pderiv none (pderiv (some e) (homogenizingDerivative a (independencePolynomial M))) ≠ 0 := by
  rw [pderiv_some_homogenizingDerivative_eq_contract M a he,
    ← homogenizingDerivative_succ]
  apply homogenizingDerivative_independencePolynomial_ne_zero
  simp only [Matroid.contract_ground, Set.ncard_sdiff_singleton_of_mem he.mem_ground]
  omega

 theorem pderiv_homogenizingDerivative_eq_zero_of_not_active
    (M : Matroid α) [M.Finite] (a : ℕ) (i : Option α)
    (hi : i ∉ independenceActiveVariables M) :
    pderiv i (homogenizingDerivative a (independencePolynomial M)) = 0 := by
  cases i with
  | none => exact (hi (none_mem_independenceActiveVariables M)).elim
  | some e =>
    apply pderiv_some_homogenizingDerivative_eq_zero_of_not_nonloop
    exact fun he => hi ((some_mem_independenceActiveVariables M e).mpr he)

theorem pderiv_none_homogenizingDerivative_ne_zero
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a < M.E.ncard) :
    pderiv none (homogenizingDerivative a (independencePolynomial M)) ≠ 0 := by
  rw [← homogenizingDerivative_succ]
  exact homogenizingDerivative_independencePolynomial_ne_zero M (a + 1) (by omega)

/-- Under positive remaining degree, the finite set above is exactly the
nonzero coordinate-derivative support. -/
theorem pderiv_homogenizingDerivative_ne_zero_iff_active
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a < M.E.ncard) (i : Option α) :
    pderiv i (homogenizingDerivative a (independencePolynomial M)) ≠ 0 ↔
      i ∈ independenceActiveVariables M := by
  constructor
  · intro hi
    by_contra h
    exact hi (pderiv_homogenizingDerivative_eq_zero_of_not_active M a i h)
  · intro hi
    cases i with
    | none => exact pderiv_none_homogenizingDerivative_ne_zero M a ha
    | some e =>
      exact pderiv_some_homogenizingDerivative_ne_zero M a ha
        ((some_mem_independenceActiveVariables M e).mp hi)

 theorem pderiv_some_twice_homogenizingDerivative_independencePolynomial
    (M : Matroid α) [M.Finite] (a : ℕ) (e : α) :
    pderiv (some e) (pderiv (some e)
      (homogenizingDerivative a (independencePolynomial M))) = 0 := by
  rw [pderiv_homogenizingDerivative, pderiv_homogenizingDerivative,
    pderiv_some_twice_independencePolynomial, homogenizingDerivative_map_zero]

/-- A nonempty proper cut of the actual derivative support has a nonzero mixed
partial crossing the cut. The homogenizing coordinate is the center of a star. -/
 theorem homogenizingDerivative_independencePolynomial_connected
    (M : Matroid α) [M.Finite] (a : ℕ) (ha : a + 2 ≤ M.E.ncard) :
    ∀ s : Finset (Option α), s ⊆ independenceActiveVariables M → s.Nonempty →
      s ≠ independenceActiveVariables M →
      ∃ i ∈ s, ∃ j ∈ independenceActiveVariables M, j ∉ s ∧
        pderiv i (pderiv j (homogenizingDerivative a (independencePolynomial M))) ≠ 0 := by
  intro s hst hs hne
  by_cases hn : none ∈ s
  · have hts : ¬independenceActiveVariables M ⊆ s :=
      fun h => hne (Finset.Subset.antisymm hst h)
    obtain ⟨j, hjt, hjs⟩ := Finset.not_subset.mp hts
    cases j with
    | none => exact (hjs hn).elim
    | some e =>
      refine ⟨none, hn, some e, hjt, hjs, ?_⟩
      exact pderiv_none_some_homogenizingDerivative_ne_zero M a ha
        ((some_mem_independenceActiveVariables M e).mp hjt)
  · obtain ⟨i, his⟩ := hs
    cases i with
    | none => exact (hn his).elim
    | some e =>
      refine ⟨some e, his, none, none_mem_independenceActiveVariables M, hn, ?_⟩
      rw [pderiv_commutation]
      exact pderiv_none_some_homogenizingDerivative_ne_zero M a ha
        ((some_mem_independenceActiveVariables M e).mp (hst his))

#print axioms pderiv_some_independencePolynomial_eq_contract
#print axioms pderiv_some_twice_independencePolynomial
#print axioms homogenizingDerivative_independencePolynomial
#print axioms coeff_homogenizingDerivative_exponent
#print axioms pderiv_some_homogenizingDerivative_eq_contract
#print axioms pderiv_homogenizingDerivative_ne_zero_iff_active
#print axioms pderiv_some_twice_homogenizingDerivative_independencePolynomial
#print axioms homogenizingDerivative_independencePolynomial_connected

end StrongMasonAudit

end SingleFileModule04
/- END ORIGINAL MODULE: Submission.MatroidDerivative -/

/- BEGIN ORIGINAL MODULE: Submission.CommonKernel -/
section SingleFileModule05





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

end SingleFileModule05
/- END ORIGINAL MODULE: Submission.CommonKernel -/

/- BEGIN ORIGINAL MODULE: Submission.SignatureBridge -/
section SingleFileModule06



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

end SingleFileModule06
/- END ORIGINAL MODULE: Submission.SignatureBridge -/

/- BEGIN ORIGINAL MODULE: Submission.BoundaryHyperplane -/
section SingleFileModule07


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

end SingleFileModule07
/- END ORIGINAL MODULE: Submission.BoundaryHyperplane -/

/- BEGIN ORIGINAL MODULE: Submission.CommonNormal -/
section SingleFileModule08



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

end SingleFileModule08
/- END ORIGINAL MODULE: Submission.CommonNormal -/

/- BEGIN ORIGINAL MODULE: Submission.HessianPositivity -/
section SingleFileModule09


set_option autoImplicit false

/-! The actual positive witness for homogeneous polynomial Hessians. A zero
partial derivative is handled by the zero bilinear form, separately from every
strict-positivity statement. -/

namespace StrongMasonAudit

open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp]
theorem hessianBilin_zero (w : ι → ℝ) :
    hessianBilin (0 : MvPolynomial ι ℝ) w = 0 := by
  have hz : formalHessian (0 : MvPolynomial ι ℝ) w = 0 := by
    ext i j
    simp [formalHessian]
  simp [hessianBilin, hz]

/-- A nonzero homogeneous polynomial of degree at least two, with nonnegative
coefficients, has the positive vector itself as a positive Hessian witness. -/
theorem hessianBilin_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : 0 < hessianBilin p w w w := by
  rw [hessianBilin_witness_euler hhom]
  have hd0 : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hd
  have hd1 : 0 < d - 1 :=
    Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hd)
  exact mul_pos (mul_pos (Nat.cast_pos.mpr hd0) (Nat.cast_pos.mpr hd1))
    (eval_pos_of_nonnegativeCoefficients hp hp0 hw)

theorem hessianBilin_pos_iff_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    0 < hessianBilin p w w w ↔ p ≠ 0 := by
  constructor
  · intro h hp0
    simp [hp0] at h
  · exact fun hp0 => hessianBilin_pos_of_nonnegativeCoefficients hhom hd hp hp0 hw

/-- The positive-witness hypothesis required for every nonzero first
derivative in the homogeneous common-kernel argument. -/
theorem hessianBilin_pderiv_pos_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (i : ι) (hi : pderiv i p ≠ 0)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) :
    0 < hessianBilin (pderiv i p) w w w := by
  exact hessianBilin_pos_of_nonnegativeCoefficients hhom.pderiv
    (Nat.le_sub_of_add_le hd) (hp.pderiv i) hi hw

/-- An inactive derivative contributes the zero form; every active derivative
has a strict positive witness. This disjunction does not discard inactive
variables from the index type. -/
theorem hessianBilin_pderiv_zero_or_pos
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ j, 0 < w j) (i : ι) :
    hessianBilin (pderiv i p) w = 0 ∨
      0 < hessianBilin (pderiv i p) w w w := by
  by_cases hi : pderiv i p = 0
  · left
    simp [hi]
  · right
    exact hessianBilin_pderiv_pos_of_nonnegativeCoefficients hhom hd hp i hi hw

#print axioms hessianBilin_zero
#print axioms hessianBilin_pos_of_nonnegativeCoefficients
#print axioms hessianBilin_pos_iff_of_nonnegativeCoefficients
#print axioms hessianBilin_pderiv_pos_of_nonnegativeCoefficients
#print axioms hessianBilin_pderiv_zero_or_pos

end StrongMasonAudit

end SingleFileModule09
/- END ORIGINAL MODULE: Submission.HessianPositivity -/

/- BEGIN ORIGINAL MODULE: Submission.SignaturePropagation -/
section SingleFileModule10


set_option autoImplicit false

/-! A connected finite-sum form of ALGV Lemma 3.4. The argument is algebraic:
it glues summands with a common nonzero normal, and uses no continuity of inertia. -/

namespace StrongMasonAudit

open scoped BigOperators

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem sigPos_smul_le (B : LinearMap.BilinForm ℝ V) {a : ℝ} (ha : 0 < a) :
    sigPos (a • B).toQuadraticMap ≤ sigPos B.toQuadraticMap := by
  obtain ⟨S, hdim, hpos⟩ :=
    exists_finrank_eq_sigPos_and_posDef (a • B).toQuadraticMap
  rw [← hdim]
  apply le_sigPos_of_posDef
  intro x hx
  have h := hpos x hx
  change 0 < a * B (x : V) (x : V) at h
  exact (mul_pos_iff_of_pos_left ha).mp h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Abstract symmetric third-derivative tensors propagate positive index through
connected support. Connectivity is the cut condition: every nonempty proper
set of indices has a positive tensor entry crossing its cut. -/
theorem sigPos_sum_le_one_of_connected_tensor_on
    (B : ι → LinearMap.BilinForm ℝ V) (e : ι → V)
    (hB : ∀ i, (B i).IsSymm)
    (hsig : ∀ i, sigPos (B i).toQuadraticMap ≤ 1)
    (hentry : ∀ i j k, 0 ≤ B i (e j) (e k))
    (hmixed : ∀ i j, B i (e j) = B j (e i))
    (t : Finset ι) (ht : t.Nonempty)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ ∃ k, 0 < B i (e j) (e k))
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    sigPos (∑ i ∈ t, a i • B i).toQuadraticMap ≤ 1 := by
  classical
  let A : Finset ι → LinearMap.BilinForm ℝ V := fun s => ∑ i ∈ s, a i • B i
  have hstep (s : Finset ι) (hst : s ⊆ t) (hs : s.Nonempty)
      (hsigS : sigPos (A s).toQuadraticMap ≤ 1) (hsu : s ≠ t) :
      ∃ j ∈ t, j ∉ s ∧ sigPos (A (insert j s)).toQuadraticMap ≤ 1 := by
    obtain ⟨i, hi, j, hjt, hj, k, hijk⟩ := hconnected s hst hs hsu
    let b : V := ∑ i ∈ s, a i • e i
    let c : V := a j • e j
    have hAsymm : (A s).IsSymm := by
      constructor
      intro x y
      simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro l hl
      rw [(hB l).eq]
    have hCsymm : (a j • B j).IsSymm := by
      constructor
      intro x y
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [(hB j).eq]
    have hnormal : (A s) c = (a j • B j) b := by
      ext z
      simp only [A, b, c, LinearMap.sum_apply, LinearMap.smul_apply,
        map_sum, map_smul, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      have h := congrArg (fun f : V →ₗ[ℝ] ℝ => f z) (hmixed l j)
      rw [h]
      ring
    have hAeval (x y : V) : (A s) x y = ∑ l ∈ s, a l * B l x y := by
      simp only [A, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have hnonzero : (A s) c ≠ 0 := by
      intro hz
      have heq : (A s) c (e k) = 0 := by rw [hz, LinearMap.zero_apply]
      have hpos : 0 < (A s) c (e k) := by
        rw [hAeval]
        simp only [c, LinearMap.BilinForm.smul_left]
        apply Finset.sum_pos'
        · intro l hl
          exact mul_nonneg (ha l).le (mul_nonneg (ha j).le (hentry l j k))
        · exact ⟨i, hi, mul_pos (ha i) (mul_pos (ha j) hijk)⟩
      exact (ne_of_gt hpos) heq
    have hcc : 0 ≤ (A s) c c := by
      rw [hAeval]
      simp only [c, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
      exact Finset.sum_nonneg fun l _ =>
        mul_nonneg (ha l).le (mul_nonneg (ha j).le
          (mul_nonneg (ha j).le (hentry l j j)))
    have hbb : 0 ≤ (a j • B j) b b := by
      change 0 ≤ a j * B j b b
      apply mul_nonneg (ha j).le
      simp only [b, map_sum, map_smul]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      apply Finset.sum_nonneg
      intro l hl
      apply mul_nonneg (ha l).le
      apply Finset.sum_nonneg
      intro m hm
      exact mul_nonneg (ha m).le (hentry j m l)
    refine ⟨j, hjt, hj, ?_⟩
    have hadd := sigPos_add_le_one_of_common_normal (A s) (a j • B j)
      hAsymm hCsymm hsigS ((sigPos_smul_le (B j) (ha j)).trans (hsig j))
      c b hcc hbb hnormal hnonzero
    have hAinsert : A (insert j s) = A s + a j • B j := by
      simp only [A, Finset.sum_insert hj]
      exact add_comm _ _
    rwa [hAinsert]
  have hgrow : ∀ n : ℕ, ∀ s : Finset ι, (t \ s).card = n → s ⊆ t →
      s.Nonempty → sigPos (A s).toQuadraticMap ≤ 1 →
      sigPos (A t).toQuadraticMap ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hst hs hsigS
      by_cases hsu : s = t
      · simpa only [hsu] using hsigS
      · obtain ⟨j, hjt, hj, hsigIns⟩ := hstep s hst hs hsigS hsu
        apply ih ((t \ insert j s).card) ?_ (insert j s) rfl (Finset.insert_subset hjt hst)
          (Finset.insert_nonempty j s) hsigIns
        rw [← hn, Finset.sdiff_insert]
        exact Finset.card_erase_lt_of_mem (by simp [hjt, hj])
  obtain ⟨i, hit⟩ := ht
  have hinit : sigPos (A {i}).toQuadraticMap ≤ 1 := by
    simpa only [A, Finset.sum_singleton] using
      (sigPos_smul_le (B i) (ha i)).trans (hsig i)
  simpa only [A] using hgrow (t \ {i}).card {i} rfl
    (Finset.singleton_subset_iff.mpr hit) (Finset.singleton_nonempty i) hinit

section Polynomial

open MvPolynomial

/-- Coordinate evaluation of the actual polynomial Hessian bilinear form. -/
theorem hessianBilin_coordinate (p : MvPolynomial ι ℝ) (w : ι → ℝ) (i j : ι) :
    hessianBilin p w (Pi.single i 1) (Pi.single j 1) = formalHessian p w i j := by
  classical
  simp [hessianBilin, Matrix.toBilin'_apply, Pi.single_apply]

/-- Equality of mixed third partials gives the common normals required in the
finite-sum gluing argument. -/
theorem hessianBilin_pderiv_mixed (p : MvPolynomial ι ℝ) (w : ι → ℝ) (i j : ι) :
    hessianBilin (pderiv i p) w (Pi.single j 1) =
      hessianBilin (pderiv j p) w (Pi.single i 1) := by
  classical
  have hthird (k : ι) : pderiv j (pderiv k (pderiv i p)) =
      pderiv i (pderiv k (pderiv j p)) := by
    rw [pderiv_commutation p k i, pderiv_commutation (pderiv k p) j i,
      pderiv_commutation p k j]
  ext z
  simp [hessianBilin, Matrix.toBilin'_apply, Pi.single_apply, formalHessian, hthird]

/-- A nonzero mixed second partial of degree at least one has a positive
third-partial entry at every strictly positive point. -/
theorem exists_pos_third_of_second_ne_zero
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) (i j : ι)
    (hij : pderiv i (pderiv j p) ≠ 0) :
    ∃ k, 0 < hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
  have hc : 0 < ((d - 2 : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 3) hd))
  have hsecond : 0 < formalHessian p w i j :=
    eval_pos_of_nonnegativeCoefficients ((hp.pderiv j).pderiv i) hij hw
  have hsum : 0 < ∑ k, w k * formalHessian (pderiv i p) w k j := by
    rw [formalHessian_euler_row hhom]
    exact mul_pos hc hsecond
  have hnonneg (k : ι) : 0 ≤ w k * formalHessian (pderiv i p) w k j := by
    apply mul_nonneg (hw k).le
    exact eval_nonneg_of_nonnegativeCoefficients (((hp.pderiv i).pderiv j).pderiv k)
      (fun l => (hw l).le)
  obtain ⟨k, _, hk⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ => hnonneg k)).mp hsum
  refine ⟨k, ?_⟩
  rw [hessianBilin_coordinate, formalHessian_symm (pderiv i p) w j k]
  exact (mul_pos_iff_of_pos_left (hw k)).mp hk

/-- Pointwise ALGV connected-derivative propagation. Connectivity is stated on
nonzero mixed second partials; entry positivity and equality of mixed third
partials are derived from the actual polynomial. -/
theorem homogeneous_derivative_sum_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (t : Finset ι) (ht : t.Nonempty)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    sigPos (∑ i ∈ t, a i • hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1 := by
  have hentry (i j k : ι) :
      0 ≤ hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
    rw [hessianBilin_coordinate]
    exact eval_nonneg_of_nonnegativeCoefficients (((hp.pderiv i).pderiv k).pderiv j)
      (fun l => (hw l).le)
  have hconn : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ ∃ k,
        0 < hessianBilin (pderiv i p) w (Pi.single j 1) (Pi.single k 1) := by
    intro s hst hs hne
    obtain ⟨i, hi, j, hjt, hj, hij⟩ := hconnected s hst hs hne
    obtain ⟨k, hk⟩ := exists_pos_third_of_second_ne_zero hhom hd hp hw i j hij
    exact ⟨i, hi, j, hjt, hj, k, hk⟩
  exact sigPos_sum_le_one_of_connected_tensor_on
    (fun i => hessianBilin (pderiv i p) w) (fun i => Pi.single i 1)
    (fun i => hessianBilin_isSymm (pderiv i p) w) hsig
    hentry (hessianBilin_pderiv_mixed p w) t ht hconn a ha

/-- The parent Hessian has positive index at most one if its nonzero derivative
support is connected and every derivative Hessian has positive index at most
one. Variables outside `t` are retained in the ambient Hessian and are required
to be inactive; no nonsingularity assumption is used. -/
theorem homogeneous_hessian_sigPos_le_one_of_connected
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (t : Finset ι) (ht : t.Nonempty)
    (hinactive : ∀ i ∉ t, pderiv i p = 0)
    (hconnected : ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0) :
    sigPos (hessianBilin p w).toQuadraticMap ≤ 1 := by
  have hc : 0 < ((d - 2 : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 2 < 3) hd))
  have hsum := homogeneous_derivative_sum_sigPos_le_one hhom hd hp hw hsig
    t ht hconnected w hw
  have hEuler : (∑ i ∈ t, w i • hessianBilin (pderiv i p) w) =
      ((d - 2 : ℕ) : ℝ) • hessianBilin p w := by
    have hfull : (∑ i ∈ t, w i • hessianBilin (pderiv i p) w) =
        ∑ i, w i • hessianBilin (pderiv i p) w := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro i _ hi
      simp [hinactive i hi]
    rw [hfull]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using
      (hessianBilin_euler hhom w x y).symm
  rw [hEuler] at hsum
  have hcancel : (((d - 2 : ℕ) : ℝ)⁻¹) •
      (((d - 2 : ℕ) : ℝ) • hessianBilin p w) = hessianBilin p w := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hbound := (sigPos_smul_le
    (((d - 2 : ℕ) : ℝ) • hessianBilin p w) (inv_pos.mpr hc)).trans hsum
  rwa [hcancel] at hbound

end Polynomial

#print axioms hessianBilin_coordinate
#print axioms hessianBilin_pderiv_mixed
#print axioms exists_pos_third_of_second_ne_zero
#print axioms homogeneous_derivative_sum_sigPos_le_one
#print axioms homogeneous_hessian_sigPos_le_one_of_connected

#print axioms sigPos_smul_le
#print axioms sigPos_sum_le_one_of_connected_tensor_on

end StrongMasonAudit

end SingleFileModule10
/- END ORIGINAL MODULE: Submission.SignaturePropagation -/

/- BEGIN ORIGINAL MODULE: Submission.DirectionalDerivative -/
section SingleFileModule11



set_option autoImplicit false

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Formal differentiation in a constant real direction. -/
noncomputable def directionalDerivative (v : ι → ℝ) (p : MvPolynomial ι ℝ) :
    MvPolynomial ι ℝ := ∑ i, v i • pderiv i p

@[simp] theorem directionalDerivative_add (v : ι → ℝ) (p q : MvPolynomial ι ℝ) :
    directionalDerivative v (p + q) =
      directionalDerivative v p + directionalDerivative v q := by
  simp [directionalDerivative, smul_add, Finset.sum_add_distrib]

@[simp] theorem pderiv_directionalDerivative
    (v : ι → ℝ) (p : MvPolynomial ι ℝ) (j : ι) :
    pderiv j (directionalDerivative v p) = directionalDerivative v (pderiv j p) := by
  simp only [directionalDerivative, map_sum, Derivation.map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [pderiv_commutation p j i]

@[simp] theorem eval_directionalDerivative
    (v : ι → ℝ) (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    eval w (directionalDerivative v p) = ∑ i, v i * eval w (pderiv i p) := by
  simp [directionalDerivative, smul_eq_C_mul]

theorem directionalDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (v : ι → ℝ) :
    (directionalDerivative v p).IsHomogeneous (d - 1) := by
  change directionalDerivative v p ∈ homogeneousSubmodule ι ℝ (d - 1)
  exact (homogeneousSubmodule ι ℝ (d - 1)).sum_mem (fun i _ =>
    (homogeneousSubmodule ι ℝ (d - 1)).smul_mem (v i) (hp.pderiv (i := i)))

theorem NonnegativeCoefficients.directionalDerivative
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 ≤ v i) :
    NonnegativeCoefficients (directionalDerivative v p) := by
  intro m
  simp only [MvPolynomial.lcoeff_apply]
  unfold StrongMasonAudit.directionalDerivative
  rw [coeff_sum]
  simp only [coeff_smul, smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) ((hp.pderiv i) m))

/-- The evaluated gradient, as a linear functional on displacement vectors. -/
noncomputable def gradientFunctional (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, eval w (pderiv i p) • LinearMap.proj i

@[simp] theorem gradientFunctional_apply
    (p : MvPolynomial ι ℝ) (w z : ι → ℝ) :
    gradientFunctional p w z = ∑ i, z i * eval w (pderiv i p) := by
  simp [gradientFunctional, mul_comm]

variable [DecidableEq ι]

/-- Differentiating in a direction and taking the gradient gives the
corresponding row functional of the Hessian. -/
theorem hessianBilin_row_eq_gradient_directionalDerivative
    (p : MvPolynomial ι ℝ) (w v : ι → ℝ) :
    hessianBilin p w v = gradientFunctional (directionalDerivative v p) w := by
  apply LinearMap.ext
  intro z
  simp only [hessianBilin, Matrix.toBilin'_apply, gradientFunctional_apply,
    pderiv_directionalDerivative, eval_directionalDerivative]
  change (∑ i, ∑ j, v i * formalHessian p w i j * z j) =
    ∑ j, z j * (∑ i, v i * formalHessian p w i j)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hessianBilin_directionalDerivative
    (p : MvPolynomial ι ℝ) (w v : ι → ℝ) :
    hessianBilin (directionalDerivative v p) w =
      ∑ i, v i • hessianBilin (pderiv i p) w := by
  have hm : formalHessian (directionalDerivative v p) w =
      ∑ i, v i • formalHessian (pderiv i p) w := by
    ext j k
    simp [formalHessian, directionalDerivative, smul_eq_C_mul, Matrix.sum_apply]
  have hb := congrArg
    (Matrix.toBilin' : Matrix ι ι ℝ ≃ₗ[ℝ] LinearMap.BilinForm ℝ (ι → ℝ)) hm
  simpa [hessianBilin] using hb

@[simp] theorem hessianBilin_add (p q : MvPolynomial ι ℝ) (w : ι → ℝ) :
    hessianBilin (p + q) w = hessianBilin p w + hessianBilin q w := by
  have hm : formalHessian (p + q) w = formalHessian p w + formalHessian q w := by
    ext i j
    simp [formalHessian]
  unfold hessianBilin
  rw [hm, map_add]

omit [Fintype ι] [DecidableEq ι] in
theorem formalHessian_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (i j : ι) :
    0 ≤ formalHessian p w i j :=
  eval_nonneg_of_nonnegativeCoefficients ((hp.pderiv j).pderiv i) hw

theorem hessianBilin_nonneg_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    {w x y : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i) :
    0 ≤ hessianBilin p w x y := by
  simp only [hessianBilin, Matrix.toBilin'_apply]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (hx i)
      (formalHessian_nonneg_of_nonnegativeCoefficients hp hw i j)) (hy j)))

omit [DecidableEq ι] in
/-- A positive-degree nonzero homogeneous polynomial with nonnegative
coefficients has nonzero gradient at every strictly positive point. -/
theorem gradientFunctional_ne_zero_of_nonnegativeCoefficients
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (hd : 1 ≤ d)
    (hcoeff : NonnegativeCoefficients p) (hp0 : p ≠ 0)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) : gradientFunctional p w ≠ 0 := by
  have hpos : 0 < gradientFunctional p w w := by
    rw [gradientFunctional_apply, homogeneous_euler_eval hp]
    exact mul_pos (Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd))
      (eval_pos_of_nonnegativeCoefficients hcoeff hp0 hw)
  intro hz
  exact (ne_of_gt hpos) (by rw [hz]; rfl)

#print axioms directionalDerivative_add
#print axioms pderiv_directionalDerivative
#print axioms eval_directionalDerivative
#print axioms directionalDerivative_isHomogeneous
#print axioms NonnegativeCoefficients.directionalDerivative
#print axioms gradientFunctional_apply
#print axioms hessianBilin_row_eq_gradient_directionalDerivative
#print axioms hessianBilin_directionalDerivative
#print axioms hessianBilin_add
#print axioms formalHessian_nonneg_of_nonnegativeCoefficients
#print axioms hessianBilin_nonneg_of_nonnegativeCoefficients
#print axioms gradientFunctional_ne_zero_of_nonnegativeCoefficients

end StrongMasonAudit

end SingleFileModule11
/- END ORIGINAL MODULE: Submission.DirectionalDerivative -/

/- BEGIN ORIGINAL MODULE: Submission.SignatureClosure -/
section SingleFileModule12





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

end SingleFileModule12
/- END ORIGINAL MODULE: Submission.SignatureClosure -/

/- BEGIN ORIGINAL MODULE: Submission.CompleteLogConcavity -/
section SingleFileModule13


set_option autoImplicit false

/-! The coordinate-quadratic sufficient criterion underlying ALGV Theorem 3.2.
This module uses positive-index language; it does not redefine log-concavity. -/

namespace StrongMasonAudit

open Filter MvPolynomial
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def iteratedPartialDerivative : List ι → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | i :: is, p => pderiv i (iteratedPartialDerivative is p)

noncomputable def iteratedDirectionalDerivative :
    List (ι → ℝ) → MvPolynomial ι ℝ → MvPolynomial ι ℝ
  | [], p => p
  | v :: vs, p => directionalDerivative v (iteratedDirectionalDerivative vs p)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem pderiv_iteratedPartialDerivative (is : List ι)
    (p : MvPolynomial ι ℝ) (i : ι) :
    pderiv i (iteratedPartialDerivative is p) =
      iteratedPartialDerivative is (pderiv i p) := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    change pderiv i (pderiv j (iteratedPartialDerivative js p)) =
      pderiv j (iteratedPartialDerivative js (pderiv i p))
    rw [pderiv_commutation (iteratedPartialDerivative js p) i j, ih]

omit [DecidableEq ι] in
@[simp] theorem pderiv_iteratedDirectionalDerivative (vs : List (ι → ℝ))
    (p : MvPolynomial ι ℝ) (i : ι) :
    pderiv i (iteratedDirectionalDerivative vs p) =
      iteratedDirectionalDerivative vs (pderiv i p) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [iteratedDirectionalDerivative, pderiv_directionalDerivative, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem iteratedPartialDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d) (is : List ι) :
    (iteratedPartialDerivative is p).IsHomogeneous (d - is.length) := by
  induction is with
  | nil => simpa only [iteratedPartialDerivative, List.length_nil, Nat.sub_zero] using hp
  | cons i is ih =>
    simpa only [iteratedPartialDerivative, List.length_cons, Nat.sub_sub] using ih.pderiv (i := i)

omit [DecidableEq ι] in
theorem iteratedDirectionalDerivative_isHomogeneous
    {p : MvPolynomial ι ℝ} {d : ℕ} (hp : p.IsHomogeneous d)
    (vs : List (ι → ℝ)) :
    (iteratedDirectionalDerivative vs p).IsHomogeneous (d - vs.length) := by
  induction vs with
  | nil => simpa only [iteratedDirectionalDerivative, List.length_nil, Nat.sub_zero] using hp
  | cons v vs ih =>
    simpa only [iteratedDirectionalDerivative, List.length_cons, Nat.sub_sub] using
      directionalDerivative_isHomogeneous ih v

omit [DecidableEq ι] in
theorem NonnegativeCoefficients.iteratedDirectionalDerivative
    {p : MvPolynomial ι ℝ} (hp : NonnegativeCoefficients p)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i) :
    NonnegativeCoefficients (iteratedDirectionalDerivative vs p) := by
  induction vs with
  | nil => exact hp
  | cons v vs ih =>
    exact (ih (fun u hu => hv u (List.mem_cons_of_mem v hu))).directionalDerivative
      (hv v (List.mem_cons_self))

/-- Positive directions detect every nonzero homogeneous polynomial of positive
degree with nonnegative coefficients. -/
theorem directionalDerivative_eq_zero_iff_of_pos
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 1 ≤ d) (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    directionalDerivative v p = 0 ↔ p = 0 := by
  constructor
  · intro hzero
    by_contra hp0
    have hpos : 0 < eval v (directionalDerivative v p) := by
      rw [eval_directionalDerivative, homogeneous_euler_eval hhom]
      exact mul_pos (Nat.cast_pos.mpr (by omega))
        (eval_pos_of_nonnegativeCoefficients hp hp0 hv)
    exact (ne_of_gt hpos) (by rw [hzero, map_zero])
  · intro hp0
    simp [hp0, directionalDerivative]

/-- An explicit cut formulation of connected active variable support. The zero
polynomial is included as a separate case. -/
def ConnectedPartialSupport (p : MvPolynomial ι ℝ) : Prop :=
  p = 0 ∨ ∃ t : Finset ι, t.Nonempty ∧
    (∀ i ∉ t, pderiv i p = 0) ∧
    ∀ s : Finset ι, s ⊆ t → s.Nonempty → s ≠ t →
      ∃ i ∈ s, ∃ j ∈ t, j ∉ s ∧ pderiv i (pderiv j p) ≠ 0

/-- Strictly positive directional differentiation preserves the cut graph when
the initial degree is at least three. -/
theorem ConnectedPartialSupport.directionalDerivative
    {p : MvPolynomial ι ℝ} {d : ℕ} (hconn : ConnectedPartialSupport p)
    (hhom : p.IsHomogeneous d) (hd : 3 ≤ d)
    (hp : NonnegativeCoefficients p)
    {v : ι → ℝ} (hv : ∀ i, 0 < v i) :
    ConnectedPartialSupport (directionalDerivative v p) := by
  rcases hconn with hzero | ⟨t, ht, hinactive, hcut⟩
  · left
    simp [hzero, StrongMasonAudit.directionalDerivative]
  · right
    refine ⟨t, ht, ?_, ?_⟩
    · intro i hi
      rw [pderiv_directionalDerivative, hinactive i hi]
      simp [StrongMasonAudit.directionalDerivative]
    · intro s hst hs hne
      obtain ⟨i, hi, j, hjt, hj, hij⟩ := hcut s hst hs hne
      refine ⟨i, hi, j, hjt, hj, ?_⟩
      simp only [pderiv_directionalDerivative]
      exact mt (directionalDerivative_eq_zero_iff_of_pos
        ((hhom.pderiv (i := j)).pderiv (i := i)) (by omega)
        ((hp.pderiv j).pderiv i) hv).mp hij

/-- A positive directional derivative preserves connected support throughout
all iterations whose final degree is at least two. -/
theorem ConnectedPartialSupport.iteratedDirectionalDerivative
    {p : MvPolynomial ι ℝ} {d : ℕ} (hconn : ConnectedPartialSupport p)
    (hhom : p.IsHomogeneous d) (hp : NonnegativeCoefficients p)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2) (hd : 2 ≤ d)
    (hv : ∀ v ∈ vs, ∀ i, 0 < v i) :
    ConnectedPartialSupport (iteratedDirectionalDerivative vs p) := by
  induction vs with
  | nil => exact hconn
  | cons v vs ih =>
    have hvvs : ∀ u ∈ vs, ∀ i, 0 < u i := fun u hu => hv u (List.mem_cons_of_mem v hu)
    exact (ih (by simp only [List.length_cons] at hlen; omega) hvvs).directionalDerivative
      (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by simp only [List.length_cons] at hlen; omega)
      (hp.iteratedDirectionalDerivative vs (fun u hu i => (hvvs u hu i).le))
      (hv v List.mem_cons_self)

/-- Pointwise parent-signature propagation with the zero-support case included. -/
theorem hessian_sigPos_le_one_of_connectedPartialSupport
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ConnectedPartialSupport p) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1) :
    sigPos (hessianBilin p w).toQuadraticMap ≤ 1 := by
  rcases hconn with hz | ⟨t, ht, hinactive, hcut⟩
  · rw [hz, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · exact homogeneous_hessian_sigPos_le_one_of_connected hhom hd hp hw hsig
      t ht hinactive hcut

/-- Pointwise positive-direction propagation with inactive variables retained. -/
theorem directionalDerivative_sigPos_le_one_of_connectedPartialSupport
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 3 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ConnectedPartialSupport p) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hsig : ∀ i, sigPos (hessianBilin (pderiv i p) w).toQuadraticMap ≤ 1)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    sigPos (hessianBilin (directionalDerivative v p) w).toQuadraticMap ≤ 1 := by
  rcases hconn with hz | ⟨t, ht, hinactive, hcut⟩
  · simp only [hz, StrongMasonAudit.directionalDerivative, map_zero,
      smul_zero, Finset.sum_const_zero, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · rw [hessianBilin_directionalDerivative]
    have hfull : (∑ i ∈ t, v i • hessianBilin (pderiv i p) w) =
        ∑ i, v i • hessianBilin (pderiv i p) w := by
      apply Finset.sum_subset (Finset.subset_univ t)
      intro i _ hi
      simp [hinactive i hi]
    rw [← hfull]
    exact homogeneous_derivative_sum_sigPos_le_one hhom hd hp hw hsig t ht hcut v hv

/-- Positive-direction part of the ALGV coordinate-quadratic criterion. The
connectivity hypothesis concerns only coordinate derivatives, and the signature
hypothesis only terminal quadratic coordinate derivatives. -/
theorem positive_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2)
    (hv : ∀ v ∈ vs, ∀ i, 0 < v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  induction d using Nat.strong_induction_on generalizing p vs with
  | h d ih =>
    by_cases hd2 : d = 2
    · have hvs : vs = [] := List.length_eq_zero_iff.mp (by omega)
      subst vs
      exact hbase [] (by simp [hd2]) w hw
    · have hd3 : 3 ≤ d := by omega
      have hpartial (i : ι) (us : List (ι → ℝ)) (hus : us.length ≤ (d - 1) - 2)
          (hu : ∀ u ∈ us, ∀ j, 0 < u j) :
          sigPos (hessianBilin (iteratedDirectionalDerivative us (pderiv i p)) w).toQuadraticMap ≤ 1 := by
        apply ih (d - 1) (by omega) hhom.pderiv (by omega) (hp.pderiv i) ?_ ?_ us hus hu
        · intro is his
          have hh := hconn (i :: is) (by simp only [List.length_cons]; omega)
          simpa only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative] using hh
        · intro is his z hz
          have hh := hbase (i :: is) (by simp only [List.length_cons]; omega) z hz
          simpa only [iteratedPartialDerivative, pderiv_iteratedPartialDerivative] using hh
      cases vs with
      | nil =>
        apply hessian_sigPos_le_one_of_connectedPartialSupport hhom hd3 hp
          (hconn [] (by simp)) hw
        intro i
        exact hpartial i [] (by simp) (by simp)
      | cons v vs =>
        have hvs : vs.length ≤ d - 3 := by simp only [List.length_cons] at hlen; omega
        have hvvs : ∀ u ∈ vs, ∀ i, 0 < u i := fun u hu => hv u (List.mem_cons_of_mem v hu)
        change sigPos (hessianBilin
          (directionalDerivative v (iteratedDirectionalDerivative vs p)) w).toQuadraticMap ≤ 1
        apply directionalDerivative_sigPos_le_one_of_connectedPartialSupport
          (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega)
          (hp.iteratedDirectionalDerivative vs (fun u hu i => (hvvs u hu i).le))
          ((hconn [] (by simp)).iteratedDirectionalDerivative hhom hp vs (by omega) hd hvvs) hw
        · intro i
          rw [pderiv_iteratedDirectionalDerivative]
          exact hpartial i vs (by omega) hvvs
        · exact hv v List.mem_cons_self

omit [DecidableEq ι] in
/-- Simultaneous regularization of a finite list of directions is continuous
under every polynomial evaluation. No positivity assumption is needed here. -/
theorem tendsto_eval_iteratedDirectionalDerivative_add
    (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    Tendsto (fun ε : ℝ => eval w (iteratedDirectionalDerivative
      (vs.map (fun v i => v i + ε)) p)) (𝓝[>] (0 : ℝ))
      (𝓝 (eval w (iteratedDirectionalDerivative vs p))) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  induction vs generalizing p with
  | nil => exact tendsto_const_nhds
  | cons v vs ih =>
    simp only [List.map_cons, iteratedDirectionalDerivative, eval_directionalDerivative,
      pderiv_iteratedDirectionalDerivative]
    apply tendsto_finsetSum Finset.univ
    intro i _
    have hvi : Tendsto (fun ε : ℝ => v i + ε) (𝓝[>] (0 : ℝ)) (𝓝 (v i)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := v i)).add heps
    exact hvi.mul (ih (pderiv i p))

/-- Pointwise Hessian convergence under simultaneous list regularization. -/
theorem tendsto_hessianBilin_iteratedDirectionalDerivative_add
    (vs : List (ι → ℝ)) (p : MvPolynomial ι ℝ) (w x y : ι → ℝ) :
    Tendsto (fun ε : ℝ => hessianBilin (iteratedDirectionalDerivative
      (vs.map (fun v i => v i + ε)) p) w x y) (𝓝[>] (0 : ℝ))
      (𝓝 (hessianBilin (iteratedDirectionalDerivative vs p) w x y)) := by
  simp only [hessianBilin, Matrix.toBilin'_apply, formalHessian,
    pderiv_iteratedDirectionalDerivative]
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((tendsto_const_nhds (x := x i)).mul
    (tendsto_eval_iteratedDirectionalDerivative_add vs (pderiv i (pderiv j p)) w)).mul
    (tendsto_const_nhds (x := y j))

/-- The ALGV coordinate-quadratic criterion for arbitrary nonnegative
iterated directions down to degree two, expressed by positive index. -/
theorem nonnegative_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hlen : vs.length ≤ d - 2)
    (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  by_cases hz : iteratedDirectionalDerivative vs p = 0
  · rw [hz, hessianBilin_zero, sigPos_zero_bilinForm]
    exact Nat.zero_le 1
  · let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
      hessianBilin (iteratedDirectionalDerivative (vs.map (fun v i => v i + ε)) p) w
    apply sigPos_le_one_of_tendsto_of_positive_witness B
      (hessianBilin (iteratedDirectionalDerivative vs p) w) (𝓝[>] (0 : ℝ))
    · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
    · apply Filter.Eventually.mono (self_mem_nhdsWithin :
        ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
      intro ε hε
      apply positive_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase
        (vs.map (fun v i => v i + ε)) (by simpa only [List.length_map] using hlen) ?_ w hw
      intro v hvmap i
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hvmap
      exact add_pos_of_nonneg_of_pos (hv u hu i) hε
    · intro x y
      exact tendsto_hessianBilin_iteratedDirectionalDerivative_add vs p w x y
    · exact hessianBilin_pos_of_nonnegativeCoefficients
        (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega)
        (hp.iteratedDirectionalDerivative vs hv) hz hw

/-- Homogeneous constants and linear polynomials have zero Hessian. -/
theorem hessianBilin_eq_zero_of_isHomogeneous_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d) (hd : d ≤ 1)
    (w : ι → ℝ) : hessianBilin p w = 0 := by
  have hm : formalHessian p w = 0 := by
    ext i j
    have hj : (pderiv j p).IsHomogeneous 0 := by
      simpa only [show d - 1 = 0 by omega] using hhom.pderiv (i := j)
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hj
    change eval w (pderiv i (pderiv j p)) = 0
    rw [hj, pderiv_C, map_zero]
  simp only [hessianBilin, hm, map_zero]

/-- The coordinate-quadratic criterion controls arbitrary finite lists of
nonnegative directions, including derivatives of order beyond the degree. -/
theorem all_nonnegative_iterated_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  by_cases hlen : vs.length ≤ d - 2
  · exact nonnegative_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase vs hlen hv w hw
  · rw [hessianBilin_eq_zero_of_isHomogeneous_le_one
      (iteratedDirectionalDerivative_isHomogeneous hhom vs) (by omega) w,
      sigPos_zero_bilinForm]
    exact Nat.zero_le 1

omit [Fintype ι] [DecidableEq ι] in
/-- Polynomial evaluation is continuous when the same scalar is added to every
coordinate. This finite-sum proof needs no topology on the polynomial ring. -/
theorem tendsto_eval_add_scalar (p : MvPolynomial ι ℝ) (w : ι → ℝ) :
    Tendsto (fun ε : ℝ => eval (fun i => w i + ε) p) (𝓝[>] (0 : ℝ))
      (𝓝 (eval w p)) := by
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simp only [eval_eq]
  apply tendsto_finsetSum p.support
  intro m _
  apply Tendsto.mul tendsto_const_nhds
  apply tendsto_finsetProd m.support
  intro i _
  have hi : Tendsto (fun ε : ℝ => w i + ε) (𝓝[>] (0 : ℝ)) (𝓝 (w i)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := w i)).add heps
  exact hi.pow (m i)

/-- Pointwise Hessian closure as the evaluation vector approaches the boundary. -/
theorem tendsto_hessianBilin_add_scalar (p : MvPolynomial ι ℝ) (w x y : ι → ℝ) :
    Tendsto (fun ε : ℝ => hessianBilin p (fun i => w i + ε) x y) (𝓝[>] (0 : ℝ))
      (𝓝 (hessianBilin p w x y)) := by
  simp only [hessianBilin, Matrix.toBilin'_apply, formalHessian]
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact ((tendsto_const_nhds (x := x i)).mul
    (tendsto_eval_add_scalar (pderiv i (pderiv j p)) w)).mul
    (tendsto_const_nhds (x := y j))

/-- The full Hessian positive-index consequence of ALGV Theorem 3.2: all finite
nonnegative directional derivatives at all nonnegative evaluation vectors. -/
theorem complete_hessian_sigPos_le_one
    {p : MvPolynomial ι ℝ} {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : 2 ≤ d) (hp : NonnegativeCoefficients p)
    (hconn : ∀ is : List ι, is.length ≤ d - 2 →
      ConnectedPartialSupport (iteratedPartialDerivative is p))
    (hbase : ∀ is : List ι, is.length = d - 2 → ∀ w : ι → ℝ,
      (∀ i, 0 < w i) →
      sigPos (hessianBilin (iteratedPartialDerivative is p) w).toQuadraticMap ≤ 1)
    (vs : List (ι → ℝ)) (hv : ∀ v ∈ vs, ∀ i, 0 ≤ v i)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    sigPos (hessianBilin (iteratedDirectionalDerivative vs p) w).toQuadraticMap ≤ 1 := by
  let B : ℝ → LinearMap.BilinForm ℝ (ι → ℝ) := fun ε =>
    hessianBilin (iteratedDirectionalDerivative vs p) (fun i => w i + ε)
  apply sigPos_le_one_of_tendsto B
    (hessianBilin (iteratedDirectionalDerivative vs p) w) (𝓝[>] (0 : ℝ))
  · exact Eventually.of_forall (fun ε => hessianBilin_isSymm _ _)
  · apply Filter.Eventually.mono (self_mem_nhdsWithin :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioi 0)
    intro ε hε
    exact all_nonnegative_iterated_hessian_sigPos_le_one hhom hd hp hconn hbase vs hv
      (fun i => w i + ε) (fun i => add_pos_of_nonneg_of_pos (hw i) hε)
  · intro x y
    exact tendsto_hessianBilin_add_scalar (iteratedDirectionalDerivative vs p) w x y

#print axioms hessianBilin_eq_zero_of_isHomogeneous_le_one
#print axioms all_nonnegative_iterated_hessian_sigPos_le_one
#print axioms tendsto_eval_add_scalar
#print axioms tendsto_hessianBilin_add_scalar
#print axioms complete_hessian_sigPos_le_one

#print axioms tendsto_eval_iteratedDirectionalDerivative_add
#print axioms tendsto_hessianBilin_iteratedDirectionalDerivative_add
#print axioms nonnegative_iterated_hessian_sigPos_le_one

#print axioms hessian_sigPos_le_one_of_connectedPartialSupport
#print axioms directionalDerivative_sigPos_le_one_of_connectedPartialSupport
#print axioms positive_iterated_hessian_sigPos_le_one

#print axioms directionalDerivative_eq_zero_iff_of_pos
#print axioms ConnectedPartialSupport.directionalDerivative
#print axioms ConnectedPartialSupport.iteratedDirectionalDerivative

end StrongMasonAudit

end SingleFileModule13
/- END ORIGINAL MODULE: Submission.CompleteLogConcavity -/

/- BEGIN ORIGINAL MODULE: Submission.MatroidQuadratic -/
section SingleFileModule14








set_option autoImplicit false

/-! The quadratic matroid base case: parallel classes are defined by equality
of singleton closures. All quadratic inequalities below allow arbitrary real
weights. No nonnegativity of the weight vector is imposed. -/

namespace StrongMasonAudit

open scoped BigOperators

section FinitePartition

variable {E C : Type*} [Fintype E] [Fintype C] [DecidableEq C]

/-- Sum of real weights in a fiber of a finite partition map. -/
def fiberWeight (f : E → C) (z : E → ℝ) (c : C) : ℝ :=
  ∑ e, if f e = c then z e else 0

theorem sum_fiberWeight (f : E → C) (z : E → ℝ) :
    ∑ c, fiberWeight f z c = ∑ e, z e := by
  unfold fiberWeight
  rw [Finset.sum_comm]
  simp

theorem sum_sq_fiberWeight (f : E → C) (z : E → ℝ) :
    ∑ c, fiberWeight f z c ^ 2 =
      ∑ e, ∑ e', if f e = f e' then z e * z e' else 0 := by
  calc
    ∑ c, fiberWeight f z c ^ 2 =
        ∑ c, ∑ e, if f e = c then z e * fiberWeight f z c else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      rw [pow_two, fiberWeight, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : f e = c <;> simp [h]
    _ = ∑ e, z e * fiberWeight f z (f e) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp
    _ = ∑ e, ∑ e', if f e = f e' then z e * z e' else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [fiberWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e' _
      by_cases h : f e = f e' <;> simp [h, eq_comm]

theorem partition_pair_sum (f : E → C) (z : E → ℝ) :
    (∑ e, z e) ^ 2 - ∑ c, fiberWeight f z c ^ 2 =
      ∑ e, ∑ e', if f e ≠ f e' then z e * z e' else 0 := by
  rw [sum_sq_fiberWeight, pow_two, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e' _
  by_cases h : f e = f e' <;> simp [h]

/-- Cauchy--Schwarz on the class sums, without a sign restriction on `z`. -/
theorem partition_sum_sq_le (f : E → C) (z : E → ℝ) :
    (∑ e, z e) ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, fiberWeight f z c ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C)
    (fun _ => (1 : ℝ)) (fiberWeight f z)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sum_fiberWeight] using h

/-- A partition into at most `n` classes gives the quadratic index-one bound. -/
theorem partition_quadratic_bound (f : E → C) (z : E → ℝ) (n : ℕ)
    (hcard : Fintype.card C ≤ n) :
    (n - 1 : ℝ) * (∑ e, z e) ^ 2 ≥
      (n : ℝ) * ∑ e, ∑ e', if f e ≠ f e' then z e * z e' else 0 := by
  have hc : (Fintype.card C : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
  have hs : 0 ≤ ∑ c, fiberWeight f z c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := (partition_sum_sq_le f z).trans (mul_le_mul_of_nonneg_right hc hs)
  rw [← partition_pair_sum]
  nlinarith

end FinitePartition

section MatroidParallel

attribute [local instance] Classical.propDecidable

variable {E : Type*} (M : Matroid E)

/-- The parallel-class setoid on nonloops. -/
def nonloopParallelSetoid : Setoid {e // M.IsNonloop e} :=
  Setoid.ker (fun e => M.closure {e.val})

abbrev NonloopParallelClass := Quotient (nonloopParallelSetoid M)

def nonloopParallelClass (e : {e // M.IsNonloop e}) : NonloopParallelClass M :=
  Quotient.mk (nonloopParallelSetoid M) e

theorem nonloopParallelClass_eq_iff (e f : {e // M.IsNonloop e}) :
    nonloopParallelClass M e = nonloopParallelClass M f ↔
      M.closure {e.val} = M.closure {f.val} :=
  Quotient.eq

theorem nonloopParallelClass_ne_iff (e f : {e // M.IsNonloop e}) :
    nonloopParallelClass M e ≠ nonloopParallelClass M f ↔
      e.val ≠ f.val ∧ M.Indep {e.val, f.val} := by
  rw [ne_eq, nonloopParallelClass_eq_iff,
    e.property.closure_eq_closure_iff_eq_or_dep f.property]
  simp only [not_or, not_not, ne_eq]

variable [M.Finite]

noncomputable instance matroidNonloopFintype : Fintype {e // M.IsNonloop e} :=
  (M.ground_finite.subset (fun _ h => h.mem_ground)).fintype

noncomputable instance nonloopParallelClassFintype : Fintype (NonloopParallelClass M) :=
  Fintype.ofFinite _

theorem nonloopParallelClass_card_le_ground :
    Fintype.card (NonloopParallelClass M) ≤ M.E.ncard := by
  classical
  letI : Fintype M.E := M.ground_finite.fintype
  have hN : Fintype.card {e // M.IsNonloop e} ≤ Fintype.card M.E := by
    apply Fintype.card_le_of_injective
      (fun e : {e // M.IsNonloop e} => (⟨e.val, e.property.mem_ground⟩ : M.E))
    intro e f h
    exact Subtype.ext (congrArg (fun x : M.E => x.val) h)
  have hC : Fintype.card (NonloopParallelClass M) ≤ Fintype.card {e // M.IsNonloop e} :=
    Fintype.card_le_of_surjective (nonloopParallelClass M)
      (by intro c; exact Quotient.exists_rep c)
  simpa only [Set.fintypeCard_eq_ncard] using hC.trans hN

/-- The ordered independent-pair quadratic sum on the actual nonloops of a
finite-ground matroid, on an arbitrary ambient type. All weights may have
arbitrary signs. The normalization uses the exact ground-set cardinality. -/
theorem matroid_quadratic_bound_nonloops (z : E → ℝ) :
    (M.E.ncard - 1 : ℝ) * (∑ e : {e // M.IsNonloop e}, z e.val) ^ 2 ≥
      (M.E.ncard : ℝ) *
        ∑ e : {e // M.IsNonloop e}, ∑ f : {e // M.IsNonloop e},
          if e.val ≠ f.val ∧ M.Indep {e.val, f.val} then z e.val * z f.val else 0 := by
  classical
  simpa only [nonloopParallelClass_ne_iff] using
    partition_quadratic_bound (nonloopParallelClass M) (fun e => z e.val)
      M.E.ncard (nonloopParallelClass_card_le_ground M)

/-- The precise parallel-class decomposition underlying the quadratic bound. -/
theorem matroid_independent_pair_decomposition (z : E → ℝ) :
    (∑ e : {e // M.IsNonloop e}, z e.val) ^ 2 -
        ∑ c : NonloopParallelClass M,
          fiberWeight (nonloopParallelClass M) (fun e => z e.val) c ^ 2 =
      ∑ e : {e // M.IsNonloop e}, ∑ f : {e // M.IsNonloop e},
        if e.val ≠ f.val ∧ M.Indep {e.val, f.val} then z e.val * z f.val else 0 := by
  classical
  simpa only [nonloopParallelClass_ne_iff] using
    partition_pair_sum (nonloopParallelClass M) (fun e => z e.val)

end MatroidParallel


section FiniteAmbient

attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] (M : Matroid E)

theorem sum_nonloops_eq_sum_ite (z : E → ℝ) :
    (∑ e : {e // M.IsNonloop e}, z e.val) =
      ∑ e, if M.IsNonloop e then z e else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter M.IsNonloop) (by simp) z]
  exact Finset.sum_filter _ _

theorem sum_nonloops_eq_sum_of_support (z : E → ℝ)
    (hz : ∀ e, ¬M.IsNonloop e → z e = 0) :
    (∑ e : {e // M.IsNonloop e}, z e.val) = ∑ e, z e := by
  rw [sum_nonloops_eq_sum_ite]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : M.IsNonloop e <;> simp [h, hz e]

theorem independent_pair_sum_eq_nonloop_sum (z : E → ℝ) :
    (∑ e, ∑ f, if e ≠ f ∧ M.Indep {e, f} then z e * z f else 0) =
      ∑ e : {e // M.IsNonloop e}, ∑ f : {e // M.IsNonloop e},
        if e.val ≠ f.val ∧ M.Indep {e.val, f.val} then z e.val * z f.val else 0 := by
  classical
  have hinner (e : E) :
      (∑ f : {f // M.IsNonloop f},
        if e ≠ f.val ∧ M.Indep {e, f.val} then z e * z f.val else 0) =
      ∑ f, if e ≠ f ∧ M.Indep {e, f} then z e * z f else 0 := by
    apply sum_nonloops_eq_sum_of_support M (fun f => if e ≠ f ∧ M.Indep {e, f} then z e * z f else 0)
    intro f hf
    split_ifs with h
    · exact (hf (h.2.isNonloop_of_mem (by simp))).elim
    · rfl
  simp_rw [hinner]
  symm
  apply sum_nonloops_eq_sum_of_support M (fun e => ∑ f, if e ≠ f ∧ M.Indep {e, f} then z e * z f else 0)
  intro e he
  apply Finset.sum_eq_zero
  intro f _
  split_ifs with h
  · exact (he (h.2.isNonloop_of_mem (by simp))).elim
  · rfl

/-- The matroid quadratic bound expressed directly in ambient coordinates;
loops and elements outside the ground have zero contribution. -/
theorem matroid_quadratic_bound (z : E → ℝ) (n : ℕ) (hcard : M.E.ncard ≤ n) :
    (n - 1 : ℝ) * (∑ e, if M.IsNonloop e then z e else 0) ^ 2 ≥
      (n : ℝ) * ∑ e, ∑ f, if e ≠ f ∧ M.Indep {e, f} then z e * z f else 0 := by
  classical
  rw [independent_pair_sum_eq_nonloop_sum, ← sum_nonloops_eq_sum_ite]
  simpa only [nonloopParallelClass_ne_iff] using
    partition_quadratic_bound (nonloopParallelClass M) (fun e => z e.val)
      n ((nonloopParallelClass_card_le_ground M).trans hcard)

/-- The Hessian-shaped matrix of the homogenized matroid quadratic. -/
noncomputable def matroidQuadraticMatrix (n : ℕ) : Matrix (Option E) (Option E) ℝ :=
  fun i j => match i, j with
    | none, none => (n : ℝ) * (n - 1)
    | none, some e => if M.IsNonloop e then (n - 1 : ℝ) else 0
    | some e, none => if M.IsNonloop e then (n - 1 : ℝ) else 0
    | some e, some f => if e ≠ f ∧ M.Indep {e, f} then 1 else 0

omit [Fintype E] in
theorem matroidQuadraticMatrix_isSymm (n : ℕ) :
    (matroidQuadraticMatrix M n).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro i j
  cases i <;> cases j <;>
    simp [matroidQuadraticMatrix, ne_comm, Set.pair_comm]

noncomputable def matroidQuadraticBilin (n : ℕ) :
    LinearMap.BilinForm ℝ (Option E → ℝ) := (matroidQuadraticMatrix M n).toBilin'

theorem matroidQuadraticBilin_diag (n : ℕ) (x : Option E → ℝ) :
    matroidQuadraticBilin M n x x =
      (n : ℝ) * (n - 1) * x none ^ 2 +
      2 * (n - 1 : ℝ) * x none * (∑ e, if M.IsNonloop e then x (some e) else 0) +
      ∑ e, ∑ f, if e ≠ f ∧ M.Indep {e, f} then x (some e) * x (some f) else 0 := by
  classical
  have hcross : (∑ e, if M.IsNonloop e then x none * (n - 1) * x (some e) else 0) =
      (n - 1 : ℝ) * x none * ∑ e, if M.IsNonloop e then x (some e) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : M.IsNonloop e
    · simp only [if_pos h]
      ring
    · simp [h]
  have hcross' : (∑ e, if M.IsNonloop e then x (some e) * (n - 1) * x none else 0) =
      (n - 1 : ℝ) * x none * ∑ e, if M.IsNonloop e then x (some e) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases h : M.IsNonloop e
    · simp only [if_pos h]
      ring
    · simp [h]
  simp only [matroidQuadraticBilin, Matrix.toBilin'_apply, Fintype.sum_option,
    matroidQuadraticMatrix, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
    Finset.sum_add_distrib]
  rw [hcross, hcross']
  ring

/-- Normal of the nonpositive hyperplane of the matroid quadratic. -/
noncomputable def matroidQuadraticNormal (n : ℕ) : (Option E → ℝ) →ₗ[ℝ] ℝ :=
  (n : ℝ) • LinearMap.proj none +
    ∑ e, if M.IsNonloop e then LinearMap.proj (some e) else 0

theorem matroidQuadraticNormal_apply (n : ℕ) (x : Option E → ℝ) :
    matroidQuadraticNormal M n x =
      (n : ℝ) * x none + ∑ e, if M.IsNonloop e then x (some e) else 0 := by
  classical
  simp [matroidQuadraticNormal, LinearMap.sum_apply, LinearMap.proj_apply, apply_ite, ite_apply]

theorem matroidQuadraticNormal_ne_zero (n : ℕ) (hn : 0 < n) :
    matroidQuadraticNormal M n ≠ 0 := by
  classical
  intro h
  have hx := congrArg (fun L : (Option E → ℝ) →ₗ[ℝ] ℝ => L (Pi.single none 1)) h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  apply hn'
  simpa [matroidQuadraticNormal_apply, Pi.single_apply] using hx

/-- The actual homogenized matroid quadratic is nonpositive on the kernel
of its explicit normal, including all loop coordinates. -/
theorem matroidQuadraticBilin_nonpos_on_kernel (n : ℕ)
    (hn : 0 < n) (hcard : M.E.ncard ≤ n) (x : Option E → ℝ)
    (hx : matroidQuadraticNormal M n x = 0) :
    matroidQuadraticBilin M n x x ≤ 0 := by
  classical
  have hbound := matroid_quadratic_bound M (fun e => x (some e)) n hcard
  have hcalc : (n : ℝ) * matroidQuadraticBilin M n x x =
      (n - 1 : ℝ) * (matroidQuadraticNormal M n x) ^ 2 +
      (n : ℝ) * (∑ e, ∑ f, if e ≠ f ∧ M.Indep {e, f}
        then x (some e) * x (some f) else 0) -
      (n - 1 : ℝ) * (∑ e, if M.IsNonloop e then x (some e) else 0) ^ 2 := by
    rw [matroidQuadraticBilin_diag, matroidQuadraticNormal_apply]
    ring
  have hprod : (n : ℝ) * matroidQuadraticBilin M n x x ≤ 0 := by
    rw [hcalc, hx]
    simpa only [sq, zero_mul, mul_zero, zero_add, sub_nonpos] using hbound
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  by_contra h
  exact (not_le_of_gt (mul_pos hn' (lt_of_not_ge h))) hprod

/-- Positive index at most one for the actual matroid adjacency matrix with
homogenizing entry `n(n-1)` and nonloop mixed entries `n-1`. -/
theorem matroidQuadraticBilin_sigPos_le_one (n : ℕ)
    (hn : 0 < n) (hcard : M.E.ncard ≤ n) :
    sigPos (matroidQuadraticBilin M n).toQuadraticMap ≤ 1 := by
  classical
  apply sigPos_le_one_of_nonpos_on_kernel _ (matroidQuadraticNormal M n)
    (matroidQuadraticNormal_ne_zero M n hn)
  intro x hx
  exact matroidQuadraticBilin_nonpos_on_kernel M n hn hcard x hx

end FiniteAmbient

#print axioms partition_pair_sum
#print axioms partition_quadratic_bound
#print axioms nonloopParallelClass_ne_iff
#print axioms nonloopParallelClass_card_le_ground
#print axioms matroid_independent_pair_decomposition
#print axioms matroid_quadratic_bound_nonloops
#print axioms matroid_quadratic_bound
#print axioms matroidQuadraticMatrix_isSymm
#print axioms matroidQuadraticBilin_diag
#print axioms matroidQuadraticBilin_nonpos_on_kernel
#print axioms matroidQuadraticBilin_sigPos_le_one

end StrongMasonAudit

end SingleFileModule14
/- END ORIGINAL MODULE: Submission.MatroidQuadratic -/

/- BEGIN ORIGINAL MODULE: Submission.MatroidQuadraticPolynomial -/
section SingleFileModule15



set_option autoImplicit false

/-! The actual quadratic terminal Hessian of the independent-set polynomial. -/

namespace StrongMasonAudit

open MvPolynomial Classical
open scoped BigOperators

theorem formalHessian_eq_coeff_of_homogeneous_two
    {ι : Type*} (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 2)
    (w : ι → ℝ) (i j : ι) :
    formalHessian p w i j =
      MvPolynomial.lcoeff ℝ (Finsupp.single i 1 + Finsupp.single j 1) p *
        (if i = j then 2 else 1) := by
  classical
  simp only [MvPolynomial.lcoeff_apply]
  have hzero : (pderiv i (pderiv j p)).IsHomogeneous 0 := by
    simpa using (hp.pderiv (i := j)).pderiv (i := i)
  have heq : pderiv i (pderiv j p) = C (MvPolynomial.lcoeff ℝ 0 (pderiv i (pderiv j p))) :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous ι).mpr hzero)
  change eval w (pderiv i (pderiv j p)) = _
  rw [heq, eval_C, MvPolynomial.lcoeff_apply, coeff_pderiv, coeff_pderiv]
  by_cases hij : i = j
  · subst j
    norm_num
  · simp [hij, Ne.symm hij]

variable {α : Type*}

theorem independentExponent_two_empty :
    independentExponent 2 (∅ : Finset α) =
      Finsupp.single none 1 + Finsupp.single none 1 := by
  classical
  ext o
  cases o <;> simp

theorem independentExponent_two_singleton (e : α) :
    independentExponent 2 {e} =
      Finsupp.single none 1 + Finsupp.single (some e) 1 := by
  classical
  ext o
  cases o with
  | none => simp
  | some j =>
    by_cases h : j = e
    · subst j
      simp
    · simp [h]

theorem independentExponent_two_pair (e f : α) (hef : e ≠ f) :
    independentExponent 2 {e, f} =
      Finsupp.single (some e) 1 + Finsupp.single (some f) 1 := by
  classical
  ext o
  cases o with
  | none => simp [hef]
  | some j =>
    by_cases hje : j = e
    · subst j
      simp [hef]
    · by_cases hjf : j = f
      · subst j
        simp [Ne.symm hef]
      · simp [hje, hjf]

private theorem descFactorial_quadratic_none (n : ℕ) (hn : 2 ≤ n) :
    (n.descFactorial (n - 2) : ℝ) * 2 =
      ((n - 2).factorial : ℝ) * (n : ℝ) * (n - 1) := by
  have hdiff : n - (n - 2) = 2 := by omega
  have ha := Nat.factorial_mul_descFactorial (n := n) (k := n - 2) (Nat.sub_le n 2)
  rw [hdiff, Nat.factorial_two] at ha
  have hb := Nat.factorial_mul_descFactorial (n := n) (k := 2) hn
  have hnat : n.descFactorial (n - 2) * 2 = (n - 2).factorial * (n - 1) * n := by
    calc
      _ = n.factorial := by simpa only [Nat.mul_comm] using ha
      _ = (n - 2).factorial * ((n - 1) * n) := by
        rw [← hb]
        simp [Nat.descFactorial_succ, Nat.descFactorial_zero]
      _ = _ := by ring
  have hr : (n.descFactorial (n - 2) : ℝ) * 2 =
      ((n - 2).factorial : ℝ) * ((n - 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hnat
  rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] at hr
  calc
    _ = _ := hr
    _ = _ := by ring

private theorem descFactorial_quadratic_mixed (n : ℕ) (hn : 2 ≤ n) :
    ((n - 1).descFactorial (n - 2) : ℝ) =
      ((n - 2).factorial : ℝ) * (n - 1) := by
  have hdiff : (n - 1) - (n - 2) = 1 := by omega
  have ha := Nat.factorial_mul_descFactorial (n := n - 1) (k := n - 2) (by omega)
  rw [hdiff, Nat.factorial_one, one_mul] at ha
  have hb := Nat.factorial_mul_descFactorial (n := n - 1) (k := 1) (by omega)
  have hb' : (n - 2).factorial * (n - 1) = (n - 1).factorial := by
    simpa only [Nat.sub_sub, Nat.descFactorial_one] using hb
  have hr : ((n - 1).descFactorial (n - 2) : ℝ) =
      ((n - 2).factorial : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast ha.trans hb'.symm
  simpa only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using hr

section FiniteAmbient

variable [Fintype α] (M : Matroid α) [M.Finite]

omit [Fintype α] in
theorem formalHessian_homogenizingDerivative_independencePolynomial
    {n : ℕ} (hcard : M.E.ncard = n) (hn : 2 ≤ n) (w : Option α → ℝ) :
    formalHessian (homogenizingDerivative (n - 2) (independencePolynomial M)) w =
      ((n - 2).factorial : ℝ) • matroidQuadraticMatrix M n := by
  classical
  have hdiff : n - (n - 2) = 2 := by omega
  have hhom : (homogenizingDerivative (n - 2)
      (independencePolynomial M)).IsHomogeneous 2 := by
    simpa only [hcard, hdiff] using
      homogenizingDerivative_independencePolynomial_homogeneous M (n - 2)
  have hc (I : Finset α) :
      MvPolynomial.lcoeff ℝ (independentExponent 2 I)
        (homogenizingDerivative (n - 2) (independencePolynomial M)) =
      if M.Indep (I : Set α) then ((n - I.card).descFactorial (n - 2) : ℝ) else 0 := by
    simpa only [hcard, hdiff] using coeff_homogenizingDerivative_exponent M (n - 2) I
  ext i j
  cases i with
  | none =>
    cases j with
    | none =>
      rw [formalHessian_eq_coeff_of_homogeneous_two _ hhom,
        ← independentExponent_two_empty, hc]
      simp only [Finset.coe_empty, M.empty_indep, if_true, Finset.card_empty,
        Nat.sub_zero, Matrix.smul_apply, smul_eq_mul, matroidQuadraticMatrix]
      simpa only [mul_assoc] using descFactorial_quadratic_none n hn
    | some e =>
      rw [formalHessian_eq_coeff_of_homogeneous_two _ hhom,
        ← independentExponent_two_singleton e, hc]
      simp only [Finset.coe_singleton, Matroid.indep_singleton, Finset.card_singleton,
        reduceCtorEq, if_false, mul_one, Matrix.smul_apply, smul_eq_mul,
        matroidQuadraticMatrix]
      by_cases he : M.IsNonloop e
      · simpa only [he, if_true] using descFactorial_quadratic_mixed n hn
      · simp [he]
  | some e =>
    cases j with
    | none =>
      rw [formalHessian_symm]
      rw [formalHessian_eq_coeff_of_homogeneous_two _ hhom,
        ← independentExponent_two_singleton e, hc]
      simp only [Finset.coe_singleton, Matroid.indep_singleton, Finset.card_singleton,
        reduceCtorEq, if_false, mul_one, Matrix.smul_apply, smul_eq_mul,
        matroidQuadraticMatrix]
      by_cases he : M.IsNonloop e
      · simpa only [he, if_true] using descFactorial_quadratic_mixed n hn
      · simp [he]
    | some f =>
      by_cases hef : e = f
      · subst f
        simp [formalHessian, pderiv_homogenizingDerivative,
          pderiv_some_twice_independencePolynomial, matroidQuadraticMatrix]
      · rw [formalHessian_eq_coeff_of_homogeneous_two _ hhom,
          ← independentExponent_two_pair e f hef, hc]
        simp [hef, Nat.descFactorial_self, matroidQuadraticMatrix]

theorem hessianBilin_homogenizingDerivative_independencePolynomial
    (hn : 2 ≤ M.E.ncard) (w : Option α → ℝ) :
    hessianBilin (homogenizingDerivative (M.E.ncard - 2) (independencePolynomial M)) w =
      ((M.E.ncard - 2).factorial : ℝ) • matroidQuadraticBilin M M.E.ncard := by
  have hm := formalHessian_homogenizingDerivative_independencePolynomial M rfl hn w
  have hb := congrArg
    (Matrix.toBilin' : Matrix (Option α) (Option α) ℝ ≃ₗ[ℝ]
      LinearMap.BilinForm ℝ (Option α → ℝ)) hm
  simpa [hessianBilin, matroidQuadraticBilin] using hb

theorem hessianBilin_homogenizingDerivative_independencePolynomial_sigPos_le_one
    (hn : 2 ≤ M.E.ncard) (w : Option α → ℝ) :
    sigPos (hessianBilin
      (homogenizingDerivative (M.E.ncard - 2) (independencePolynomial M)) w).toQuadraticMap ≤ 1 := by
  rw [hessianBilin_homogenizingDerivative_independencePolynomial M hn w]
  exact (sigPos_smul_le _ (Nat.cast_pos.mpr (Nat.factorial_pos _))).trans
    (matroidQuadraticBilin_sigPos_le_one M M.E.ncard (by omega) le_rfl)

end FiniteAmbient

set_option pp.fullNames true

#print axioms formalHessian_eq_coeff_of_homogeneous_two
#print axioms independentExponent_two_empty
#print axioms independentExponent_two_singleton
#print axioms independentExponent_two_pair
#print axioms formalHessian_homogenizingDerivative_independencePolynomial
#print axioms hessianBilin_homogenizingDerivative_independencePolynomial
#print axioms hessianBilin_homogenizingDerivative_independencePolynomial_sigPos_le_one

end StrongMasonAudit

end SingleFileModule15
/- END ORIGINAL MODULE: Submission.MatroidQuadraticPolynomial -/

/- BEGIN ORIGINAL MODULE: Submission.MatroidSignature -/
section SingleFileModule16



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

end SingleFileModule16
/- END ORIGINAL MODULE: Submission.MatroidSignature -/

/- BEGIN ORIGINAL MODULE: Submission.PolynomialRename -/
section SingleFileModule17



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

end SingleFileModule17
/- END ORIGINAL MODULE: Submission.PolynomialRename -/

/- BEGIN ORIGINAL MODULE: Submission.BinarySpecialization -/
section SingleFileModule18


set_option autoImplicit false

/-! Merging all element variables gives exactly the challenge's count sequence. -/

namespace StrongMasonAudit

open MvPolynomial
open scoped BigOperators

variable {α : Type*}

def binaryVariable : Option α → Bool
  | none => false
  | some _ => true

theorem rename_independentMonomial_binary (n : ℕ) (I : Finset α) :
    rename binaryVariable (independentMonomial n I) =
      (X false : MvPolynomial Bool ℝ) ^ (n - I.card) * X true ^ I.card := by
  classical
  simp [independentMonomial_eq_product, binaryVariable]

theorem rename_independencePolynomial_binary_counts
    (M : Matroid α) [M.Finite] :
    rename binaryVariable (independencePolynomial M) =
      ∑ k ∈ Finset.range (M.E.ncard + 1),
        C ({I ∈ Set.powersetCard α k | M.Indep I}.ncard : ℝ) *
          X false ^ (M.E.ncard - k) * X true ^ k := by
  classical
  rw [independencePolynomial, map_sum]
  simp only [rename_independentMonomial_binary]
  have h := independentFinsets_sum_by_card M
    (fun k : ℕ => (X false : MvPolynomial Bool ℝ) ^ (M.E.ncard - k) * X true ^ k)
  simpa only [nsmul_eq_mul, independentSetCount_finset_bridge, map_natCast,
    mul_assoc] using h

#print axioms rename_independentMonomial_binary
#print axioms rename_independencePolynomial_binary_counts

end StrongMasonAudit

end SingleFileModule18
/- END ORIGINAL MODULE: Submission.BinarySpecialization -/

/- BEGIN ORIGINAL MODULE: Submission.HessianInequality -/
section SingleFileModule19


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

end SingleFileModule19
/- END ORIGINAL MODULE: Submission.HessianInequality -/

/- BEGIN ORIGINAL MODULE: Submission.MatroidBinaryInequality -/
section SingleFileModule20




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

end SingleFileModule20
/- END ORIGINAL MODULE: Submission.MatroidBinaryInequality -/

/- BEGIN ORIGINAL MODULE: Submission.CountNormalization -/
section SingleFileModule21


set_option autoImplicit false

/-! Clearing the factorial factors supplied by a binary quadratic derivative. -/

namespace StrongMasonAudit

theorem factorial_certificate_normalization
    (a b c : ℝ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hcert :
      (a * ((n - k + 1).factorial : ℝ) * ((k - 1).factorial : ℝ)) *
        (c * ((n - k - 1).factorial : ℝ) * ((k + 1).factorial : ℝ)) ≤
      (b * ((n - k).factorial : ℝ) * (k.factorial : ℝ)) ^ 2) :
    a * c * ((k + 1 : ℕ) : ℝ) * ((n - k + 1 : ℕ) : ℝ) ≤
      b ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) := by
  have ht : 0 < n - k := Nat.sub_pos_of_lt hkn
  have hfk : (k.factorial : ℝ) = (k : ℝ) * ((k - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt hk)).symm
  have hft : ((n - k).factorial : ℝ) =
      ((n - k : ℕ) : ℝ) * ((n - k - 1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (Nat.ne_of_gt ht)).symm
  have hfk1 : ((k + 1).factorial : ℝ) =
      ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ k
  have hft1 : ((n - k + 1).factorial : ℝ) =
      ((n - k + 1 : ℕ) : ℝ) * ((n - k).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ (n - k)
  let f : ℝ := (k : ℝ) * ((n - k : ℕ) : ℝ) *
    (((n - k - 1).factorial : ℝ) * ((k - 1).factorial : ℝ)) ^ 2
  have hf : 0 < f := by
    exact mul_pos
      (mul_pos (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr ht))
      (sq_pos_of_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
        (Nat.cast_pos.mpr (Nat.factorial_pos _))))
  apply (mul_le_mul_iff_left₀ hf).mp
  have hleft :
      a * c * ((k + 1 : ℕ) : ℝ) * ((n - k + 1 : ℕ) : ℝ) * f =
      (a * ((n - k + 1).factorial : ℝ) * ((k - 1).factorial : ℝ)) *
        (c * ((n - k - 1).factorial : ℝ) * ((k + 1).factorial : ℝ)) := by
    rw [hft1, hfk1, hfk, hft]
    dsimp [f]
    ring
  have hright : b ^ 2 * (k : ℝ) * ((n - k : ℕ) : ℝ) * f =
      (b * ((n - k).factorial : ℝ) * (k.factorial : ℝ)) ^ 2 := by
    rw [hfk, hft]
    dsimp [f]
    ring
  rwa [hleft, hright]

/-- The exact natural-number inequality expected by the benchmark follows
from the factorial-weighted Hessian certificate. -/
theorem nat_count_inequality_of_factorial_certificate
    (I : ℕ → ℕ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hcert :
      ((I (k - 1) : ℝ) * ((n - k + 1).factorial : ℝ) * ((k - 1).factorial : ℝ)) *
        ((I (k + 1) : ℝ) * ((n - k - 1).factorial : ℝ) * ((k + 1).factorial : ℝ)) ≤
      ((I k : ℝ) * ((n - k).factorial : ℝ) * (k.factorial : ℝ)) ^ 2) :
    I (k - 1) * I (k + 1) * (k + 1) * (n - k + 1) ≤
      I k ^ 2 * k * (n - k) := by
  exact_mod_cast factorial_certificate_normalization
    (I (k - 1)) (I k) (I (k + 1)) n k hk hkn hcert

#print axioms factorial_certificate_normalization
#print axioms nat_count_inequality_of_factorial_certificate

end StrongMasonAudit

end SingleFileModule21
/- END ORIGINAL MODULE: Submission.CountNormalization -/

/- BEGIN ORIGINAL MODULE: Submission.BinaryCoefficients -/
section SingleFileModule22


set_option autoImplicit false

/-! Exact factorial extraction from binary count polynomials. -/

namespace StrongMasonAudit

open MvPolynomial Classical
open scoped BigOperators

variable {ι : Type*}

/-- Iterated coordinate partials are the corresponding unit-direction derivatives. -/
theorem directionalDerivative_single_basis [Fintype ι] [DecidableEq ι] (i : ι) (p : MvPolynomial ι ℝ) :
    directionalDerivative (Pi.single i 1) p = pderiv i p := by
  classical
  simp [directionalDerivative, Pi.single_apply]

 theorem iteratedPartialDerivative_eq_directional_single [Fintype ι] [DecidableEq ι]
    (is : List ι) (p : MvPolynomial ι ℝ) :
    iteratedPartialDerivative is p =
      iteratedDirectionalDerivative (is.map (fun i => Pi.single i 1)) p := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [iteratedPartialDerivative, List.map_cons, iteratedDirectionalDerivative,
      directionalDerivative_single_basis, ih]

 theorem iteratedPartialDerivative_append (is js : List ι) (p : MvPolynomial ι ℝ) :
    iteratedPartialDerivative (is ++ js) p =
      iteratedPartialDerivative is (iteratedPartialDerivative js p) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, iteratedPartialDerivative, ih]

/-- Coefficients after repeated differentiation in one coordinate, without any
homogeneity or coefficient-sign assumption. -/
theorem coeff_iteratedPartialDerivative_replicate
    (i : ι) (a : ℕ) (p : MvPolynomial ι ℝ) (m : ι →₀ ℕ) :
    MvPolynomial.lcoeff ℝ m (iteratedPartialDerivative (List.replicate a i) p) =
      MvPolynomial.lcoeff ℝ (m + Finsupp.single i a) p * ((m i + a).descFactorial a : ℝ) := by
  simp only [MvPolynomial.lcoeff_apply]
  induction a generalizing m with
  | zero => simp [iteratedPartialDerivative]
  | succ a ih =>
    simp only [List.replicate_succ, iteratedPartialDerivative, coeff_pderiv]
    rw [ih]
    have hexp : m + Finsupp.single i 1 + Finsupp.single i a =
        m + Finsupp.single i (a + 1) := by
      rw [add_assoc, ← Finsupp.single_add, Nat.add_comm 1 a]
    have hind : ((m + Finsupp.single i 1 : ι →₀ ℕ) i) + a = m i + (a + 1) := by simp; omega
    have hsub : m i + (a + 1) - a = m i + 1 := by omega
    rw [hexp, hind, Nat.descFactorial_succ, hsub, Nat.cast_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

/-- False is the homogenizing variable; true is the common element variable. -/
noncomputable def binaryCountPolynomial (n : ℕ) (I : ℕ → ℕ) : MvPolynomial Bool ℝ :=
  ∑ j ∈ Finset.range (n + 1), C (I j : ℝ) * X false ^ (n - j) * X true ^ j

noncomputable def binaryExponent (n j : ℕ) : Bool →₀ ℕ :=
  Finsupp.single false (n - j) + Finsupp.single true j

@[simp] theorem binaryExponent_false (n j : ℕ) : binaryExponent n j false = n - j := by
  simp [binaryExponent]

@[simp] theorem binaryExponent_true (n j : ℕ) : binaryExponent n j true = j := by
  simp [binaryExponent]

 theorem binaryExponent_injective (n : ℕ) : Function.Injective (binaryExponent n) := by
  intro j k h
  simpa using congrArg (fun m : Bool →₀ ℕ => m true) h

 theorem binaryCountPolynomial_eq_monomial (n : ℕ) (I : ℕ → ℕ) :
    binaryCountPolynomial n I =
      ∑ j ∈ Finset.range (n + 1), monomial (binaryExponent n j) (I j : ℝ) := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [binaryExponent, ← mul_one (I j : ℝ), ← monomial_mul]
  simp only [X_pow_eq_monomial]
  rw [C_mul']
  simp [smul_monomial]

@[simp] theorem coeff_binaryCountPolynomial_exponent (n : ℕ) (I : ℕ → ℕ)
    (j : ℕ) (hj : j ≤ n) :
    MvPolynomial.lcoeff ℝ (binaryExponent n j) (binaryCountPolynomial n I) = (I j : ℝ) := by
  rw [binaryCountPolynomial_eq_monomial]
  simp only [MvPolynomial.lcoeff_apply, coeff_sum, coeff_monomial, (binaryExponent_injective n).eq_iff]
  simp [Finset.mem_range.mpr (by omega : j < n + 1)]

/-- A convenient two-block coordinate derivative. -/
noncomputable def binaryPartialDerivative (a b : ℕ) (p : MvPolynomial Bool ℝ) :
    MvPolynomial Bool ℝ :=
  iteratedPartialDerivative (List.replicate a false)
    (iteratedPartialDerivative (List.replicate b true) p)

@[simp] theorem pderiv_false_binaryPartialDerivative (a b : ℕ) (p : MvPolynomial Bool ℝ) :
    pderiv false (binaryPartialDerivative a b p) = binaryPartialDerivative (a + 1) b p := by
  simp only [binaryPartialDerivative, List.replicate_succ, iteratedPartialDerivative]

@[simp] theorem pderiv_true_binaryPartialDerivative (a b : ℕ) (p : MvPolynomial Bool ℝ) :
    pderiv true (binaryPartialDerivative a b p) = binaryPartialDerivative a (b + 1) p := by
  simp only [binaryPartialDerivative, List.replicate_succ, iteratedPartialDerivative,
    pderiv_iteratedPartialDerivative]

 theorem eval_zero_binaryPartialDerivative (n : ℕ) (I : ℕ → ℕ) (a b : ℕ)
    (hab : a + b = n) :
    eval (0 : Bool → ℝ) (binaryPartialDerivative a b (binaryCountPolynomial n I)) =
      (I b : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) := by
  rw [eval_zero]
  change MvPolynomial.lcoeff ℝ 0 (binaryPartialDerivative a b (binaryCountPolynomial n I)) = _
  simp only [binaryPartialDerivative, coeff_iteratedPartialDerivative_replicate,
    zero_add, Finsupp.zero_apply, Finsupp.single_eq_of_ne (by decide : true ≠ false),
    Nat.descFactorial_self]
  have hexp : Finsupp.single false a + Finsupp.single true b = binaryExponent n b := by
    dsimp [binaryExponent]
    congr 2
    omega
  rw [hexp, coeff_binaryCountPolynomial_exponent n I b (by omega)]
  ring

/-- The derivative orders that leave the three neighboring coefficients in a
binary quadratic. -/
def binaryDerivativeIndices (n k : ℕ) : List Bool :=
  List.replicate (n - k - 1) false ++ List.replicate (k - 1) true

noncomputable def binaryQuadraticDerivative (n : ℕ) (I : ℕ → ℕ) (k : ℕ) :
    MvPolynomial Bool ℝ :=
  iteratedPartialDerivative (binaryDerivativeIndices n k) (binaryCountPolynomial n I)

 theorem binaryQuadraticDerivative_eq_binaryPartialDerivative (n : ℕ) (I : ℕ → ℕ) (k : ℕ) :
    binaryQuadraticDerivative n I k =
      binaryPartialDerivative (n - k - 1) (k - 1) (binaryCountPolynomial n I) := by
  simp only [binaryQuadraticDerivative, binaryDerivativeIndices,
    iteratedPartialDerivative_append, binaryPartialDerivative]

 theorem binaryQuadraticDerivative_eq_iteratedDirectionalDerivative
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) :
    binaryQuadraticDerivative n I k =
      iteratedDirectionalDerivative
        ((binaryDerivativeIndices n k).map (fun i => Pi.single i 1))
        (binaryCountPolynomial n I) :=
  iteratedPartialDerivative_eq_directional_single _ _

 theorem formalHessian_binaryQuadraticDerivative_false_false
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    formalHessian (binaryQuadraticDerivative n I k) (0 : Bool → ℝ) false false =
      (I (k - 1) : ℝ) * ((n - k + 1).factorial : ℝ) * ((k - 1).factorial : ℝ) := by
  rw [binaryQuadraticDerivative_eq_binaryPartialDerivative]
  simp only [formalHessian, pderiv_false_binaryPartialDerivative]
  have ha : n - k - 1 + 1 + 1 = n - k + 1 := by omega
  rw [ha]
  exact eval_zero_binaryPartialDerivative n I (n - k + 1) (k - 1) (by omega)

 theorem formalHessian_binaryQuadraticDerivative_false_true
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    formalHessian (binaryQuadraticDerivative n I k) (0 : Bool → ℝ) false true =
      (I k : ℝ) * ((n - k).factorial : ℝ) * (k.factorial : ℝ) := by
  rw [binaryQuadraticDerivative_eq_binaryPartialDerivative]
  simp only [formalHessian, pderiv_true_binaryPartialDerivative,
    pderiv_false_binaryPartialDerivative]
  have ha : n - k - 1 + 1 = n - k := by omega
  have hb : k - 1 + 1 = k := by omega
  rw [ha, hb]
  exact eval_zero_binaryPartialDerivative n I (n - k) k (by omega)

 theorem formalHessian_binaryQuadraticDerivative_true_true
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    formalHessian (binaryQuadraticDerivative n I k) (0 : Bool → ℝ) true true =
      (I (k + 1) : ℝ) * ((n - k - 1).factorial : ℝ) * ((k + 1).factorial : ℝ) := by
  rw [binaryQuadraticDerivative_eq_binaryPartialDerivative]
  simp only [formalHessian, pderiv_true_binaryPartialDerivative]
  have hb : k - 1 + 1 + 1 = k + 1 := by omega
  rw [hb]
  exact eval_zero_binaryPartialDerivative n I (n - k - 1) (k + 1) (by omega)

 theorem hessianBilin_binaryQuadraticDerivative_false_false
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
        (Pi.single false 1) (Pi.single false 1) =
      (I (k - 1) : ℝ) * ((n - k + 1).factorial : ℝ) * ((k - 1).factorial : ℝ) := by
  rw [hessianBilin_coordinate]
  exact formalHessian_binaryQuadraticDerivative_false_false n I k hk hkn

 theorem hessianBilin_binaryQuadraticDerivative_false_true
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
        (Pi.single false 1) (Pi.single true 1) =
      (I k : ℝ) * ((n - k).factorial : ℝ) * (k.factorial : ℝ) := by
  rw [hessianBilin_coordinate]
  exact formalHessian_binaryQuadraticDerivative_false_true n I k hk hkn

 theorem hessianBilin_binaryQuadraticDerivative_true_true
    (n : ℕ) (I : ℕ → ℕ) (k : ℕ) (hk : 0 < k) (hkn : k < n) :
    hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
        (Pi.single true 1) (Pi.single true 1) =
      (I (k + 1) : ℝ) * ((n - k - 1).factorial : ℝ) * ((k + 1).factorial : ℝ) := by
  rw [hessianBilin_coordinate]
  exact formalHessian_binaryQuadraticDerivative_true_true n I k hk hkn

/-- The exact natural count inequality follows from the actual two-direction
Hessian certificate, after extracting all three factorial factors. -/
theorem nat_count_inequality_of_binaryQuadratic_certificate
    (I : ℕ → ℕ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hcert :
      hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
          (Pi.single false 1) (Pi.single false 1) *
        hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
          (Pi.single true 1) (Pi.single true 1) ≤
      (hessianBilin (binaryQuadraticDerivative n I k) (0 : Bool → ℝ)
          (Pi.single false 1) (Pi.single true 1)) ^ 2) :
    I (k - 1) * I (k + 1) * (k + 1) * (n - k + 1) ≤
      I k ^ 2 * k * (n - k) := by
  apply nat_count_inequality_of_factorial_certificate I n k hk hkn
  simpa only [hessianBilin_binaryQuadraticDerivative_false_false n I k hk hkn,
    hessianBilin_binaryQuadraticDerivative_false_true n I k hk hkn,
    hessianBilin_binaryQuadraticDerivative_true_true n I k hk hkn] using hcert

 theorem nat_count_inequality_of_binaryQuadratic_sigPos
    (I : ℕ → ℕ) (n k : ℕ) (hk : 0 < k) (hkn : k < n)
    (hsig : sigPos (hessianBilin (binaryQuadraticDerivative n I k)
      (0 : Bool → ℝ)).toQuadraticMap ≤ 1) :
    I (k - 1) * I (k + 1) * (k + 1) * (n - k + 1) ≤
      I k ^ 2 * k * (n - k) := by
  apply nat_count_inequality_of_binaryQuadratic_certificate I n k hk hkn
  apply bilin_diagonal_mul_le_cross_sq _ (hessianBilin_isSymm _ _) hsig
  rw [hessianBilin_binaryQuadraticDerivative_false_false n I k hk hkn]
  positivity

#print axioms coeff_iteratedPartialDerivative_replicate
#print axioms eval_zero_binaryPartialDerivative
#print axioms formalHessian_binaryQuadraticDerivative_false_false
#print axioms formalHessian_binaryQuadraticDerivative_false_true
#print axioms formalHessian_binaryQuadraticDerivative_true_true
#print axioms nat_count_inequality_of_binaryQuadratic_certificate
#print axioms nat_count_inequality_of_binaryQuadratic_sigPos

end StrongMasonAudit

end SingleFileModule22
/- END ORIGINAL MODULE: Submission.BinaryCoefficients -/

/- BEGIN ORIGINAL MODULE: Submission.GroundReduction -/
section SingleFileModule23


set_option autoImplicit false

/-! Exact transfer from an arbitrary ambient type to the finite ground subtype. -/

namespace StrongMasonAudit

variable {α : Type*}

noncomputable def groundFinsetEmbedding (M : Matroid α) :
    Finset M.E ↪ Finset α :=
  ⟨Finset.map (Function.Embedding.subtype _), Finset.map_injective _⟩

@[simp] theorem groundFinsetEmbedding_card (M : Matroid α) (I : Finset M.E) :
    (groundFinsetEmbedding M I).card = I.card := Finset.card_map _

theorem independentFinsets_ground_map (M : Matroid α) [M.Finite] :
    (independentFinsets (M.restrictSubtype M.E)).map (groundFinsetEmbedding M) =
      independentFinsets M := by
  classical
  ext I
  constructor
  · intro hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.mp hI
    apply (mem_independentFinsets M _).mpr
    have hJ' := (mem_independentFinsets (M.restrictSubtype M.E) J).mp hJ
    rw [Matroid.restrictSubtype_indep_iff] at hJ'
    change M.Indep (J.map (Function.Embedding.subtype _) : Set α)
    simpa using hJ'
  · intro hI
    have hInd := (mem_independentFinsets M I).mp hI
    let J : Finset M.E := I.subtype (· ∈ M.E)
    have hmap : groundFinsetEmbedding M J = I :=
      Finset.subtype_map_of_mem (fun x hx => hInd.subset_ground hx)
    apply Finset.mem_map.mpr
    refine ⟨J, ?_, hmap⟩
    apply (mem_independentFinsets (M.restrictSubtype M.E) J).mpr
    rw [Matroid.restrictSubtype_indep_iff]
    have hcoe : Subtype.val '' (J : Set M.E) =
        (groundFinsetEmbedding M J : Set α) := by
      simp [groundFinsetEmbedding]
    rw [hcoe, hmap]
    exact hInd

/-- Passing to the ground subtype preserves the exact challenge count. -/
theorem independentSetCount_ground_eq (M : Matroid α) [M.Finite] (k : ℕ) :
    {I ∈ Set.powersetCard M.E k | (M.restrictSubtype M.E).Indep I}.ncard =
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard := by
  classical
  rw [independentSetCount_finset_bridge, independentSetCount_finset_bridge,
    ← independentFinsets_ground_map M, Finset.filter_map]
  simp only [Function.comp_apply, groundFinsetEmbedding_card, Finset.card_map]

@[simp] theorem groundMatroid_ncard (M : Matroid α) :
    (M.restrictSubtype M.E).E.ncard = M.E.ncard := by
  rw [Matroid.restrictSubtype_ground, Set.ncard_univ, Nat.card_coe_set_eq]

/-- The ground subtype is finite, so finite-coordinate polynomial results apply
without an additional assumption on the original ambient type. -/
@[reducible] noncomputable def groundFintype (M : Matroid α) [M.Finite] : Fintype M.E :=
  M.ground_finite.fintype

#print axioms independentFinsets_ground_map
#print axioms independentSetCount_ground_eq
#print axioms groundMatroid_ncard

end StrongMasonAudit

end SingleFileModule23
/- END ORIGINAL MODULE: Submission.GroundReduction -/

/- BEGIN ORIGINAL MODULE: Submission.StrongMason -/
section SingleFileModule24



set_option autoImplicit false

/-! The division-free Strong Mason inequality for the exact challenge count. -/

namespace StrongMasonAudit

variable {α : Type*}

theorem strong_mason_count_finite_ambient [Fintype α]
    (M : Matroid α) [M.Finite] (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    {I ∈ Set.powersetCard α (k - 1) | M.Indep I}.ncard *
        {I ∈ Set.powersetCard α (k + 1) | M.Indep I}.ncard *
          (k + 1) * (M.E.ncard - k + 1) ≤
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard ^ 2 * k * (M.E.ncard - k) := by
  classical
  let I : ℕ → ℕ := fun j => {J ∈ Set.powersetCard α j | M.Indep J}.ncard
  have hpoly : MvPolynomial.rename binaryVariable (independencePolynomial M) =
      binaryCountPolynomial M.E.ncard I :=
    rename_independencePolynomial_binary_counts M
  apply nat_count_inequality_of_binaryQuadratic_certificate I M.E.ncard k hk hkn
  rw [binaryQuadraticDerivative_eq_iteratedDirectionalDerivative]
  rw [← hpoly]
  apply independencePolynomial_binary_hessian_inequality M (by omega)
    ((binaryDerivativeIndices M.E.ncard k).map (fun i => Pi.single i 1))
    ?_ 0 (by simp) (Pi.single false 1) (Pi.single true 1) ?_
  · intro v hv i
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num

/-- The ambient type is arbitrary. Passing to the finite ground subtype
preserves both the exact independent-set counts and the ground cardinality. -/
theorem strong_mason_count
    (M : Matroid α) [M.Finite] (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    {I ∈ Set.powersetCard α (k - 1) | M.Indep I}.ncard *
        {I ∈ Set.powersetCard α (k + 1) | M.Indep I}.ncard *
          (k + 1) * (M.E.ncard - k + 1) ≤
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard ^ 2 * k * (M.E.ncard - k) := by
  letI : Fintype M.E := groundFintype M
  simpa only [independentSetCount_ground_eq, groundMatroid_ncard] using
    strong_mason_count_finite_ambient (M.restrictSubtype M.E) k hk
      (by simpa only [groundMatroid_ncard] using hkn)

#print axioms strong_mason_count_finite_ambient
#print axioms strong_mason_count

end StrongMasonAudit

end SingleFileModule24
/- END ORIGINAL MODULE: Submission.StrongMason -/

/- BEGIN ORIGINAL MODULE: Submission -/
section SingleFileModule25


set_option autoImplicit false


namespace Submission

theorem strong_mason_conjecture {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    {I ∈ Set.powersetCard α (k - 1) | M.Indep I}.ncard * {I ∈ Set.powersetCard α (k + 1) | M.Indep I}.ncard *
          (k + 1) * (M.E.ncard - k + 1) ≤
      {I ∈ Set.powersetCard α k | M.Indep I}.ncard ^ 2 * k * (M.E.ncard - k) := by
  exact StrongMasonAudit.strong_mason_count M k hk hkn

#print axioms strong_mason_conjecture

end Submission

end SingleFileModule25
/- END ORIGINAL MODULE: Submission -/
