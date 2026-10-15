import Submission.CommonNormal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
