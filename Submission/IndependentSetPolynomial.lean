import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Set.PowersetCard
import Submission.PolynomialPositivity

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
  simp only [independentMonomial, coeff_monomial]
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
  simp only [independencePolynomial, coeff_sum]
  exact Finset.sum_nonneg fun I _ => independentMonomial_nonnegative M.E.ncard I m

@[simp] theorem coeff_independencePolynomial_exponent (M : Matroid α) [M.Finite]
    (I : Finset α) :
    coeff (independentExponent M.E.ncard I) (independencePolynomial M) =
      if M.Indep (I : Set α) then 1 else 0 := by
  classical
  simp only [independencePolynomial, coeff_sum, independentMonomial, coeff_monomial]
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
