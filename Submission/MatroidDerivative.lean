import Submission.IndependentSetPolynomial
import Submission.PolynomialHessian
import Mathlib.Combinatorics.Matroid.Minor.Contract

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
    coeff (independentExponent (M.E.ncard - a) I)
      (homogenizingDerivative a (independencePolynomial M)) =
      if M.Indep (I : Set α) then ((M.E.ncard - I.card).descFactorial a : ℝ) else 0 := by
  classical
  rw [homogenizingDerivative_independencePolynomial]
  simp only [coeff_sum, independentMonomial, coeff_smul, coeff_monomial]
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
  rw [hz, coeff_zero] at h
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
    convert ih.pderiv using 1; omega

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
