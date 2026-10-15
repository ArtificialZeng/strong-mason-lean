import Submission.MatroidDerivative
import Submission.MatroidQuadratic
import Submission.SignaturePropagation

set_option autoImplicit false

/-! The actual quadratic terminal Hessian of the independent-set polynomial. -/

namespace StrongMasonAudit

open MvPolynomial Classical
open scoped BigOperators

theorem formalHessian_eq_coeff_of_homogeneous_two
    {ι : Type*} (p : MvPolynomial ι ℝ) (hp : p.IsHomogeneous 2)
    (w : ι → ℝ) (i j : ι) :
    formalHessian p w i j =
      coeff (Finsupp.single i 1 + Finsupp.single j 1) p *
        (if i = j then 2 else 1) := by
  classical
  have hzero : (pderiv i (pderiv j p)).IsHomogeneous 0 := by
    simpa using (hp.pderiv (i := j)).pderiv (i := i)
  have heq : pderiv i (pderiv j p) = C (coeff 0 (pderiv i (pderiv j p))) :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous ι).mpr hzero)
  change eval w (pderiv i (pderiv j p)) = _
  rw [heq, eval_C, coeff_pderiv, coeff_pderiv]
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
      coeff (independentExponent 2 I)
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
