import Submission.CompleteLogConcavity
import Submission.CountNormalization

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
    coeff m (iteratedPartialDerivative (List.replicate a i) p) =
      coeff (m + Finsupp.single i a) p * ((m i + a).descFactorial a : ℝ) := by
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
    coeff (binaryExponent n j) (binaryCountPolynomial n I) = (I j : ℝ) := by
  rw [binaryCountPolynomial_eq_monomial]
  simp only [coeff_sum, coeff_monomial, (binaryExponent_injective n).eq_iff]
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
  change coeff 0 (binaryPartialDerivative a b (binaryCountPolynomial n I)) = _
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
