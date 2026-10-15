import Submission.IndependentSetPolynomial
import Mathlib.Algebra.MvPolynomial.Rename

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
