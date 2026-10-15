import Submission.HessianInequality
import Mathlib.Data.Nat.Factorial.Basic

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
