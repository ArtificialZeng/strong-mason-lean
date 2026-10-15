import ChallengeDeps
import Submission.StrongMason

set_option autoImplicit false

open LeanEval.Combinatorics.StrongMason

namespace Submission

theorem strong_mason_conjecture {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) *
          (k + 1) * (M.E.ncard - k + 1) ≤
      independentSetCount M k ^ 2 * k * (M.E.ncard - k) := by
  exact StrongMasonAudit.strong_mason_count M k hk hkn

#print axioms strong_mason_conjecture

end Submission
