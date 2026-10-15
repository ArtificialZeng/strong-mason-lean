import ChallengeDeps
import Submission

open LeanEval.Combinatorics.StrongMason

theorem strong_mason_conjecture {α : Type*} (M : Matroid α) [M.Finite]
    (k : ℕ) (hk : 0 < k) (hkn : k < M.E.ncard) :
    independentSetCount M (k - 1) * independentSetCount M (k + 1) *
          (k + 1) * (M.E.ncard - k + 1) ≤
      independentSetCount M k ^ 2 * k * (M.E.ncard - k) := by
  exact Submission.strong_mason_conjecture M k hk hkn
