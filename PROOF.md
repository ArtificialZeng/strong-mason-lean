# Strong Mason formalization

This package targets the exact Lean-Eval `strong_mason_conjecture` statement at
`3f3786f3b4d9a4b64a5859b3036aca190cd25613`.
Lean: `4.32.2`; Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`.

This variant contains the entire proof in a single `Submission.lean`.
The 25 module bodies were concatenated in dependency order, with imports
collected at the top and fresh section scopes; no mathematical proof body
was changed. It is a controlled test of the website intake after its
25-file submission returned a generic comparator rejection with private logs.
The trusted challenge, definitions, solution wrapper, Lake configuration,
toolchain, comparator configuration and test harness are unchanged.
The count is the original number of independent finite subsets; the ambient
type is arbitrary and only the explicit matroid ground must be finite.

The mathematical route follows Anari, Liu, Oveis Gharan and Vinzant,
*Log-concave polynomials III*, arXiv:1811.01600, particularly the
coordinate-quadratic criterion and the parallel-class quadratic base.
The formalization proves the required Hessian positive-index consequence
without introducing a separate function-log-concavity equivalence.

1. Enumerate actual independent finite subsets and form their homogenized polynomial.
2. Prove coordinate differentiation equals matroid contraction, including zero cases.
3. Prove connected active support and the actual factorial-scaled quadratic Hessian.
4. Propagate the positive-index bound through arbitrary nonnegative directional derivatives.
5. Merge element variables, extract the three exact factorial coefficients,
   and cancel positive factors to obtain the natural-number inequality.
6. Transfer counts from the finite ground subtype to the original ambient type.

Both the complete research theorem and the packaged `Submission.strong_mason_conjecture`
compiled locally with only `propext`, `Classical.choice`, and `Quot.sound`.
The unchanged `Solution.lean` wrapper also compiled successfully.
The original multi-file package at `6a5302e473de4bee11d7c9b3247970d118f308ad`
passed the frozen comparator, nanoda and Lean kernel on Linux in
[GitHub run 38794157224](https://github.com/ArtificialZeng/strong-mason-lean/actions/runs/38794157224).
This single-file variant has compiled locally; its own Linux replay and
website verdict remain pending.
No official acceptance is claimed by this document. The original challenge file contains the trusted
benchmark placeholder; no proof file uses `sorry`, new axioms or `native_decide`.

Developed with Codex and GPT-6.1 Sol research subagents. Historical accepted
submission metadata was inspected, but its unavailable private proof source
was not used. This is a formalization of a known theorem, not a new proof of
an open mathematical conjecture.
