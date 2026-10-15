# Strong Mason formalization

This package targets the exact Lean-Eval `strong_mason_conjecture` statement at
`3f3786f3b4d9a4b64a5859b3036aca190cd25613`.
Lean: `4.32.2`; Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`.

This variant contains the entire proof in a single `Submission.lean`.
The 25 module bodies were concatenated in dependency order, with imports
collected at the top and fresh section scopes. This variant imports only
Mathlib modules, including `Mathlib` itself, and expands the three occurrences
of the challenge's count definition in the final theorem statement. No
mathematical proof body, parameter or hypothesis was changed. The final
statement must pass the unchanged official comparator against the original
challenge; it counts exactly the same independent finite subsets.
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
The preceding single-file version at `741645fba42ab286674969cdaf8a96fb39afcffb`
also passed the full frozen comparator and both kernels in
[GitHub run 38797695080](https://github.com/ArtificialZeng/strong-mason-lean/actions/runs/38797695080).
Both prior website submissions nevertheless failed. The second receipt
reports a successful source overlay followed by a private `lean_compile`
preflight failure, without the underlying Lean diagnostic. A separate local
Linux experiment reproduced a missing `ChallengeDeps.olean` error when
checking the preceding file directly before building trusted local modules;
building only `ChallengeDeps` made that same file pass. This does not establish
the private worker's actual command or failure cause.

The present variant removes that local-module dependency and has passed direct
Lean checking in a fresh Linux workspace containing no local build objects.
The unchanged official `lake test` then passed the exact theorem comparison,
allowed-axiom checks, nanoda and Lean kernel replay on Linux. This local run
reused the audited frozen tools and Mathlib dependency cache from the preceding
full ARM64 replay; all target-local objects were rebuilt. Its source SHA-256 is
`7fe995a849bb5a1e785d0136ec59974435d571e53d33093fed4fd306a443fff2`.
Its independent GitHub replay and website verdict are pending at this commit.
No official acceptance is claimed by this document. The original challenge file contains the trusted
benchmark placeholder; no proof file uses `sorry`, new axioms or `native_decide`.

Developed with Codex and GPT-6.1 Sol research subagents. Historical accepted
submission metadata was inspected, but its unavailable private proof source
was not used. This is a formalization of a known theorem, not a new proof of
an open mathematical conjecture.
