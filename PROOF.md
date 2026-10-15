# Strong Mason formalization

This package targets the exact Lean-Eval `strong_mason_conjecture` statement at
`3f3786f3b4d9a4b64a5859b3036aca190cd25613`.
Lean: `4.32.2`; Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`.

This variant contains the entire proof in a single `Submission.lean`.
The 25 module bodies were concatenated in dependency order, with imports
collected at the top and fresh section scopes. This variant imports only
Mathlib modules, including `Mathlib` itself, and expands the three occurrences
of the challenge's count definition in the final theorem statement. It uses
the coefficient linear map `MvPolynomial.lcoeff` and explicit `lcoeff_apply`
rewrites, which work with both tested Mathlib versions. The final theorem,
parameters, hypotheses and independent finite subsets being counted are
unchanged. The original official comparator remains the acceptance check.
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
The preceding standalone version at `86ac947db595bbd51b835d79816f3efd0f06c9dd`
also passed the full frozen replay in
[GitHub run 38802362260](https://github.com/ArtificialZeng/strong-mason-lean/actions/runs/38802362260).
All three prior website submissions nevertheless failed. The latter receipts
report a successful source overlay followed by a private `lean_compile`
preflight failure, without the underlying Lean diagnostic. A separate local
Linux experiment reproduced a missing `ChallengeDeps.olean` error when
checking the preceding file directly before building trusted local modules;
building only `ChallengeDeps` made that same file pass. This does not establish
the private worker's actual command or failure cause.

The current official upstream workspace at
`38361be884302c7edce1908c4aef8296eb2cb27e` uses Lean `4.35.0-rc3` and Mathlib
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`. Its main challenge and solution
wrapper are byte-identical to the frozen target, while its environment differs.
Checking the preceding source there produced real coefficient-API errors.
This variant resolves them with the common linear-map API, replaces the old
coefficient-zero alias with `map_zero`, and permits a conversion tactic to
produce no remaining goals. It changes no imported definition or reducibility
attribute and uses no compatibility override.

The exact same source has compiled successfully under both Lean/Mathlib pairs,
with only the three permitted axioms. The package retains the original frozen
toolchain and all eight trusted files. Its source SHA-256 is
`b6595b7c7cb97f85a9f773017ab68d5fc136d402bb493fd4ca0fb396283256fb`.
The exact source passed the unchanged frozen `lake test` in a new Linux target
workspace: original theorem comparison, permitted axioms, nanoda and Lean kernel
replay all succeeded. Trusted tool binaries and dependency caches were reused
from the preceding audited frozen ARM64 replay; all target objects were built
fresh and all eight trusted source hashes remained unchanged. Its independent
GitHub replay and website verdict are pending at this commit's preparation.

The private website's actual environment and compiler diagnostic remain
unavailable. Public-current compatibility does not establish its failure cause.
No official acceptance is claimed by this document. The original challenge file contains the trusted
benchmark placeholder; no proof file uses `sorry`, new axioms or `native_decide`.

Developed with Codex and GPT-6.1 Sol research subagents. Historical accepted
submission metadata was inspected, but its unavailable private proof source
was not used. This is a formalization of a known theorem, not a new proof of
an open mathematical conjecture.
