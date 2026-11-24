# AI Usage Disclosure

This file documents the use of AI systems in producing this Lean 4 formalization of
*A Syntactic Approach to Ulmer's Bialgebras*, alongside the structured `automation` and `review`
metadata in `formalization.yaml`.

## Authorship and responsibility

All mathematical content originates with the human author, who directed the formalization's scope,
architecture, and statement choices, and assumes sole responsibility for this repository. No AI
system is listed as an author or maintainer. Any material extracted from this repository for
upstream submission (for example to Mathlib) is reviewed and justified line by line by the human
author under the receiving project's own disclosure policy.

## Systems and roles

Several AI coding agents participated in the development repository under the author's direction:

- **Claude (Anthropic)** — coordination and technical leadership (writing task specifications,
  reviewing diffs, running local verification and integration checks, and release tooling);
  drafting Lean statements alongside the author; writing Lean proofs across the library, Mathlib
  alignment, universe generalizations, code-quality cleanup, and review aids (plain-language
  read-backs and check scripts).
- **Codex (OpenAI)** — writing Lean proofs and constructions, bicategory and universe migrations,
  proof-route alignment, verification and release scripts, and statement audits.
- **Antigravity (Google)** — closing and conversion tasks, non-vacuity and definition tests,
  documentation and paper-map synchronization, code-quality cleanup, and independent second-key
  reviews.
- **DeepSeek** — early-phase Lean proofs (including internal-group exactness and Newman
  correspondence components) and statement and definition audits.
- **Aristotle (Harmonic)** — earlier Lean formalizations produced with the author in a sibling
  internal-groups project, parts of which were ported into the supporting `InternalGroups` library.
  The development repository's modules `InternalGroups.ExtensiveTwo`,
  `InternalGroups.GrpComplementedRegular` and `InternalGroups.GrpWreathRegular` were ported from
  the author's earlier formalization made with Aristotle; this tree keeps the parts of them that
  its checked statements use.

## Time and cost

- **Wall-clock time:** not disclosed.
- **Spend:** about 160 USD (about 145 EUR).
- **Hardware and services:** not disclosed.

## Human review of statements

The author reviewed every definition and every statement against the paper: all 175 checked statements (the 32 statements of the paper's 13 main results, and 143 more) and the definitions they are stated with, the paper's numbered definitions among them. `docs/STATE.yml` records the approval statement by statement: an entry with checked statements is `approved: true` when the author approved all of them; an entry for one of the paper's definitions has no checked statement of its own. Reviews compared the Lean statements and definitions side by side with the
manuscript, assisted for many statements by plain-language read-backs and blind re-formalizations checked for
logical equivalence against the checked statements.

## Mechanical verification

Correctness of the proofs does not rely on trusting any AI system; every checked result is verified
mechanically on toolchain `leanprover/lean4:v4.36.0` with Mathlib `v4.36.0 (fc4f59e577fe)`:

- **Axiom check (`scripts/check_axioms.py`):** confirms that all 175 checked statements
  in `comparator.all.json` are proved with `0` occurrences of `sorry` and depend only on Lean's three
  standard axioms (`propext`, `Quot.sound`, and `Classical.choice`).
- **Compiled type check (`scripts/check_compiled_types.lean`):** confirms that every theorem in
  `Companion.Proofs` has the exact compiled type of the corresponding statement in
  `Companion.Statements`.
- **Comparator (`lake comparator`):** rebuilds `Companion.Statements` and `Companion.Proofs`
  from source inside a `bubblewrap` sandbox and checks every theorem of `comparator.all.json` with
  Lean's kernel. The Palomar entries, one for each main theorem, were also checked with the
  independent `nanoda` and `con-ron` kernels.
