# A Syntactic Approach to Ulmer's Bialgebras, in Lean 4

This repository contains a computer-checked version of the results of D. Forsman, *A Syntactic
Approach to Ulmer's Bialgebras*. The results are written in [Lean 4](https://lean-lang.org), a
programming language in which a proof is checked line by line by the computer, on top of
[Mathlib](https://leanprover-community.github.io), Lean's library of mathematics. The paper itself
is here too, as `paper/paper.pdf`: this is **version 2** of the paper, in which every formalized
result links to its Lean code (version 1 is arXiv:2607.19587v1).

Exported from the development repository at commit `9e9491abe72d2b97637162feea52474234db274b`. It holds every checked statement of the development.

## Where to start

You do not need to install anything to read this repository: on GitHub, click a folder to open it
and a file to read it. Pick the starting point that fits what you want to know.

| If you want to… | read |
|---|---|
| read the mathematics, and jump from a result to its Lean version | [`paper/paper.pdf`](paper/paper.pdf) (see *The paper and its links* below) |
| find the Lean version of a numbered result of the paper | [`PAPER_LINKS.md`](PAPER_LINKS.md), one row per numbered item, with links to the code |
| see how each Lean statement compares with the paper's, and where its proof is | [docs/PAPER_MAP.md](docs/PAPER_MAP.md) |
| learn to read the Lean statements, without knowing Lean | [docs/READING_THE_CHALLENGE.md](docs/READING_THE_CHALLENGE.md), a walk through the headline theorems that explains the notation and traces each definition to Mathlib |
| know exactly what is checked and every difference from the paper | [`CHALLENGE.md`](CHALLENGE.md) |
| build the project and run the checks yourself | *How to check it* below |
| know how the formalization was made, and with which tools | [`AI_USAGE.md`](AI_USAGE.md) |

## The paper and its links

In `paper/paper.pdf`, each numbered result that is formalized is followed by a small box such as
[Lean 1 2]. Each number is a link to the Lean statement on GitHub, at release `v1.0.0` of this
repository: the link opens the file in `UlmerBialgebras/Paper/` and highlights the line where the
statement starts. A word after the links (*stronger*, *weaker*, *different* or *scope*) says how
the Lean statement differs from the paper's; without one, it states what the paper states. The
proof of a statement is the declaration of the same name in `UlmerBialgebras/Proofs/` (in
`Companion/Proofs/` for the statements beyond the paper's numbered results). At most four links
fit in a box; "+n" leads to the full list in [`PAPER_LINKS.md`](PAPER_LINKS.md).

## How the formalization is organized

The formalization is written *statements first*, in two layers:

- **Statements.** `UlmerBialgebras/Paper/` contains the paper's definitions and results, section
  by section, in files named after the sections (`Sec3.lean`, `Sec5.lean`, …; the files with
  `Defs` in their name hold definitions). Every result there is stated with `sorry` in place of
  its proof: `sorry` is Lean's word for "proof omitted". This layer is short and is what a reader
  compares with the paper.
- **Proofs.** `UlmerBialgebras/Proofs/` states the same results again, with full proofs. The
  proofs draw on the library folders listed below.

A tool (Lean's Comparator, below) checks that every proved theorem states exactly what its
`sorry` version states, and that the proofs use only the three standard axioms of Lean's logic.
So a reader who trusts Lean only needs to read the statements and the definitions they use.

What is proved:

- **175 checked statements**, listed in `comparator.all.json`, all proved with only the
  axioms `propext`, `Quot.sound` and `Classical.choice`. 127 of them state the
  paper's numbered results; 48 are statements the paper uses without a number,
  or additions beyond the paper.
- The author reviewed every definition and every statement against the paper (see [What the author reviewed](#what-the-author-reviewed)).

## A map of the repository

| Path | Contents |
|---|---|
| `UlmerBialgebras/Paper/` | The paper's statements, each proved by `sorry`, and the definitions they use, section by section. **This is what a reader checks against the paper.** |
| `UlmerBialgebras/Proofs/` | The same statements, with proofs, section by section. |
| `Foundations/` | General category theory and algebra the library uses. |
| `UlmerBialgebras/` | The library of the paper: syntax, models, the constructions. |
| `Hopf/` | Hopf algebras, comodules and coalgebras (Section 6). |
| `InternalGroups/` | Internal groups in a cartesian monoidal category: subgroups, stabilizers, cosets and the exactness of `Grp C` (Section 6 and the announced results). |
| `AffineGroupSchemes/` | Affine group schemes and flatness (Section 6). |
| `Companion/` | The checked statements beyond the paper's numbered results, with their proofs (`Companion/Statements/`, `Companion/Proofs/`), and the library modules that only they use (`Companion/Foundations/`, `Companion/Hopf/`, `Companion/InternalGroups/`, `Companion/UlmerBialgebras/`). `Companion/Statements.lean` and `Companion/Proofs.lean` are the two roots that the Comparator checks: they gather all the checked statements, the paper's included. |
| `Palomar/` | Thirteen self-contained entries for the Palomar Registry (`3.22`, `4.7`, `4.19`, `5.5`, `5.7`, `5.10`, `5.11`, `6.3`, `6.6`, `7.4`, `7.6`, `7.7`, `A.5`): each main result restated using Mathlib only, with its proof. `palomar/<id>/comparator.json` configures the check of each. |
| `paper/` | The paper (version 2): `paper/paper.pdf` and its LaTeX sources. |
| `PAPER_LINKS.md` | The index from the paper's numbered items to their Lean declarations. |
| `docs/` | The guides `PAPER_MAP.md` and `READING_THE_CHALLENGE.md`, and the ledger `STATE.yml` (each result's record: statements, approvals, how it compares with the paper). |
| `CHALLENGE.md` | What is checked, and every difference from the paper. |
| `comparator.all.json` | The list of checked statements, read by Lean's Comparator (repository-wide; not a standalone Palomar entry). |
| `AI_USAGE.md` | How the formalization was produced. |
| `scripts/` | The checks below. |
| `docbuild/` | Builds browsable HTML documentation of the Lean code (see `docbuild/README.md`). |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | The build configuration: the Lean version and the exact Mathlib version. |

## How to check it

Building is only needed to check the proofs yourself; reading needs nothing. You need:

1. [elan](https://github.com/leanprover/elan), Lean's installer, which picks the right Lean
   version by itself (see [lean-lang.org](https://lean-lang.org) for installation help);
2. a copy of this repository: either `git clone` it, or on GitHub use the green **Code** button,
   then **Download ZIP**, and unpack it.

Then, in a terminal, in the repository's folder:

```
lake exe cache get                          # Mathlib's prebuilt files
lake build                                  # every library
python3 scripts/check_axioms.py             # the axioms of every checked statement
lake env lean scripts/check_compiled_types.lean   # the proofs state exactly the statements' types
# Lean's Comparator (needs bubblewrap; toolchain bin on PATH exposes nanoda_bin):
export PATH="$(lean --print-prefix)/bin:$PATH"
lake comparator --config comparator.all.json
```

On four cores, `lake build` takes about ten minutes after `lake exe cache get`, and
`lake comparator` about five; the `.lake` directory then takes about 9 GB, most of it Mathlib.

`check_axioms.py` should end with `175 proved, 0 open (sorry), 0 with other axioms,
of 175`.

`lake comparator` is Lean's Comparator, a subcommand of Lake in this toolchain (`lake comparator
--help`); `lake comparator --config comparator.all.json` runs it on `comparator.all.json`. It rebuilds both layers in a sandbox and checks with the
kernel that every theorem of `comparator.all.json` in `Companion.Proofs` proves the statement of the
same name in `Companion.Statements`, with no axiom outside the three above. These two modules gather
all 175 checked statements, the paper's included. The sandbox is `bubblewrap`, which
needs unprivileged user namespaces or a setuid install. The trusted Comparator result is the
sandboxed run; a run with `--inadvisably-no-sandbox` is only an advisory local check. The workflow
in `.github/workflows/ci.yml` runs the sandboxed check.

Toolchain: `leanprover/lean4:v4.36.0`, Mathlib `v4.36.0 (fc4f59e577fe)`.

## Announced results

Part of this repository formalizes results that are not yet published. They were announced
by the author in the talk *On the exactness of categories of internal groups from the
perspective of cosets and stabilizers* (XVI Portuguese Category Seminar, Coimbra, 13 November
2026; slides: <https://flnlucatelli.github.io/2026/pcs/slides/david-forsman.pdf>) and will
appear in a forthcoming preprint by the author. Until the preprint is available, please
cite this repository for them. The top-level theorems:

The route to the exactness of `Grp C`, general first, then specialized; these results are due to
D. Forsman:

- `UlmerBialgebras.KernelPairComparison.isPullback_comparison`,
  `UlmerBialgebras.KernelPairComparison.isExtremalEpi_comparison_of_isExtremalEpi`: the pullback
  comparison lemma;
- `UlmerBialgebras.SectionEpi.mono_of_stablySEpi_of_comp_of_isPullback`,
  `UlmerBialgebras.SectionEpi.isRegularEpi_of_isExtremalEpi`: the mono lemma, and extremal
  epimorphisms are regular when regular epimorphisms are stably section-extremal;
- `UlmerBialgebras.regular_iff_classEpi`: a characterization of regular categories through stably
  extremal epimorphisms;
- `InternalGroups.regularEpiStablySEpi_stabilizers`,
  `InternalGroups.regular_grp_of_monos_are_stabilizers`: under a condition (S′) on `C`, the regular
  epimorphisms of `Grp C` are stably stabilizer-extremal, so `Grp C` is regular when every
  monomorphism is a stabilizer;
- `InternalGroups.isBarrExact_grp_of_regularEpiCosetCompHom_of_monos`,
  `InternalGroups.subgroupCorrespondence_iff_monos_are_stabilizers`,
  `InternalGroups.isBarrExact_grp_of_subgroupCorrespondence`: `Grp C` is then Barr-exact, and
  Newman's correspondence says exactly that monomorphisms are stabilizers and that epimorphic coset
  quotients are regular, which gives (S′);
- `InternalGroups.subgroupCorrespondence_commComon_iff_monos_are_stabilizers`,
  `InternalGroups.forall_biIdealMap_bijective_iff_monos_are_stabilizers`,
  `InternalGroups.isBarrExact_grp_commComon`, `InternalGroups.isBarrExact_grp_commComon_of_biIdeal`:
  the case of cocommutative comonoids;
- `UlmerBialgebras.CocommComon.isBarrExact_grp_of_field`: by this route, the cocommutative Hopf
  algebras over a field form a Barr-exact category (first proved by Gran, Sterck and
  Vercruysse).

Two further results of the talk that the route uses:

- `InternalGroups.galoisConnection_quot_stab`: the Galois connection between the subgroups of an
  internal group and its quotients;
- `InternalGroups.SubGrpObj.isEffectiveCoset_of_kernelSub_quot_equiv`: the effectiveness of coset
  relations.

## What the author reviewed

The author reviewed every definition and every statement against the paper: all 175 checked statements (the 32 statements of the paper's 13 main results, and 143 more) and the definitions they are stated with, the paper's numbered definitions among them. `docs/STATE.yml` records the approval statement by statement: an entry with checked statements is `approved: true` when the author approved all of them; an entry for one of the paper's definitions has no checked statement of its own. Each statement was compared, together with the definitions it uses, against
the paper. For many of them two aids were used: a *read-back*, the Lean statement retold in plain mathematical
language by a reader who had seen neither the paper nor this project, to compare with the paper;
and a *blind re-formalization*, new Lean written from that prose alone, then proved logically
equivalent to the original statement.

## Licence and citation

The code is released under the Apache License 2.0 (`LICENSE`); the paper (`paper/`, `paper/paper.pdf`)
is released under CC BY 4.0 (`paper/LICENSE`). To cite the formalization, see `CITATION.cff`; its DOI is
[10.5281/zenodo.24483241](https://doi.org/10.5281/zenodo.24483241).

## References

`references.bib` lists every work that this repository cites, in the docstrings, the documents and
the paper.
