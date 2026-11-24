module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import UlmerBialgebras.Paper.Sec6DefsHopf
public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism
public import Foundations.CategoryTheory.Factorization.ExactCategory

/-!
# Challenge: Corollary 6.11

`T` ranges over the multi-sorted theories of universal algebra extending the theory of groups in
each sort: an equational theory `T` over `UniversalAlgebra.grpExtLanguage S Fn' arity' argSorts'
resSort'`, the many-sorted language of groups in each sort `s ∈ S` together with further function
symbols `Fn'`, that contains the group axioms translated along the inclusion
`UniversalAlgebra.grpInl` (`∀ φ ∈ grpEqTheory S, grpInl.translateEquation φ ∈ T`). For a category
`B` with finite products, `B^T` is `T.ModelCat B`, the category of models of `T` in `B`.

Exactness is Barr-exactness `CategoryTheory.BarrExact` (Mathlib's regular categories in which
every equivalence relation is effective), which is the paper's Definition 6.4 by `def_6_4_exact`.
It is used both in the hypothesis on cocommutative Hopf monoids and in the conclusions.

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_barrExact_reduction`: under the stated
  hypotheses on a symmetric monoidal category `A`, if `Grp (CommComon A)` is Barr-exact then so is
  `(Comon_A^coc)^T` (a step of the proof of Corollary 6.11).
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_barrExact`: for a commutative von Neumann
  regular ring `R`, `(Comon_A^coc)^T` is Barr-exact for `A = Mod_R^op` and for `A = Mod_R`
  (Corollary 6.11).
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_barrExact_moduleCat`: the same for
  `Mod_R = ModuleCat.{u} R`, with objects in `Type (u + 1)` and morphisms in `Type u`
  (Corollary 6.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (with Lemma 6.10, Corollary 6.9)
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by Takeuchi*]
  [GRAN20194171]
* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes]
* [M. Bevilacqua, *Coalgebraic Models of Ω-Groups*][bevilacquaCoalgebraicModelsOmega2026]
* [M. Gran, A. Sciandra, *Hopf braces and semi-abelian categories*][granHopfBracesSemiabelian2026]
* [A. Agore, A. Chirvasitu, *On the category of Hopf braces*][agoreCategoryHopfBraces2026]
* [I. Angiono, C. Galindo, L. Vendramin, *Hopf braces and Yang-Baxter operators*][Angiono_2016]
-/

@[expose] public section

universe u v u₁

namespace UlmerBialgebras.Paper.UniversalAlgebra

open CategoryTheory Limits MonoidalCategory Cart Loc MSLanguage

/-- **Corollary 6.11, reduction to groups** ([forsman2026syntactic], §6).

```latex
Consider a symmetric monoidal category $A$ and denote by $\mathbf{Comon}^{\mathrm{coc}}_A$ the
category of internal cocommutative comonoids. The category of internal cocommutative Hopf algebras
$\Hopf_A^{\mathrm{coc}}$ in $A$ is defined as the category
$\mathbf{Grp}(\mathbf{Comon}^{\mathrm{coc}}_A)$ of internal groups within
$\mathbf{Comon}^{\mathrm{coc}}_A$. In the case where $A$ is the symmetric monoidal category of
$k$-vector spaces or its dual, it has been shown that the category $\Hopf^{\mathrm{coc}}_A$ is
exact (even semi-abelian) \cite{GRAN20194171, forsman2026semiabeliannessaffinegroupschemes}. The
following corollary generalizes some exactness results found in
\cite{bevilacquaCoalgebraicModelsOmega2026, granHopfBracesSemiabelian2026} by showing that
$(\mathbf{Comon}^{\mathrm{coc}}_A)^T$ is exact for all algebraic theories $T$ extending the theory
of groups, when $A$ is either the symmetric monoidal category of $R$-modules or its dual for a
commutative regular ring $R$:
```

```latex
Consider a commutative regular ring $R$. Let $T$ be a multi-sorted theory of universal algebra
extending the theory of groups in each sort $s\in S$. Then $(\Comon_A^\coc)^T$ is exact for $A =
\Mod_R, \Mod_R^\mathrm{op}$.
```

**Reading.**
* "symmetric monoidal category $A$" ↦ `[Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]`.
* "$\Hopf_A^{\mathrm{coc}} = \mathbf{Grp}(\mathbf{Comon}^{\mathrm{coc}}_A)$ exact" ↦
  `[BarrExact (Grp (CategoryTheory.CommComon A))]`.
* "$T$ a multi-sorted theory of universal algebra extending the theory of groups in each sort" ↦
  an equational theory `T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory`, over the
  language of groups in each sort of `S` with further function symbols `Fn'`, containing the
  translated group axioms (`hT`).
* "$(\Comon_A^\coc)^T$" ↦ `T.ModelCat (CategoryTheory.CommComon A)`, the category of models.
* auxiliary reduction step in the paper's proof of Corollary 6.11 via Corollary 6.9 (`cor_6_9`).

**Deviations.**
- route: the reduction applies Corollary 6.9 (`isExactCat_thyObj_of_restrict`), as in the paper;
  the route of Corollary 6.11 as a whole is regrouped at its first step (docs/STATE.yml,
  proof_route).
-/
theorem modelCat_barrExact_reduction {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (A : Type u) [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A] [HasCoreflexiveEqualizers A] [HasReflexiveCoequalizers A]
    [∀ Z : A, PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ Z : A, PreservesCoreflexiveEq (tensorRight Z)]
    [∀ Z : A, Monad.PreservesColimitOfIsReflexivePair (tensorLeft Z)]
    [∀ Z : A, Monad.PreservesColimitOfIsReflexivePair (tensorRight Z)]
    [BarrExact (Grp (CategoryTheory.CommComon A))]
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon A)) := sorry

/-- **Corollary 6.11** ([forsman2026syntactic], §6).

```latex
Consider a symmetric monoidal category $A$ and denote by $\mathbf{Comon}^{\mathrm{coc}}_A$ the
category of internal cocommutative comonoids. The category of internal cocommutative Hopf algebras
$\Hopf_A^{\mathrm{coc}}$ in $A$ is defined as the category
$\mathbf{Grp}(\mathbf{Comon}^{\mathrm{coc}}_A)$ of internal groups within
$\mathbf{Comon}^{\mathrm{coc}}_A$. In the case where $A$ is the symmetric monoidal category of
$k$-vector spaces or its dual, it has been shown that the category $\Hopf^{\mathrm{coc}}_A$ is
exact (even semi-abelian) \cite{GRAN20194171, forsman2026semiabeliannessaffinegroupschemes}. The
following corollary generalizes some exactness results found in
\cite{bevilacquaCoalgebraicModelsOmega2026, granHopfBracesSemiabelian2026} by showing that
$(\mathbf{Comon}^{\mathrm{coc}}_A)^T$ is exact for all algebraic theories $T$ extending the theory
of groups, when $A$ is either the symmetric monoidal category of $R$-modules or its dual for a
commutative regular ring $R$:
```

```latex
Consider a commutative regular ring $R$. Let $T$ be a multi-sorted theory of universal algebra
extending the theory of groups in each sort $s\in S$. Then $(\Comon_A^\coc)^T$ is exact for $A =
\Mod_R, \Mod_R^\mathrm{op}$.
```

**Reading.**
* "commutative regular ring $R$" ↦ `[CommRing R] (hR : IsVonNeumannRegularRing R)`.
* "$T$ a multi-sorted theory of universal algebra extending the theory of groups in each sort" ↦
  an equational theory `T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory`, over the
  language of groups in each sort of `S` with further function symbols `Fn'`, containing the
  translated group axioms (`hT`).
* "$(\Comon_A^\coc)^T$" ↦ `T.ModelCat (CategoryTheory.CommComon A)`, the category of models.
* "$A = \Mod_R^\mathrm{op}$" (affine schemes) ↦ `(ModU R)ᵒᵖ`, and "$A = \Mod_R$" ↦ `ModU R`.
* "exact" ↦ `CategoryTheory.BarrExact` (Definition 6.4, `def_6_4_exact`).

**Deviations.**
- stronger: also proves the case the paper cites from Gran, Sterck and Vercruysse: Hopf_k^coc is
  Barr-exact for every field k (CHALLENGE.md, *Stronger than the paper*).
- different: `modelCat_barrExact` is stated for `ModU R` (hom-sets lifted to `Type (u + 1)`);
  `modelCat_barrExact_moduleCat` states it for `ModuleCat.{u} R` itself.
- route regrouped: the localizations of modules are lifted to comonoids by a direct construction
  instead of Lemma 6.10; the proof uses Lemma 6.5(3) and Corollary 6.9 (docs/STATE.yml,
  proof_route).
-/
theorem modelCat_barrExact {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R))) := sorry

/-- **Corollary 6.11, for `ModuleCat R`** ([forsman2026syntactic], §6).

```latex
Consider a commutative regular ring $R$. Let $T$ be a multi-sorted theory of universal algebra
extending the theory of groups in each sort $s\in S$. Then $(\Comon_A^\coc)^T$ is exact for $A =
\Mod_R, \Mod_R^\mathrm{op}$.
```

**Reading.**
* "commutative regular ring $R$" ↦ `[CommRing R] (hR : IsVonNeumannRegularRing R)`.
* "$T$ a multi-sorted theory of universal algebra extending the theory of groups in each sort" ↦
  an equational theory `T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory`, over the
  language of groups in each sort of `S` with further function symbols `Fn'`, containing the
  translated group axioms (`hT`).
* "$(\Comon_A^\coc)^T$" ↦ `T.ModelCat (CategoryTheory.CommComon A)`, the category of models.
* "$A = \Mod_R^\mathrm{op}$" and "$A = \Mod_R$" ↦ `(ModuleCat.{u} R)ᵒᵖ` and `ModuleCat.{u} R`
  (with objects in `Type (u + 1)` and morphisms in `Type u`, instead of the copy `ModU R` used in
  `modelCat_barrExact`).
* "exact" ↦ `CategoryTheory.BarrExact`.

**Deviations.**
- stronger: also proves the case the paper cites from Gran, Sterck and Vercruysse: Hopf_k^coc is
  Barr-exact for every field k (CHALLENGE.md, *Stronger than the paper*).
- route regrouped: the localizations of modules are lifted to comonoids by a direct construction
  instead of Lemma 6.10; the proof uses Lemma 6.5(3) and Corollary 6.9 (docs/STATE.yml,
  proof_route).
-/
theorem modelCat_barrExact_moduleCat {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R))) := sorry

end UlmerBialgebras.Paper.UniversalAlgebra
