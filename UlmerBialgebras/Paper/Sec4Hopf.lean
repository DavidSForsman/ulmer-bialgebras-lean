module

public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Kan.SiftedApplications
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Challenge: Example 4.20 (limits and colimits of Hopf monoids)

`C` is a braided monoidal category and `U : M^{T_Hopf} → M₀` the forgetful 1-cell of its
Hopf model (`UlmerBialgebras/Paper/Sec3DefsHopfModel.lean`); `M₀` is `C` itself, indexed by the
single sort.
The paper assumes `C` symmetric monoidal closed, complete and cocomplete, with `⊗`
preserving finite limits in each variable; each statement below uses only the part of
these hypotheses it needs. The statements are instances of Corollary 4.17 (and its dual)
and Theorem 4.19 (and its dual).

## Main results

* `UlmerBialgebras.Paper.ex_4_20_1_coeq`, `UlmerBialgebras.Paper.ex_4_20_1_eq`: if `C` is monoidal
  closed, `U` strictly creates reflexive coequalizers; if `⊗` preserves finite limits in each
  variable, `U` strictly creates coreflexive equalizers (Example 4.20 (1)).
* `UlmerBialgebras.Paper.ex_4_20_2_pushout`, `UlmerBialgebras.Paper.ex_4_20_2_pullback`: `U`
  strictly creates wide pushouts of diagrams whose legs it sends to regular epimorphisms, and joint
  pullbacks of finite families it sends to regular monomorphisms, under the stated hypotheses on `C`
  (Example 4.20 (2)).
* `UlmerBialgebras.Paper.ex_4_20_3`: if `C` is monoidal closed, `U` strictly creates filtered
  colimits (Example 4.20 (3)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 4.20 (with Corollary 4.17 and Theorem 4.19)
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory Limits

/-- **Example 4.20 (1), reflexive coequalizers** ([forsman2026syntactic], §4).

```latex
Consider a symmetric monoidal closed category $\C = (\C,\otimes,I)$ that is both complete and
cocomplete. Assume the tensor $\otimes$ preserves finite limits componentwise. Consider the
category $\Hopf$ of Hopf algebras in $\C$. Corollary~\ref{cor:liftingSifted} allows one to compute
the following limits and colimits in $\Hopf$ by strictly creating them from $\C$:
```

```latex
\item Reflexive coequalizers and coreflexive equalizers in $\Hopf$ are strictly created from $\C$
as the tensor preserves such (co)limits (Corollary \ref{cor:liftingSifted} and its dual).
```

**Reading.**
* "$\Hopf$" ↦ `HopfModel.thyCat C`: the object $M^{T_{\mathrm{Hopf}}}$ of internal Hopf algebras.
* "strictly created from $\C$" ↦ `StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C)`:
  the forgetful 1-cell strictly creates the left Kan extension along the functor to the terminal
  category.
* "reflexive coequalizers" ↦ diagram shape `J : Cat.{v, u}` equivalent to `WalkingReflexivePair`.
* hypotheses on `C`: assumes braided monoidal closed with limits and colimits in `Cat.{v, u}`,
  rather than full completeness and cocompleteness.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each statement
  (CHALLENGE.md, *Differences of detail*).
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*; docs/STATE.yml, deviations).
-/
theorem ex_4_20_1_coeq (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (J : Cat.{v, u})
    (e : WalkingReflexivePair ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C) :
    StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C) := sorry

/-- **Example 4.20 (1), coreflexive equalizers** ([forsman2026syntactic], §4).

```latex
Consider a symmetric monoidal closed category $\C = (\C,\otimes,I)$ that is both complete and
cocomplete. Assume the tensor $\otimes$ preserves finite limits componentwise. Consider the
category $\Hopf$ of Hopf algebras in $\C$. Corollary~\ref{cor:liftingSifted} allows one to compute
the following limits and colimits in $\Hopf$ by strictly creating them from $\C$:
```

```latex
\item Reflexive coequalizers and coreflexive equalizers in $\Hopf$ are strictly created from $\C$
as the tensor preserves such (co)limits (Corollary \ref{cor:liftingSifted} and its dual).
```

**Reading.**
* "coreflexive equalizers" ↦ diagram shape `J : Cat.{v, u}` equivalent to
  `WalkingCoreflexivePair`.
* "strictly created from $\C$" ↦ `StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C)`.
* "tensor preserves finite limits componentwise" ↦ `∀ X : C, PreservesFiniteLimits (tensorLeft X)`.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each statement
  (CHALLENGE.md, *Differences of detail*).
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*; docs/STATE.yml, deviations).
-/
theorem ex_4_20_1_eq (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [∀ X : C, PreservesFiniteLimits (tensorLeft X)] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] [HasChosenProductsOfSize.{0} Cat.{v, u}]
    (J : Cat.{v, u}) (e : WalkingCoreflexivePair ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C) :=
  sorry

/-- **Example 4.20 (2), wide pushouts** ([forsman2026syntactic], §4).

```latex
Consider a symmetric monoidal closed category $\C = (\C,\otimes,I)$ that is both complete and
cocomplete. Assume the tensor $\otimes$ preserves finite limits componentwise. Consider the
category $\Hopf$ of Hopf algebras in $\C$. Corollary~\ref{cor:liftingSifted} allows one to compute
the following limits and colimits in $\Hopf$ by strictly creating them from $\C$:
```

```latex
\item More generally, consider morphisms $f_i\colon x_i\to y$ in $\Hopf$ that are regular
monomorphisms in $\C$ for $i\leq n$. The joint pullback of the $f_i$ is strictly created from $\C$
(dual of Theorem \ref{thm:creation_wide_pushouts}). Similarly, any wide pushout of morphisms in
$\Hopf$ that are regular epimorphisms in $\C$ is strictly created from $\C$. This explains why for
a field $k$ one can compute finite intersections of Hopf subalgebras in $\Hopf_k$ in the
underlying category $\Vect_k$ of $k$-vector spaces.
```

**Reading.**
* "wide pushout of morphisms in $\Hopf$ that are regular epimorphisms in $\C$" ↦ diagram shape
  `J` equivalent to `WidePushoutShape K`, with legs mapped to regular epimorphisms by `hd`.
* "strictly created from $\C$" ↦ `StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C)`.
* hypotheses on `C`: `HasPullbacks C` and `MonoidalClosed C`.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each statement
  (CHALLENGE.md, *Differences of detail*).
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*; docs/STATE.yml, deviations).
-/
theorem ex_4_20_2_pushout (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [MonoidalClosed C] [HasPullbacks C] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] [HasChosenProductsOfSize.{0} Cat.{v, u}] (K : Type v)
    (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ HopfModel.forget C).toFunctor.map
        (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (HopfModel.forget C) :=
  sorry

/-- **Example 4.20 (2), joint pullbacks** ([forsman2026syntactic], §4).

```latex
Consider a symmetric monoidal closed category $\C = (\C,\otimes,I)$ that is both complete and
cocomplete. Assume the tensor $\otimes$ preserves finite limits componentwise. Consider the
category $\Hopf$ of Hopf algebras in $\C$. Corollary~\ref{cor:liftingSifted} allows one to compute
the following limits and colimits in $\Hopf$ by strictly creating them from $\C$:
```

```latex
\item More generally, consider morphisms $f_i\colon x_i\to y$ in $\Hopf$ that are regular
monomorphisms in $\C$ for $i\leq n$. The joint pullback of the $f_i$ is strictly created from $\C$
(dual of Theorem \ref{thm:creation_wide_pushouts}). Similarly, any wide pushout of morphisms in
$\Hopf$ that are regular epimorphisms in $\C$ is strictly created from $\C$. This explains why for
a field $k$ one can compute finite intersections of Hopf subalgebras in $\Hopf_k$ in the
underlying category $\Vect_k$ of $k$-vector spaces.
```

**Reading.**
* "joint pullback of morphisms in $\Hopf$ that are regular monomorphisms in $\C$ for $i \leq n$" ↦
  finite indexing `[Finite K]`, diagram shape `J` equivalent to `WidePullbackShape K`, with legs
  mapped to regular monomorphisms by `hd`.
* "strictly created from $\C$" ↦ `StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C)`.
* hypotheses on `C`: `HasPushouts C` and `∀ X : C, PreservesFiniteLimits (tensorLeft X)`.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each statement
  (CHALLENGE.md, *Differences of detail*).
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*; docs/STATE.yml, deviations).
-/
theorem ex_4_20_2_pullback (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [∀ X : C, PreservesFiniteLimits (tensorLeft X)] [HasPushouts C]
    [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (K : Type v) [Finite K]
    (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u)) (d : J ⟶ HopfModel.thyCat C)
    (hd : ∀ j, Nonempty (RegularMono ((d ≫ HopfModel.forget C).toFunctor.map
        (e.functor.map (WidePullbackShape.Hom.term j))))) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget C) :=
  sorry

/-- **Example 4.20 (3)** ([forsman2026syntactic], §4).

```latex
Consider a symmetric monoidal closed category $\C = (\C,\otimes,I)$ that is both complete and
cocomplete. Assume the tensor $\otimes$ preserves finite limits componentwise. Consider the
category $\Hopf$ of Hopf algebras in $\C$. Corollary~\ref{cor:liftingSifted} allows one to compute
the following limits and colimits in $\Hopf$ by strictly creating them from $\C$:
```

```latex
\item Any filtered colimit in $\Hopf$ is strictly created from $\C$.
```

**Reading.**
* "any filtered colimit in $\Hopf$ is strictly created from $\C$" ↦ `[IsFiltered (I : Type u)]`
  implies `StrictlyCreatesLeftKan (toOne I) d (HopfModel.forget C)`.
* hypotheses on `C`: assumes monoidal closed, rather than complete and cocomplete.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each statement
  (CHALLENGE.md, *Differences of detail*).
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*; docs/STATE.yml, deviations).
-/
theorem ex_4_20_3 (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (I : Cat.{v, u}) [IsFiltered (I : Type u)]
    (d : I ⟶ HopfModel.thyCat C) :
    StrictlyCreatesLeftKan (toOne I) d (HopfModel.forget C) := sorry

universe w

/-- **Example 4.20 (3), small shapes** ([forsman2026syntactic], §4): the companion of `ex_4_20_3`
for filtered shapes of any size that are small with respect to `C`.

```latex
\item Any filtered colimit in $\Hopf$ is strictly created from $\C$.
```

**Reading.**
* "any filtered colimit" ↦ any filtered `J : Type w` with `[Category.{w} J]`, `u`-small and
  locally `v`-small (`[Small.{u} J]`, `[LocallySmall.{v} J]`; for instance `w ≤ u, v`), so that
  the shape need not be a 1-cell of `Cat.{v, u}`.
* "created" ↦ Mathlib's `CreatesColimitsOfShape` for `J` and the forgetful functor (creation up
  to isomorphism, as a `Nonempty`); the strict form for shapes in `Cat.{v, u}` is `ex_4_20_3`.

**Deviations.**
- stronger: as for `ex_4_20_3`.
- different: creation in Mathlib's sense, up to isomorphism (chosen by the author).
-/
theorem ex_4_20_3_small (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [MonoidalClosed C] [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    [HasChosenProductsOfSize.{0} Cat.{v, u}] (J : Type w) [Category.{w} J] [Small.{u} J]
    [LocallySmall.{v} J] [IsFiltered J] :
    Nonempty (CreatesColimitsOfShape J (HopfModel.forget C).toFunctor) := sorry

end UlmerBialgebras.Paper
