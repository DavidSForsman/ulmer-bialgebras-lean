module

public import UlmerBialgebras.Paper.Sec4DefsEx420
public import UlmerBialgebras.Kan.SiftedModel
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive

/-!
# Example 4.20: the case of `Vect_k`, and the closing remark

Two statements of Example 4.20 of [forsman2026syntactic] that `UlmerBialgebras/Paper/Sec4Hopf.lean`
does not
cover:

* `ex_4_20_2_vect`: for a field `k`, finite intersections of Hopf subalgebras in `Hopf_k` are
  computed in `Vect_k`. The joint pullback of finitely many morphisms of Hopf monoids in `Vect_k`
  whose underlying linear maps are injective is strictly created by the forgetful functor.
* `ex_4_20_general`: the closing remark. Items (1)–(3) hold for any theory `T` and any `Σ`-model
  `M` in `CAT` whose categories have, and whose functors preserve componentwise, sifted colimits
  and finite cosifted limits, and whose categories have kernel pairs and cokernel pairs: the
  conjunction of the five statements, each under the conditions it needs.

`Vect_k` is `ModuleCat.{u} k` with its symmetric monoidal structure. Its Hopf model lives in
`Cat.{u, u + 1}`, so the shape of a joint pullback is any `J : Cat.{u, u + 1}` equivalent to
`WidePullbackShape K` for a finite `K : Type u`.

## Main results

* `UlmerBialgebras.Paper.ex_4_20_2_vect`
* `UlmerBialgebras.Paper.ex_4_20_general`, `UlmerBialgebras.Paper.ex_4_20_general_2`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section


universe v u w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory Limits

/-- **Example 4.20 (2), the case of $\Vect_k$** ([forsman2026syntactic], §4).

```latex
\item More generally, consider morphisms $f_i\colon x_i\to y$ in $\Hopf$ that are regular
monomorphisms in $\C$ for $i\leq n$. The joint pullback of the $f_i$ is strictly created from $\C$
(dual of Theorem \ref{thm:creation_wide_pushouts}). Similarly, any wide pushout of morphisms in
$\Hopf$ that are regular epimorphisms in $\C$ is strictly created from $\C$. This explains why for
a field $k$ one can compute finite intersections of Hopf subalgebras in $\Hopf_k$ in the
underlying category $\Vect_k$ of $k$-vector spaces.
```

**Reading.**
* field $k$ and category $\Vect_k$ of $k$-vector spaces ↦ `k : Type u` with `[Field k]` and
  `ModuleCat.{u} k`.
* category $\Hopf_k$ of Hopf algebras over $k$ ↦ `HopfModel.thyCat (ModuleCat.{u} k)`.
* finite family of Hopf subalgebras $f_i \colon x_i \to y$ ↦ finite indexing type `K : Type u`
  with `[Finite K]`, diagram shape `J : Cat.{u, u + 1}` with equivalence
  `e : WidePullbackShape K ≌ (J : Type (u + 1))`, diagram
  `d : J ⟶ HopfModel.thyCat (ModuleCat.{u} k)`, and `hd` stating that each leg's underlying
  $k$-linear map via `hopfVectForget k` is `Function.Injective`.
* "compute finite intersections of Hopf subalgebras in $\Hopf_k$ in the underlying category
  $\Vect_k$" ↦ `StrictlyCreatesRightKan (toOne J) d (HopfModel.forget (ModuleCat.{u} k))`.

**Deviations.**
- different (size): takes `[Category.{v} C]` with `Cat.{v, u}` instances (CHALLENGE.md, *Size
  migration*),
  specialized here to `ModuleCat.{u} k` in `Cat.{u, u + 1}`.
-/
theorem ex_4_20_2_vect (k : Type u) [Field k] (K : Type u) [Finite K] (J : Cat.{u, u + 1})
    (e : WidePullbackShape K ≌ (J : Type (u + 1)))
    (d : J ⟶ HopfModel.thyCat (ModuleCat.{u} k))
    (hd : ∀ j, Function.Injective ((hopfVectForget k).map
      (d.toFunctor.map (e.functor.map (WidePullbackShape.Hom.term j)))).hom) :
    StrictlyCreatesRightKan (toOne J) d (HopfModel.forget (ModuleCat.{u} k)) := sorry

/-- **Example 4.20, closing remark, items (1) and (3)** ([forsman2026syntactic], §4).

```latex
\item Reflexive coequalizers and coreflexive equalizers in $\Hopf$ are strictly created from $\C$
as the tensor preserves such (co)limits (Corollary \ref{cor:liftingSifted} and its dual).
```

```latex
\item Any filtered colimit in $\Hopf$ is strictly created from $\C$.
```

```latex
Of course, there is nothing special about $\Hopf$. We could have chosen any bialgebraic theory $T$
and considered $\C^T$, and obtained the same results. Similarly, nothing depends on the symmetric
monoidal structure: we could have chosen any $\Sigma$-model $M$, where the categories $M_c$ have
and the functors $M(B)$ (componentwise) preserve sifted colimits and finite cosifted limits, and
the categories $M_c$ have kernel pairs and cokernel pairs.
```

**Reading.**
* "any bialgebraic theory $T$" and "any $\Sigma$-model $M$" ↦ `Sg : TwoSig`,
  `M : Model Sg Cat.{v, u}`, `sg : OneSig Sg`, `T : Theory sg`, with category of bialgebras
  `M.thyObj sg T` and forgetful 1-cell `M.e sg T ≫ M.u sg`.
* "categories $M_c$ have and the functors $M(B)$ (componentwise) preserve sifted colimits and
  finite cosifted limits" ↦ `M.SiftedColimitsComponentwise` and
  `M.FinCosiftedLimitsComponentwise`. "Sifted colimits" are small ones relative to
  `CAT = Cat.{v, u}`: shapes with objects and morphisms in `Type v`.
* item (1), reflexive coequalizers and coreflexive equalizers ↦ shapes `J : Cat.{v, u}` equivalent
  to `WalkingReflexivePair` (`StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)`) and
  `WalkingCoreflexivePair` (`StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)`).
* item (3), filtered colimits ↦ shapes `I : Cat.{v, u}` with `[IsFiltered (I : Type u)]` and
  `[EssentiallySmall.{v} (I : Type u)]`, the filtered categories equivalent to small ones
  (`StrictlyCreatesLeftKan (toOne I) d (M.e sg T ≫ M.u sg)`).
* item (2) is stated separately in `ex_4_20_general_2`.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each clause
  (CHALLENGE.md, *Differences of detail*).
- different (size): stated for models `M : Model Sg Cat.{v, u}`, with the products, inserters and
  equifiers of `Cat.{v, u}` as instance arguments (CHALLENGE.md, *Size migration*).
-/
theorem ex_4_20_general [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] :
    -- (1) reflexive coequalizers and coreflexive equalizers
    (M.SiftedColimitsComponentwise →
      ∀ (J : Cat.{v, u}) (_ : WalkingReflexivePair ≌ (J : Type u)) (d : J ⟶ M.thyObj sg T),
        StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    (M.FinCosiftedLimitsComponentwise →
      ∀ (J : Cat.{v, u}) (_ : WalkingCoreflexivePair ≌ (J : Type u)) (d : J ⟶ M.thyObj sg T),
        StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    -- (3) filtered colimits
    (M.SiftedColimitsComponentwise →
      ∀ (I : Cat.{v, u}) [IsFiltered (I : Type u)] [EssentiallySmall.{v} (I : Type u)]
        (d : I ⟶ M.thyObj sg T),
        StrictlyCreatesLeftKan (toOne I) d (M.e sg T ≫ M.u sg)) := sorry

/-- **Example 4.20, closing remark, item (2)** ([forsman2026syntactic], §4).

```latex
\item More generally, consider morphisms $f_i\colon x_i\to y$ in $\Hopf$ that are regular
monomorphisms in $\C$ for $i\leq n$. The joint pullback of the $f_i$ is strictly created from $\C$
(dual of Theorem \ref{thm:creation_wide_pushouts}). Similarly, any wide pushout of morphisms in
$\Hopf$ that are regular epimorphisms in $\C$ is strictly created from $\C$. This explains why for
a field $k$ one can compute finite intersections of Hopf subalgebras in $\Hopf_k$ in the
underlying category $\Vect_k$ of $k$-vector spaces.
```

```latex
Of course, there is nothing special about $\Hopf$. We could have chosen any bialgebraic theory $T$
and considered $\C^T$, and obtained the same results. Similarly, nothing depends on the symmetric
monoidal structure: we could have chosen any $\Sigma$-model $M$, where the categories $M_c$ have
and the functors $M(B)$ (componentwise) preserve sifted colimits and finite cosifted limits, and
the categories $M_c$ have kernel pairs and cokernel pairs.
```

**Reading.**
* "categories $M_c$ have kernel pairs and cokernel pairs" ↦ `M.HasKernelPairs` and
  `M.HasCokernelPairs`, together with `M.SiftedColimitsComponentwise` and
  `M.FinCosiftedLimitsComponentwise`.
* joint pullback of finitely many morphisms that the forgetful functor sends to regular
  monomorphisms ↦ `K : Type v` with `[Finite K]`, shape `J : Cat.{v, u}` with
  `e : WidePullbackShape K ≌ (J : Type u)`, legs mapped to `RegularMono` under
  `M.e sg T ≫ M.u sg`, and `StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)`.
* wide pushout of morphisms that the forgetful functor sends to regular epimorphisms ↦ `K : Type v`,
  shape `J : Cat.{v, u}` with `e : WidePushoutShape K ≌ (J : Type u)`, legs mapped to
  `RegularEpi` under `M.e sg T ≫ M.u sg`, and
  `StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)`.

**Deviations.**
- stronger: assumes only the necessary part of the paper's hypotheses for each clause
  (CHALLENGE.md, *Differences of detail*).
- different (size): stated for models `M : Model Sg Cat.{v, u}`, with the products, inserters and
  equifiers of `Cat.{v, u}` as instance arguments (CHALLENGE.md, *Size migration*).
-/
theorem ex_4_20_general_2 [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] :
    (M.FinCosiftedLimitsComponentwise → M.HasCokernelPairs →
      ∀ (K : Type v) [Finite K] (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u))
        (d : J ⟶ M.thyObj sg T),
        (∀ j, Nonempty (RegularMono ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
          (e.functor.map (WidePullbackShape.Hom.term j))))) →
        StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg)) ∧
    (M.SiftedColimitsComponentwise → M.HasKernelPairs →
      ∀ (K : Type v) (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
        (d : J ⟶ M.thyObj sg T),
        (∀ j, Nonempty (RegularEpi ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
          (e.functor.map (WidePushoutShape.Hom.init j))))) →
        StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg)) := sorry

end UlmerBialgebras.Paper
