module

public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec5DefsCart
public import UlmerBialgebras.Paper.Sec5DefsKanIns
public import Foundations.CategoryTheory.Factorization.ExactCategory
public import UlmerBialgebras.Kan.SiftedModel
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Creates
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Kan.SiftedApplications
public import UlmerBialgebras.Paper.Sec6DefsAlgTheory

/-!
# Challenge: Corollary 5.9, for theories of universal algebra

Corollary 5.9 quantifies over "single-sorted theories of universal algebra with a countable
signature". Here such a theory is an equational theory `T : L.Theory` over a many-sorted language
`L : MSLanguage` with one sort and countably many function symbols, and `C^T` is the category
`T.ModelCat C` of its models in `C` (`UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean`). The companion
statement for
shapes of any size, `cor_5_9_small`, stays in `UlmerBialgebras/Paper/Sec5.lean`.

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_monadic`: `T.ModelCat C` has countable
  colimits and its forgetful functor is monadic.
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_strictlyCreates`: the forgetful functor
  strictly creates countable sifted colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 5.9
-/

@[expose] public section

universe v w s

namespace UlmerBialgebras.Paper.UniversalAlgebra

open CategoryTheory Limits MSLanguage

attribute [local instance] catOfSizeHom in
/-- **Corollary 5.9** ([forsman2026syntactic], §5): monadicity and countable colimits.

```latex
Let $\C$ be a cartesian closed category with countable colimits. Then for any single-sorted theory
$T$ of universal algebra with a countable signature, the category $\C^T$ has countable colimits and
the forgetful functor $U\colon \C^T\to \C$ is monadic and $U$ strictly creates countable sifted
colimits.
```

**Reading.**
* cartesian closed category with countable colimits ↦
  `[Category.{max s v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]` and
  `HasColimitsOfSizeLE Cardinal.aleph0.{max s v} C`.
* single-sorted theory of universal algebra with a countable signature ↦ an equational theory
  `T : L.Theory` over a many-sorted language `L : MSLanguage` with one sort (`[Unique L.Sorts]`)
  and countably many function symbols (`Cardinal.mk L.Functions ≤ Cardinal.aleph0`).
* `$\C^T$` ↦ `T.ModelCat C`, the category of models of `T` in `C`, with its forgetful functor
  `Theory.ModelCat.forget C T`.
* "$\C^T$ has countable colimits and $U$ is monadic" ↦ the two conjuncts. The strict creation of
  countable sifted colimits is `modelCat_strictlyCreates`.

**Deviations.**
- different (size): `C` has objects in `Type (max s v w)` and morphisms in `Type (max s v)`
  (CHALLENGE.md, *Size migration*).
-/
theorem modelCat_monadic {L : MSLanguage.{s, s}} (C : Type (max s v w))
    [Category.{max s v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{max s v} C) [Unique L.Sorts]
    (hsize : Cardinal.mk L.Functions ≤ Cardinal.aleph0) (T : L.Theory) :
    Nonempty (MonadicRightAdjoint (Theory.ModelCat.forget C T)) ∧
      HasColimitsOfSizeLE Cardinal.aleph0.{max s v} (T.ModelCat C) := sorry

attribute [local instance] catOfSizeHom in
/-- **Corollary 5.9** ([forsman2026syntactic], §5): strict creation of countable sifted
colimits.

```latex
the forgetful functor $U\colon \C^T\to \C$ is monadic and $U$ strictly creates countable sifted
colimits.
```

**Reading.**
* the hypotheses ↦ those of `modelCat_monadic`.
* "$U$ strictly creates countable sifted colimits" ↦ `StrictlyCreatesLeftKan` along `toOne I` for
  every sifted `I : Cat` with countably many objects and every diagram `d : I ⟶ T.ModelCat C`.

**Deviations.**
- different (size): as for `modelCat_monadic`.
- stronger: the creation clause bounds the objects of `I` only, not its morphisms.
-/
theorem modelCat_strictlyCreates {L : MSLanguage.{s, s}} (C : Type (max s v w))
    [Category.{max s v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{max s v} C) [Unique L.Sorts]
    (hsize : Cardinal.mk L.Functions ≤ Cardinal.aleph0) (T : L.Theory)
    (I : Cat.{max s v, max s v w}) [IsSifted (I : Type (max s v w))]
    (hI : Cardinal.mk (I : Type (max s v w)) ≤ Cardinal.aleph0)
    (d : I ⟶ Cat.of (T.ModelCat C)) :
    StrictlyCreatesLeftKan (toOne I) d (Theory.ModelCat.forget C T).toCatHom := sorry


end UlmerBialgebras.Paper.UniversalAlgebra
