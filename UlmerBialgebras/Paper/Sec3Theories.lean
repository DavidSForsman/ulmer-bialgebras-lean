module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Hopf_
public import UlmerBialgebras.Paper.Sec3DefsHopfModel
public import UlmerBialgebras.Paper.Sec3DefsLaxLimit

/-!
# Challenge: Examples 3.20 (2) and (4)

* Hopf algebras: for the Hopf model of a braided monoidal category `C`
  (`UlmerBialgebras/Paper/Sec3DefsHopfModel.lean`), the category `M^{T_Hopf}` is Mathlib's category
  `Hopf C` of
  Hopf monoids. The paper states this for symmetric monoidal `C`.
* Lax-limit theories: the theory `T_Lax` of a 2-signature is algebraic, and for the
  signatures of a monad, a monoidal category and a symmetric monoidal category it is the
  theory of monad algebras, monoids and commutative monoids
  (`UlmerBialgebras/Paper/Sec3DefsLaxLimit.lean`).

## Main results

* `UlmerBialgebras.Paper.ex_3_20_2`: for the Hopf model of a braided monoidal category `C`,
  `M^{T_Hopf}` is isomorphic over `C` to `Hopf C` (Examples 3.20 (2)).
* `UlmerBialgebras.Paper.ex_3_20_4_algebraic`: the lax-limit theory `T_Lax` is algebraic
  (Examples 3.20 (4)).
* `UlmerBialgebras.Paper.ex_3_20_4_mnd`, `UlmerBialgebras.Paper.ex_3_20_4_mon`,
  `UlmerBialgebras.Paper.ex_3_20_4_smon`: `M^{T_Lax}` is isomorphic over `C` to the Eilenberg–Moore
  category of a monad, to `Mon C`, and to `CommMon C` (Examples 3.20 (4)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (2), (4)
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [A. Joyal, R. Street, *Braided Tensor Categories*][joyalBraidedTensorCategories1993]
* [R. Street, *Quantum Groups: A Path to Current Algebra*][streetQuantumGroupsPath2007]
* [R. Street, *Limits indexed by category-valued 2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v uu₁ uu₂ uu₃

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory

/-- **Examples 3.20 (2)** ([forsman2026syntactic], §3).

```latex
We give the theories of monoids, Hopf algebras and fields, and a family of theories generalizing
lax limits:
```

```latex
Evaluating this theory in $\CAT$ over a symmetric monoidal category $M$ yields precisely the
classical category $\Hopf_M$ of internal Hopf algebras.
```

**Reading.**
* "symmetric monoidal category $M$" ↦ `(C : Type (max u v)) [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]`: the formalization assumes only a braided monoidal category.
* "evaluating this theory in $\CAT$ ... yields precisely the classical category $\Hopf_M$" ↦
  mutually inverse functors `F : HopfModel.ThyObj C ⥤ Hopf C` and `G : Hopf C ⥤ HopfModel.ThyObj C`
  (an isomorphism of categories).
* "over $M$" ↦ compatibility over `C`: `F ⋙ HopfModel.hopfForget C = (HopfModel.forget C).toFunctor
  ⋙ (((HopfModel.hopfModel C).P0 HopfEx.oneSig).π ()).toFunctor`.
* $\Hopf_M$ ↦ Mathlib's `CategoryTheory.Hopf C` (aliased as `Hopf C`).

**Deviations.**
- stronger: assumes only a braided monoidal category rather than symmetric (CHALLENGE.md,
  *Differences of detail*).
-/
theorem ex_3_20_2 (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] :
    ∃ (F : HopfModel.ThyObj C ⥤ Hopf C) (G : Hopf C ⥤ HopfModel.ThyObj C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ HopfModel.hopfForget C =
          (HopfModel.forget C).toFunctor ⋙
            (((HopfModel.hopfModel C).P0 HopfEx.oneSig).π ()).toFunctor := sorry

/-- **Examples 3.20 (4)** ([forsman2026syntactic], §3; generalizing lax limits,
[streetLimitsIndexedCategoryvalued1976], [lack2CategoriesCompanion2010]).

```latex
We give the theories of monoids, Hopf algebras and fields, and a family of theories generalizing
lax limits:
```

```latex
Consider an arbitrary $2$-signature $\Sigma = (C,\mathcal{F},\mathcal{T})$. We construct an
associated algebraic theory $T$ for $\Sigma$ which generalizes the notion of a lax limit of a
strict $2$-functor \cite{streetLimitsIndexedCategoryvalued1976, lack2CategoriesCompanion2010} to the
cartesian (multivariable) setting.
```

**Reading.**
* "associated algebraic theory $T$ for $\Sigma$" ↦ `(LaxEx.theory Sg).IsAlgebraic`: the theory
  satisfies `IsAlgebraic` (every equation in the theory is between a term-graph path and a function
  symbol application).
* "$2$-signature $\Sigma$" ↦ `(Sg : TwoSig.{uu₁, uu₂, uu₃})`: with sorts, operations and 2-cells in
  independent universe levels.

**Deviations.** none recorded.
-/
theorem ex_3_20_4_algebraic (Sg : TwoSig.{uu₁, uu₂, uu₃}) : (LaxEx.theory Sg).IsAlgebraic := sorry

/-- **Examples 3.20 (4), monads** ([forsman2026syntactic], §3).

```latex
We give the theories of monoids, Hopf algebras and fields, and a family of theories generalizing
lax limits:
```

```latex
If $\Sigma$ is the signature for a monad, a monoidal category or a symmetric monoidal category,
then the associated algebraic theory is the theory of monad algebras, monoids and commutative
monoids, respectively.
```

**Reading.**
* category $C$ with monad $T$ ↦ `{C : Type (max u v)} [Category.{v} C] (T : Monad C)`.
* "signature for a monad" ↦ `SigEx.mndSig`: the 2-signature with sort c, 1-cell T, and 2-cells
  μ and η.
* "associated algebraic theory is the theory of monad algebras" ↦ mutually inverse functors
  `F : LaxLimit.ThyObj (MndEx.model T) ⥤ T.Algebra` and
  `G : T.Algebra ⥤ LaxLimit.ThyObj (MndEx.model T)` (an isomorphism of categories).
* "over $C$" ↦ `F` commutes with the forgetful functors to `C`:
  `F ⋙ T.forget` equals the model projection.
* "monad algebras" ↦ Mathlib's `CategoryTheory.Monad.Algebra T`.

**Deviations.** none recorded.
-/
theorem ex_3_20_4_mnd {C : Type (max u v)} [Category.{v} C] (T : Monad C) :
    ∃ (F : LaxLimit.ThyObj (MndEx.model T) ⥤ T.Algebra)
      (G : T.Algebra ⥤ LaxLimit.ThyObj (MndEx.model T)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ T.forget = ((MndEx.model T).thyForget (LaxEx.oneSig SigEx.mndSig)
            (LaxEx.theory SigEx.mndSig)).toFunctor ⋙
          (((MndEx.model T).P0 (LaxEx.oneSig SigEx.mndSig)).π ()).toFunctor := sorry

/-- **Examples 3.20 (4), monoidal categories** ([forsman2026syntactic], §3).

```latex
We give the theories of monoids, Hopf algebras and fields, and a family of theories generalizing
lax limits:
```

```latex
If $\Sigma$ is the signature for a monad, a monoidal category or a symmetric monoidal category,
then the associated algebraic theory is the theory of monad algebras, monoids and commutative
monoids, respectively.
```

**Reading.**
* monoidal category $C$ ↦ `(C : Type (max u v)) [Category.{v} C] [MonoidalCategory C]`.
* "signature for a monoidal category" ↦ `SigEx.monSig`: the 2-signature of monoidal categories with
  sort c, tensor product, unit, and associator/unitors.
* "associated algebraic theory is the theory of monoids" ↦ mutually inverse functors
  `F : LaxLimit.ThyObj (LaxLimit.monModel C) ⥤ Mon C` and
  `G : Mon C ⥤ LaxLimit.ThyObj (LaxLimit.monModel C)` (an isomorphism of categories).
* "over $C$" ↦ `F` commutes with the forgetful functors to `C`:
  `F ⋙ Mon.forget C` equals the model projection.
* "monoids" ↦ Mathlib's `CategoryTheory.Mon C`.

**Deviations.** none recorded.
-/
theorem ex_3_20_4_mon (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] :
    ∃ (F : LaxLimit.ThyObj (LaxLimit.monModel C) ⥤ Mon C)
      (G : Mon C ⥤ LaxLimit.ThyObj (LaxLimit.monModel C)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Mon.forget C = ((LaxLimit.monModel C).thyForget (LaxEx.oneSig SigEx.monSig)
            (LaxEx.theory SigEx.monSig)).toFunctor ⋙
          (((LaxLimit.monModel C).P0 (LaxEx.oneSig SigEx.monSig)).π ()).toFunctor := sorry

/-- **Examples 3.20 (4), symmetric monoidal categories** ([forsman2026syntactic], §3).

```latex
We give the theories of monoids, Hopf algebras and fields, and a family of theories generalizing
lax limits:
```

```latex
If $\Sigma$ is the signature for a monad, a monoidal category or a symmetric monoidal category,
then the associated algebraic theory is the theory of monad algebras, monoids and commutative
monoids, respectively.
```

**Reading.**
* symmetric monoidal category $C$ ↦
  `(C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]`.
* "signature for a symmetric monoidal category" ↦ `SigEx.smonSig`: the 2-signature with monoidal
  structure and braiding/symmetry 2-cells.
* "associated algebraic theory is the theory of commutative monoids" ↦ mutually inverse functors
  `F : LaxLimit.ThyObj (Loc.smonModel C) ⥤ CommMon C` and
  `G : CommMon C ⥤ LaxLimit.ThyObj (Loc.smonModel C)` (an isomorphism of categories).
* "over $C$" ↦ `F` commutes with the forgetful functors to `C`:
  `F ⋙ CommMon.forget C` equals the model projection.
* "commutative monoids" ↦ Mathlib's `CategoryTheory.CommMon C`.

**Deviations.** none recorded.
-/
theorem ex_3_20_4_smon (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C]
    [SymmetricCategory C] :
    ∃ (F : LaxLimit.ThyObj (Loc.smonModel C) ⥤ CommMon C)
      (G : CommMon C ⥤ LaxLimit.ThyObj (Loc.smonModel C)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ CommMon.forget C = ((Loc.smonModel C).thyForget (LaxEx.oneSig SigEx.smonSig)
            (LaxEx.theory SigEx.smonSig)).toFunctor ⋙
          (((Loc.smonModel C).P0 (LaxEx.oneSig SigEx.smonSig)).π ()).toFunctor := sorry

end UlmerBialgebras.Paper
