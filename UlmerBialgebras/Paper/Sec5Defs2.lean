module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Adjunction
public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Kan.ColimKan
public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Density.AAdjointRep

/-!
# Challenge: auxiliary definitions

Further definitions used by the statements of the challenge.  Like
`UlmerBialgebras/Paper/Sec3Defs.lean`,
this file is part of the trusted base and must be reviewed against the paper.

## Main results

* `UlmerBialgebras.Paper.IsMonadic2`, `UlmerBialgebras.Paper.IsComonadic2`: monadic and comonadic
  1-cells in a 2-category (Definition 5.1).
* `UlmerBialgebras.Paper.HasChainColimitsUpTo`: `κ_≤`-cocompleteness (Definition 5.4).
* `UlmerBialgebras.Paper.OrthogonalLE1`: `e ⊥_! m`, at most one diagonal filler (Definition 6.1).
* `UlmerBialgebras.Paper.HasUniqueLiftedOFS`: the lifted pair is an orthogonal factorization system
  on `M^T` and the unique one preserved by `U : M^T → M₀` (Corollary 6.7).
* `UlmerBialgebras.Paper.PreservesWidePushoutsOfRegEpis`: preservation of `K`-indexed wide pushouts
  of regular epimorphisms (Corollary 4.18, Theorem 4.19).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 5.1, 5.4, 6.1, Corollaries 4.18, 4.21, 6.7, 6.9, Theorem 4.19
-/

@[expose] public section

universe u v w u' v' uu₁ uu₂ uu₃ s s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- The identity 1-cell `a ⟶ b` along an equality `a = b` of objects. Used to compare
1-cells whose codomains are equal but not definitionally so. -/
def castHom {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] {a b : Obj} (h : a =
  b) : a ⟶ b :=
  h ▸ 𝟙 a

/-- **Definition 5.4** ([forsman2026syntactic]): `C` is `κ_≤`-cocomplete: it has colimits of
`μ`-chains for every infinite cardinal `μ ≤ κ` (a `μ`-chain is a functor out of `μ`, viewed as a
well-ordered set). -/
def HasChainColimitsUpTo (κ : Cardinal.{w}) (C : Type u) [Category.{v} C] : Prop :=
  ∀ μ : Cardinal.{w}, Cardinal.aleph0 ≤ μ → μ ≤ κ → HasColimitsOfShape μ.ord.ToType C

/-- `F` preserves the joint epicness of colimiting cocones of shape `J`. -/
def PreservesJointEpiOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cocone Kd), IsColimit c → ∀ ⦃y : D⦄ (p q : F.obj c.pt ⟶ y),
    (∀ j, F.map (c.ι.app j) ≫ p = F.map (c.ι.app j) ≫ q) → p = q

/-- `F` preserves the joint monicness of limiting cones of shape `J`. -/
def PreservesJointMonoOfShape (J : Type w) [Category.{v'} J] {C : Type u} [Category.{v} C]
    {D : Type u'} [Category D] (F : C ⥤ D) : Prop :=
  ∀ (Kd : J ⥤ C) (c : Cone Kd), IsLimit c → ∀ ⦃y : D⦄ (p q : y ⟶ F.obj c.pt),
    (∀ j, p ≫ F.map (c.π.app j) = q ≫ F.map (c.π.app j)) → p = q

/-- `C` has all colimits of size at most `κ` (indexed by small categories with at most `κ`
morphisms). -/
def HasColimitsOfSizeLE (κ : Cardinal.{w}) (C : Type u) [Category.{v} C] : Prop :=
  ∀ (J : Type w) [SmallCategory J], Cardinal.mk (Σ X Y : J, X ⟶ Y) ≤ κ →
    HasColimitsOfShape J C

/-! ## Definition 5.1: monadicity in a 2-category -/

section Monadic2

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 5.1** ([forsman2026syntactic]). A 1-cell `g : d ⟶ c` is **monadic** if it has a
left adjoint `f` (unit `η`, counit `ε`) such that `(d, g, gε)` is an Eilenberg–Moore object of the
monad `(gf, gεf, η)` up to equivalence: for each object `x`, the comparison functor
`K(x, d) → K(x, c)^{K(x, gf)}`, `h ↦ (gh, gεh)`, of the induced adjunction
`K(x, f) ⊣ K(x, g)` (`UlmerBialgebras.TwoAdj.postcompAdj`) is an equivalence of categories. -/
def IsMonadic2 {c d : Obj} (g : d ⟶ c) : Prop :=
  ∃ (f : c ⟶ d) (A : TwoAdj f g), ∀ x : Obj, (Monad.comparison (A.postcompAdj x)).IsEquivalence

/-- **Definition 5.1** ([forsman2026syntactic]), dual: `f : c ⟶ d` is **comonadic** if it has a
right adjoint `g` such that, for each object `x`, the comparison functor of the induced adjunction
`K(x, f) ⊣ K(x, g)` into the coalgebras of the comonad `K(x, fg)` is an equivalence. -/
def IsComonadic2 {c d : Obj} (f : c ⟶ d) : Prop :=
  ∃ (g : d ⟶ c) (A : TwoAdj f g), ∀ x : Obj,
    (Comonad.comparison (A.postcompAdj x)).IsEquivalence

end Monadic2

end UlmerBialgebras.Paper

/-! ## Corollary 6.9: sub-1-signatures and sub-theories

(Definitions from `UlmerBialgebras/Proofs/Sec6/SubSigExact.lean`; [forsman2026syntactic], Corollary
6.9.) -/

namespace UlmerBialgebras

end UlmerBialgebras
