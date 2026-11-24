module

public import UlmerBialgebras.Paper.Sec6DefsAlgTheory

/-!
# Equational theories as `Σ_Cart`-theories (addition beyond the paper)

Not a result of the paper. For a many-sorted equational theory `T` (`MSLanguage.Theory`;
[ARV, Ch. 1 and 14]) and its translation `T'` relative to `Σ_Cart`
(`MSLanguage.Theory.toCartTheory`), the category `T.ModelCat C` of models of `T` in a category
`C` with finite products is **isomorphic** (not only equivalent) to the category `C^{T'}` of
Definition 3.14 of [forsman2026syntactic], over the forgetful functors to `C^S`.

**Universes.** The universes of `C` are general: `C : Type u` with `Category.{v} C` and
finite products, with `u` and `v` independent. The language of the isomorphisms is
`L : MSLanguage.{s, s}`: its sorts and function symbols live in one size universe `s`, like the
symbols of a 1-signature (Definition 3.5). `C^{T'}` is computed in `CAT` for the small copy
`AsSmall.{s} C`, since the `Σ_Cart`-model `cartModel` needs a category whose objects and morphisms
share a universe. The bridges `ofLanguage_model_iff` and `ofLanguage_isHom_iff` hold for any
`FirstOrder.Language.{uF, uR}`; since `ofLanguage L'` has its one sort in `Type`, they chain with
the isomorphisms for `uF = 0`.

Isomorphisms of categories are stated as a pair of functors that are inverse up to equality of
functors, and that commute with the forgetful functors up to equality.

* `modelCat_iso_cartThy_univ`: `Mod_C(T) ≅ C^{T'}` over `C^S`, for `C : Type u` with
  `Category.{v} C` and finite products, with `C^{T'}` computed for `AsSmall C`; `C^S` is
  identified with `(AsSmall C)^S` along `AsSmall.up`.
* `modelCat_type_iso_cartThy`: the Set case, the instance `C := Type u` of
  `modelCat_iso_cartThy_univ`.
* `ofLanguage_model_iff`, `ofLanguage_isHom_iff`: for a single-sorted Mathlib language (algebraic
  for homomorphisms), models and homomorphisms in `Type w` are exactly Mathlib's (`M ⊨ T` and
  `M →[L] N`), so the Set case is about Mathlib's first-order models.
* `grp_modelCat_iso`: the equational theory of groups and the `Σ_Cart`-theory of groups
  `grpTheory S` of Corollary 6.11 have isomorphic categories of models over `C^S`; with
  `GrpModels.grpModelEquiv` this identifies the models with `S → Grp C`.

## Main results

* `UlmerBialgebras.Paper.modelCat_iso_cartThy_univ`
* `UlmerBialgebras.Paper.modelCat_type_iso_cartThy`
* `UlmerBialgebras.Paper.ofLanguage_model_iff`
* `UlmerBialgebras.Paper.ofLanguage_isHom_iff`
* `UlmerBialgebras.Paper.grp_modelCat_iso`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19, Definition 3.14, Corollaries 5.9 and 6.11
-/

@[expose] public section

universe v u w uF uR s

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cart MSLanguage

/-- **Models of an equational theory are `Σ_Cart`-models** (addition beyond
[forsman2026syntactic]): for a cartesian monoidal category `C` (objects in `Type (max s v w)`,
morphisms in `Type (max s v)`), the category of models of a theory `T` over a language
`L : MSLanguage.{s, s}` in `C` is isomorphic to `C^{T'}`, over `C^S`. -/
theorem modelCat_iso_cartThy_univ (C : Type (max s v w)) [Category.{max s v} C]
    [CartesianMonoidalCategory C] {L : MSLanguage.{s, s}} (T : L.Theory) :
    ∃ (F : T.ModelCat C ⥤ Theory.cartThy.{v, w, s} C T)
      (G : Theory.cartThy.{v, w, s} C T ⥤ T.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Theory.cartThyForget.{v, w, s} C T = Theory.ModelCat.forget C T := sorry

/-- **The Set case** (addition beyond [forsman2026syntactic]): the category of models of `T` in
`Set = Type (max s u)` is isomorphic to `Set^{T'}`, over `Set^S`. -/
theorem modelCat_type_iso_cartThy {L : MSLanguage.{s, s}} (T : L.Theory) :
    ∃ (F : T.ModelCat (Type (max s u)) ⥤ Theory.cartThy.{u, max s u + 1, s} (Type (max s u)) T)
      (G : Theory.cartThy.{u, max s u + 1, s} (Type (max s u)) T ⥤ T.ModelCat (Type (max s u))),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Theory.cartThyForget.{u, max s u + 1, s} (Type (max s u)) T =
          Theory.ModelCat.forget (Type (max s u)) T := sorry

/-- **Set models are Mathlib's first-order models** (addition beyond [forsman2026syntactic]): for
a single-sorted Mathlib language `L'` and an equational theory `T` over it, a Mathlib
`L'`-structure `M` satisfies the first-order theory `T.toFOTheory` (Mathlib's `M ⊨ T`) iff the
one-sorted family `M` in `Type w` is a model of `T`. -/
theorem ofLanguage_model_iff {L' : FirstOrder.Language.{uF, uR}} (T : (ofLanguage L').Theory)
    (M : Type w) [L'.Structure M] :
    FirstOrder.Language.Theory.Model M (Theory.toFOTheory T) ↔
      MSLanguage.Theory.Model (fun _ : Unit => M) T := sorry

/-- **Set homomorphisms are Mathlib's homomorphisms** (addition beyond [forsman2026syntactic]):
for an algebraic single-sorted Mathlib language `L'`, a function `g : M → N` underlies a Mathlib
homomorphism `M →[L'] N` iff it underlies a homomorphism of the one-sorted families. -/
theorem ofLanguage_isHom_iff {L' : FirstOrder.Language.{uF, uR}} [L'.IsAlgebraic]
    (M N : Type w) [L'.Structure M] [L'.Structure N] (g : M → N) :
    (∃ φ : FirstOrder.Language.Hom L' M N, ⇑φ = g) ↔
      ∃ h : (ofLanguage L').Hom (fun _ : Unit => M) (fun _ : Unit => N),
        ∀ s, h.toFun s = TypeCat.ofHom g := sorry

/-- **The theory of groups, reconciled** (addition beyond [forsman2026syntactic]): for a
cartesian monoidal category `C` (objects in `Type (max v w)`, morphisms in `Type v`), the models
of the equational theory of groups in each sort of `S` form a category isomorphic, over `C^S`, to
the category of models of the `Σ_Cart`-theory of groups `grpTheory S` (Corollary 6.11) in `C`. -/
theorem grp_modelCat_iso (C : Type (max v w)) [Category.{v} C] [CartesianMonoidalCategory C]
    (S : Type) :
    ∃ (F : (grpEqTheory S).ModelCat C ⥤
        ((cartModel C).thyObj (grpSig S) (grpTheory S) : Cat.{v, max v w}))
      (G : ((cartModel C).thyObj (grpSig S) (grpTheory S) : Cat.{v, max v w}) ⥤
        (grpEqTheory S).ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ ((cartModel C).e (grpSig S) (grpTheory S) ≫ (cartModel C).u (grpSig S)).toFunctor =
          Theory.ModelCat.forget C (grpEqTheory S) := sorry

end UlmerBialgebras.Paper
