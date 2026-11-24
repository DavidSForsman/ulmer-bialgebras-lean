module

public import UlmerBialgebras.Proofs.Sec6.AlgTheoryGrp

/-!
# Solution: equational theories as `Σ_Cart`-theories

Proofs of the statements of `Companion/Statements/ExtrasAlgTheory.lean` (an addition beyond the
paper).

* `modelCat_iso_cartThy_univ` composes the transport of models along `AsSmall.up`
  (`modelCat_transport`) with the isomorphism for a cartesian category
  (`CartIso.modelCat_iso_cartThy`).
* `modelCat_type_iso_cartThy` is the instance `C := Type u` of `modelCat_iso_cartThy_univ`.
* `grp_modelCat_iso` composes these with the isomorphism of the translated theory of groups with
  `grpTheory S` (`GrpIso.cartThy_iso_grpModel`).
* `ofLanguage_model_iff` and `ofLanguage_isHom_iff`, which compare realizations and
  homomorphisms with Mathlib's, are in the companion file `Companion/Proofs/ExtrasAlgTheoryFO.lean`.

## Main results

* `UlmerBialgebras.Paper.modelCat_iso_cartThy_univ`
* `UlmerBialgebras.Paper.modelCat_type_iso_cartThy`
* `UlmerBialgebras.Paper.grp_modelCat_iso`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.14, Corollary 6.11
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
        F ⋙ Theory.cartThyForget.{v, w, s} C T = Theory.ModelCat.forget C T :=
  CartIso.modelCat_iso_cartThy.{s, v, w} C T

/-- **The Set case** (addition beyond [forsman2026syntactic]): the category of models of `T` in
`Set = Type (max s u)` is isomorphic to `Set^{T'}`, over `Set^S`. -/
theorem modelCat_type_iso_cartThy {L : MSLanguage.{s, s}} (T : L.Theory) :
    ∃ (F : T.ModelCat (Type (max s u)) ⥤ Theory.cartThy.{u, max s u + 1, s} (Type (max s u)) T)
      (G : Theory.cartThy.{u, max s u + 1, s} (Type (max s u)) T ⥤ T.ModelCat (Type (max s u))),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Theory.cartThyForget.{u, max s u + 1, s} (Type (max s u)) T =
          Theory.ModelCat.forget (Type (max s u)) T :=
  CartIso.modelCat_iso_cartThy.{s, u, max s u + 1} (Type (max s u)) T

attribute [local instance] catOfSizeHom in
/-- `grp_modelCat_iso` for sorts in any universe `s`: for a cartesian monoidal category `C`
(objects in `Type (max s v w)`, morphisms in `Type (max s v)`), the models of the equational theory
of groups in each sort of `S : Type s` form a category isomorphic, over `C^S`, to the category of
models of the `Σ_Cart`-theory of groups `grpTheory S` in `C`. -/
theorem grp_modelCat_iso_univ (C : Type (max s v w)) [Category.{max s v} C]
    [CartesianMonoidalCategory C] (S : Type s) :
    ∃ (F : (grpEqTheory S).ModelCat C ⥤
        ((cartModel C).thyObj (grpSig S) (grpTheory S) : Cat.{max s v, max s v w}))
      (G : ((cartModel C).thyObj (grpSig S) (grpTheory S) : Cat.{max s v, max s v w}) ⥤
        (grpEqTheory S).ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ ((cartModel C).e (grpSig S) (grpTheory S) ≫ (cartModel C).u (grpSig S)).toFunctor =
          Theory.ModelCat.forget C (grpEqTheory S) := by
  obtain ⟨F₂, G₂, hFG₂, hGF₂, hforget₂⟩ := CartIso.modelCat_iso_cartThy.{s, v, w} C (grpEqTheory S)
  obtain ⟨F₃, G₃, hFG₃, hGF₃, hforget₃⟩ := GrpIso.cartThy_iso_grpModel.{v, w, s} C S
  refine ⟨F₂ ⋙ F₃, G₃ ⋙ G₂, ?_, ?_, ?_⟩
  · rw [Functor.assoc, ← Functor.assoc F₃, hFG₃, Functor.id_comp, hFG₂]
  · rw [Functor.assoc, ← Functor.assoc G₂, hGF₂, Functor.id_comp, hGF₃]
  · rw [Functor.assoc, hforget₃]
    exact hforget₂

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
          Theory.ModelCat.forget C (grpEqTheory S) := by
  exact grp_modelCat_iso_univ.{v, w, 0} C S

end UlmerBialgebras.Paper
