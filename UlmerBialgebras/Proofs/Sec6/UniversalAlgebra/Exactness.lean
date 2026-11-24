module

public import UlmerBialgebras.Proofs.Sec5.UniversalAlgebra.Monadicity
public import UlmerBialgebras.Proofs.Sec6.UniversalAlgebra.Paths
public import UlmerBialgebras.Proofs.Sec6.Sec6Hopf
public import UlmerBialgebras.Proofs.Sec6.Support.CartSmall
public import UlmerBialgebras.Proofs.Sec5.ExtrasAlgTheory
public import UlmerBialgebras.Proofs.Sec5.AlgTheoryTransport

/-!
# Exactness of categories of models of a theory of universal algebra extending groups

Corollary 6.11 of [forsman2026syntactic]: for a commutative von Neumann regular ring `R` and a
multi-sorted theory `T` of universal algebra extending the theory of groups in each sort,
`(Comon_A^coc)^T` is exact for `A = Mod_R^op` and `A = Mod_R`.
`UlmerBialgebras.Paper.grpExt_barrExact` states it for the `Σ_Cart`-theories `grpExtTheory`. This
file states it for an equational theory `T` over `grpExtLanguage S Fn' …` that contains the
translated group axioms (`UlmerBialgebras/Paper/Sec6DefsTheoryMorphism.lean`), with `T.ModelCat` the
category of
models of `T`.

The proof follows `Cart.isExactCat_grpExtTheory`. The translated theory `T.toCartTheory`
restricts, along the group symbols, to the translation of the equational theory of groups
(`ofRestrictFn_toPath`). The models of that translation are the models of the theory of groups
(`modelCat_iso_cartThy_univ`, `grp_modelCat_iso`), an exact category when `Grp B` is
Barr-exact (`Cart.isExactCat_grpModel`). Corollary 6.9 (`isExactCat_thyObj_of_restrict`) passes
exactness to `T.toCartTheory`, and the isomorphism `T.ModelCat B ≅ B^{T'}` to `T.ModelCat B`.
The sorts and function symbols may lie in any universe `u₁`. For a category `B` in any universes,
the proof goes through the copy `CartSmall B`, with objects and hom-sets lifted to a universe that
contains `u₁` and the universes of `B`, and transports the models back along `AsSmall.up`
(`modelCat_transport`).

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.isExactCat_modelCat`: if `Grp B` is Barr-exact, the
  models of `T` in `B` form an exact category.
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_barrExact`: Corollary 6.11 for `T.ModelCat`.
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_barrExact_moduleCat`: the same for
  `ModuleCat.{u} R` itself.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollaries 6.9
  and 6.11
-/

@[expose] public section

universe u v u₁

namespace UlmerBialgebras.Paper.UniversalAlgebra

open CategoryTheory Limits MonoidalCategory Cart MSLanguage

/-- An isomorphism of categories, given by two functors that are mutually inverse, as an
equivalence. -/
noncomputable def equivOfInverse {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    (h₁ : F ⋙ G = 𝟭 C) (h₂ : G ⋙ F = 𝟭 D) : C ≌ D :=
  CategoryTheory.Equivalence.mk F G (eqToIso h₁.symm) (eqToIso h₂)

variable {S Fn' : Type u₁} {arity' : Fn' → ℕ} {argSorts' : ∀ f, Fin (arity' f) → S}
  {resSort' : Fn' → S}

section Core

variable {B : Type (max u₁ u)} [Category.{max u₁ u} B] [CartesianMonoidalCategory B]
  [HasFiniteLimits B]
  [HasReflexiveCoequalizers B] [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]

include B in
/-- The models of the translation of the equational theory of groups form an exact category, when
`Grp B` is Barr-exact. -/
theorem isExactCat_cartThy_grpEqTheory (h : CategoryTheory.IsBarrExact (Grp B)) :
    IsExactCat (Theory.cartThy.{u, u, u₁} B (grpEqTheory S)) := by
  obtain ⟨F, G, h₁, h₂, -⟩ := grp_modelCat_iso_univ.{u, u, u₁} B S
  have := isExactCat_grpModel S h
  exact (this.of_equivalence (equivOfInverse F G h₁ h₂).symm).of_equivalence
    (modelCatEquivCartThy.{u, u, u₁} B (grpEqTheory S))

variable (Fn' arity' argSorts' resSort') in
/-- The translated group axioms in `T`, as equations of `T.toCartTheory`. -/
def grpAxiomEqn (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T)
    (φ : grpEqTheory S) : T.toCartTheory.Eqn :=
  ⟨(grpInl S Fn' arity' argSorts' resSort').translateEquation φ.1, hT φ.1 φ.2⟩

attribute [local instance] catOfSizeHom in
include B in
/-- If `Grp B` is Barr-exact, the models in `B` of the translation `T.toCartTheory` of a theory `T`
over `grpExtLanguage S Fn' …` that contains the translated group axioms form an exact category. -/
theorem isExactCat_cartThy_of_grp (h : CategoryTheory.IsBarrExact (Grp B))
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    IsExactCat (Theory.cartThy.{u, u, u₁} B T) := by
  refine isExactCat_thyObj_of_restrict (cartModel B)
    (grpExtLanguage S Fn' arity' argSorts' resSort').toCartSig (Fn₁ := S × GrpFn) Sum.inl
    T.toCartTheory
    (grpAxiomEqn Fn' arity' argSorts' resSort' T hT)
    (fun φ => φ.1.lhs.toPath) (fun φ => φ.1.rhs.toPath)
    (fun φ => ofRestrictFn_toPath φ.1.lhs) (fun φ => ofRestrictFn_toPath φ.1.rhs)
    (toCartTheory_isAlgebraic T)
    (fun _ => (inferInstance : HasFiniteLimits B))
    (fun _ => (inferInstance : HasReflexiveCoequalizers B))
    cartModel_preservesReflexiveCoeqComponentwise.{max u₁ u} ?_
  change IsExactCat (Theory.cartThy.{u, u, u₁} B (grpEqTheory S))
  exact isExactCat_cartThy_grpEqTheory h

end Core

section Univ

universe vB uB

/-- **The core of Corollary 6.11 for a theory of universal algebra.** Let `B` be a cartesian
category, in any universes, with finite limits and reflexive coequalizers preserved by the tensor
product in each variable. If `Grp B` is Barr-exact, the models in `B` of a theory `T` over
`grpExtLanguage S Fn' …` (sorts and symbols in any universe) that contains the translated group
axioms form an exact category. The proof applies `isExactCat_cartThy_of_grp` to `CartSmall B`,
the copy of `B` with objects and hom-sets lifted to `Type (max u₁ uB vB)`, and transports the
models back along `AsSmall.up` (`modelCat_transport`). -/
theorem isExactCat_modelCat {B : Type uB} [Category.{vB} B]
    [CartesianMonoidalCategory B] [HasFiniteLimits B] [HasReflexiveCoequalizers B]
    [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z)]
    [∀ Z : B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z)]
    (h : CategoryTheory.IsBarrExact (Grp B))
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    IsExactCat (T.ModelCat B) := by
  let e := cartSmallEquiv.{max u₁ uB vB} B
  have : HasFiniteLimits (CartSmall.{max u₁ uB vB} B) := hasFiniteLimits_of_equivalence e.symm
  have : HasReflexiveCoequalizers (CartSmall.{max u₁ uB vB} B) := by
    have := (hasReflexiveCoequalizers_iff (C := B)).2 inferInstance
    exact hasReflexiveCoequalizers_iff.1
      (Adjunction.hasColimitsOfShape_of_equivalence e.inverse)
  have : CategoryTheory.PreservesReflexiveCoeq e.inverse := ⟨fun _ _ _ _ _ => inferInstance⟩
  have : CategoryTheory.PreservesReflexiveCoeq e.functor := ⟨fun _ _ _ _ _ => inferInstance⟩
  have : ∀ Z : CartSmall.{max u₁ uB vB} B, CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z) :=
    fun Z => inferInstanceAs (CategoryTheory.PreservesReflexiveCoeq
      (e.inverse ⋙ tensorLeft (e.inverse.obj Z) ⋙ e.functor))
  have : ∀ Z : CartSmall.{max u₁ uB vB} B, CategoryTheory.PreservesReflexiveCoeq (tensorRight Z) :=
    fun Z => inferInstanceAs (CategoryTheory.PreservesReflexiveCoeq
      (e.inverse ⋙ tensorRight (e.inverse.obj Z) ⋙ e.functor))
  have h' : CategoryTheory.IsBarrExact (Grp (CartSmall.{max u₁ uB vB} B)) :=
    isBarrExact_of_equivalence e.mapGrp.symm
  have hU := isExactCat_cartThy_of_grp.{max uB vB, u₁} (B := CartSmall.{max u₁ uB vB} B) h' T hT
  have hM : IsExactCat (T.ModelCat (CartSmall.{max u₁ uB vB} B)) :=
    hU.of_equivalence (modelCatEquivCartThy.{max uB vB, max uB vB, u₁} _ T).symm
  obtain ⟨F, G, h₁, h₂, -⟩ :=
    modelCat_transport (D := CartSmall.{max u₁ uB vB} B) e.functor e.inverse rfl rfl T
  exact hM.of_equivalence (equivOfInverse F G h₁ h₂).symm

end Univ

section Cor611

open Loc

/-- **The reduction step of Corollary 6.11, for a theory of universal algebra.** Let `A` be a
symmetric monoidal category with coreflexive equalizers and reflexive coequalizers, both preserved
by the tensor product in each variable. If `Hopf_A^coc = Grp(Comon_A^coc)` is Barr-exact, then the
models in `Comon_A^coc` of a theory `T` over `grpExtLanguage S Fn' …` that contains the translated
group axioms form a Barr-exact category. -/
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
    BarrExact (T.ModelCat (CategoryTheory.CommComon A)) := by
  have := Cor611.cocomm_hasFiniteLimits A
  have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := A)
  have := fun X => (ComonDescent.cocomm_standing A X).1
  have := fun X => (ComonDescent.cocomm_standing A X).2
  exact isExactCat_iff_barrExact.1 (isExactCat_modelCat
    (CategoryTheory.isBarrExact_iff_barrExact.2 inferInstance) T hT)

/-- **Corollary 6.11 for a theory of universal algebra** ([forsman2026syntactic]). Let `R` be a
commutative von Neumann regular ring and `T` a multi-sorted theory of universal algebra extending
the theory of groups in each sort: an equational theory over `grpExtLanguage S Fn' …` (the
language of groups in each sort of `S` and further function symbols) containing the group axioms.
Then the category of models of `T` in `Comon_A^coc` is Barr-exact, for `A = Mod_R^op` and for
`A = Mod_R`. -/
theorem modelCat_barrExact {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R))) := by
  refine ⟨?_, ?_⟩
  · have := fun Z => Loc.modUOp_preservesReflexiveCoeq_tensorLeft R hR Z
    have := fun Z => Loc.modUOp_preservesReflexiveCoeq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_op R hR).barrExact
    exact modelCat_barrExact_reduction (ModU R)ᵒᵖ T hT
  · have := fun Z => Loc.modU_preservesCoreflexiveEq_tensorLeft R hR Z
    have := fun Z => Loc.modU_preservesCoreflexiveEq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_of_field R hR
      fun k _ hk => Loc.isBarrExact_grp_commComon_modU_of_isField k hk).barrExact
    exact modelCat_barrExact_reduction (ModU R) T hT

/-- **Corollary 6.11 for a theory of universal algebra, for `ModuleCat R`**
([forsman2026syntactic]). `modelCat_barrExact` for the category of `R`-modules itself,
`ModuleCat.{u} R`, with objects in `Type (u + 1)` and morphisms in `Type u`, instead of the copy
`ModU R`: the category of models of `T` in `Comon_A^coc` is Barr-exact, for `A = Mod_R^op` and
for `A = Mod_R`. -/
theorem modelCat_barrExact_moduleCat {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R))) := by
  refine ⟨?_, ?_⟩
  · have := fun Z => Loc.moduleCatOp_preservesReflexiveCoeq_tensorLeft R hR Z
    have := fun Z => Loc.moduleCatOp_preservesReflexiveCoeq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_moduleCat_op R hR).barrExact
    exact modelCat_barrExact_reduction (ModuleCat.{u} R)ᵒᵖ T hT
  · have := fun Z => Loc.moduleCat_preservesCoreflexiveEq_tensorLeft R hR Z
    have := fun Z => Loc.moduleCat_preservesCoreflexiveEq_tensorRight R hR Z
    have := (Loc.isBarrExact_grp_commComon_moduleCat R hR
      fun k _ hk => Loc.isBarrExact_grp_commComon_modU_of_isField k hk).barrExact
    exact modelCat_barrExact_reduction (ModuleCat.{u} R) T hT

end Cor611

end UlmerBialgebras.Paper.UniversalAlgebra
