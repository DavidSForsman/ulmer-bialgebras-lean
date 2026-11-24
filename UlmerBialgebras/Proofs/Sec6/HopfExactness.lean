module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Monoidal.Closed.Transport
public import UlmerBialgebras.Paper.Sec6DefsHopf
public import UlmerBialgebras.Proofs.Sec6.GrpTheoryExactness
public import UlmerBialgebras.Proofs.Sec6.ComonDescent
public import UlmerBialgebras.Proofs.Sec6.Sec6Loc
public import UlmerBialgebras.Proofs.Sec6.AffGrpLoc
public import UlmerBialgebras.Proofs.Sec6.CommComonOp
public import UlmerBialgebras.Proofs.Sec6.CommMonModule

/-!
# The two instances of Corollary 6.11: `A = Mod_R` and `A = Mod_R^op`

For a commutative von Neumann regular ring `R`:

* **Limits and tensor products.** `Mod_R` and `Mod_R^op` have finite limits and finite colimits.
  Every `R`-module is flat, so `X ⊗ -` and `- ⊗ X` preserve finite limits as well as all
  colimits. Hence both `Mod_R` and `Mod_R^op` satisfy the hypotheses of the reduction
  `grpExt_barrExact_reduction`.
* **Affine group schemes.** `commComonOpEquivCommAlgOp R : Comon^coc_{Mod_R^op} ≌ (CommAlg_R)ᵒᵖ`
  is the composite of `CommComonOp.commMonOpEquiv`, the transport along `Mod_R ≌ ModuleCat R`,
  and `CommMonModuleEquivalenceCommAlgebra.equivalence`. Along it, Barr-exactness of affine group
  schemes over `R` (`AffGrp.isBarrExact_affGrp_vnr`) gives Barr-exactness of
  `Hopf^coc_{Mod_R^op}`.
* **Cocommutative Hopf algebras.** Descent along the localizations at the maximal ideals
  (`ComonDescent.isBarrExact_cocommHopf`) reduces Barr-exactness of `Hopf^coc_{Mod_R}` to the
  residue fields. There it is the hypothesis `hk` (the theorem of Gran, Sterck and Vercruysse
  [GRAN20194171]).

## Main results

* `UlmerBialgebras.Paper.Loc.commComonOpEquivCommAlgOp`: an equivalence
  `CommComon (ModU R)ᵒᵖ ≌ (CommAlgCat R)ᵒᵖ`.
* `UlmerBialgebras.Paper.Loc.isBarrExact_grp_commComon_op`: for a von Neumann regular ring `R`,
  `Grp (CommComon (ModU R)ᵒᵖ)` is Barr-exact (Corollary 6.11, `A = Mod_R^op`).
* `UlmerBialgebras.Paper.Loc.isBarrExact_grp_commComon_of_field`: for a von Neumann regular ring
  `R`, if `Grp (CommComon (ModU k))` is Barr-exact for every field `k`, then so is
  `Grp (CommComon (ModU R))` (Corollary 6.11, `A = Mod_R`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.10 and Corollary 6.11
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes]
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative
  Algebra*][atiyah_introduction_1969], Chapter 2, Exercise 27; Chapter 3, Exercise 10
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory Limits MonoidalCategory Opposite Loc

noncomputable section

/-! ## Limits and tensor products in `Mod_R` and `Mod_R^op` -/

section Mod

variable (R : Type u) [CommRing R]

/-- `Mod_R` (`ModU R`) has finite colimits, transported from `ModuleCat R` along `modEquiv R`. -/
instance modU_hasFiniteColimits : HasFiniteColimits (ModU R) :=
  ⟨fun _ _ _ => Adjunction.hasColimitsOfShape_of_equivalence (modEquiv R).inverse⟩

/-- In `Mod_R`, `- ⊗ X` preserves finite colimits (from `X ⊗ -` via the braiding). -/
instance modU_preservesFiniteColimits_tensorRight (X : ModU R) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- Over a von Neumann regular ring `R`, `- ⊗ X` on `Mod_R` preserves finite limits (every module is
flat), from the case of `X ⊗ -` via the braiding. -/
theorem modU_preservesFiniteLimits_tensorRight (hR : IsVonNeumannRegularRing R) (X : ModU R) :
    PreservesFiniteLimits (tensorRight X) :=
  haveI := tensorLeft_preservesFiniteLimits R hR X
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- In `Mod_R`, `X ⊗ -` preserves reflexive coequalizers. -/
instance modU_preservesReflexiveCoeq_tensorLeft (X : ModU R) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft X) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- In `Mod_R`, `- ⊗ X` preserves reflexive coequalizers. -/
instance modU_preservesReflexiveCoeq_tensorRight (X : ModU R) :
    CategoryTheory.PreservesReflexiveCoeq (tensorRight X) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- Over a von Neumann regular ring `R`, `X ⊗ -` on `Mod_R` preserves coreflexive equalizers, since
it preserves finite limits. -/
theorem modU_preservesCoreflexiveEq_tensorLeft (hR : IsVonNeumannRegularRing R) (X : ModU R) :
    PreservesCoreflexiveEq (tensorLeft X) :=
  haveI := tensorLeft_preservesFiniteLimits R hR X
  preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- Over a von Neumann regular ring `R`, `- ⊗ X` on `Mod_R` preserves coreflexive equalizers, since
it preserves finite limits. -/
theorem modU_preservesCoreflexiveEq_tensorRight (hR : IsVonNeumannRegularRing R) (X : ModU R) :
    PreservesCoreflexiveEq (tensorRight X) :=
  haveI := modU_preservesFiniteLimits_tensorRight R hR X
  preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- In `Cᵒᵖ`, tensoring with `Z` is the opposite of tensoring with `unop Z`. -/
lemma tensorLeft_op_eq {C : Type*} [Category* C] [MonoidalCategory C] (Z : Cᵒᵖ) :
    tensorLeft Z = (tensorLeft (unop Z)).op := rfl

/-- In `Cᵒᵖ`, `- ⊗ Z` is the opposite of `- ⊗ unop Z` (definitionally). -/
lemma tensorRight_op_eq {C : Type*} [Category* C] [MonoidalCategory C] (Z : Cᵒᵖ) :
    tensorRight Z = (tensorRight (unop Z)).op := rfl

/-- In `Mod_R^op`, `Z ⊗ -` preserves coreflexive equalizers, being the opposite of `unop Z ⊗ -`,
which preserves finite colimits. -/
instance modUOp_preservesCoreflexiveEq_tensorLeft (Z : (ModU R)ᵒᵖ) :
    PreservesCoreflexiveEq (tensorLeft Z) := by
  have := preservesFiniteLimits_op (tensorLeft (unop Z))
  rw [tensorLeft_op_eq]
  exact preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- In `Mod_R^op`, `- ⊗ Z` preserves coreflexive equalizers, being the opposite of `- ⊗ unop Z`,
which preserves finite colimits. -/
instance modUOp_preservesCoreflexiveEq_tensorRight (Z : (ModU R)ᵒᵖ) :
    PreservesCoreflexiveEq (tensorRight Z) := by
  have := preservesFiniteLimits_op (tensorRight (unop Z))
  rw [tensorRight_op_eq]
  exact preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- Over a von Neumann regular ring `R`, `Z ⊗ -` on `Mod_R^op` preserves reflexive coequalizers,
being the opposite of `unop Z ⊗ -`, which preserves finite limits (every module is flat). -/
theorem modUOp_preservesReflexiveCoeq_tensorLeft (hR : IsVonNeumannRegularRing R)
    (Z : (ModU R)ᵒᵖ) : CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z) := by
  have := tensorLeft_preservesFiniteLimits R hR (unop Z)
  have := preservesFiniteColimits_op (tensorLeft (unop Z))
  rw [tensorLeft_op_eq]
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

/-- Over a von Neumann regular ring `R`, `- ⊗ Z` on `Mod_R^op` preserves reflexive coequalizers,
being the opposite of `- ⊗ unop Z`, which preserves finite limits (every module is flat). -/
theorem modUOp_preservesReflexiveCoeq_tensorRight (hR : IsVonNeumannRegularRing R)
    (Z : (ModU R)ᵒᵖ) : CategoryTheory.PreservesReflexiveCoeq (tensorRight Z) := by
  have := modU_preservesFiniteLimits_tensorRight R hR (unop Z)
  have := preservesFiniteColimits_op (tensorRight (unop Z))
  rw [tensorRight_op_eq]
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

end Mod

/-! ## Affine group schemes: `Comon^coc_{Mod_R^op} ≌ (CommAlg_R)ᵒᵖ` -/

section Aff

variable (R : Type u) [CommRing R]

/-- The functor `Mod_R ⥤ ModuleCat R` of `(modEquiv R).symm` is braided. -/
instance : (modEquiv R).symm.functor.Braided :=
  inferInstanceAs (modEquiv R).inverse.Braided

/-- The functor `ModuleCat R ⥤ Mod_R` of `(modEquiv R).symm` is braided. -/
instance : (modEquiv R).symm.inverse.Braided :=
  inferInstanceAs (modEquiv R).functor.Braided

/-- **Cocommutative comonoids in `Mod_R^op` are affine `R`-schemes.** -/
def commComonOpEquivCommAlgOp : CategoryTheory.CommComon (ModU R)ᵒᵖ ≌ (CommAlgCat.{u} R)ᵒᵖ :=
  (CommComonOp.commMonOpEquiv (ModU R)).trans
    (((modEquiv R).symm.mapCommMon).trans (CommMonModuleEquivalenceCommAlgebra.equivalence R)).op

/-- **`Hopf^coc_{Mod_R^op}` is Barr-exact** for a von Neumann regular ring `R`: it is the category
of affine group schemes over `R`. -/
theorem isBarrExact_grp_commComon_op (hR : IsVonNeumannRegularRing R) :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU R)ᵒᵖ)) := by
  have := fun Z => modUOp_preservesReflexiveCoeq_tensorLeft R hR Z
  have := Cor611.cocomm_hasFiniteLimits (ModU R)ᵒᵖ
  have := UlmerBialgebras.CommComon.hasReflexiveCoequalizers (V := (ModU R)ᵒᵖ)
  have := fun A => (ComonDescent.cocomm_standing (ModU R)ᵒᵖ A).1
  have := fun A => (ComonDescent.cocomm_standing (ModU R)ᵒᵖ A).2
  have := AffGrp.allFlat_of_vnr R hR
  have := fun W => AffGrp.preservesReflexiveCoeq_tensorLeft R W
  have := fun W => AffGrp.preservesReflexiveCoeq_tensorRight R W
  have : CategoryTheory.IsBarrExact (Grp (CommAlgCat.{u} R)ᵒᵖ) :=
    AffGrp.isBarrExact_affGrp_vnr R hR
  refine GrpDescent.isBarrExact_grp (D := fun _ : PUnit.{1} => (CommAlgCat.{u} R)ᵒᵖ)
    (fun _ => (commComonOpEquivCommAlgOp R).functor) (fun _ => ⟨fun _ _ _ _ _ => inferInstance⟩) ?_
  refine ⟨?_⟩
  intro X Y f hf
  have := hf PUnit.unit
  exact isIso_of_reflects_iso f (commComonOpEquivCommAlgOp R).functor

end Aff

/-! ## Cocommutative Hopf algebras: descent along localizations -/

section Hopf

variable (R : Type u) [CommRing R]

/-- **`Hopf^coc_{Mod_R}` is Barr-exact** for a von Neumann regular ring `R`, provided that
`Hopf^coc_k` is Barr-exact for every field `k`. -/
theorem isBarrExact_grp_commComon_of_field (hR : IsVonNeumannRegularRing R)
    (hk : ∀ (k : Type u) [CommRing k], IsField k →
      CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU k)))) :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU R))) := by
  have hfield : ∀ p : AffGrp.MaxIdeal R, IsField (Localization.AtPrime p.1) :=
    fun p => IsVonNeumannRegular.isField_localizationAtPrime hR p.1
  have hvnr : ∀ p : AffGrp.MaxIdeal R, IsVonNeumannRegularRing (Localization.AtPrime p.1) :=
    fun p => IsVonNeumannRegularRing.of_isField (hfield p)
  have := fun Z => modU_preservesCoreflexiveEq_tensorLeft R hR Z
  have := fun Z => modU_preservesCoreflexiveEq_tensorRight R hR Z
  have := fun (p : AffGrp.MaxIdeal R) Z =>
    modU_preservesCoreflexiveEq_tensorLeft (Localization.AtPrime p.1) (hvnr p) Z
  have := fun (p : AffGrp.MaxIdeal R) Z =>
    modU_preservesCoreflexiveEq_tensorRight (Localization.AtPrime p.1) (hvnr p) Z
  have : ∀ p : AffGrp.MaxIdeal R, CategoryTheory.IsBarrExact
      (Grp (CategoryTheory.CommComon (ModU (Localization.AtPrime p.1)))) :=
    fun p => hk _ (hfield p)
  have : ∀ p : AffGrp.MaxIdeal R, PreservesCoreflexiveEq (locFunctor R p.1) := fun p =>
    haveI := locFunctor_preservesFiniteLimits R p.1
    preservesCoreflexiveEq_of_preservesLimitsOfShape _
  refine ComonDescent.isBarrExact_cocommHopf (ModU R)
    (fun p : AffGrp.MaxIdeal R => ModU (Localization.AtPrime p.1)) (fun p => locFunctor R p.1)
    (fun _ => ⟨fun _ _ _ _ _ => inferInstance⟩) ?_
  refine ⟨?_⟩
  intro X Y f hf
  exact locFunctor_jointlyConservative R f (fun P _ => hf ⟨P, ‹_›⟩)

end Hopf

/-! ## `ModuleCat R` itself -/

section ModCat

variable (R : Type u) [CommRing R]

/-- Over a von Neumann regular ring `R`, `X ⊗ -` on `ModuleCat R` preserves finite limits (every
module is flat). -/
theorem moduleCat_preservesFiniteLimits_tensorLeft (hR : IsVonNeumannRegularRing R)
    (X : ModuleCat.{u} R) : PreservesFiniteLimits (tensorLeft X) :=
  haveI : Module.Flat R X := IsVonNeumannRegular.flat hR _
  inferInstance

/-- Over a von Neumann regular ring `R`, `- ⊗ X` on `ModuleCat R` preserves finite limits. -/
theorem moduleCat_preservesFiniteLimits_tensorRight (hR : IsVonNeumannRegularRing R)
    (X : ModuleCat.{u} R) : PreservesFiniteLimits (tensorRight X) :=
  haveI := moduleCat_preservesFiniteLimits_tensorLeft R hR X
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- In `ModuleCat R`, `- ⊗ X` preserves finite colimits (from `X ⊗ -` via the braiding). -/
instance moduleCat_preservesFiniteColimits_tensorRight (X : ModuleCat.{u} R) :
    PreservesFiniteColimits (tensorRight X) :=
  preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- In `ModuleCat R`, `X ⊗ -` preserves reflexive coequalizers. -/
instance moduleCat_preservesReflexiveCoeq_tensorLeft (X : ModuleCat.{u} R) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft X) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- In `ModuleCat R`, `- ⊗ X` preserves reflexive coequalizers. -/
instance moduleCat_preservesReflexiveCoeq_tensorRight (X : ModuleCat.{u} R) :
    CategoryTheory.PreservesReflexiveCoeq (tensorRight X) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- Over a von Neumann regular ring `R`, `X ⊗ -` on `ModuleCat R` preserves coreflexive
equalizers. -/
theorem moduleCat_preservesCoreflexiveEq_tensorLeft (hR : IsVonNeumannRegularRing R)
    (X : ModuleCat.{u} R) : PreservesCoreflexiveEq (tensorLeft X) :=
  haveI := moduleCat_preservesFiniteLimits_tensorLeft R hR X
  preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- Over a von Neumann regular ring `R`, `- ⊗ X` on `ModuleCat R` preserves coreflexive
equalizers. -/
theorem moduleCat_preservesCoreflexiveEq_tensorRight (hR : IsVonNeumannRegularRing R)
    (X : ModuleCat.{u} R) : PreservesCoreflexiveEq (tensorRight X) :=
  haveI := moduleCat_preservesFiniteLimits_tensorRight R hR X
  preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- In `(ModuleCat R)ᵒᵖ`, `Z ⊗ -` preserves coreflexive equalizers. -/
instance moduleCatOp_preservesCoreflexiveEq_tensorLeft (Z : (ModuleCat.{u} R)ᵒᵖ) :
    PreservesCoreflexiveEq (tensorLeft Z) := by
  have := preservesFiniteLimits_op (tensorLeft (unop Z))
  rw [tensorLeft_op_eq]
  exact preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- In `(ModuleCat R)ᵒᵖ`, `- ⊗ Z` preserves coreflexive equalizers. -/
instance moduleCatOp_preservesCoreflexiveEq_tensorRight (Z : (ModuleCat.{u} R)ᵒᵖ) :
    PreservesCoreflexiveEq (tensorRight Z) := by
  have := preservesFiniteLimits_op (tensorRight (unop Z))
  rw [tensorRight_op_eq]
  exact preservesCoreflexiveEq_of_preservesLimitsOfShape _

/-- Over a von Neumann regular ring `R`, `Z ⊗ -` on `(ModuleCat R)ᵒᵖ` preserves reflexive
coequalizers. -/
theorem moduleCatOp_preservesReflexiveCoeq_tensorLeft (hR : IsVonNeumannRegularRing R)
    (Z : (ModuleCat.{u} R)ᵒᵖ) : CategoryTheory.PreservesReflexiveCoeq (tensorLeft Z) := by
  have := moduleCat_preservesFiniteLimits_tensorLeft R hR (unop Z)
  have := preservesFiniteColimits_op (tensorLeft (unop Z))
  rw [tensorLeft_op_eq]
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

/-- Over a von Neumann regular ring `R`, `- ⊗ Z` on `(ModuleCat R)ᵒᵖ` preserves reflexive
coequalizers. -/
theorem moduleCatOp_preservesReflexiveCoeq_tensorRight (hR : IsVonNeumannRegularRing R)
    (Z : (ModuleCat.{u} R)ᵒᵖ) : CategoryTheory.PreservesReflexiveCoeq (tensorRight Z) := by
  have := moduleCat_preservesFiniteLimits_tensorRight R hR (unop Z)
  have := preservesFiniteColimits_op (tensorRight (unop Z))
  rw [tensorRight_op_eq]
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

/-- **`Hopf^coc_{ModuleCat R}` is Barr-exact** for a von Neumann regular ring `R`, provided that
`Hopf^coc_k` is Barr-exact for every field `k` (for `ModU k`). It is transported from `Mod_R`
(`ModU R`) along the braided equivalence `ModuleCat R ≌ Mod_R`. -/
theorem isBarrExact_grp_commComon_moduleCat (hR : IsVonNeumannRegularRing R)
    (hk : ∀ (k : Type u) [CommRing k], IsField k →
      CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU k)))) :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModuleCat.{u} R))) := by
  have : CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU R))) :=
    isBarrExact_grp_commComon_of_field R hR hk
  exact GrpDescent.isBarrExact_grp_of_equivalence (ComonDescent.commComonEquiv (modEquiv R))

/-- Cocommutative comonoids in `(ModuleCat R)ᵒᵖ` are affine `R`-schemes. -/
def commComonOpEquivCommAlgOp' :
    CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ ≌ (CommAlgCat.{u} R)ᵒᵖ :=
  (CommComonOp.commMonOpEquiv (ModuleCat.{u} R)).trans
    (CommMonModuleEquivalenceCommAlgebra.equivalence R).op

/-- **`Hopf^coc_{(ModuleCat R)ᵒᵖ}` is Barr-exact** for a von Neumann regular ring `R`: it is the
category of affine group schemes over `R`. -/
theorem isBarrExact_grp_commComon_moduleCat_op (hR : IsVonNeumannRegularRing R) :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ)) := by
  have : CategoryTheory.IsBarrExact (Grp (CommAlgCat.{u} R)ᵒᵖ) :=
    AffGrp.isBarrExact_affGrp_vnr R hR
  exact GrpDescent.isBarrExact_grp_of_equivalence (commComonOpEquivCommAlgOp' R)

end ModCat

end

end UlmerBialgebras.Paper.Loc
