module

public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import UlmerBialgebras.Proofs.Sec6.GrpDescent
public import UlmerBialgebras.Proofs.Sec6.AffTensorEqualizer
public import UlmerBialgebras.Proofs.Sec6.LocModel
public import AffineGroupSchemes.CoexactTheorem
public import AffineGroupSchemes.HopfGrpEquiv
public import Foundations.CategoryTheory.Exact.SemiAbelianEquiv
public import AffineGroupSchemes.VonNeumannRegular

/-!
# Affine group schemes over a von Neumann regular ring, by localization

The method of the proof of Corollary 6.11, case `A = Mod_R^op`. Write
`AffGrp_R = Grp (CommAlgCat R)ᵒᵖ`. For each maximal ideal `p`, base change
`A ↦ R_p ⊗_R A` induces `(CommAlgCat R)ᵒᵖ ⥤ (CommAlgCat R_p)ᵒᵖ`. It preserves finite limits,
because base change is a left adjoint, and reflexive coequalizers, because `R_p` is flat. These
functors are jointly conservative by the local–global principle. Over a von Neumann regular ring
every module is flat, so the product of affine schemes preserves reflexive coequalizers, and
each `R_p` is a field, where `AffGrp_{R_p}` is exact
([forsman2026semiabeliannessaffinegroupschemes], Theorem 3.15, via Takeuchi's correspondence
[Takeuchi1972]; `isBarrExact_commHopfAlgCat_op`).
The general descent theorem `GrpDescent.isBarrExact_grp` concludes.

## Main results

* `UlmerBialgebras.Paper.AffGrp.loc_jointlyConservative`: the localizations at the maximal ideals
  are jointly conservative on affine schemes over `R`.
* `UlmerBialgebras.Paper.AffGrp.isBarrExact_affGrp_of_isField`: over a field, `Grp (CommAlgCat R)ᵒᵖ`
  is Barr exact.
* `UlmerBialgebras.Paper.AffGrp.isBarrExact_affGrp_vnr`: over a von Neumann regular ring `R`,
  `Grp (CommAlgCat R)ᵒᵖ` is Barr exact (by the method of Corollary 6.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.10 and Corollary 6.11
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.15
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative
  Algebra*][atiyah_introduction_1969], Chapter 3
-/

@[expose] public section

universe u

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits

namespace UlmerBialgebras.Paper.AffGrp

open CategoryTheory Limits MonoidalCategory Opposite CommRingCat TensorProduct

variable (R : Type u) [CommRing R]

/-! ## Base change of commutative algebras -/

/-- Base change `A ↦ S ⊗_R A` of commutative algebras. -/
noncomputable def bc (S : Type u) [CommRing S] [Algebra R S] :
    CommAlgCat.{u} R ⥤ CommAlgCat.{u} S :=
  (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ CommRingCat.tensorProd (CommRingCat.of R)
      (CommRingCat.of S) ⋙
    (commAlgCatEquivUnder (CommRingCat.of S)).inverse

/-- Base change `A ↦ S ⊗_R A` is a left adjoint (it is pushout along `R → S` in rings under `R`). -/
instance bc_isLeftAdjoint (S : Type u) [CommRing S] [Algebra R S] : (bc R S).IsLeftAdjoint := by
  have : (Under.pushout (CommRingCat.ofHom (algebraMap R S))).IsLeftAdjoint :=
    ⟨_, ⟨Under.mapPushoutAdj _⟩⟩
  have : (CommRingCat.tensorProd (CommRingCat.of R) (CommRingCat.of S)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso
        (CommRingCat.tensorProdIsoPushout (CommRingCat.of R) (CommRingCat.of S)).symm
  unfold bc
  infer_instance

/-- For flat `S`, base change `A ↦ S ⊗_R A` of commutative `R`-algebras preserves finite limits. -/
theorem bc_preservesFiniteLimits (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S] :
    PreservesFiniteLimits (bc R S) := by
  unfold bc
  infer_instance

/-- If base change of `g` is an isomorphism, its base change of linear maps is bijective. -/
lemma baseChange_bijective_of_isIso {R₀ S₀ : CommRingCat.{u}} [Algebra R₀ S₀] {A B : Under R₀}
    (g : A ⟶ B) [IsIso ((CommRingCat.tensorProd R₀ S₀).map g)] :
    Function.Bijective ((CommRingCat.toAlgHom g).toLinearMap.baseChange S₀) := by
  have h3 : Function.Bijective (((CommRingCat.tensorProd R₀ S₀).map g).right.hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (inferInstance : IsIso ((Under.forget _).map ((CommRingCat.tensorProd R₀ S₀).map g)))
  have : ⇑((CommRingCat.toAlgHom g).toLinearMap.baseChange S₀) =
      ⇑(((CommRingCat.tensorProd R₀ S₀).map g).right.hom) := by
    funext x
    induction x using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add, ha, hb]; exact (map_add _ a b).symm
    | tmul s a => rfl
  rw [this]
  exact h3

/-- Local–global bijectivity for morphisms of rings under `R₀`. -/
lemma bijective_of_local {R₀ : CommRingCat.{u}} {A B : Under R₀} (g : A ⟶ B)
    (h : ∀ (P : Ideal R₀) [P.IsMaximal], IsIso ((CommRingCat.tensorProd R₀
      (CommRingCat.of (Localization.AtPrime P))).map g)) :
    Function.Bijective (CommRingCat.toAlgHom g) :=
  Loc.bijective_of_baseChange R₀ (CommRingCat.toAlgHom g).toLinearMap
    (fun P _ => by
      have := h P
      have := baseChange_bijective_of_isIso (S₀ := CommRingCat.of (Localization.AtPrime P)) g
      exact this)

/-! ## The localization functors on affine schemes -/

/-- Localization at `p` on affine `R`-schemes. -/
noncomputable abbrev loc (p : Ideal R) [p.IsPrime] :
    (CommAlgCat.{u} R)ᵒᵖ ⥤ (CommAlgCat.{u} (Localization.AtPrime p))ᵒᵖ :=
  (bc R (Localization.AtPrime p)).op

/-- Localization `Spec A ↦ Spec (R_p ⊗_R A)` preserves finite limits of affine schemes, being the
opposite of the left adjoint `bc` (which preserves finite colimits). -/
instance loc_preservesFiniteLimits (p : Ideal R) [p.IsPrime] : PreservesFiniteLimits (loc R p) :=
  preservesFiniteLimits_op _

/-- Localization at a prime `p` preserves reflexive coequalizers of affine schemes, since `R_p` is
flat over `R` and so base change preserves finite limits of algebras. -/
theorem loc_preservesReflexiveCoeq (p : Ideal R) [p.IsPrime] :
    CategoryTheory.PreservesReflexiveCoeq (loc R p) := by
  have := bc_preservesFiniteLimits R (Localization.AtPrime p)
  have : PreservesFiniteColimits (loc R p) := preservesFiniteColimits_op _
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

/-- The maximal ideals of `R`. -/
abbrev MaxIdeal := {p : Ideal R // p.IsMaximal}

/-- A maximal ideal in `MaxIdeal R` is maximal (and hence prime), as an instance. -/
instance (p : MaxIdeal R) : p.1.IsMaximal := p.2

/-- The localizations at the maximal ideals are jointly conservative on affine schemes. -/
theorem loc_jointlyConservative :
    CategoryTheory.JointlyConservative
      (D := fun p : MaxIdeal R => (CommAlgCat.{u} (Localization.AtPrime p.1))ᵒᵖ)
      (fun p => loc R p.1) := by
  refine ⟨?_⟩
  intro X Y f hf
  let e := commAlgCatEquivUnder (CommRingCat.of R)
  let g : e.functor.obj Y.unop ⟶ e.functor.obj X.unop := e.functor.map f.unop
  have hb : Function.Bijective (CommRingCat.toAlgHom g) := by
    refine bijective_of_local g (fun P hP => ?_)
    have h1 := hf ⟨P, hP⟩
    change IsIso ((loc R P).map f) at h1
    have : IsIso ((bc R (Localization.AtPrime P)).map f.unop) :=
      (inferInstance : IsIso ((loc R P).map f).unop)
    exact @Functor.map_isIso _ _ _ _ _ _ (commAlgCatEquivUnder _).functor
      ((bc R (Localization.AtPrime P)).map f.unop) this
  have : IsIso f.unop := (ConcreteCategory.isIso_iff_bijective f.unop).mpr hb
  exact (inferInstance : IsIso f.unop.op)

/-! ## The standing hypothesis over an absolutely flat base -/

section H

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

variable (k : Type u) [CommRing k] [AffineGroupSchemes.AllFlat k]

/-- If every `k`-module is flat (`AllFlat k`), `W × -` on affine `k`-schemes (`A ↦ W ⊗_k A` on
algebras) preserves reflexive coequalizers. -/
theorem preservesReflexiveCoeq_tensorLeft (W : (CommAlgCat.{u} k)ᵒᵖ) :
    CategoryTheory.PreservesReflexiveCoeq (tensorLeft W) :=
  ⟨fun _ _ _ _ _ => inferInstance⟩

/-- If every `k`-module is flat (`AllFlat k`), `- × W` on affine `k`-schemes preserves reflexive
coequalizers (from the left case via the braiding). -/
theorem preservesReflexiveCoeq_tensorRight (W : (CommAlgCat.{u} k)ᵒᵖ) :
    CategoryTheory.PreservesReflexiveCoeq (tensorRight W) := by
  have : PreservesColimitsOfShape WalkingParallelPair (tensorRight W) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight W)
  exact ⟨fun _ _ _ _ _ => inferInstance⟩

end H

/-! ## Affine group schemes over a von Neumann regular ring -/

/-- Every module over a von Neumann regular ring is flat. -/
theorem allFlat_of_vnr (hR : IsVonNeumannRegularRing R) : AffineGroupSchemes.AllFlat R :=
  AffineGroupSchemes.AllFlat.of_vnr R hR

/-- Over a field, affine group schemes form a Barr-exact category
([forsman2026semiabeliannessaffinegroupschemes], Theorem 3.15, via Takeuchi [Takeuchi1972]). -/
theorem isBarrExact_affGrp_of_isField (hk : IsField R) :
    CategoryTheory.IsBarrExact (Grp (CommAlgCat.{u} R)ᵒᵖ) := by
  have h : CategoryTheory.IsBarrExact (CommHopfAlgCat.{u} R)ᵒᵖ := by
    let : Field R := hk.toField
    exact AffineGroupSchemes.isBarrExact_commHopfAlgCat_op R
  have := h
  exact CategoryTheory.isBarrExact_of_equivalence
      (AffineGroupSchemes.opCommHopfAlgCatEquivGrp R).symm

/-- **Affine group schemes over a von Neumann regular ring are Barr-exact**, proved by the
method of Corollary 6.11 ([forsman2026syntactic]): localization at the maximal ideals, the field
case, and descent along the jointly conservative family of localizations
(`GrpDescent.isBarrExact_grp`). -/
theorem isBarrExact_affGrp_vnr (hR : IsVonNeumannRegularRing R) :
    CategoryTheory.IsBarrExact (Grp (CommAlgCat.{u} R)ᵒᵖ) := by
  have := allFlat_of_vnr R hR
  have hfield : ∀ p : MaxIdeal R, IsField (Localization.AtPrime p.1) :=
    fun p => IsVonNeumannRegular.isField_localizationAtPrime hR p.1
  have : ∀ p : MaxIdeal R, AffineGroupSchemes.AllFlat (Localization.AtPrime p.1) := fun p =>
    allFlat_of_vnr _ (IsVonNeumannRegularRing.of_isField (hfield p))
  have : ∀ p : MaxIdeal R, CategoryTheory.IsBarrExact
      (Grp (CommAlgCat.{u} (Localization.AtPrime p.1))ᵒᵖ) :=
    fun p => isBarrExact_affGrp_of_isField _ (hfield p)
  have := fun W => preservesReflexiveCoeq_tensorLeft R W
  have := fun W => preservesReflexiveCoeq_tensorRight R W
  have := fun (p : MaxIdeal R) W => preservesReflexiveCoeq_tensorLeft (Localization.AtPrime p.1) W
  have := fun (p : MaxIdeal R) W =>
    preservesReflexiveCoeq_tensorRight (Localization.AtPrime p.1) W
  exact GrpDescent.isBarrExact_grp (D := fun p : MaxIdeal R =>
      (CommAlgCat.{u} (Localization.AtPrime p.1))ᵒᵖ)
    (fun p => loc R p.1) (fun p => loc_preservesReflexiveCoeq R p.1) (loc_jointlyConservative R)

end UlmerBialgebras.Paper.AffGrp
