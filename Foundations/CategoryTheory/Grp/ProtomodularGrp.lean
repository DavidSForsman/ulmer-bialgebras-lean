module

public import Foundations.CategoryTheory.Grp.GrpObjPullback
public import Foundations.CategoryTheory.Exact.SemiAbelian

/-!
# Internal group objects form a protomodular category

Let `C` be a cartesian monoidal category with pullbacks.  We prove that the category `Grp C`
of internal group objects of `C` is protomodular in the sense of Definition 2.1 (4) of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

This is the "split short five lemma" argument, carried out with generalized elements: given a
split epimorphism `r : X ⟶ Y` with section `s` and a pullback `k : A ⟶ X` of a morphism along
`r`, any monomorphism `m : Z ⟶ X` through which both `s` and `k` factor is an isomorphism,
because every generalized element `f` of `X` can be written as
`(f · (r ≫ s)(f)⁻¹) · (r ≫ s)(f)`, whose first factor lies in the "kernel" of `r`, hence in the
image of `k`, and whose second factor lies in the image of `s`.

For `C = (CommAlgCat R)ᵒᵖ` this is the protomodularity of the category of affine group schemes
over `R`, i.e. the coprotomodularity of commutative Hopf algebras (Proposition 3.1).

## Main results

* `CategoryTheory.protomodular_grp`: the category of group objects in a cartesian monoidal category
  with pullbacks is protomodular (Definition 2.1 (4) of
  [forsman2026semiabeliannessaffinegroupschemes]);
* `CategoryTheory.isIso_of_isIso_hom`: a morphism of group objects whose underlying morphism is an
  isomorphism is an isomorphism;
* `CategoryTheory.preservesLimitCospanGrpForget`: the forgetful functor `Grp C ⥤ C` preserves
  pullbacks.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Definition 2.1 (4) and Proposition 3.1
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian categories*]
  [BorceuxBourn2004]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory
open CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A morphism of group objects whose underlying morphism is an isomorphism is an
isomorphism. -/
lemma isIso_of_isIso_hom {A B : Grp C} (m : A ⟶ B) (h : IsIso m.hom.hom) : IsIso m := by
  have : IsIso ((Mon.forget C).map m.hom) := h
  have : IsIso m.hom := isIso_of_reflects_iso m.hom (Mon.forget C)
  refine ⟨Grp.homMk' (inv m.hom), ?_, ?_⟩ <;> ext <;> simp

variable [HasPullbacks C]

/-- The forgetful functor `Grp C ⥤ C` preserves pullbacks: they are computed in `C`. -/
noncomputable instance preservesLimitCospanGrpForget {A B D : Grp C} (φ : A ⟶ D) (ψ : B ⟶ D) :
    PreservesLimit (cospan φ ψ) (Grp.forget C) :=
  preservesLimit_of_preserves_limit_cone (grpPullbackConeIsLimit φ ψ)
    ((isLimitMapConePullbackConeEquiv _ _).symm (pullbackIsPullback φ.hom.hom ψ.hom.hom))

/-- **Protomodularity of internal groups.**  The category of group objects in a cartesian
monoidal category with pullbacks is protomodular. -/
instance protomodular_grp : Protomodular (Grp C) where
  hasPullback_of_isSplitEpi _ _ _ := inferInstance
  jointlyExtremalEpiPair := by
    intro X Y A B r s hsr k t u hP Z m hm g₁ g₂ h₁ h₂
    have := hm
    have hmono : Mono m.hom.hom := mono_hom_of_mono m
    have hPC : IsPullback t.hom.hom k.hom.hom u.hom.hom r.hom.hom := hP.map (Grp.forget C)
    have hsr' : s.hom.hom ≫ r.hom.hom = 𝟙 Y.X :=
      congr(($(hsr)).hom.hom)
    have h₁' : g₁.hom.hom ≫ m.hom.hom = s.hom.hom :=
      congr(($(h₁)).hom.hom)
    have h₂' : g₂.hom.hom ≫ m.hom.hom = k.hom.hom :=
      congr(($(h₂)).hom.hom)
    -- the "kernel part" of the identity of `X`
    set n₀ : X.X ⟶ X.X := 𝟙 X.X / (r.hom.hom ≫ s.hom.hom) with hn₀def
    have hn₀ : n₀ ≫ r.hom.hom = 1 := by
      rw [hn₀def, GrpObj.div_comp, Category.id_comp, Category.assoc, hsr', Category.comp_id,
        div_self']
    have hcond : (1 : X.X ⟶ B.X) ≫ u.hom.hom = n₀ ≫ r.hom.hom := by rw [one_comp, hn₀]
    -- it factors through the pullback projection `k`
    set l : X.X ⟶ A.X := hPC.lift 1 n₀ hcond with hldef
    have hl : l ≫ k.hom.hom = n₀ := hPC.lift_snd _ _ _
    -- hence the identity of `X` factors through `m`
    set n : X.X ⟶ Z.X := (l ≫ g₂.hom.hom) * (r.hom.hom ≫ g₁.hom.hom) with hndef
    have key : n ≫ m.hom.hom = 𝟙 X.X := by
      rw [hndef, mul_comp, Category.assoc, Category.assoc, h₁', h₂', hl, hn₀def,
        div_mul_cancel]
    have hmn : m.hom.hom ≫ n = 𝟙 Z.X := by
      apply (cancel_mono m.hom.hom).1
      rw [Category.assoc, key, Category.comp_id, Category.id_comp]
    exact isIso_of_isIso_hom m ⟨n, hmn, key⟩

end CategoryTheory
