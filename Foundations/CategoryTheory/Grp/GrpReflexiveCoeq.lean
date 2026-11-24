module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Foundations.CategoryTheory.Monoidal.MonObjReflexiveCoeq
public import Foundations.CategoryTheory.Limits.ReflexivePairMap

/-!
# Reflexive coequalizers of group objects are created in the base

Let `D` be a cartesian monoidal category in which the binary product preserves the coequalizers
of reflexive pairs componentwise.  We show that the coequalizer of a reflexive pair of morphisms
of group objects is computed in `D`: the coequalizer carries a unique group structure making the
projection a morphism of group objects, and the resulting cofork is a colimit in `Grp D`.

This is the group-object half of the argument of Theorem 4.2 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

## Main results

* `CategoryTheory.GrpReflexiveCoeq.grpObj`: the group structure on the coequalizer;
* `CategoryTheory.GrpReflexiveCoeq.isColimitCoforkGrp`: the cofork is a colimit in `Grp D`;
* `CategoryTheory.GrpReflexiveCoeq.hasReflexiveCoequalizers_grp`;
* `CategoryTheory.GrpReflexiveCoeq.preservesReflexiveCoeq_grpForget`.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.17,
  Example 4.20
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 4.2
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory MonObj

section
open CategoryTheory CategoryTheory.MonReflexiveCoeq

namespace CategoryTheory.GrpReflexiveCoeq

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [∀ Z : D, PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : D, PreservesReflexiveCoeq (tensorRight Z)]

section

variable {M N : Grp D} {u v : M ⟶ N} (hr : IsReflexivePair u.hom.hom v.hom.hom)
  {Q : D} {q : N.X ⟶ Q} {w : u.hom.hom ≫ q = v.hom.hom ≫ q}
  (hq : IsColimit (Cofork.ofπ q w))

include hr hq

/-- The inverse induced on a reflexive coequalizer of group objects. -/
noncomputable def invQ : Q ⟶ Q :=
  Cofork.IsColimit.desc hq (ι[N.X] ≫ q) (by
    rw [← Category.assoc, ← GrpObj.inv_hom, ← Category.assoc, ← GrpObj.inv_hom,
      Category.assoc, Category.assoc, w])

omit hr in
omit [∀ (Z : D), PreservesReflexiveCoeq (tensorLeft Z)]
    [∀ (Z : D), PreservesReflexiveCoeq (tensorRight Z)] in
/-- The inverse `invQ hq` on the coequalizer satisfies `q ≫ invQ hq = ι[N.X] ≫ q`. -/
@[reassoc (attr := simp)]
lemma comp_invQ : q ≫ invQ hq = ι[N.X] ≫ q :=
  Cofork.IsColimit.π_desc' hq _ _

/-- The left inverse law for `invQ hq` and the multiplication
`CategoryTheory.MonReflexiveCoeq.mul hr hq`: `lift (invQ hq) (𝟙 Q) ≫ mul = toUnit Q ≫ (η[N.X] ≫ q)`.
-/
lemma left_inv_aux :
    lift (invQ hq) (𝟙 Q) ≫ CategoryTheory.MonReflexiveCoeq.mul hr hq = toUnit Q ≫ (η[N.X] ≫ q) := by
  have : Epi q := epi_of_isColimit_cofork hq
  rw [← cancel_epi q, ← Category.assoc, comp_lift, Category.comp_id, comp_invQ hq]
  rw [show lift (ι[N.X] ≫ q) q = lift ι[N.X] (𝟙 N.X) ≫ (q ⊗ₘ q) by simp]
  rw [Category.assoc, CategoryTheory.MonReflexiveCoeq.tensorHom_comp_mul hr hq, ← Category.assoc,
    GrpObj.left_inv, Category.assoc, ← Category.assoc q, toUnit_unique (q ≫ toUnit Q) (toUnit N.X)]

/-- The right inverse law for `invQ hq` and the multiplication
`CategoryTheory.MonReflexiveCoeq.mul hr hq`: `lift (𝟙 Q) (invQ hq) ≫ mul = toUnit Q ≫ (η[N.X] ≫ q)`.
-/
lemma right_inv_aux :
    lift (𝟙 Q) (invQ hq) ≫ CategoryTheory.MonReflexiveCoeq.mul hr hq = toUnit Q ≫ (η[N.X] ≫ q) := by
  have : Epi q := epi_of_isColimit_cofork hq
  rw [← cancel_epi q, ← Category.assoc, comp_lift, Category.comp_id, comp_invQ hq]
  rw [show lift q (ι[N.X] ≫ q) = lift (𝟙 N.X) ι[N.X] ≫ (q ⊗ₘ q) by simp]
  rw [Category.assoc, CategoryTheory.MonReflexiveCoeq.tensorHom_comp_mul hr hq, ← Category.assoc,
    GrpObj.right_inv, Category.assoc, ← Category.assoc q,
    toUnit_unique (q ≫ toUnit Q) (toUnit N.X)]

/-- The group structure induced on a reflexive coequalizer of group objects. -/
@[instance_reducible]
noncomputable def grpObj : GrpObj Q :=
  letI := CategoryTheory.MonReflexiveCoeq.monObj hr hq
  { inv := invQ hq
    left_inv := left_inv_aux hr hq
    right_inv := right_inv_aux hr hq }

/-- The coequalizer of a reflexive pair of group objects. -/
noncomputable abbrev coeqGrp : Grp D :=
  letI := grpObj hr hq
  .mk Q

/-- The projection onto the coequalizer, as a morphism of group objects. -/
noncomputable def coeqGrpπ : N ⟶ coeqGrp hr hq :=
  letI := grpObj hr hq
  letI := CategoryTheory.MonReflexiveCoeq.isMonHom_q hr hq
  Grp.homMk q

/-- The underlying morphism of `coeqGrpπ hr hq` is `q`. -/
@[simp]
lemma coeqGrpπ_hom : (coeqGrpπ hr hq).hom.hom = q := rfl

/-- The projection `coeqGrpπ hr hq` coequalizes `u` and `v` in `Grp D`. -/
lemma coeqGrp_condition : u ≫ coeqGrpπ hr hq = v ≫ coeqGrpπ hr hq :=
  Grp.hom_ext _ _ (by simpa using w)

/-- **Reflexive coequalizers of group objects are created in the base category.** -/
noncomputable def isColimitCoforkGrp :
    IsColimit (Cofork.ofπ (coeqGrpπ hr hq) (coeqGrp_condition hr hq)) :=
  Cofork.IsColimit.mk _
    (fun s =>
      letI := grpObj hr hq
      letI := CategoryTheory.MonReflexiveCoeq.isMonHom_descMon hr hq s.π.hom.hom
        (congr(($(s.condition)).hom.hom))
      Grp.homMk (CategoryTheory.MonReflexiveCoeq.descMon hq s.π.hom.hom
        (congr(($(s.condition)).hom.hom))))
    (fun s => Grp.hom_ext _ _
      (CategoryTheory.MonReflexiveCoeq.comp_descMon hq s.π.hom.hom
          (congr(($(s.condition)).hom.hom))))
    (fun s m hm => Grp.hom_ext _ _ (by
      refine Cofork.IsColimit.hom_ext hq ?_
      have h1 : q ≫ m.hom.hom = s.π.hom.hom := congr(($(hm)).hom.hom)
      simp only [Cofork.π_ofπ]
      rw [h1]
      exact (CategoryTheory.MonReflexiveCoeq.comp_descMon hq s.π.hom.hom
        (congr(($(s.condition)).hom.hom))).symm))

end

section Instances

variable (D)
variable [HasReflexiveCoequalizers D]

/-- The category of group objects has reflexive coequalizers, computed in the base category. -/
instance hasReflexiveCoequalizers_grp : HasReflexiveCoequalizers (Grp D) where
  has_coeq {M N} u v h := by
    have hr : IsReflexivePair u.hom.hom v.hom.hom :=
      CategoryTheory.isReflexivePair_map (Grp.forget D) h
    have := HasReflexiveCoequalizers.has_coeq u.hom.hom v.hom.hom
    exact HasColimit.mk ⟨_, isColimitCoforkGrp hr
      (coequalizerIsCoequalizer u.hom.hom v.hom.hom)⟩

/-- The forgetful functor `Grp D ⥤ D` preserves reflexive coequalizers. -/
instance preservesReflexiveCoeq_grpForget : PreservesReflexiveCoeq (Grp.forget D) where
  preserves {M N} u v h := by
    have hr : IsReflexivePair u.hom.hom v.hom.hom :=
      CategoryTheory.isReflexivePair_map (Grp.forget D) h
    have := HasReflexiveCoequalizers.has_coeq u.hom.hom v.hom.hom
    exact preservesColimit_of_preserves_colimit_cocone
      (isColimitCoforkGrp hr (coequalizerIsCoequalizer u.hom.hom v.hom.hom))
      ((isColimitMapCoconeCoforkEquiv (Grp.forget D) _).symm
        (coequalizerIsCoequalizer u.hom.hom v.hom.hom))

end Instances

end CategoryTheory.GrpReflexiveCoeq

end
