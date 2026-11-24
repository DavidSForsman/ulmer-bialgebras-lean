module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Left adjoints of functors into a product of categories

Two elementary constructions of left adjoints, used to produce the left adjoint of the
coarity 1-cell of an algebraic theory.

## Main results

* `UlmerBialgebras.Pi.eval_isRightAdjoint` — the evaluation functor `(∀ j, C j) ⥤ C i` has a left
  adjoint as soon as every `C j` has an initial object: the left adjoint extends an object
  of `C i` by initial objects in the other coordinates.
* `UlmerBialgebras.pi'_isRightAdjoint` — if `A` has `ι`-indexed coproducts and each `H i : A ⥤ C i`
  has a left adjoint `L i`, then `Functor.pi' H : A ⥤ ∀ i, C i` has the left adjoint
  `Z ↦ ∐ i, L i (Z i)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 5.8 (proof)
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

section Eval

variable {ι : Type w} (C : ι → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, HasInitial (C i)]

section Single

variable [DecidableEq ι]

/-- The object of `∀ j, C j` which is `x` in the coordinate `i` and initial elsewhere. -/
noncomputable def piSingleObj (i : ι) (x : C i) (j : ι) : C j :=
  if h : i = j then (congrArg C h) ▸ x else ⊥_ (C j)

/-- At the distinguished coordinate `i`, `piSingleObj C i x` is `x`. -/
@[simp] lemma piSingleObj_self (i : ι) (x : C i) : piSingleObj C i x i = x := by
  simp [piSingleObj]

/-- At a coordinate `j ≠ i`, `piSingleObj C i x` is the initial object `⊥_ (C j)`. -/
lemma piSingleObj_of_ne (i : ι) (x : C i) {j : ι} (h : i ≠ j) :
    piSingleObj C i x j = ⊥_ (C j) := by
  simp [piSingleObj, h]

/-- Away from the distinguished coordinate, `piSingleObj` is initial. -/
noncomputable def isInitialPiSingleObj (i : ι) (x : C i) {j : ι} (h : i ≠ j) :
    IsInitial (piSingleObj C i x j) :=
  IsInitial.ofIso initialIsInitial (eqToIso (piSingleObj_of_ne C i x h)).symm

/-- The component at the distinguished coordinate of a morphism out of `piSingleObj`. -/
noncomputable def piSingleDescAux (i : ι) {x : C i} (Q : ∀ j, C j) (v : x ⟶ Q i) :
    ∀ (j : ι), i = j → (piSingleObj C i x j ⟶ Q j)
  | _, rfl => eqToHom (piSingleObj_self C i x) ≫ v

/-- The morphism out of `piSingleObj C i x` induced by a morphism `x ⟶ Q i`. -/
noncomputable def piSingleDesc (i : ι) {x : C i} (Q : ∀ j, C j) (v : x ⟶ Q i) :
    piSingleObj C i x ⟶ Q := fun j =>
  if h : i = j then piSingleDescAux C i Q v j h
  else eqToHom (piSingleObj_of_ne C i x h) ≫ initial.to (Q j)

/-- At the distinguished coordinate `i`, `piSingleDesc C i Q v` is `v` up to the identification
`piSingleObj_self`. -/
lemma piSingleDesc_self (i : ι) {x : C i} (Q : ∀ j, C j) (v : x ⟶ Q i) :
    piSingleDesc C i Q v i = eqToHom (piSingleObj_self C i x) ≫ v := by
  simp [piSingleDesc, piSingleDescAux]

/-- `piSingleDesc` restricts to `v` at the distinguished coordinate. -/
lemma eqToHom_comp_piSingleDesc_self (i : ι) {x : C i} (Q : ∀ j, C j) (v : x ⟶ Q i) :
    eqToHom (piSingleObj_self C i x).symm ≫ piSingleDesc C i Q v i = v := by
  rw [piSingleDesc_self, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- A morphism at the distinguished coordinate restricting to `v` is the component of
`piSingleDesc`. -/
lemma eq_piSingleDesc_self (i : ι) {x : C i} (Q : ∀ j, C j) (v : x ⟶ Q i)
    (w : piSingleObj C i x i ⟶ Q i) (hw : eqToHom (piSingleObj_self C i x).symm ≫ w = v) :
    w = piSingleDesc C i Q v i := by
  rw [piSingleDesc_self, ← hw, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]

end Single

/-- If every `C j` has an initial object, every object of `C i` has a free object along the
evaluation functor: the category of structured arrows from it has an initial object. -/
theorem hasInitial_structuredArrow_eval (i : ι) (x : C i) :
    HasInitial (StructuredArrow x (CategoryTheory.Pi.eval C i)) := by
  classical
  refine IsInitial.hasInitial (X := StructuredArrow.mk (S := x)
    (T := CategoryTheory.Pi.eval C i) (Y := piSingleObj C i x)
    (eqToHom (piSingleObj_self C i x).symm)) ?_
  refine IsInitial.ofUniqueHom
    (fun A => StructuredArrow.homMk (piSingleDesc C i A.right A.hom) ?_) ?_
  · exact eqToHom_comp_piSingleDesc_self C i A.right A.hom
  · intro A m
    apply StructuredArrow.hom_ext
    funext j
    by_cases h : i = j
    · subst h
      exact eq_piSingleDesc_self C i A.right A.hom (m.right i) (StructuredArrow.w m)
    · exact (isInitialPiSingleObj C i x h).hom_ext _ _

/-- The evaluation functor out of a product of categories has a left adjoint, provided all
the other factors have initial objects. -/
theorem Pi.eval_isRightAdjoint (i : ι) :
    (CategoryTheory.Pi.eval C i).IsRightAdjoint := by
  have : ∀ x : C i, HasInitial (StructuredArrow x (CategoryTheory.Pi.eval C i)) :=
    hasInitial_structuredArrow_eval C i
  exact isRightAdjointOfStructuredArrowInitials _

end Eval

section Pi'

variable {ι : Type w} {A : Type u'} [Category.{v'} A] {C : ι → Type u}
  [∀ i, Category.{v} (C i)]

/-- Every object of `∀ i, C i` has a free object along `Functor.pi' H`. -/
theorem hasInitial_structuredArrow_pi' (H : ∀ i, A ⥤ C i) [∀ i, (H i).IsRightAdjoint]
    [HasCoproductsOfShape ι A] (Z : ∀ i, C i) :
    HasInitial (StructuredArrow Z (Functor.pi' H)) := by
  let adj : ∀ i, (H i).leftAdjoint ⊣ H i := fun i => Adjunction.ofIsRightAdjoint (H i)
  let u : Z ⟶ (Functor.pi' H).obj (∐ (fun i => ((H i).leftAdjoint).obj (Z i))) := fun i =>
    (adj i).unit.app (Z i) ≫ (H i).map (Sigma.ι (fun i => ((H i).leftAdjoint).obj (Z i)) i)
  refine IsInitial.hasInitial
    (X := StructuredArrow.mk (S := Z) (T := Functor.pi' H) u) ?_
  refine IsInitial.ofUniqueHom
    (fun B => StructuredArrow.homMk
      (Sigma.desc (fun i => ((adj i).homEquiv _ _).symm (B.hom i))) ?_) ?_
  · funext i
    exact (Category.assoc _ _ _).trans (((adj i).unit.app (Z i) ≫=
      ((H i).map_comp _ _).symm).trans (((adj i).unit.app (Z i) ≫=
        (H i).congr_map (Sigma.ι_comp_desc _ i)).trans (((adj i).homEquiv_unit _ _ _).symm.trans
          (Equiv.apply_symm_apply _ _))))
  · intro B m
    apply StructuredArrow.hom_ext
    refine colimit.hom_ext ?_
    intro i
    have hm : u i.as ≫ (H i.as).map m.right = B.hom i.as := congr($(StructuredArrow.w m) i.as)
    simp only [StructuredArrow.homMk_right, colimit.ι_desc, Cofan.mk_ι_app]
    apply ((adj i.as).homEquiv _ _).injective
    exact ((adj i.as).homEquiv_unit _ _ _).trans (((adj i.as).unit.app (Z i.as) ≫=
      (H i.as).map_comp _ _).trans (((Category.assoc _ _ _).symm.trans hm).trans
        (Equiv.apply_symm_apply _ _).symm))

/-- A functor into a product of categories has a left adjoint as soon as all its components
have one and the domain has coproducts of the relevant shape. -/
theorem pi'_isRightAdjoint (H : ∀ i, A ⥤ C i) [∀ i, (H i).IsRightAdjoint]
    [HasCoproductsOfShape ι A] : (Functor.pi' H).IsRightAdjoint := by
  have : ∀ Z : (∀ i, C i), HasInitial (StructuredArrow Z (Functor.pi' H)) :=
    hasInitial_structuredArrow_pi' H
  exact isRightAdjointOfStructuredArrowInitials _

end Pi'

end UlmerBialgebras
