module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Sites.Sieves.Basic

/-!
# Pullbacks of internal group objects

Let `C` be a cartesian monoidal category with pullbacks.  We show that the category `Grp C`
of internal group objects of `C` has pullbacks, computed as in `C`. Mathlib supplies the
limit-existence instances; this file keeps an explicit pullback cone and its group structure
for calculations with the underlying projections.

This is the technical input for the protomodularity of `Grp C`, which is the categorical heart
of Proposition 3.1 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

the case `C = (CommAlgCat R)ᵒᵖ` being the category of affine group schemes over `R`.

The group-object structure on the pullback is obtained through the Yoneda description of group
objects (`GrpObj.ofRepresentableBy`): the pullback represents the presheaf of groups sending
`T` to the subgroup of `(T ⟶ G) × (T ⟶ H)` of pairs which agree in `K`.

## Main results

* `CategoryTheory.grpObjPullback`: the group-object structure on the pullback of two morphisms of
  group objects;
* `CategoryTheory.isMonHom_pullback_fst`, `CategoryTheory.isMonHom_pullback_snd`: the projections of
  this pullback are morphisms of group objects;
* `CategoryTheory.grpPullbackConeIsLimit`: the pullback cone of two morphisms of group objects is a
  limit cone, i.e. pullbacks in `Grp C` are computed in `C`;
* `CategoryTheory.mono_hom_of_mono`: monomorphisms of group objects are monomorphisms of the
  underlying objects.

## References

* [H.-E. Porst, *On categories of monoids, comonoids, and bimonoids*][Porst01062008]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.11
* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Proposition 3.1
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits Opposite CartesianMonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

section MonHom

/-- A morphism of monoid objects can be recognised on generalized elements: if postcomposition
with `φ` is multiplicative and unital on all hom-sets, then `φ` is a morphism of monoid
objects. -/
lemma isMonHom_of_mul {X Y : C} [MonObj X] [MonObj Y] (φ : X ⟶ Y)
    (hmul : ∀ (T : C) (a b : T ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ))
    (hone : ∀ T : C, (1 : T ⟶ X) ≫ φ = 1) : IsMonHom φ where
  one_hom := by
    have := hone (𝟙_ C)
    rwa [Hom.one_def, Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _), Category.id_comp,
      Category.id_comp] at this
  mul_hom := by
    have := hmul _ (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp, Hom.mul_def] at this
    rw [this]
    congr 1
    ext <;> simp

/-- For group objects, multiplicativity of postcomposition alone already implies that `φ` is a
morphism of monoid (hence group) objects. -/
lemma isMonHom_of_mul' {X Y : C} [GrpObj X] [GrpObj Y] (φ : X ⟶ Y)
    (hmul : ∀ (T : C) (a b : T ⟶ X), (a * b) ≫ φ = (a ≫ φ) * (b ≫ φ)) : IsMonHom φ :=
  isMonHom_of_mul φ hmul (fun T => map_one (MonoidHom.mk' (fun a : T ⟶ X => a ≫ φ) (hmul T)))

/-- The bijection exhibiting `X` as representing a presheaf of monoids is multiplicative for the
induced monoid-object structure on `X`. -/
lemma homEquiv_mul (X : C) (F : Cᵒᵖ ⥤ MonCat.{v}) (α : (F ⋙ forget _).RepresentableBy X)
    {T : C} (a b : T ⟶ X) :
    letI := MonObj.ofRepresentableBy X F α
    α.homEquiv' (a * b) = α.homEquiv' a * α.homEquiv' b := by
  let := MonObj.ofRepresentableBy X F α
  exact ((yonedaMonObjIsoOfRepresentableBy X F α).hom.app (op T)).hom.map_mul a b

end MonHom

section Pullback

variable [HasPullbacks C] {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K]

/-- The subgroup of `(T ⟶ G) × (T ⟶ H)` consisting of the pairs which agree in `K`. -/
def pbSubgroup (f : G ⟶ K) [IsMonHom f] (g : H ⟶ K) [IsMonHom g] (T : Cᵒᵖ) :
    Subgroup ((T.unop ⟶ G) × (T.unop ⟶ H)) where
  carrier := {p | p.1 ≫ f = p.2 ≫ g}
  mul_mem' := by
    rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb
    simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul, mul_comp] at *
    rw [ha, hb]
  one_mem' := by simp [Set.mem_ofPred_eq]
  inv_mem' := by
    rintro ⟨a₁, a₂⟩ ha
    simp only [Set.mem_ofPred_eq, Prod.fst_inv, Prod.snd_inv, GrpObj.inv_comp] at *
    rw [ha]

variable {f : G ⟶ K} [IsMonHom f] {g : H ⟶ K} [IsMonHom g]

omit [HasPullbacks C] in
/-- A pair `(a, b)` of generalized elements lies in `pbSubgroup f g T` iff `a ≫ f = b ≫ g`. -/
lemma mem_pbSubgroup {T : Cᵒᵖ} (p : (T.unop ⟶ G) × (T.unop ⟶ H)) :
    p ∈ pbSubgroup f g T ↔ p.1 ≫ f = p.2 ≫ g := Iff.rfl

variable (f g)

/-- The presheaf of groups represented by the pullback of two morphisms of group objects. -/
@[simps]
def pbPresheaf : Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (pbSubgroup f g T)
  map {T T'} φ := GrpCat.ofHom
    { toFun := fun p => ⟨(φ.unop ≫ p.1.1, φ.unop ≫ p.1.2), by
        have h2 := (mem_pbSubgroup (f := f) (g := g) p.1).1 p.2
        rw [mem_pbSubgroup]
        simp only [Category.assoc, h2]⟩
      map_one' := by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [comp_mul] }
  map_id T := by ext p <;> simp
  map_comp φ ψ := by ext p <;> simp

/-- The pullback of `f` and `g` represents the presheaf of groups `pbPresheaf f g`. -/
noncomputable def pbRepresentableBy :
    (pbPresheaf f g ⋙ forget _).RepresentableBy (pullback f g) where
  homEquiv {T} :=
    { toFun := fun u => ⟨(u ≫ pullback.fst f g, u ≫ pullback.snd f g), by
        rw [mem_pbSubgroup]; simp [Category.assoc, pullback.condition]⟩
      invFun := fun p => pullback.lift p.1.1 p.1.2 ((mem_pbSubgroup p.1).1 p.2)
      left_inv := fun u => by apply pullback.hom_ext <;> simp
      right_inv := fun p => Subtype.ext (Prod.ext (by simp) (by simp)) }
  homEquiv_comp := by
    intros
    exact Subtype.ext (Prod.ext (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- The group-object structure on the pullback of two morphisms of group objects. -/
@[instance_reducible]
noncomputable def grpObjPullback : GrpObj (pullback f g) :=
  GrpObj.ofRepresentableBy _ (pbPresheaf f g) (pbRepresentableBy f g)

attribute [instance] grpObjPullback

/-- The underlying pair of an element of the presheaf `pbPresheaf f g`. -/
def pbVal {T : C} (x : (pbPresheaf f g ⋙ forget GrpCat).obj (op T)) : (T ⟶ G) × (T ⟶ H) := x.1

variable {f g}

/-- Postcomposition with `pullback.fst f g` is multiplicative for the group structure on
`pullback f g`. -/
@[reassoc]
lemma pullback_mul_fst {T : C} (u v : T ⟶ pullback f g) :
    (u * v) ≫ pullback.fst f g = (u ≫ pullback.fst f g) * (v ≫ pullback.fst f g) :=
  congr((pbVal (f := f) (g := g)
    $(homEquiv_mul (pullback f g) (pbPresheaf f g ⋙ forget₂ GrpCat MonCat)
      (pbRepresentableBy f g) u v)).1)

/-- Postcomposition with `pullback.snd f g` is multiplicative for the group structure on
`pullback f g`. -/
@[reassoc]
lemma pullback_mul_snd {T : C} (u v : T ⟶ pullback f g) :
    (u * v) ≫ pullback.snd f g = (u ≫ pullback.snd f g) * (v ≫ pullback.snd f g) :=
  congr((pbVal (f := f) (g := g)
    $(homEquiv_mul (pullback f g) (pbPresheaf f g ⋙ forget₂ GrpCat MonCat)
      (pbRepresentableBy f g) u v)).2)

/-- The first projection of the pullback of group objects is a morphism of group objects. -/
instance isMonHom_pullback_fst : IsMonHom (pullback.fst f g) :=
  isMonHom_of_mul' _ (fun _ u v => pullback_mul_fst u v)

/-- The second projection of the pullback of group objects is a morphism of group objects. -/
instance isMonHom_pullback_snd : IsMonHom (pullback.snd f g) :=
  isMonHom_of_mul' _ (fun _ u v => pullback_mul_snd u v)

/-- The morphism into a pullback induced by two morphisms of group objects is again a morphism
of group objects. -/
lemma isMonHom_pullback_lift {T : C} [GrpObj T] (a : T ⟶ G) (b : T ⟶ H) [IsMonHom a]
    [IsMonHom b] (w : a ≫ f = b ≫ g) : IsMonHom (pullback.lift a b w) := by
  refine isMonHom_of_mul' _ (fun S u v => pullback.hom_ext ?_ ?_)
  · rw [Category.assoc, pullback.lift_fst, mul_comp, pullback_mul_fst]
    simp
  · rw [Category.assoc, pullback.lift_snd, mul_comp, pullback_mul_snd]
    simp

end Pullback

section GrpPullbacks

variable [HasPullbacks C] {A B D : Grp C} (φ : A ⟶ D) (ψ : B ⟶ D)

/-- The pullback of two morphisms of group objects, as a group object. -/
noncomputable def grpPullback : Grp C := .mk (pullback φ.hom.hom ψ.hom.hom)

/-- The pullback cone of two morphisms of group objects. -/
noncomputable def grpPullbackCone : PullbackCone φ ψ :=
  PullbackCone.mk (W := grpPullback φ ψ)
    (@Grp.homMk _ _ _ (grpPullback φ ψ) _ (pullback.fst φ.hom.hom ψ.hom.hom) isMonHom_pullback_fst)
    (@Grp.homMk _ _ _ (grpPullback φ ψ) _ (pullback.snd φ.hom.hom ψ.hom.hom) isMonHom_pullback_snd)
    (by ext; exact pullback.condition)

/-- The pullback cone of two morphisms of group objects is a limit cone: pullbacks in `Grp C`
are computed in `C`. -/
noncomputable def grpPullbackConeIsLimit : IsLimit (grpPullbackCone φ ψ) := by
  refine PullbackCone.IsLimit.mk _
    (fun s => ?_) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)
  · have w : s.fst.hom.hom ≫ φ.hom.hom = s.snd.hom.hom ≫ ψ.hom.hom :=
      congr(($(s.condition)).hom.hom)
    haveI := isMonHom_pullback_lift s.fst.hom.hom s.snd.hom.hom w
    exact @Grp.homMk _ _ _ _ (grpPullback φ ψ) (pullback.lift s.fst.hom.hom s.snd.hom.hom w) this
  · ext; exact pullback.lift_fst _ _ _
  · ext; exact pullback.lift_snd _ _ _
  · ext
    refine pullback.hom_ext ?_ ?_
    · exact congr(($(h₁)).hom.hom).trans
        (pullback.lift_fst (f := φ.hom.hom) (g := ψ.hom.hom) _ _ _).symm
    · exact congr(($(h₂)).hom.hom).trans
        (pullback.lift_snd (f := φ.hom.hom) (g := ψ.hom.hom) _ _ _).symm

/-- Monomorphisms of group objects are monomorphisms of the underlying objects. -/
lemma mono_hom_of_mono {A B : Grp C} (m : A ⟶ B) [Mono m] : Mono m.hom.hom := by
  have key : pullback.fst m.hom.hom m.hom.hom = pullback.snd m.hom.hom m.hom.hom := by
    have h : (@Grp.homMk _ _ _ (grpPullback m m) A (pullback.fst m.hom.hom m.hom.hom)
          isMonHom_pullback_fst) ≫ m =
        (@Grp.homMk _ _ _ (grpPullback m m) A (pullback.snd m.hom.hom m.hom.hom)
          isMonHom_pullback_snd) ≫ m := by
      ext; exact pullback.condition
    exact congr(($((cancel_mono m).1 h)).hom.hom)
  refine ⟨fun {W} a b hab => ?_⟩
  have ha : pullback.lift a b hab ≫ pullback.fst m.hom.hom m.hom.hom = a := by simp
  have hb : pullback.lift a b hab ≫ pullback.snd m.hom.hom m.hom.hom = b := by simp
  rw [← ha, key, hb]

end GrpPullbacks

end CategoryTheory
