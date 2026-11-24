module

public import Hopf.Cocommutative.CocommProj
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Hopf_

/-!
# Group objects of cocommutative comonoids are cocommutative Hopf monoids

Let `V` be a symmetric monoidal category and `C = CommComon V` the category of cocommutative
comonoids, which is cartesian monoidal with the tensor product of `V` as product (Fox's theorem,
`Foundations/CategoryTheory/Monoidal/CocommProducts.lean`).  A group object `H : Grp C` is a
cocommutative Hopf monoid of `V`.  This file constructs the Hopf monoid structure on the underlying
object `H.X.X`, at the generality of an arbitrary symmetric monoidal `V`: it generalizes the
`ModuleCat k` computation of `Hopf/Cocommutative/GrpCocommHopf.lean`.

Conversely, a cocommutative Hopf monoid is a group object of `CommComon V`: its multiplication,
unit and antipode are morphisms of comonoids (for the antipode this uses cocommutativity and
Mathlib's `HopfObj.antipode_comul`).  The two constructions give an **equivalence of categories**
between `Grp (CommComon V)` and the full subcategory `CocommHopf V` of `Hopf V` on the
cocommutative Hopf monoids.

## Main definitions

* `UlmerBialgebras.GrpHopf.mulHom`, `unitHom`, `invHom`: the multiplication, unit and antipode of
  `H.X.X`, read off from the group object `H`;
* `UlmerBialgebras.GrpHopf.instHopfObj`: the Hopf monoid structure on `H.X.X`;
* `UlmerBialgebras.GrpHopf.toHopf`: the functor `Grp (CommComon V) ⥤ Hopf V`;
* `UlmerBialgebras.GrpHopf.ofHopf`: the group object of a cocommutative Hopf monoid;
* `UlmerBialgebras.GrpHopf.CocommHopf`: the full subcategory of cocommutative Hopf monoids.

## Main results

* `UlmerBialgebras.GrpHopf.mul_hom_eq`: the product of two generalized elements `x y : T ⟶ H.X`
  has underlying morphism the convolution `lift x y ≫ mulHom H`;
* `UlmerBialgebras.GrpHopf.associator_hom_hom`, `leftUnitor_hom_hom`, `rightUnitor_hom_hom`: the
  structure morphisms of the cartesian structure of `CommComon V` are those of `V`;
* `UlmerBialgebras.GrpHopf.isComonHom_antipode`: the antipode of a cocommutative Hopf monoid is a
  morphism of comonoids;
* `UlmerBialgebras.GrpHopf.grpCommComonEquivCocommHopf`: the equivalence
  `Grp (CommComon V) ≌ CocommHopf V`.

## References

* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Section 6.3 (`Hopf_k^coc = Grp(Comon_k^coc)`)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory MonObj ComonObj
open scoped MonObj ComonObj HopfObj

namespace UlmerBialgebras.GrpHopf

open UlmerBialgebras.CocommComon (fst snd)

attribute [local instance_reducible] CommComon.toComon CommComon.trivial

attribute [local instance] ComonObj.instTensorUnit

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

/-! ## Preliminaries on `CommComon V` -/

/-- The counit `ε : X → 𝟙_` of a comonoid object is a morphism of comonoids. -/
instance isComonHom_counit (X : V) [ComonObj X] : IsComonHom (ε[X] : X ⟶ 𝟙_ V) where
  hom_counit := by simp
  hom_comul := by simp [unitors_inv_equal]

/-- The comparison morphism from the tensor product of two cocommutative comonoids to their
categorical product. -/
noncomputable def eHom (X Y : CommComon V) : UlmerBialgebras.CommComon.tensorObj X Y ⟶ X ⊗ Y :=
  lift (UlmerBialgebras.CommComon.homMk (fst X.X Y.X))
    (UlmerBialgebras.CommComon.homMk (snd X.X Y.X))

/-- The unique morphism to the trivial cocommutative comonoid. -/
noncomputable def toTrivial (T : CommComon V) : T ⟶ CommComon.trivial V :=
  UlmerBialgebras.CommComon.homMk (A := T) (B := CommComon.trivial V) ε[T.X]

/-- The underlying morphism of the identity of a cocommutative comonoid is the identity. -/
lemma id_hom_hom (A : CommComon V) : (𝟙 A : A ⟶ A).hom.hom = 𝟙 A.X := rfl

/-- The underlying morphism of a composite is the composite. -/
lemma comp_hom_hom {A B D : CommComon V} (f : A ⟶ B) (g : B ⟶ D) :
    (f ≫ g).hom.hom = f.hom.hom ≫ g.hom.hom := rfl

variable (H : Grp (CommComon V))

/-! ## The multiplication, the unit and the antipode -/

/-- The multiplication of the group object, as a morphism `H ⊗ H ⟶ H` of `V`. -/
noncomputable def mulHom : H.X.X ⊗ H.X.X ⟶ H.X.X := (eHom H.X H.X ≫ μ[H.X]).hom.hom

/-- The unit of the group object, as a morphism out of the trivial comonoid. -/
noncomputable def oneMor : CommComon.trivial V ⟶ H.X := 1

/-- The unit of the group object, as a morphism `𝟙_ V ⟶ H` of `V`. -/
noncomputable def unitHom : 𝟙_ V ⟶ H.X.X := (oneMor H).hom.hom

/-- The antipode of the group object, as a morphism of `V`. -/
noncomputable def invHom : H.X.X ⟶ H.X.X := ((𝟙 H.X)⁻¹ : H.X ⟶ H.X).hom.hom

instance : IsComonHom (mulHom H) := (eHom H.X H.X ≫ μ[H.X]).hom.isComonHom_hom

instance : IsComonHom (unitHom H) := (oneMor H).hom.isComonHom_hom

instance : IsComonHom (invHom H) := ((𝟙 H.X)⁻¹ : H.X ⟶ H.X).hom.isComonHom_hom

/-! ## Multiplication of generalized elements is convolution -/

/-- The pairing `lift x y` into `H.X ⊗ H.X` is the tensor-product pairing of `x` and `y`
followed by the comparison morphism. -/
lemma lift_eq {T : CommComon V} (x y : T ⟶ H.X) :
    lift x y = UlmerBialgebras.CommComon.homMk
      (UlmerBialgebras.CocommComon.lift x.hom.hom y.hom.hom) ≫ eHom H.X H.X := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst, Category.assoc, eHom, lift_fst]
    ext : 2
    exact (UlmerBialgebras.CocommComon.lift_fst x.hom.hom y.hom.hom).symm
  · rw [lift_snd, Category.assoc, eHom, lift_snd]
    ext : 2
    exact (UlmerBialgebras.CocommComon.lift_snd x.hom.hom y.hom.hom).symm

/-- **The product of two generalized elements is their convolution product.** -/
lemma mul_hom_eq {T : CommComon V} (x y : T ⟶ H.X) :
    (x * y).hom.hom = UlmerBialgebras.CocommComon.lift x.hom.hom y.hom.hom ≫ mulHom H := by
  rw [CategoryTheory.Hom.mul_def, lift_eq H x y, Category.assoc, comp_hom_hom,
    UlmerBialgebras.CommComon.homMk_hom]
  rfl

/-- **The unit generalized element is the counit followed by the unit.** -/
lemma one_hom_eq {T : CommComon V} :
    (1 : T ⟶ H.X).hom.hom = ε[T.X] ≫ unitHom H := by
  have h : (1 : T ⟶ H.X) = toTrivial T ≫ oneMor H := by
    rw [oneMor, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  rw [h, comp_hom_hom]
  rfl

/-! ## The monoid and antipode identities -/

/-- Associativity of the multiplication. -/
theorem mulHom_assoc :
    (mulHom H ⊗ₘ 𝟙 H.X.X) ≫ mulHom H
      = (α_ H.X.X H.X.X H.X.X).hom ≫ (𝟙 H.X.X ⊗ₘ mulHom H) ≫ mulHom H := by
  let T : CommComon V := CommComon.mk ((H.X.X ⊗ H.X.X) ⊗ H.X.X)
  let p1 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk
    (fst (H.X.X ⊗ H.X.X) H.X.X ≫ fst H.X.X H.X.X)
  let p2 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk
    (fst (H.X.X ⊗ H.X.X) H.X.X ≫ snd H.X.X H.X.X)
  let p3 : T ⟶ H.X := UlmerBialgebras.CommComon.homMk (snd (H.X.X ⊗ H.X.X) H.X.X)
  have key := congr(($(mul_assoc p1 p2 p3)).hom.hom)
  simp only [mul_hom_eq, UlmerBialgebras.CommComon.homMk_hom, p1, p2, p3] at key
  rw [CocommComon.lift_comp_left, CocommComon.lift_fst_fst_snd H.X.X H.X.X H.X.X,
    CocommComon.lift_fst_snd_self (H.X.X ⊗ H.X.X) H.X.X] at key
  rw [CocommComon.lift_comp_right, CocommComon.lift_eq_associator H.X.X H.X.X H.X.X] at key
  rw [Category.assoc, Category.assoc] at key
  exact (Category.id_comp _).symm.trans key

/-- The left unit law. -/
theorem unitHom_mulHom_left :
    (λ_ H.X.X).inv ≫ (unitHom H ▷ H.X.X) ≫ mulHom H = 𝟙 H.X.X := by
  have h := congr(($(one_mul (𝟙 H.X))).hom.hom)
  simp only [mul_hom_eq, one_hom_eq, id_hom_hom] at h
  have h1 : CocommComon.lift ε[H.X.X] (𝟙 H.X.X) = (λ_ H.X.X).inv := by
    rw [CocommComon.lift, ComonObj.counit_comul_hom, Category.id_comp]
  rw [CocommComon.lift_comp_left, h1, MonoidalCategory.tensorHom_id, Category.assoc] at h
  exact h

/-- The right unit law. -/
theorem unitHom_mulHom_right :
    (ρ_ H.X.X).inv ≫ (H.X.X ◁ unitHom H) ≫ mulHom H = 𝟙 H.X.X := by
  have h := congr(($(mul_one (𝟙 H.X))).hom.hom)
  simp only [mul_hom_eq, one_hom_eq, id_hom_hom] at h
  have h1 : CocommComon.lift (𝟙 H.X.X) ε[H.X.X] = (ρ_ H.X.X).inv := by
    rw [CocommComon.lift, ComonObj.comul_counit_hom, Category.id_comp]
  rw [CocommComon.lift_comp_right, h1, MonoidalCategory.id_tensorHom, Category.assoc] at h
  exact h

/-- The first antipode identity. -/
theorem invHom_mulHom :
    CocommComon.lift (invHom H) (𝟙 H.X.X) ≫ mulHom H = ε[H.X.X] ≫ unitHom H := by
  have h := congr(($(inv_mul_cancel (𝟙 H.X))).hom.hom)
  simp only [mul_hom_eq, one_hom_eq] at h
  exact h

/-- The second antipode identity. -/
theorem mulHom_invHom :
    CocommComon.lift (𝟙 H.X.X) (invHom H) ≫ mulHom H = ε[H.X.X] ≫ unitHom H := by
  have h := congr(($(mul_inv_cancel (𝟙 H.X))).hom.hom)
  simp only [mul_hom_eq, one_hom_eq] at h
  exact h

/-! ## The Hopf monoid structure -/

/-- The monoid structure of the underlying object of a group object of `CommComon V`. -/
noncomputable instance instMonObj : MonObj H.X.X where
  one := unitHom H
  mul := mulHom H
  one_mul := by
    have h := unitHom_mulHom_left H
    rw [← cancel_epi (λ_ H.X.X).inv, h, Iso.inv_hom_id]
  mul_one := by
    have h := unitHom_mulHom_right H
    rw [← cancel_epi (ρ_ H.X.X).inv, h, Iso.inv_hom_id]
  mul_assoc := by
    simpa only [tensorHom_id, id_tensorHom] using mulHom_assoc H

/-- The multiplication `μ[H.X.X]` of the monoid structure is `mulHom H`. -/
lemma mul_eq : μ[H.X.X] = mulHom H := rfl

/-- The unit `η[H.X.X]` of the monoid structure is `unitHom H`. -/
lemma one_eq : η[H.X.X] = unitHom H := rfl

/-- **The Hopf monoid underlying a group object of `CommComon V`.**  The multiplication and the
unit are morphisms of comonoids, which are the bimonoid axioms, and the antipode identities are the
group axioms. -/
noncomputable instance instHopfObj : HopfObj H.X.X where
  mul_comul := by
    rw [mul_eq, IsComonHom.hom_comul (mulHom H), Comon.tensorObj_comul, Category.assoc]
  one_comul := by
    rw [one_eq, IsComonHom.hom_comul (unitHom H)]
    rfl
  mul_counit := by
    rw [mul_eq, IsComonHom.hom_counit (mulHom H)]
  one_counit := by
    rw [one_eq, IsComonHom.hom_counit (unitHom H)]
    rfl
  antipode := invHom H
  antipode_left := by
    have h := invHom_mulHom H
    rw [CocommComon.lift, tensorHom_id, Category.assoc] at h
    exact h
  antipode_right := by
    have h := mulHom_invHom H
    rw [CocommComon.lift, id_tensorHom, Category.assoc] at h
    exact h

/-! ## Morphisms -/

/-- The categorical product of two morphisms of cocommutative comonoids has underlying morphism
their tensor product. -/
lemma tensorHom_hom_hom {A B A' B' : CommComon V} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g).hom.hom = f.hom.hom ⊗ₘ g.hom.hom := by
  change Δ[(UlmerBialgebras.CommComon.tensorObj A B).X] ≫
      ((fst A.X B.X ≫ f.hom.hom) ⊗ₘ (snd A.X B.X ≫ g.hom.hom)) = _
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, ← Category.assoc, CocommComon.lift_fst_snd,
    Category.id_comp]

/-- The comparison `eHom` is the identity for Fox's product. -/
lemma eHom_eq_id (X Y : CommComon V) : eHom X Y = 𝟙 _ :=
  CartesianMonoidalCategory.lift_fst_snd

/-- The multiplication of a group object is its structure morphism `μ`. -/
lemma mulHom_eq : mulHom H = μ[H.X].hom.hom := by
  rw [mulHom, eHom_eq_id, Category.id_comp]

/-- The unit of a group object is its structure morphism `η`. -/
lemma unitHom_eq : unitHom H = η[H.X].hom.hom := by
  have h : oneMor H = η[H.X] := by
    rw [oneMor, CategoryTheory.Hom.one_def]
    rw [toUnit_unique (toUnit (CommComon.trivial V)) (𝟙 (𝟙_ (CommComon V)))]
    exact Category.id_comp _
  rw [unitHom, h]

variable {H} {G : Grp (CommComon V)} (f : G ⟶ H)

/-- The underlying morphism of `V` of a morphism of group objects. -/
abbrev underlying : G.X.X ⟶ H.X.X := f.hom.hom.hom.hom

/-- **A morphism of group objects intertwines the multiplications.** -/
lemma mulHom_comp : mulHom G ≫ underlying f = (underlying f ⊗ₘ underlying f) ≫ mulHom H := by
  have h : μ[G.X] ≫ f.hom.hom = (f.hom.hom ⊗ₘ f.hom.hom) ≫ μ[H.X] :=
    IsMonHom.mul_hom (f := f.hom.hom)
  have h2 := congr(($h).hom.hom)
  rw [comp_hom_hom, comp_hom_hom, tensorHom_hom_hom] at h2
  rw [mulHom_eq, mulHom_eq, underlying, h2]

/-- **A morphism of group objects preserves the units.** -/
lemma unitHom_comp : unitHom G ≫ underlying f = unitHom H := by
  have h : η[G.X] ≫ f.hom.hom = η[H.X] := IsMonHom.one_hom (f := f.hom.hom)
  have h1 : oneMor G ≫ f.hom.hom = oneMor H := by
    rw [oneMor, oneMor, CategoryTheory.Hom.one_def, CategoryTheory.Hom.one_def, Category.assoc, h]
  exact congr(($h1).hom.hom)

instance : IsMonHom (underlying f) where
  one_hom := unitHom_comp f
  mul_hom := mulHom_comp f

instance : IsComonHom (underlying f) := f.hom.hom.hom.isComonHom_hom

end UlmerBialgebras.GrpHopf

namespace UlmerBialgebras.BimonHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory C]

/-- A monoid morphism between bimonoid objects, as a morphism of their monoids. -/
def monHomMk {X Y : C} [BimonObj X] [BimonObj Y] (f : X ⟶ Y) [IsMonHom f] :
    (Bimon.mk' X).X ⟶ (Bimon.mk' Y).X :=
  Mon.Hom.mk' f (by exact IsMonHom.one_hom f) (by exact IsMonHom.mul_hom f)

/-- A morphism which is both a monoid and a comonoid morphism, as a morphism of bimonoids. -/
def bimonHomMk {X Y : C} [BimonObj X] [BimonObj Y] (f : X ⟶ Y) [IsMonHom f] [IsComonHom f] :
    Bimon.mk' X ⟶ Bimon.mk' Y :=
  letI : ComonObj (Bimon.mk' X).X := Comon.comon (C := Mon C) (Bimon.mk' X)
  letI : ComonObj (Bimon.mk' Y).X := Comon.comon (C := Mon C) (Bimon.mk' Y)
  letI : IsComonHom (monHomMk f) :=
    { hom_counit := by ext; exact IsComonHom.hom_counit f
      hom_comul := by ext; exact IsComonHom.hom_comul f }
  Comon.Hom.mk (C := Mon C) (monHomMk f)

/-- The underlying morphism of `bimonHomMk f` is `f`. -/
@[simp]
lemma bimonHomMk_hom_hom {X Y : C} [BimonObj X] [BimonObj Y] (f : X ⟶ Y) [IsMonHom f]
    [IsComonHom f] : (bimonHomMk f).hom.hom = f := rfl

/-- A morphism which is both a monoid and a comonoid morphism, as a morphism of Hopf monoids. -/
def hopfHomMk {X Y : C} [HopfObj X] [HopfObj Y] (f : X ⟶ Y) [IsMonHom f] [IsComonHom f] :
    (Hopf.mk X : Hopf C) ⟶ Hopf.mk Y :=
  InducedCategory.homMk (bimonHomMk f)

/-- The underlying morphism of `hopfHomMk f` is `f`. -/
@[simp]
lemma hopfHomMk_hom_hom_hom {X Y : C} [HopfObj X] [HopfObj Y] (f : X ⟶ Y) [IsMonHom f]
    [IsComonHom f] : (hopfHomMk f).hom.hom.hom = f := rfl

end UlmerBialgebras.BimonHom

namespace UlmerBialgebras.GrpHopf

variable {V : Type u} [Category.{v} V] [MonoidalCategory.{v} V] [SymmetricCategory V]

/-- **The functor from group objects of `CommComon V` to Hopf monoids of `V`.** -/
noncomputable def toHopf : Grp (CommComon V) ⥤ Hopf V where
  obj H := Hopf.mk H.X.X
  map f := BimonHom.hopfHomMk (underlying f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying object of `toHopf.obj H` is `H.X.X`. -/
@[simp]
lemma toHopf_obj_X (H : Grp (CommComon V)) : (toHopf.obj H).X = H.X.X := rfl

/-- The underlying morphism of `toHopf.map f` is the underlying morphism of `f` in `V`. -/
@[simp]
lemma toHopf_map_hom {G H : Grp (CommComon V)} (f : G ⟶ H) :
    (toHopf.map f).hom.hom.hom = f.hom.hom.hom.hom := rfl

/-- The underlying morphism of a morphism of Hopf monoids is a morphism of comonoids. -/
lemma isComonHom_hopfHom {X Y : Hopf V} (φ : X ⟶ Y) : IsComonHom φ.hom.hom.hom where
  hom_counit := congr(($(φ.hom.isComonHom_hom.hom_counit)).hom)
  hom_comul := congr(($(φ.hom.isComonHom_hom.hom_comul)).hom)

instance : (toHopf (V := V)).Faithful where
  map_injective {G H} f g h := by
    apply Grp.hom_ext
    apply CategoryTheory.CommComon.hom_ext
    exact congr(($h).hom.hom.hom)

instance : (toHopf (V := V)).Full where
  map_surjective {G H} φ := by
    let u : G.X.X ⟶ H.X.X := φ.hom.hom.hom
    have : IsComonHom u := isComonHom_hopfHom φ
    have hu : IsMonHom u := inferInstanceAs (IsMonHom φ.hom.hom.hom)
    let c : G.X ⟶ H.X := UlmerBialgebras.CommComon.homMk u
    have : IsMonHom c :=
      { one_hom := by
          apply CategoryTheory.CommComon.hom_ext
          rw [comp_hom_hom, UlmerBialgebras.CommComon.homMk_hom, ← unitHom_eq, ← unitHom_eq]
          exact hu.one_hom
        mul_hom := by
          apply CategoryTheory.CommComon.hom_ext
          rw [comp_hom_hom, comp_hom_hom, UlmerBialgebras.CommComon.homMk_hom, tensorHom_hom_hom,
            ← mulHom_eq, ← mulHom_eq]
          exact hu.mul_hom }
    refine ⟨Grp.homMk c, ?_⟩
    apply InducedCategory.hom_ext
    apply Bimon.ext
    rfl

attribute [local instance] ComonObj.instTensorUnit

/-! ## The structure morphisms of `CommComon V` on underlying objects -/

/-- The underlying morphism of the pairing `lift f g` in `CommComon V` is `CocommComon.lift`. -/
lemma lift_hom_hom {T A B : CommComon V} (f : T ⟶ A) (g : T ⟶ B) :
    (lift f g).hom.hom = CocommComon.lift f.hom.hom g.hom.hom := rfl

/-- The left unitor of `CommComon V` has underlying morphism the left unitor of `V`. -/
lemma leftUnitor_hom_hom (M : CommComon V) : (λ_ M).hom.hom.hom = (λ_ M.X).hom := by
  rw [CartesianMonoidalCategory.leftUnitor_hom]
  change ε[𝟙_ V] ▷ M.X ≫ (λ_ M.X).hom = _
  simp

/-- The right unitor of `CommComon V` has underlying morphism the right unitor of `V`. -/
lemma rightUnitor_hom_hom (M : CommComon V) : (ρ_ M).hom.hom.hom = (ρ_ M.X).hom := by
  rw [CartesianMonoidalCategory.rightUnitor_hom]
  change M.X ◁ ε[𝟙_ V] ≫ (ρ_ M.X).hom = _
  simp

/-- Right whiskering in `CommComon V` has underlying morphism the right whiskering in `V`. -/
lemma whiskerRight_hom_hom {A B : CommComon V} (f : A ⟶ B) (M : CommComon V) :
    (f ▷ M).hom.hom = f.hom.hom ▷ M.X := by
  rw [← tensorHom_id]
  exact (tensorHom_hom_hom f (𝟙 M)).trans (MonoidalCategory.tensorHom_id _ _)

/-- Left whiskering in `CommComon V` has underlying morphism the left whiskering in `V`. -/
lemma whiskerLeft_hom_hom (M : CommComon V) {A B : CommComon V} (f : A ⟶ B) :
    (M ◁ f).hom.hom = M.X ◁ f.hom.hom := by
  rw [← id_tensorHom]
  exact (tensorHom_hom_hom (𝟙 M) f).trans (MonoidalCategory.id_tensorHom _ _)

/-- The associator of `CommComon V` is the comonoid morphism given by the associator of `V`. -/
lemma associator_hom_eq (A B C : CommComon V) :
    (α_ A B C).hom = UlmerBialgebras.CommComon.homMk (A := (A ⊗ B) ⊗ C) (B := A ⊗ (B ⊗ C))
      (α_ A.X B.X C.X).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [CartesianMonoidalCategory.associator_hom_fst]
    ext
    exact (CocommComon.associator_hom_fst A.X B.X C.X).symm
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.associator_hom_snd_fst]
      ext
      exact (CocommComon.associator_hom_snd_fst A.X B.X C.X).symm
    · rw [Category.assoc, Category.assoc, CartesianMonoidalCategory.associator_hom_snd_snd]
      ext
      exact (CocommComon.associator_hom_snd_snd A.X B.X C.X).symm

/-- The associator of `CommComon V` has underlying morphism the associator of `V`. -/
lemma associator_hom_hom (A B C : CommComon V) :
    (α_ A B C).hom.hom.hom = (α_ A.X B.X C.X).hom := by
  rw [associator_hom_eq]
  rfl

/-! ## From cocommutative Hopf monoids to group objects -/

section OfHopf

variable (X : V) [HopfObj X] [IsCommComonObj X]

/-- The multiplication of a bimonoid is a morphism of comonoids. -/
instance isComonHom_mul : IsComonHom μ[X] where
  hom_counit := BimonObj.mul_counit X
  hom_comul := by rw [BimonObj.mul_comul, Comon.tensorObj_comul, Category.assoc]

/-- The unit of a bimonoid is a morphism of comonoids. -/
instance isComonHom_one : IsComonHom η[X] where
  hom_counit := by rw [BimonObj.one_counit]; rfl
  hom_comul := by rw [BimonObj.one_comul]; rfl

/-- **The antipode of a cocommutative Hopf monoid is a morphism of comonoids.** -/
instance isComonHom_antipode : IsComonHom 𝒮[X] where
  hom_counit := HopfObj.antipode_counit X
  hom_comul := by
    rw [HopfObj.antipode_comul, ← Category.assoc, IsCommComonObj.comul_comm]

/-- The cocommutative comonoid underlying a cocommutative Hopf monoid. -/
abbrev comonOf : CommComon V := CommComon.mk X

/-- The monoid structure in `CommComon V` of a cocommutative Hopf monoid. -/
noncomputable instance monObjOf : MonObj (comonOf X) where
  one := @UlmerBialgebras.CommComon.homMk V _ _ _ (𝟙_ (CommComon V)) (comonOf X) η[X]
    (isComonHom_one X)
  mul := UlmerBialgebras.CommComon.homMk (A := comonOf X ⊗ comonOf X) (B := comonOf X) μ[X]
  one_mul := by
    ext
    rw [comp_hom_hom, whiskerRight_hom_hom, leftUnitor_hom_hom]
    exact MonObj.one_mul X
  mul_one := by
    ext
    rw [comp_hom_hom, whiskerLeft_hom_hom, rightUnitor_hom_hom]
    exact MonObj.mul_one X
  mul_assoc := by
    ext
    rw [comp_hom_hom, comp_hom_hom, comp_hom_hom, whiskerRight_hom_hom, whiskerLeft_hom_hom,
      associator_hom_hom]
    exact MonObj.mul_assoc X

/-- The group structure in `CommComon V` of a cocommutative Hopf monoid: the inverse is the
antipode. -/
noncomputable instance grpObjOf : GrpObj (comonOf X) where
  inv := UlmerBialgebras.CommComon.homMk (A := comonOf X) (B := comonOf X) 𝒮[X]
  left_inv := by
    ext
    rw [comp_hom_hom, comp_hom_hom, lift_hom_hom,
      toUnit_unique (toUnit (comonOf X)) (toTrivial (comonOf X))]
    rw [CocommComon.lift, UlmerBialgebras.CommComon.homMk_hom, id_hom_hom]
    have h := HopfObj.antipode_left X
    rw [← tensorHom_id] at h
    exact (Category.assoc _ _ _).trans h
  right_inv := by
    ext
    rw [comp_hom_hom, comp_hom_hom, lift_hom_hom,
      toUnit_unique (toUnit (comonOf X)) (toTrivial (comonOf X))]
    rw [CocommComon.lift, UlmerBialgebras.CommComon.homMk_hom, id_hom_hom]
    have h := HopfObj.antipode_right X
    rw [← id_tensorHom] at h
    exact (Category.assoc _ _ _).trans h

/-- **The group object of `CommComon V` of a cocommutative Hopf monoid.** -/
noncomputable abbrev ofHopf : Grp (CommComon V) := Grp.mk (comonOf X)

end OfHopf

/-- The Hopf monoid of the group object of a cocommutative Hopf monoid is the Hopf monoid itself:
the identity is a morphism of Hopf monoids. -/
noncomputable def toHopfOfHopfIso (A : Hopf V) [IsCommComonObj A.X] :
    toHopf.obj (ofHopf A.X) ≅ A :=
  haveI h₁ : @IsMonHom V _ _ (ofHopf A.X).X.X A.X (instHopfObj (ofHopf A.X)).toMonObj
      A.hopf.toMonObj (𝟙 A.X) :=
    @IsMonHom.mk V _ _ (ofHopf A.X).X.X A.X (instHopfObj (ofHopf A.X)).toMonObj
      A.hopf.toMonObj (𝟙 A.X)
      ((Category.comp_id (unitHom (ofHopf A.X))).trans (unitHom_eq (ofHopf A.X)))
      ((Category.comp_id _).trans ((mulHom_eq (ofHopf A.X)).trans
        (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]; rfl)))
  haveI h₂ : @IsMonHom V _ _ A.X (ofHopf A.X).X.X A.hopf.toMonObj
      (instHopfObj (ofHopf A.X)).toMonObj (𝟙 A.X) :=
    @IsMonHom.mk V _ _ A.X (ofHopf A.X).X.X A.hopf.toMonObj
      (instHopfObj (ofHopf A.X)).toMonObj (𝟙 A.X)
      ((Category.comp_id η[A.X]).trans (unitHom_eq (ofHopf A.X)).symm)
      ((Category.comp_id μ[A.X]).trans ((mulHom_eq (ofHopf A.X)).symm.trans
        (by rw [MonoidalCategory.id_tensorHom_id, Category.id_comp]; rfl)))
  { hom := @BimonHom.hopfHomMk V _ _ _ _ _ (instHopfObj (ofHopf A.X)) A.hopf (𝟙 A.X) h₁
      inferInstance
    inv := @BimonHom.hopfHomMk V _ _ _ _ _ A.hopf (instHopfObj (ofHopf A.X)) (𝟙 A.X) h₂
      inferInstance
    hom_inv_id := by
      apply InducedCategory.hom_ext
      apply Bimon.ext
      exact Category.comp_id _
    inv_hom_id := by
      apply InducedCategory.hom_ext
      apply Bimon.ext
      exact Category.comp_id _ }

/-! ## The equivalence -/

variable (V) in
/-- The property of a Hopf monoid of being cocommutative. -/
def cocommHopf : ObjectProperty (Hopf V) := fun A => IsCommComonObj A.X

variable (V) in
/-- **The category of cocommutative Hopf monoids of `V`**, as a full subcategory of `Hopf V`. -/
abbrev CocommHopf := (cocommHopf V).FullSubcategory

/-- The functor from group objects of `CommComon V` to cocommutative Hopf monoids. -/
noncomputable abbrev toCocommHopf : Grp (CommComon V) ⥤ CocommHopf V :=
  (cocommHopf V).lift toHopf (fun H => (inferInstance : IsCommComonObj H.X.X))

instance : (toCocommHopf (V := V)).EssSurj where
  mem_essImage B := by
    have : IsCommComonObj B.obj.X := B.property
    exact ⟨ofHopf B.obj.X, ⟨(cocommHopf V).fullyFaithfulι.preimageIso
      (X := toCocommHopf.obj (ofHopf B.obj.X)) (Y := B) (toHopfOfHopfIso B.obj)⟩⟩

instance : (toCocommHopf (V := V)).Faithful :=
  Functor.Faithful.of_comp_iso
    ((cocommHopf V).liftCompιIso toHopf (fun H => (inferInstance : IsCommComonObj H.X.X)))

instance : (toCocommHopf (V := V)).Full :=
  Functor.Full.of_comp_faithful_iso
    ((cocommHopf V).liftCompιIso toHopf (fun H => (inferInstance : IsCommComonObj H.X.X)))

instance : (toCocommHopf (V := V)).IsEquivalence where

/-- **Group objects of cocommutative comonoids are cocommutative Hopf monoids**:
`Grp (CommComon V) ≌ CocommHopf V`, for any symmetric monoidal category `V`. -/
noncomputable def grpCommComonEquivCocommHopf : Grp (CommComon V) ≌ CocommHopf V :=
  (toCocommHopf (V := V)).asEquivalence

end UlmerBialgebras.GrpHopf
