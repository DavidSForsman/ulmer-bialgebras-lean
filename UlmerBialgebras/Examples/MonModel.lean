module

public import Mathlib.CategoryTheory.Monoidal.Category
public import UlmerBialgebras.Examples.MonSignature
public import UlmerBialgebras.Models.CatPIE

/-!
# A monoidal category as a model of the monoidal 2-signature

Examples 3.20 (1) of *A Syntactic Approach to Ulmer's Bialgebras*, semantic half: a monoidal
category `C` is a `Σ_Mon`-model in the 2-category `CAT`, with

* `M(□)` the tensor product, viewed as a functor on the product `∏_{i : Fin 2} C`,
* `M(I)` the constant functor at the unit object, on the empty product,
* `M(α)`, `M(λ)`, `M(ρ)` the associator and the two unitors.

The objects of `M^σ` are then triples `(x, m : x ⊗ x → x, e : 𝟙_ C → x)`, i.e. pointed
magmas in `C`, and `M^T` is the full subcategory of internal monoids; that identification
is carried out in `MonEquiv.lean`.

## Main results

* `UlmerBialgebras.MonEx.tensFunctor`, `UlmerBialgebras.MonEx.unitFunctor`: the tensor product and
  the unit object, as functors on finite products of `C`.
* `UlmerBialgebras.MonEx.monModel`: a monoidal category is a `Σ_Mon`-model in `CAT`
  (Examples 3.20 (1)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (1)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

namespace MonEx

open CategoryTheory MonoidalCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The tensor product as a functor on the product of two copies of `C`. -/
@[simps]
def tensFunctor : (∀ _ : Fin 2, C) ⥤ C where
  obj p := p 0 ⊗ p 1
  map f := f 0 ⊗ₘ f 1

/-- The unit object as a functor on the empty product. -/
@[simps]
def unitFunctor : (∀ _ : Fin 0, C) ⥤ C where
  obj _ := 𝟙_ C
  map _ := 𝟙 _

/-- The interpretation of the category and functor symbols of `Σ_Mon` in a monoidal
category. -/
def monPreModel : PreModel twoSig Cat.{v, u} where
  obj := fun _ => Cat.of C
  fn := fun B => match B with
    | .tens => (tensFunctor C).toCatHom
    | .unit => (unitFunctor C).toCatHom

/-- Reading off a component of an environment as an object of `C`. -/
def ev {n : ℕ} (p : ∀ _ : Fin n, (Cat.of C : Type u)) (i : Fin n) : C := p i

/-- Reading off a component of a morphism of environments as a morphism of `C`. -/
def evMap {n : ℕ} {p q : ∀ _ : Fin n, (Cat.of C : Type u)} (f : p ⟶ q) (i : Fin n) :
    ev C p i ⟶ ev C q i := f i

variable {C} in
/-- Naturality of the left unitor, in the form of the interpretation of `λ`. -/
lemma lunit_naturality {n : ℕ} {p q : ∀ _ : Fin n, (Cat.of C : Type u)} (f : p ⟶ q)
    (i : Fin n) :
    (𝟙 (𝟙_ C) ⊗ₘ evMap C f i) ≫ (λ_ (ev C q i)).hom = (λ_ (ev C p i)).hom ≫ evMap C f i := by
  rw [id_tensorHom]
  exact leftUnitor_naturality (evMap C f i)

variable {C} in
/-- Naturality of the inverse left unitor, in the form of the interpretation of `λ⁻¹`. -/
lemma lunit_inv_naturality {n : ℕ} {p q : ∀ _ : Fin n, (Cat.of C : Type u)} (f : p ⟶ q)
    (i : Fin n) :
    evMap C f i ≫ (λ_ (ev C q i)).inv = (λ_ (ev C p i)).inv ≫ (𝟙 (𝟙_ C) ⊗ₘ evMap C f i) := by
  rw [id_tensorHom]
  exact leftUnitor_inv_naturality (evMap C f i)

variable {C} in
/-- Naturality of the right unitor, in the form of the interpretation of `ρ`. -/
lemma runit_naturality {n : ℕ} {p q : ∀ _ : Fin n, (Cat.of C : Type u)} (f : p ⟶ q)
    (i : Fin n) :
    (evMap C f i ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (ev C q i)).hom = (ρ_ (ev C p i)).hom ≫ evMap C f i := by
  rw [tensorHom_id]
  exact rightUnitor_naturality (evMap C f i)

variable {C} in
/-- Naturality of the inverse right unitor, in the form of the interpretation of `ρ⁻¹`. -/
lemma runit_inv_naturality {n : ℕ} {p q : ∀ _ : Fin n, (Cat.of C : Type u)} (f : p ⟶ q)
    (i : Fin n) :
    evMap C f i ≫ (ρ_ (ev C q i)).inv = (ρ_ (ev C p i)).inv ≫ (evMap C f i ⊗ₘ 𝟙 (𝟙_ C)) := by
  rw [tensorHom_id]
  exact rightUnitor_inv_naturality (evMap C f i)

/-- The associator, as the interpretation of the transformation symbol `α`. -/
def assocCell :
    (monPreModel C).interp ((monPreModel C).Pctx TrSym.assoc).π (twoSig.trsrc TrSym.assoc) ⟶
      (monPreModel C).interp ((monPreModel C).Pctx TrSym.assoc).π (twoSig.trtgt TrSym.assoc) where
  toNatTrans := {
    app p := (α_ (ev C p 0) (ev C p 1) (ev C p 2)).hom
    naturality p q f := by
      dsimp [monPreModel, tensFunctor, ev]
      exact associator_naturality (evMap C f 0) (evMap C f 1) (evMap C f 2) }

/-- The right unitor, as the interpretation of the transformation symbol `ρ`. -/
def runitCell :
    (monPreModel C).interp ((monPreModel C).Pctx TrSym.runit).π (twoSig.trsrc TrSym.runit) ⟶
      (monPreModel C).interp ((monPreModel C).Pctx TrSym.runit).π (twoSig.trtgt TrSym.runit) where
  toNatTrans := {
    app p := (ρ_ (ev C p 0)).hom
    naturality p q f := by
      change (evMap C f 0 ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (ev C q 0)).hom =
        (ρ_ (ev C p 0)).hom ≫ evMap C f 0
      rw [tensorHom_id]
      exact rightUnitor_naturality (evMap C f 0) }

/-- The left unitor, as the interpretation of the transformation symbol `λ`. -/
def lunitCell :
    (monPreModel C).interp ((monPreModel C).Pctx TrSym.lunit).π (twoSig.trsrc TrSym.lunit) ⟶
      (monPreModel C).interp ((monPreModel C).Pctx TrSym.lunit).π (twoSig.trtgt TrSym.lunit) where
  toNatTrans := {
    app p := (λ_ (ev C p 0)).hom
    naturality p q f := by
      change (𝟙 (𝟙_ C) ⊗ₘ evMap C f 0) ≫ (λ_ (ev C q 0)).hom =
        (λ_ (ev C p 0)).hom ≫ evMap C f 0
      rw [id_tensorHom]
      exact leftUnitor_naturality (evMap C f 0) }

/-- **A monoidal category is a `Σ_Mon`-model in `CAT`.** -/
def monModel : Model twoSig Cat.{v, u} where
  toPreModel := monPreModel C
  tr := fun a => match a with
    | .assoc => assocCell C
    | .lunit => lunitCell C
    | .runit => runitCell C

/-- Evaluating the tensor functor symbol of `MonEx.monPreModel` on an object family tensors
indices `0` and `1`. -/
lemma monPreModel_fn_tens_obj
    (X : ∀ i : Fin (twoSig.arn FunSym.tens),
      ((monPreModel C).obj (twoSig.art FunSym.tens i) : Type u)) :
    ((monPreModel C).fn FunSym.tens).toFunctor.obj X =
      MonoidalCategoryStruct.tensorObj (C := C) (X 0) (X 1) := rfl

/-- Evaluating the tensor functor symbol of `MonEx.monPreModel` on a morphism family tensors
indices `0` and `1`. -/
lemma monPreModel_fn_tens_map
    {X Y : ∀ i : Fin (twoSig.arn FunSym.tens),
      ((monPreModel C).obj (twoSig.art FunSym.tens i) : Type u)} (f : X ⟶ Y) :
    ((monPreModel C).fn FunSym.tens).toFunctor.map f =
      MonoidalCategoryStruct.tensorHom (C := C) (f 0) (f 1) := rfl

/-- Evaluating the unit functor symbol of `MonEx.monPreModel` on an empty object family gives
`𝟙_ C`. -/
lemma monPreModel_fn_unit_obj
    (X : ∀ i : Fin (twoSig.arn FunSym.unit),
      ((monPreModel C).obj (twoSig.art FunSym.unit i) : Type u)) :
    ((monPreModel C).fn FunSym.unit).toFunctor.obj X = 𝟙_ C := rfl

/-- Evaluating the unit functor symbol of `MonEx.monPreModel` on an empty morphism family gives
`𝟙 (𝟙_ C)`. -/
lemma monPreModel_fn_unit_map
    {X Y : ∀ i : Fin (twoSig.arn FunSym.unit),
      ((monPreModel C).obj (twoSig.art FunSym.unit i) : Type u)} (f : X ⟶ Y) :
    ((monPreModel C).fn FunSym.unit).toFunctor.map f = 𝟙 (𝟙_ C) := rfl

/-- Evaluating the `assoc` transformation cell of `MonEx.monModel` gives the associator. -/
lemma monModel_tr_assoc_app (p : ((monModel C).Pctx TrSym.assoc).pt) :
    ((monModel C).tr TrSym.assoc).toNatTrans.app p =
      (MonoidalCategoryStruct.associator (C := C) (p 0) (p 1) (p 2)).hom := rfl

/-- Evaluating the `lunit` transformation cell of `MonEx.monModel` gives the left unitor. -/
lemma monModel_tr_lunit_app (p : ((monModel C).Pctx TrSym.lunit).pt) :
    ((monModel C).tr TrSym.lunit).toNatTrans.app p =
      (MonoidalCategoryStruct.leftUnitor (C := C) (p 0)).hom := rfl

/-- Evaluating the `runit` transformation cell of `MonEx.monModel` gives the right unitor. -/
lemma monModel_tr_runit_app (p : ((monModel C).Pctx TrSym.runit).pt) :
    ((monModel C).tr TrSym.runit).toNatTrans.app p =
      (MonoidalCategoryStruct.rightUnitor (C := C) (p 0)).hom := rfl

end MonEx

end UlmerBialgebras
