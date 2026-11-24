module

public import UlmerBialgebras.Paper.Sec5DefsCart
public import UlmerBialgebras.Models.UniverseChangeSig
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!
# The cartesian model of a category with lifted hom-sets

For a cartesian category `B` in `Cat.{v, max u v}`, `CartU B` is `B` with hom-sets lifted to
`Type (max u v)` and the cartesian monoidal structure of `B`, lifted. Its cartesian `Σ_Cart`-model
is the change of universe of the cartesian model of `B` (`Cart.cartModel_cartU`).

## Main results

* `UlmerBialgebras.Paper.Cart.CartU`
* `UlmerBialgebras.Paper.Cart.cartModel_cartU`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.19 (`Σ_Cart`)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits UlmerBialgebras.UnivChange

namespace UlmerBialgebras.Paper.Cart

variable (B : Type (max u v)) [Category.{v} B] [CartesianMonoidalCategory B]

/-- `B` with hom-sets lifted to `Type (max u v)`, with the monoidal structure of `B`. -/
abbrev CartU : Type (max u v) :=
  Monoidal.Transported (ULiftHom.equiv : B ≌ ULiftHom.{max u v} B)

/-- The identification of `B` with `CartU B`. -/
abbrev cartUEquiv : B ≌ CartU.{v, u} B :=
  Monoidal.equivalenceTransported (ULiftHom.equiv : B ≌ ULiftHom.{max u v} B)

variable {B}

/-- The object of `B` underlying an object of `CartU B`. -/
abbrev CartU.down (X : CartU.{v, u} B) : B := ULiftHom.objDown X

/-- The tensor unit of `CartU B` is terminal. -/
def cartUIsTerminal : IsTerminal (𝟙_ (CartU.{v, u} B)) :=
  IsTerminal.ofUniqueHom (fun X => ULift.up (toUnit (CartU.down X)))
    fun _ _ => ULift.ext (toUnit_unique _ _)

instance : SemiCartesianMonoidalCategory (CartU.{v, u} B) where
  isTerminalTensorUnit := cartUIsTerminal
  fst X Y := ULift.up (fst (CartU.down X) (CartU.down Y))
  snd X Y := ULift.up (snd (CartU.down X) (CartU.down Y))
  fst_def X Y := by
    apply ULift.ext
    refine (fst_def (CartU.down X) (CartU.down Y)).trans ?_
    change _ = (CartU.down X ◁ toUnit _) ≫ ((CartU.down X ◁ 𝟙 (𝟙_ B) ≫ (ρ_ _).hom) ≫ 𝟙 _)
    simp
    rfl
  snd_def X Y := by
    apply ULift.ext
    refine (snd_def (CartU.down X) (CartU.down Y)).trans ?_
    change _ = (toUnit _ ▷ CartU.down Y) ≫ ((𝟙 (𝟙_ B) ▷ CartU.down Y ≫ (λ_ _).hom) ≫ 𝟙 _)
    simp
    rfl

/-- `CartU B` has the products of `B`. -/
def cartUIsLimit (X Y : CartU.{v, u} B) :
    IsLimit (BinaryFan.mk (SemiCartesianMonoidalCategory.fst X Y)
      (SemiCartesianMonoidalCategory.snd X Y)) :=
  BinaryFan.IsLimit.mk _ (fun f g => ULift.up (lift f.down g.down))
    (fun f g => ULift.ext (lift_fst f.down g.down)) (fun f g => ULift.ext (lift_snd f.down g.down))
    fun f g _ h₁ h₂ => ULift.ext (hom_ext _ _
      ((ULift.ext_iff.1 h₁).trans (lift_fst f.down g.down).symm)
      ((ULift.ext_iff.1 h₂).trans (lift_snd f.down g.down).symm))

instance : CartesianMonoidalCategory (CartU.{v, u} B) where
  tensorProductIsBinaryProduct := cartUIsLimit

/-- The binary product lift in `CartU B` is the lifted binary product lift in `B`. -/
lemma cartU_lift {X Y Z : CartU.{v, u} B} (f : X ⟶ Y) (g : X ⟶ Z) :
    lift f g = ULift.up (lift f.down g.down) := rfl

/-- The first projection in `CartU B` is the lifted first projection in `B`. -/
lemma cartU_fst (X Y : CartU.{v, u} B) :
    fst X Y = ULift.up (fst (CartU.down X) (CartU.down Y)) := rfl

/-- The second projection in `CartU B` is the lifted second projection in `B`. -/
lemma cartU_snd (X Y : CartU.{v, u} B) :
    snd X Y = ULift.up (snd (CartU.down X) (CartU.down Y)) := rfl

/-- The unique morphism to the terminal object in `CartU B` is the lifted `toUnit` in `B`. -/
lemma cartU_toUnit (X : CartU.{v, u} B) : toUnit X = ULift.up (toUnit (CartU.down X)) := rfl

/-- The `diag` 2-cell of `cartModel (CartU B)` agrees with that of `upModel (cartModel B)`. -/
lemma cartModel_cartU_tr_diag : HEq ((cartModel (CartU.{v, u} B)).tr .diag)
    ((upModel.{v, u} (cartModel B)).tr .diag) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  rfl

/-- The `proj₁` 2-cell of `cartModel (CartU B)` agrees with that of `upModel (cartModel B)`. -/
lemma cartModel_cartU_tr_proj₁ : HEq ((cartModel (CartU.{v, u} B)).tr .proj₁)
    ((upModel.{v, u} (cartModel B)).tr .proj₁) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  rfl

/-- The `proj₂` 2-cell of `cartModel (CartU B)` agrees with that of `upModel (cartModel B)`. -/
lemma cartModel_cartU_tr_proj₂ : HEq ((cartModel (CartU.{v, u} B)).tr .proj₂)
    ((upModel.{v, u} (cartModel B)).tr .proj₂) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  rfl

/-- The `term` 2-cell of `cartModel (CartU B)` agrees with that of `upModel (cartModel B)`. -/
lemma cartModel_cartU_tr_term : HEq ((cartModel (CartU.{v, u} B)).tr .term)
    ((upModel.{v, u} (cartModel B)).tr .term) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  rfl

/-- **The cartesian model of `CartU B` is the change of universe of the cartesian model of
`B`.** -/
theorem cartModel_cartU : cartModel (CartU.{v, u} B) = upModel.{v, u} (cartModel B) := by
  refine Model.ext_heq ?_ fun a => ?_
  · change PreModel.mk _ _ = PreModel.mk _ _
    congr 1
    funext F
    cases F <;> rfl
  · cases a
    · exact cartModel_cartU_tr_diag
    · exact cartModel_cartU_tr_proj₁
    · exact cartModel_cartU_tr_proj₂
    · exact cartModel_cartU_tr_term

end UlmerBialgebras.Paper.Cart
