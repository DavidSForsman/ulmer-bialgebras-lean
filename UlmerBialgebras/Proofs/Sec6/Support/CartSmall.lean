module

public import UlmerBialgebras.Proofs.Sec6.Support.CartTransport

/-!
# A cartesian category with lifted objects and hom-sets

For a cartesian category `B`, `CartSmall.{w} B` is `AsSmall.{w} B` (objects and hom-sets lifted to
`Type (max w v u)`) with the cartesian monoidal structure of `B`, transported along
`AsSmall.equiv`. The transport is strict: tensor products, projections and lifts are those of `B`,
lifted. So every property of `B` stated through its monoidal structure holds for `CartSmall B` by
`inferInstanceAs` along `cartSmallEquiv`, as for `CartU` (which lifts only the hom-sets).

## Main definitions

* `UlmerBialgebras.Paper.Cart.CartSmall`
* `UlmerBialgebras.Paper.Cart.cartSmallEquiv`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (the categories it applies to, in any universe)
-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Limits

namespace UlmerBialgebras.Paper.Cart

variable (B : Type u) [Category.{v} B] [CartesianMonoidalCategory B]

/-- `B` with objects and hom-sets lifted to `Type (max w v u)`, with the monoidal structure of
`B`. -/
abbrev CartSmall : Type (max w v u) :=
  Monoidal.Transported (AsSmall.equiv.{v, u, w} : B ≌ AsSmall.{w} B)

/-- The identification of `B` with `CartSmall B`, a monoidal equivalence. -/
abbrev cartSmallEquiv : B ≌ CartSmall.{w} B :=
  Monoidal.equivalenceTransported (AsSmall.equiv.{v, u, w} : B ≌ AsSmall.{w} B)

variable {B}

/-- The object of `B` underlying an object of `CartSmall B`. -/
abbrev CartSmall.down (X : CartSmall.{w} B) : B := AsSmall.down.obj X

/-- The tensor unit of `CartSmall B` is terminal. -/
def cartSmallIsTerminal : IsTerminal (𝟙_ (CartSmall.{w} B)) :=
  IsTerminal.ofUniqueHom (fun X => ULift.up (toUnit (CartSmall.down X)))
    fun _ _ => ULift.ext (toUnit_unique _ _)

/-! The transported structure of `CartSmall B`, on the underlying morphisms of `B`. -/

/-- Composition in `CartSmall B` is composition in `B`. -/
@[simp] lemma cartSmall_comp_down {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {X Y Z : CartSmall.{w} C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).down = f.down ≫ g.down := rfl

/-- Left whiskering in `CartSmall B` is left whiskering in `B`. -/
@[simp] lemma cartSmall_whiskerLeft_down (X : CartSmall.{w} B) {Y Z : CartSmall.{w} B}
    (f : Y ⟶ Z) : (X ◁ f).down = CartSmall.down X ◁ f.down := rfl

/-- Right whiskering in `CartSmall B` is right whiskering in `B`. -/
@[simp] lemma cartSmall_whiskerRight_down {X Y : CartSmall.{w} B} (f : X ⟶ Y)
    (Z : CartSmall.{w} B) : (f ▷ Z).down = f.down ▷ CartSmall.down Z := rfl

/-- The right unitor of `CartSmall B` is the right unitor of `B`. -/
@[simp] lemma cartSmall_rightUnitor_down (X : CartSmall.{w} B) :
    (ρ_ X).hom.down = (ρ_ (CartSmall.down X)).hom :=
  (rfl : _ = (CartSmall.down X ◁ 𝟙 (𝟙_ B) ≫ (ρ_ (CartSmall.down X)).hom) ≫ 𝟙 _).trans (by simp)

/-- The left unitor of `CartSmall B` is the left unitor of `B`. -/
@[simp] lemma cartSmall_leftUnitor_down (X : CartSmall.{w} B) :
    (λ_ X).hom.down = (λ_ (CartSmall.down X)).hom :=
  (rfl : _ = (𝟙 (𝟙_ B) ▷ CartSmall.down X ≫ (λ_ (CartSmall.down X)).hom) ≫ 𝟙 _).trans (by simp)

/-- The map to the terminal tensor unit of `CartSmall B` is `toUnit` in `B`. -/
@[simp] lemma cartSmallIsTerminal_from_down (X : CartSmall.{w} B) :
    (cartSmallIsTerminal.from X).down = toUnit (CartSmall.down X) := rfl

instance : SemiCartesianMonoidalCategory (CartSmall.{w} B) where
  isTerminalTensorUnit := cartSmallIsTerminal
  fst X Y := ULift.up (fst (CartSmall.down X) (CartSmall.down Y))
  snd X Y := ULift.up (snd (CartSmall.down X) (CartSmall.down Y))
  fst_def X Y := ULift.ext <| by
    simp only [cartSmall_comp_down, cartSmall_whiskerLeft_down, cartSmall_rightUnitor_down,
      cartSmallIsTerminal_from_down]
    exact fst_def (CartSmall.down X) (CartSmall.down Y)
  snd_def X Y := ULift.ext <| by
    simp only [cartSmall_comp_down, cartSmall_whiskerRight_down, cartSmall_leftUnitor_down,
      cartSmallIsTerminal_from_down]
    exact snd_def (CartSmall.down X) (CartSmall.down Y)

/-- `CartSmall B` has the products of `B`. -/
def cartSmallIsLimit (X Y : CartSmall.{w} B) :
    IsLimit (BinaryFan.mk (SemiCartesianMonoidalCategory.fst X Y)
      (SemiCartesianMonoidalCategory.snd X Y)) :=
  BinaryFan.IsLimit.mk _ (fun f g => ULift.up (lift f.down g.down))
    (fun f g => ULift.ext (lift_fst f.down g.down)) (fun f g => ULift.ext (lift_snd f.down g.down))
    fun f g _ h₁ h₂ => ULift.ext (hom_ext _ _
      ((ULift.ext_iff.1 h₁).trans (lift_fst f.down g.down).symm)
      ((ULift.ext_iff.1 h₂).trans (lift_snd f.down g.down).symm))

instance : CartesianMonoidalCategory (CartSmall.{w} B) where
  tensorProductIsBinaryProduct := cartSmallIsLimit

end UlmerBialgebras.Paper.Cart
