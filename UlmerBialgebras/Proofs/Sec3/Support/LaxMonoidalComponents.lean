module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Components of lax monoidal model maps

These expressions record the identity components of the transports in the interpretation of
monoidal terms in `Cat`. Naming the expressions gives the component calculations their types
before the transports are simplified.

## Main results

* `UlmerBialgebras.LaxMonoidalComponents.tensorComponent`
* `UlmerBialgebras.LaxMonoidalComponents.unitComponent`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10
-/

@[expose] public section

namespace UlmerBialgebras.LaxMonoidalComponents

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D] [MonoidalCategory D]
  (F : C ⥤ D) [F.LaxMonoidal]

/-- A component with the identity transports at its two ends. -/
abbrev transportComponent {X Y : D} (f : X ⟶ Y) : X ⟶ Y :=
  𝟙 X ≫ f ≫ 𝟙 Y

/-- The tensor comparison on two components, with the transports from the product lift
and the tensorator. -/
abbrev tensorComponent {X Y : C} {P Q : D} (f : P ⟶ F.obj X) (g : Q ⟶ F.obj Y) :
    P ⊗ Q ⟶ F.obj (X ⊗ Y) :=
  (transportComponent f ⊗ₘ transportComponent g) ≫ transportComponent (μ F X Y)

/-- The unit comparison, with the identity component of the nullary operation. -/
abbrev unitComponent : 𝟙_ D ⟶ F.obj (𝟙_ C) :=
  𝟙 _ ≫ transportComponent (ε F)

end UlmerBialgebras.LaxMonoidalComponents
