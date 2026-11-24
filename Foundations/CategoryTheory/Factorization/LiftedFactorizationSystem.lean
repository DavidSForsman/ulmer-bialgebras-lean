module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Factorization systems lifted along a faithful functor

Let `U : D ⥤ C` be a faithful functor and let

* `E' = U⁻¹(Epi)`   -- the morphisms of `D` whose underlying morphism of `C` is an epimorphism,
* `M' = U⁻¹(Mono)`  -- the morphisms of `D` whose underlying morphism of `C` is a monomorphism.

When `(E', M')` is an orthogonal factorization system on `D` (for instance when `U` is the
forgetful functor from a category of Hopf monoids to the underlying symmetric monoidal abelian
category, whose `(Epi, Mono)` factorization system is being lifted), one asks when `(E', M')` is
the **extremal epimorphism / monomorphism factorization system** of `D`.

Of this theory, the present file only keeps the notion used elsewhere in the development.

## Main results

* `CategoryTheory.LiftedOFS.IsExtremalEpi`: extremal epimorphisms, an epimorphism admitting no
  nontrivial monomorphic factorization, as a compatibility name for Mathlib’s
  `CategoryTheory.ExtremalEpi`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 6.6 (1) and the discussion after Definition 6.4
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

section
namespace CategoryTheory.LiftedOFS

variable {D : Type u₁} [Category.{v₁} D] {C : Type u₂} [Category.{v₂} C]

/-- Compatibility name for Mathlib's extremal epimorphisms. -/
abbrev IsExtremalEpi {X Y : D} (f : X ⟶ Y) := ExtremalEpi f

namespace IsExtremalEpi

/-- Construct an extremal epimorphism from an epi and its mono-factorization property. -/
theorem mk {X Y : D} {f : X ⟶ Y} (hf : Epi f)
    (h : ∀ {Z : D} (e : X ⟶ Z) (m : Z ⟶ Y), Mono m → e ≫ m = f → IsIso m) :
    IsExtremalEpi f := by
  refine { toEpi := hf, isIso := ?_ }
  intro Z e m fac
  exact h e m inferInstance fac

/-- The underlying epimorphism. -/
theorem epi {X Y : D} {f : X ⟶ Y} (hf : IsExtremalEpi f) : Epi f := by
  let := hf
  infer_instance

/-- A monomorphic factor of an extremal epimorphism is an isomorphism. -/
theorem isIso_of_mono {X Y : D} {f : X ⟶ Y} (hf : IsExtremalEpi f)
    {Z : D} (e : X ⟶ Z) (m : Z ⟶ Y) (hm : Mono m) (fac : e ≫ m = f) : IsIso m := by
  let := hf
  let := hm
  exact ExtremalEpi.isIso f e m fac

end IsExtremalEpi

end CategoryTheory.LiftedOFS
end
