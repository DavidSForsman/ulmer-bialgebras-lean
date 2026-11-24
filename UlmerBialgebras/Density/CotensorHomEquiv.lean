module

public import UlmerBialgebras.Density.ACotensor

/-!
# The hom-set equivalence of a right Kan extension

A universal cotensor arrow represents restriction followed by a hom functor. This is the
hom-set bijection for the right Kan extension used in the proof of Theorem 7.4.

## Main results

* `UlmerBialgebras.IsCotensorUniv.homEquiv`: the universal-arrow hom-set equivalence.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras.IsCotensorUniv

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  {x y c : Obj} {r : x ⟶ y} {m : x ⟶ c} {t : y ⟶ c} {ε : r ≫ t ⟶ m}

/-- A universal cotensor arrow gives the hom-set equivalence of the right Kan extension. -/
noncomputable def homEquiv (h : IsCotensorUniv r ε) (n : y ⟶ c) :
    (r ≫ n ⟶ m) ≃ (n ⟶ t) where
  toFun := h.lift
  invFun β := (r ◁ β) ≫ ε
  left_inv := h.fac
  right_inv _ := (h.lift_unique rfl).symm

end UlmerBialgebras.IsCotensorUniv
