module

public import UlmerBialgebras.Factorization.Representable

/-!
# Representable regularity and exactness lift along PIE limits

A representable form of Section 6 of *A Syntactic Approach to Ulmer's Bialgebras* (not a
numbered result of the current version of the paper).  `Representable.lean` lifted a
representable orthogonal factorization system along a product, an inserter and an equifier;
the analogous lifting of representable regularity and exactness is not formalized here.  This
file contains the finite-limit ingredients of that lifting:

* `UlmerBialgebras.Inserter.forgetIso`, `UlmerBialgebras.Equifier.forgetIso` — whiskering with the
  structural 1-cell is the forgetful functor, read through the comparison equivalences of
  `HomCat.lean`;
* `UlmerBialgebras.Inserter.preservesFiniteLimits_postcomp_u`,
  `UlmerBialgebras.Equifier.preservesFiniteLimits_postcomp_e` — whiskering with the structural
  1-cell preserves finite limits;
* `UlmerBialgebras.Inserter.reflectsLimitsOfShape_postcomp_u`,
  `UlmerBialgebras.Equifier.reflectsLimitsOfShape_postcomp_e` — and reflects limits.

## Main results

* `UlmerBialgebras.Inserter.preservesFiniteLimits_postcomp_u`,
  `UlmerBialgebras.Equifier.preservesFiniteLimits_postcomp_e`: whiskering with the structural 1-cell
  of an inserter or an equifier preserves finite limits.
* `UlmerBialgebras.Inserter.reflectsLimitsOfShape_postcomp_u`,
  `UlmerBialgebras.Equifier.reflectsLimitsOfShape_postcomp_e`: whiskering with the structural 1-cell
  reflects limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4, Lemma 6.5, Theorem 6.6
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

attribute [local instance] comp_preservesFiniteLimits

/-! ## General helpers -/

section Helpers

variable {A : Type*} [Category A] {B : Type*} [Category B]

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]

end Helpers

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

open scoped CategoryTheory.Bicategory

/-! ## Products -/

namespace Product

variable {ι : Type} {c : ι → Obj} (P : Product c)

end Product

/-! ## Inserters -/

namespace Inserter

variable {a b : Obj} {u v : a ⟶ b} (I : Inserter u v)

/-- Whiskering with `u : Ins(u, v) ⟶ a` is the forgetful functor of the inserter category,
read through the comparison equivalence. -/
def forgetIso (x : Obj) :
    homFunctor I x ⋙ Ins.forget (postcomp x u) (postcomp x v) ≅ postcomp x I.u :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    -- The components are identities; the square is `comp_id` against `id_comp`.
    intro k k' α
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (x : Obj)

/-- Whiskering with the forgetful 1-cell of an inserter preserves finite limits. -/
theorem preservesFiniteLimits_postcomp_u (hlim : HasFiniteLimits (x ⟶ a))
    (hv : PreservesFiniteLimits (postcomp x v)) : PreservesFiniteLimits (postcomp x I.u) := by
  have := hlim
  have := hv
  have : PreservesFiniteLimits (Ins.forget (postcomp x u) (postcomp x v)) :=
    ⟨fun _ _ _ => inferInstance⟩
  exact preservesFiniteLimits_of_natIso (forgetIso I x)

/-- Whiskering with the forgetful 1-cell of an inserter reflects limits. -/
theorem reflectsLimitsOfShape_postcomp_u {J : Type} [SmallCategory J]
    (hv : PreservesLimitsOfShape J (postcomp x v)) :
    ReflectsLimitsOfShape J (postcomp x I.u) := by
  have := hv
  have : ReflectsLimitsOfShape J (Ins.forget (postcomp x u) (postcomp x v)) := inferInstance
  have : ReflectsLimitsOfShape J
      (homFunctor I x ⋙ Ins.forget (postcomp x u) (postcomp x v)) := inferInstance
  exact reflectsLimitsOfShape_of_natIso (forgetIso I x)

end Inserter

/-! ## Equifiers -/

namespace Equifier

variable {a b : Obj} {u v : a ⟶ b} {η θ : u ⟶ v} (E : Equifier η θ)

/-- Whiskering with `e : Eq(η, θ) ⟶ a` is the forgetful functor of the equifier category,
read through the comparison equivalence. -/
def forgetIso (x : Obj) :
    homFunctor E x ⋙ Equif.forget (postcompNat x η) (postcompNat x θ) ≅ postcomp x E.e :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    -- The components are identities; the square is `comp_id` against `id_comp`.
    intro k k' α
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (x : Obj)

/-- Whiskering with the forgetful 1-cell of an equifier preserves finite limits. -/
theorem preservesFiniteLimits_postcomp_e (hlim : HasFiniteLimits (x ⟶ a))
    (hv : PreservesFiniteLimits (postcomp x v)) : PreservesFiniteLimits (postcomp x E.e) := by
  have := hlim
  have := hv
  have : PreservesFiniteLimits (Equif.forget (postcompNat x η) (postcompNat x θ)) :=
    ⟨fun _ _ _ => inferInstance⟩
  exact preservesFiniteLimits_of_natIso (forgetIso E x)

/-- Whiskering with the forgetful 1-cell of an equifier reflects limits. -/
theorem reflectsLimitsOfShape_postcomp_e {J : Type} [SmallCategory J] :
    ReflectsLimitsOfShape J (postcomp x E.e) := by
  have : ReflectsLimitsOfShape J (Equif.forget (postcompNat x η) (postcompNat x θ)) :=
    inferInstance
  have : ReflectsLimitsOfShape J
      (homFunctor E x ⋙ Equif.forget (postcompNat x η) (postcompNat x θ)) := inferInstance
  exact reflectsLimitsOfShape_of_natIso (forgetIso E x)

end Equifier

end UlmerBialgebras
