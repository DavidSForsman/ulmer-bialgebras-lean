module

public import Foundations.CategoryTheory.Bicategory.StrictCoherence
public import UlmerBialgebras.Basic.HomCat

/-!
# Functoriality of the hom-categories of a strict 2-category

Complements to `HomCat.lean`: the post-composition functors between hom-categories of a
strict 2-category are (strictly) functorial, and the comparison functors of `HomCat.lean`
are compatible with the structural functors of the PIE limits of `CAT`.

* `UlmerBialgebras.postcomp_id₁`, `UlmerBialgebras.postcomp_comp₁`;
* `UlmerBialgebras.postcomp_comp_precomp` — pre- and post-composition commute;
* `UlmerBialgebras.Inserter.homFunctor_comp_forget`,
  `UlmerBialgebras.Equifier.homFunctor_comp_forget` — the comparison functors are compatible with
  the forgetful functor of the inserter and with the inclusion of the equifier.

All the equalities are *strict*: they hold on the nose because the 2-category is strict.

## Main results

* `UlmerBialgebras.postcomp_id₁`, `UlmerBialgebras.postcomp_comp₁`: post-composition is strictly
  functorial.
* `UlmerBialgebras.postcomp_comp_precomp`: pre- and post-composition commute.
* `UlmerBialgebras.Inserter.homFunctor_comp_forget`,
  `UlmerBialgebras.Equifier.homFunctor_comp_forget`: the comparison functors of an inserter and an
  equifier, followed by the forgetful functors, are post-composition with `u` and `e`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1, Remark 2.2 and Section 7
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Functoriality -/

/-- Post-composing with an identity 1-cell is the identity functor. -/
theorem postcomp_id₁ (x a : Obj) : postcomp x (𝟙 a) = 𝟭 (x ⟶ a) :=
  Functor.ext (fun h => Category.comp_id h) (fun _ _ α => Bicategory.Strict.whiskerRight_id α)

/-- Post-composing with a composite is the composite of the post-compositions. -/
theorem postcomp_comp₁ (x : Obj) {c d e : Obj} (u : c ⟶ d) (v : d ⟶ e) :
    postcomp x (u ≫ v) = postcomp x u ⋙ postcomp x v :=
  Functor.ext (fun h => (Category.assoc h u v).symm)
    (fun _ _ α => Bicategory.Strict.whiskerRight_comp α u v)

/-- Pre-composition and post-composition commute. -/
theorem postcomp_comp_precomp {x y : Obj} (F : x ⟶ y) {c d : Obj} (u : c ⟶ d) :
    postcomp y u ⋙ precomp F d = precomp F c ⋙ postcomp x u :=
  Functor.ext (fun h => (Category.assoc F h u).symm)
    (fun _ _ α => Bicategory.Strict.whisker_assoc F α u)

/-! ## Compatibility of the comparison functors -/

/-- The comparison functor of an inserter, followed by the forgetful functor of the inserter
category, is post-composition with the structural 1-cell. -/
theorem Inserter.homFunctor_comp_forget {a b : Obj} {f g : a ⟶ b} (I : Inserter f g)
    (x : Obj) :
    Inserter.homFunctor I x ⋙ Ins.forget (postcomp x f) (postcomp x g)
      = postcomp x I.u := rfl

/-- The comparison functor of an equifier, followed by the inclusion of the equifier
category, is post-composition with the structural 1-cell. -/
theorem Equifier.homFunctor_comp_forget {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g}
    (E : Equifier η θ) (x : Obj) :
    Equifier.homFunctor E x ⋙ Equif.forget (postcompNat x η) (postcompNat x θ)
      = postcomp x E.e := rfl

end UlmerBialgebras
