module

public import UlmerBialgebras.Appendix.VCat

/-!
# Bundling enriched functors

Construction of a `VFunctor` from an enriched functor.

## Main definitions

* `UlmerBialgebras.VFunctor.ofEnriched`: the `V`-functor `ForgetEnrichment V A ⟶ B` given by a map
  on objects and an action on hom-objects compatible with the enriched identities and composition.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma A.3,
  Definition A.4
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u u₁

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

section

variable {A : Type u₁} [EnrichedCategory V A]
  {B : Type u} [Category.{w} B] [EnrichedOrdinaryCategory V B]

/-- **A `V`-functor out of a bare enriched category**: the underlying ordinary functor of a
`V`-functor `ForgetEnrichment V A ⟶ B` is determined by the action on hom-objects, so the
data of such a `V`-functor is a map on objects together with an action on hom-objects
compatible with the enriched identities and composition. -/
def VFunctor.ofEnriched (obj : A → B)
    (emap : ∀ X Y : A, (X ⟶[V] Y) ⟶ (obj X ⟶[V] obj Y))
    (hid : ∀ X : A, eId V X ≫ emap X X = eId V (obj X))
    (hcomp : ∀ X Y Z : A, eComp V X Y Z ≫ emap X Z
      = (emap X Y ⊗ₘ emap Y Z) ≫ eComp V (obj X) (obj Y) (obj Z)) :
    VFunctor V (ForgetEnrichment V A) B where
  toFunctor :=
    { obj := fun X => obj (ForgetEnrichment.to V X)
      map := fun {_ _} f => (eHomEquiv V).symm (ForgetEnrichment.homTo V f ≫ emap _ _)
      map_id := fun X => by
        apply (eHomEquiv V).injective
        rw [Equiv.apply_symm_apply, ForgetEnrichment.homTo_id, hid, eHomEquiv_id]
      map_comp := fun {X Y Z} f g => by
        apply (eHomEquiv V).injective
        rw [Equiv.apply_symm_apply, eHomEquiv_comp, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply, ForgetEnrichment.homTo_comp]
        rw [Category.assoc, Category.assoc, hcomp, ← Category.assoc,
          ← MonoidalCategory.tensorHom_comp_tensorHom]
        simp }
  emap X Y := emap _ _
  emap_comp X Y Z := hcomp _ _ _
  emap_hom {X Y} f := by
    change ForgetEnrichment.homTo V f ≫ emap _ _
      = eHomEquiv V ((eHomEquiv V).symm (ForgetEnrichment.homTo V f ≫ emap _ _))
    rw [Equiv.apply_symm_apply]

end

end UlmerBialgebras
