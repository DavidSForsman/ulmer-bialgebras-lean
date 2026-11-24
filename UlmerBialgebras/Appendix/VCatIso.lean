module

public import UlmerBialgebras.Appendix.VCat

/-!
# Isomorphisms in the hom-categories of `CAT_V`

Two elementary facts about the 2-cells of `CAT_V` (`VCat.lean`), of use both for the
"small `V`-categories are jointly conservative" argument and for the construction of
quasi-inverses:

* `UlmerBialgebras.vNatIsoApp` — the components of an isomorphism of `V`-functors are isomorphisms;
* `UlmerBialgebras.VNatTrans.isIso_of_app` — conversely a `V`-natural transformation whose
  components are isomorphisms is an isomorphism, the inverse components being automatically
  `V`-natural.

We also fix here the notion of a **`V`-fully faithful** `V`-functor: one whose actions on
hom-objects are isomorphisms of `V`.

## Main results

* `UlmerBialgebras.vNatIsoApp`: the component at `X` of an isomorphism of `V`-functors, as an
  isomorphism.
* `UlmerBialgebras.VNatTrans.isIso_of_app`: a `V`-natural transformation whose components are
  isomorphisms is an isomorphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Appendix A
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The components of an isomorphism of `V`-functors are isomorphisms. -/
@[simps] def vNatIsoApp {C D : VCat.{w, v, u} V} {F G : C ⟶ D} (α : F ≅ G) (X : C.carrier) :
    F.obj X ≅ G.obj X where
  hom := α.hom.app X
  inv := α.inv.app X
  hom_inv_id := congr(VNatTrans.app $α.hom_inv_id X)
  inv_hom_id := congr(VNatTrans.app $α.inv_hom_id X)

namespace VNatTrans

variable {C D : VCat.{w, v, u} V} {F G : C ⟶ D}

/-- The inverse of a `V`-natural transformation with invertible components: the inverse
components are again `V`-natural. -/
noncomputable def inverse (α : F ⟶ G) (h : ∀ X, IsIso (α.app X)) : G ⟶ F where
  app X := haveI := h X; inv (α.app X)
  vnaturality X Y := by
    have := h X
    have := h Y
    have hsq := α.vnaturality X Y
    have hG : G.emap X Y
        = F.emap X Y ≫ eHomWhiskerLeft V (F.obj X) (α.app Y)
          ≫ eHomWhiskerRight V (inv (α.app X)) (G.obj Y) := by
      rw [reassoc_of% hsq, ← eHomWhiskerRight_comp, IsIso.inv_hom_id, eHomWhiskerRight_id,
        Category.comp_id]
    rw [hG, Category.assoc, Category.assoc,
      ← eHom_whisker_exchange V (inv (α.app X)) (inv (α.app Y)),
      ← eHomWhiskerLeft_comp_assoc, IsIso.hom_inv_id, eHomWhiskerLeft_id, Category.id_comp]

/-- A `V`-natural transformation whose components are isomorphisms is an isomorphism. -/
theorem isIso_of_app (α : F ⟶ G) (h : ∀ X, IsIso (α.app X)) : IsIso α := by
  refine ⟨α.inverse h, VNatTrans.ext (funext fun X => ?_), VNatTrans.ext (funext fun X => ?_)⟩
  · have := h X
    exact IsIso.hom_inv_id (α.app X)
  · have := h X
    exact IsIso.inv_hom_id (α.app X)

end VNatTrans

end UlmerBialgebras
