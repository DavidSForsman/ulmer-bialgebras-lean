module

public import UlmerBialgebras.Appendix.VCatCellDense

/-!
# The point and arrow probes of Appendix A

Reuse the existing enriched categories and their functor constructors.
The arrow classification below supplies the uniqueness part of the free
one-edge forest universal property.

The probes are the `V`-categories `1` and `2_x` of Definition A.4, used in Theorem A.5.

## Main results

* `UlmerBialgebras.Paper.Appendix.unitFunctorDataEquiv`: `V`-functors from the point probe to `C`
  are in bijection with the objects of `C`.
* `UlmerBialgebras.Paper.Appendix.arrowFunctorDataEquiv`: `V`-functors from the arrow probe `2_x` to
  `C` are in bijection with pairs of objects `c, c'` together with a morphism `x ⟶ C(c, c')`.
* `UlmerBialgebras.Paper.Appendix.arrowTransformationEquiv`: transformations between functors out of
  an arrow probe are in bijection with pairs of endpoint components satisfying the naturality square
  of the generic arrow.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition A.4 and Theorem A.5
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- An enriched functor is determined by its object function and hom maps. -/
theorem vFunctor_ext_obj_heq
    {A B : Type u} [Category.{w} A] [EnrichedOrdinaryCategory V A]
    [Category.{w} B] [EnrichedOrdinaryCategory V B]
    {F G : VFunctor V A B}
    (ho : F.toFunctor.obj = G.toFunctor.obj)
    (he : ∀ a b, HEq (F.emap a b) (G.emap a b)) : F = G := by
  rcases F with ⟨⟨fo, fm, fi, fc⟩, fe, fec, feh⟩
  rcases G with ⟨⟨go, gm, gi, gc⟩, ge, gec, geh⟩
  dsimp at ho he
  cases ho
  have hem : fe = ge := by
    funext a b
    exact eq_of_heq (he a b)
  cases hem
  have hm : @fm = @gm := by
    funext a b f
    apply (eHomEquiv V).injective
    exact (feh f).symm.trans (geh f)
  cases hm
  rfl

/-- The point probe's evaluation on objects is a bijection, not merely
essentially surjective. -/
def unitFunctorDataEquiv (C : VCat.{w, v, u} V) :
    (unitVCat.{w, v, u} V ⟶ C) ≃ C.carrier where
  toFun F := F.obj (UnitVCat.star V)
  invFun c := UnitVCat.const c
  left_inv F := by
    symm
    apply vFunctor_ext_obj_heq
    · funext a
      cases a
      rfl
    · intro a b
      cases a
      cases b
      apply heq_of_eq
      exact UnitVCat.vFunctor_emap F _ _
  right_inv c := rfl

/-- Reading the two objects and the generic hom map reconstructs an arrow functor. -/
theorem arrowVFunctor_reconstruct (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) (F : arrowVCat.{w, v, u} Z x ⟶ C) :
    F = arrowVFunctor Z x (F.obj .src) (F.obj .tgt) (F.emap .src .tgt) := by
  apply vFunctor_ext_obj_heq
  · funext a
    cases a <;> rfl
  · intro a b
    cases a <;> cases b <;> apply heq_of_eq
    · exact (Category.id_comp _).symm.trans (F.emap_id .src)
    · rfl
    · exact Z.isInitial.hom_ext _ _
    · exact (Category.id_comp _).symm.trans (F.emap_id .tgt)

/-- Functors from the free one-edge forest are precisely its labelled graph maps. -/
def arrowFunctorDataEquiv (Z : MonoidalInitial V) (x : V) (C : VCat.{w, v, u} V) :
    (arrowVCat.{w, v, u} Z x ⟶ C) ≃
      (Σ c : C.carrier, Σ c' : C.carrier, x ⟶ (c ⟶[V] c')) where
  toFun F := ⟨F.obj .src, F.obj .tgt, F.emap .src .tgt⟩
  invFun d := arrowVFunctor Z x d.1 d.2.1 d.2.2
  left_inv F := (arrowVFunctor_reconstruct Z x C F).symm
  right_inv d := by rcases d with ⟨c, c', f⟩; rfl

/-- A transformation from an arrow probe is exactly its endpoint components
subject to the generic-arrow naturality square. -/
def arrowTransformationEquiv (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) (F G : arrowVCat.{w, v, u} Z x ⟶ C) :
    (F ⟶ G) ≃
      { p : (F.obj .src ⟶ G.obj .src) × (F.obj .tgt ⟶ G.obj .tgt) //
        F.emap .src .tgt ≫ eHomWhiskerLeft V (F.obj .src) p.2 =
          G.emap .src .tgt ≫ eHomWhiskerRight V p.1 (G.obj .tgt) } where
  toFun α := ⟨(α.app .src, α.app .tgt), α.vnaturality .src .tgt⟩
  invFun p := arrowVNatTrans Z x p.1.1 p.1.2 p.2
  left_inv α := by
    apply VNatTrans.ext
    funext a
    cases a <;> rfl
  right_inv p := by
    apply Subtype.ext
    rfl

end UlmerBialgebras.Paper.Appendix
