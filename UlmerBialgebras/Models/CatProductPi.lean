module

public import UlmerBialgebras.Models.CatCells
public import UlmerBialgebras.Basic.CatTwoCat
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.OpTranslate

/-!
# Strict products in `CAT` are product categories

Let `P` be a strict product (in the sense of `UlmerBialgebras.Product`) of a family of categories
`c i` in `Cat.{v, u}`. The comparison functor `P.pt ⥤ ∀ i, c i` whose components are the
projections `P.π i` is an equivalence of categories. The proofs probe `P.pt` with the terminal
category: objects of `P.pt` are 1-cells out of `One`, and morphisms of `P.pt` are 2-cells between
them.

This is what lets statements about `CAT` take the products they need as a hypothesis
`[HasChosenProductsOfSize.{s} Cat.{v, u}]`, as the paper does, rather than a particular
construction.

## Main results

* `UlmerBialgebras.Product.toPi`: the comparison functor `P.pt ⥤ ∀ i, c i`.
* `UlmerBialgebras.Product.toPi_isEquivalence`: it is an equivalence.
* `UlmerBialgebras.Product.π_preservesColimit`: each projection `P.π i` preserves every colimit.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 2.1 and Example 2.3 (1)
-/

@[expose] public section


universe v u s

namespace UlmerBialgebras

open CategoryTheory Limits

namespace Product

variable {ι : Type s} {c : ι → Cat.{v, u}} (P : Product c)

/-- The constant 1-cell `One ⟶ X` at an object `x` of `X`. -/
abbrev constOne {X : Cat.{v, u}} (x : X) : One.{v, u} ⟶ X := ((Functor.const _).obj x).toCatHom

/-- The comparison functor from a strict product in `CAT` to the product category: its components
are the projections. -/
def toPi : (P.pt : Type u) ⥤ ∀ i, (c i : Type u) := Functor.pi' fun i => (P.π i).toFunctor

/-- The 2-cell between constant 1-cells out of `One` given by a morphism `f : x ⟶ y`. -/
def constCell {X : Cat.{v, u}} {x y : X} (f : x ⟶ y) : constOne x ⟶ constOne y :=
  ((Functor.const _).map f).toCatHom₂

/-- The 2-cell between `constOne x ≫ F` and `constOne y ≫ F` given by a morphism
`g : F x ⟶ F y`. -/
def constCellComp {X Y : Cat.{v, u}} (F : X ⟶ Y) {x y : X}
    (g : F.toFunctor.obj x ⟶ F.toFunctor.obj y) : constOne x ≫ F ⟶ constOne y ≫ F :=
  { toNatTrans :=
    { app := fun _ => g
      naturality := fun a b h => by
        cases a; cases b
        -- The only morphism of the terminal category is an identity, sent to identities.
        exact (F.toFunctor.map_id x =≫ g).trans ((Category.id_comp g).trans
          ((Category.comp_id g).symm.trans (g ≫= (F.toFunctor.map_id y).symm))) } }

/-- The comparison functor of a strict product in `CAT` is faithful. -/
instance : (toPi P).Faithful where
  map_injective {x y} f g h := by
    have key : constCell f = constCell g := P.cell_ext fun i => by
      apply Cat.Hom₂.ext
      ext a
      cases a
      exact funext_iff.mp h i
    exact NatTrans.congr_app congr(Cat.Hom₂.toNatTrans $key) One.star

/-- The comparison functor of a strict product in `CAT` is full. -/
instance : (toPi P).Full where
  map_surjective {x y} g := by
    refine ⟨(P.lift₂ (f := constOne x) (g := constOne y)
      fun i => constCellComp (P.π i) (g i)).toNatTrans.app One.star, ?_⟩
    funext i
    exact NatTrans.congr_app
      congr($(P.lift₂_π (fun i => constCellComp (P.π i) (g i)) i).toNatTrans) One.star

/-- The comparison functor of a strict product in `CAT` is essentially surjective. -/
instance : (toPi P).EssSurj where
  mem_essImage p :=
    ⟨(P.lift fun i => constOne (p i)).toFunctor.obj One.star,
      ⟨eqToIso (funext fun i =>
        congr($(P.lift_π (fun i => constOne (p i)) i).toFunctor.obj One.star))⟩⟩

/-- The comparison functor of a strict product in `CAT` is an equivalence. -/
instance toPi_isEquivalence : (toPi P).IsEquivalence where

/-- The projections of a strict product in `CAT` are evaluations after the comparison. -/
lemma toPi_comp_eval (i : ι) : toPi P ⋙ Pi.eval (fun i => (c i : Type u)) i = (P.π i).toFunctor :=
  rfl

/-- Each projection of a strict product in `CAT` preserves every colimit. -/
instance π_preservesColimit {J : Type*} [Category J] (D : J ⥤ (P.pt : Type u)) (i : ι) :
    PreservesColimit D (P.π i).toFunctor := by
  classical
  rw [← toPi_comp_eval P i]
  have : PreservesColimit (D ⋙ toPi P) (Pi.eval (fun i => (c i : Type u)) i) :=
    ⟨fun hc => ⟨piEvalIsColimit hc i⟩⟩
  infer_instance

/-- Each projection of a strict product in `CAT` preserves every limit. -/
instance π_preservesLimit {J : Type*} [Category J] (D : J ⥤ (P.pt : Type u)) (i : ι) :
    PreservesLimit D (P.π i).toFunctor := by
  classical
  rw [← toPi_comp_eval P i]
  have := OpTranslate.piEval_preservesLimitsOfShape (C := fun i => (c i : Type u)) J i
  infer_instance

/-- A lift into a strict product in `CAT`, followed by the comparison, is the functor into the
product category given by its components. -/
lemma lift_comp_toPi {X : Cat.{v, u}} (g : ∀ i, X ⟶ c i) :
    (P.lift g).toFunctor ⋙ toPi P = Functor.pi' fun i => (g i).toFunctor := by
  change Functor.pi' (fun i => (P.lift g).toFunctor ⋙ (P.π i).toFunctor) = _
  congr 1
  funext i
  exact congr($(P.lift_π g i).toFunctor)

/-- A lift into a strict product in `CAT` preserves a colimit preserved by its components. -/
lemma lift_preservesColimit {X : Cat.{v, u}} (g : ∀ i, X ⟶ c i) {J : Type*} [Category J]
    (K : J ⥤ (X : Type u)) [∀ i, PreservesColimit K (g i).toFunctor] :
    PreservesColimit K (P.lift g).toFunctor := by
  have : PreservesColimit K ((P.lift g).toFunctor ⋙ toPi P) := by
    rw [lift_comp_toPi]
    exact ⟨fun hc => ⟨piIsColimitOfEval fun i => isColimitOfPreserves (g i).toFunctor hc⟩⟩
  exact preservesColimit_of_reflects_of_preserves _ (toPi P)

end Product

end UlmerBialgebras
