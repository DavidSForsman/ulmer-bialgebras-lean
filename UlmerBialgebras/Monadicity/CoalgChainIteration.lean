module

public import Mathlib.CategoryTheory.SmallObject.TransfiniteIteration
public import UlmerBialgebras.Monadicity.InitialAlgebraChain

/-!
# Existence of the transfinite chain of an endofunctor

The initial chain `X₀ ⟶ S X₀ ⟶ S² X₀ ⟶ ⋯` of an endofunctor `S : C ⥤ C`, started at a
coalgebra `X₀ ⟶ S X₀`, is obtained as the transfinite iteration (in the sense of
`CategoryTheory.SmallObject.SuccStruct`) of the *well-pointed* endofunctor of the category
of `S`-coalgebras sending `V` to `S V` — the point being the structure morphism of `V`.

The output is a term of `UlmerBialgebras.CoalgChain S J`, so that the initial-algebra theorem
`UlmerBialgebras.CoalgChain.isInitialAlgebra` applies.

## Main results

* `UlmerBialgebras.coalgSuccStruct`: the successor structure on `S`-coalgebras sending `V` to `S V`.
* `UlmerBialgebras.coalgChain`: the initial chain of `S` started at a coalgebra `V₀`.
* `UlmerBialgebras.coalgChainBotIso`, `UlmerBialgebras.coalgChainBotIso_str`: the bottom stage of
  the chain is `V₀`, compatibly with the structure maps.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.5
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits Endofunctor SmallObject

variable {C : Type u} [Category.{v} C] (S : C ⥤ C)

/-- The successor structure on the category of `S`-coalgebras with base the coalgebra `V₀`:
the successor of `V` is `S V` with structure morphism `S (str V)`, and the transition
morphism is the structure morphism of `V`. -/
@[simps]
def coalgSuccStruct (V₀ : Endofunctor.Coalgebra S) : SuccStruct (Endofunctor.Coalgebra S) where
  X₀ := V₀
  succ V := ⟨S.obj V.V, S.map V.str⟩
  toSucc V := ⟨V.str, rfl⟩

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [HasIterationOfShape J C]

/-- The initial chain of the endofunctor `S`, started at the coalgebra `V₀`. -/
noncomputable def coalgChain (hmax : ∀ j : J, ¬ IsMax j) (V₀ : Endofunctor.Coalgebra S) :
    CoalgChain S J where
  W := (coalgSuccStruct S V₀).iterationFunctor J ⋙ Endofunctor.Coalgebra.forget S
  str :=
    { app := fun j => (((coalgSuccStruct S V₀).iterationFunctor J).obj j).str
      naturality := fun _ _ f => (((coalgSuccStruct S V₀).iterationFunctor J).map f).h.symm }
  succIso := fun j => (Endofunctor.Coalgebra.forget S).mapIso
      ((coalgSuccStruct S V₀).iterationFunctorObjSuccIso j (hmax j))
  map_succ := fun j => by
    have h : ((coalgSuccStruct S V₀).iterationFunctor J).map (homOfLE (Order.le_succ j)) ≫
        ((coalgSuccStruct S V₀).iterationFunctorObjSuccIso j (hmax j)).hom
        = (coalgSuccStruct S V₀).toSucc _ := by
      rw [(coalgSuccStruct S V₀).iterationFunctor_map_succ j (hmax j), Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    exact congrArg (Endofunctor.Coalgebra.forget S).map h
  str_succ := fun j =>
    (((coalgSuccStruct S V₀).iterationFunctorObjSuccIso j (hmax j)).hom.h).symm
  continuous := by
    constructor
    intro m hm
    have := Limits.hasColimitsOfShape_of_isSuccLimit C m hm
    have hE := ((coalgSuccStruct S V₀).iterationFunctor J).isColimitOfIsWellOrderContinuous m hm
    exact ⟨IsColimit.ofIsoColimit
      (isColimitOfPreserves (Endofunctor.Coalgebra.forget S) hE)
      (Cocone.ext (Iso.refl _) (fun _ => Category.comp_id _))⟩

/-- The bottom stage of the chain is the base coalgebra `V₀`. -/
noncomputable def coalgChainBotIso (hmax : ∀ j : J, ¬ IsMax j) (V₀ : Endofunctor.Coalgebra S) :
    (coalgChain S hmax V₀).W.obj (⊥ : J) ≅ V₀.V :=
  (Endofunctor.Coalgebra.forget S).mapIso ((coalgSuccStruct S V₀).iterationFunctorObjBotIso J)

/-- `coalgChainBotIso` commutes with the structure maps of the bottom stage and of `V₀`. -/
lemma coalgChainBotIso_str (hmax : ∀ j : J, ¬ IsMax j) (V₀ : Endofunctor.Coalgebra S) :
    (coalgChain S hmax V₀).str.app ⊥ ≫ S.map (coalgChainBotIso S hmax V₀).hom
      = (coalgChainBotIso S hmax V₀).hom ≫ V₀.str :=
  ((coalgSuccStruct S V₀).iterationFunctorObjBotIso J).hom.h

end UlmerBialgebras
