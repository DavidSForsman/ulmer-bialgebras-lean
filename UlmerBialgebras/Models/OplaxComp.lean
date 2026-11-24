module

public import UlmerBialgebras.Models.Oplax
public import UlmerBialgebras.Models.LaxComp

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Identities and composites of oplax data

The data of the identity oplax morphism and of the composite of two oplax morphisms
(Proposition 3.11). The structure 2-cell of a composite at a functor symbol `B : c̄ → d` is

`ϕ^B : (GF)_d ∘ M(B) ⟹ G_d ∘ N(B) ∘ F_c̄ ⟹ P(B) ∘ (GF)_c̄`.

That the composite of oplax morphisms of models is again one follows by duality from the lax
case: `UlmerBialgebras.OplaxMor.comp` in `UlmerBialgebras/Models/CoMor.lean`.

## Main results

* `UlmerBialgebras.OplaxData.comp`: the composite of oplax data (Proposition 3.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Proposition 3.11
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

namespace OplaxData

/-! ## The identity oplax morphism -/

/-! ## Composition -/

variable {M N Pm : PreModel Sg Obj}

/-- Reassociates the composite 1-cell projections in `OplaxData.comp`. -/
lemma comp_prod_lift_eq (F : OplaxData M N) (G : OplaxData N Pm) (B : Sg.Fun) :
    (Pm.P B).lift (fun i => ((M.P B).π i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) ≫
        Pm.fn B =
      (Pm.P B).lift (fun i => (M.P B).π i ≫ F.cell (Sg.art B i) ≫ G.cell (Sg.art B i)) ≫
        Pm.fn B := by
  rw [show (fun i => (M.P B).π i ≫ (F.cell (Sg.art B i) ≫ G.cell (Sg.art B i))) =
    (fun i => ((M.P B).π i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) from
    funext fun i => (Category.assoc _ _ _).symm]

/-- The composite of the data of two oplax morphisms (Proposition 3.11). -/
def comp (F : OplaxData M N) (G : OplaxData N Pm) : OplaxData M Pm where
  cell c := F.cell c ≫ G.cell c
  str B :=
    eqToHom (Category.assoc (M.fn B) (F.cell (Sg.fcod B)) (G.cell (Sg.fcod B))).symm ≫
    (F.str B ▷ G.cell (Sg.fcod B)) ≫
    G.strAt B (fun i => (M.P B).π i ≫ F.cell (Sg.art B i)) ≫
    eqToHom (comp_prod_lift_eq F G B)

end OplaxData

end UlmerBialgebras
