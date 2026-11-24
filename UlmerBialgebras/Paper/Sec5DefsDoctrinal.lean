module

public import UlmerBialgebras.Models.LaxCell
public import UlmerBialgebras.Models.Oplax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Doctrinal adjunction for Σ-models: definitions

Definitions for the doctrinal adjunction of Σ-models (the ingredient behind the proof of
Theorem 7.4 of [forsman2026syntactic]). Let `M, N` be Σ-models in a PIE-complete strict
2-category `K`, `G : M → N` a lax morphism (Definition 3.10), and `F_c ⊣ G_c` adjunctions in `K`
for the category symbols `c`.

* `prodL`, `prodR`: the 1-cells `F_c̄`, `G_c̄` on the products of the arity of a functor symbol.
* `prodUnit`: the unit of the product adjunction `F_c̄ ⊣ G_c̄`, componentwise.
* `mateStr`: the mate `N(B) ≫ F_d ⇒ F_c̄ ≫ M(B)` of a structure 2-cell
  `G_c̄ ≫ N(B) ⇒ M(B) ≫ G_d` (diagrammatic order), pasted from the unit of `F_c̄ ⊣ G_c̄` and the
  counit of `F_d ⊣ G_d`.
* `mateOplaxData`: the oplax data `N → M` with cells `F_c` and the mates as structure 2-cells.
* `invLaxData`: the lax data with the inverses of invertible oplax structure 2-cells.
* `LaxData.idData`: the identity lax data.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11, Theorem 7.4
* [R. Houston, *Linear logic without units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

universe u v w

namespace UlmerBialgebras.Paper.Doctrinal

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig}

section Mate

variable {M N : PreModel Sg Obj} (Fc : ∀ c, N.obj c ⟶ M.obj c) (Gc : ∀ c, M.obj c ⟶ N.obj c)

/-- The 1-cell `F_c̄ : N_c̄ → M_c̄` on the product of the arity of `B`. -/
abbrev prodL (B : Sg.Fun) : (N.P B).pt ⟶ (M.P B).pt :=
  (M.P B).lift (fun i => (N.P B).π i ≫ Fc (Sg.art B i))

/-- The 1-cell `G_c̄ : M_c̄ → N_c̄` on the product of the arity of `B`. -/
abbrev prodR (B : Sg.Fun) : (M.P B).pt ⟶ (N.P B).pt :=
  (N.P B).lift (fun i => (M.P B).π i ≫ Gc (Sg.art B i))

variable {Fc Gc} (A : ∀ c, TwoAdj (Fc c) (Gc c))

/-- The unit `1 ⇒ G_c̄ ∘ F_c̄` of the product adjunction `F_c̄ ⊣ G_c̄`: the units of the
`F_{c_i} ⊣ G_{c_i}` on the factors. -/
def prodUnit (B : Sg.Fun) : 𝟙 (N.P B).pt ⟶ prodL Fc B ≫ prodR Gc B :=
  (N.P B).lift₂ (fun i => eqToHom (Category.id_comp _) ≫ eqToHom (Category.comp_id _).symm ≫
    ((N.P B).π i ◁ (A (Sg.art B i)).unit') ≫
    eqToHom ((N.P B).lift_comp_lift_π (M.P B) (fun j => Fc (Sg.art B j))
      (fun j => Gc (Sg.art B j)) i).symm)

/-- **The mate** `F_d ∘ N(B) ⇒ M(B) ∘ F_c̄` of a structure 2-cell `s : N(B) ∘ G_c̄ ⇒ G_d ∘ M(B)`
under the adjunctions `F_c̄ ⊣ G_c̄` and `F_d ⊣ G_d`:
`N(B) ≫ F_d ⇒ F_c̄ ≫ G_c̄ ≫ N(B) ≫ F_d ⇒ F_c̄ ≫ M(B) ≫ G_d ≫ F_d ⇒ F_c̄ ≫ M(B)`. -/
def mateStr (B : Sg.Fun) (s : prodR Gc B ≫ N.fn B ⟶ M.fn B ≫ Gc (Sg.fcod B)) :
    N.fn B ≫ Fc (Sg.fcod B) ⟶ prodL Fc B ≫ M.fn B :=
  eqToHom (Category.id_comp _).symm ≫ (prodUnit A B ▷ (N.fn B ≫ Fc (Sg.fcod B))) ≫
    eqToHom ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)) ≫
    (prodL Fc B ◁ (s ▷ Fc (Sg.fcod B))) ≫
    eqToHom (congrArg (_ ≫ ·) (Category.assoc _ _ _)) ≫
    (prodL Fc B ◁ (M.fn B ◁ (A (Sg.fcod B)).counit')) ≫
    eqToHom (congrArg (_ ≫ ·) (Category.comp_id _))

end Mate

variable {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}

/-- The oplax data `N → M` of mates of a lax data `G : M → N` along adjunctions `F_c ⊣ G_c`. -/
def mateOplaxData (G : LaxData M.toPreModel N.toPreModel) (A : ∀ c, TwoAdj (Fc c) (G.cell c)) :
    OplaxData N.toPreModel M.toPreModel where
  cell := Fc
  str B := mateStr A B (G.str B)

/-- The lax data with the inverse structure 2-cells of an oplax data whose structure 2-cells are
invertible. -/
noncomputable def invLaxData {M N : PreModel Sg Obj} (F : OplaxData M N)
    [∀ B, IsIso (F.str B)] : LaxData M N where
  cell := F.cell
  str B := inv (F.str B)

/-- The identity lax data of a premodel. -/
def LaxData.idData (M : PreModel Sg Obj) : LaxData M M where
  cell c := 𝟙 (M.obj c)
  str B := eqToHom ((congrArg (· ≫ M.fn B) (M.P B).lift_π_comp_id).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm))

end UlmerBialgebras.Paper.Doctrinal
