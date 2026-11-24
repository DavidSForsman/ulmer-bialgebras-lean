module

public import UlmerBialgebras.Models.Co
public import UlmerBialgebras.Models.Lax
public import UlmerBialgebras.Models.Oplax

/-!
# Models in `K^co`

The dual `Σ^co` of a 2-signature `Σ` swaps the source and target terms of every transformation
symbol. A `Σ`-model `M` in `K` is a `Σ^co`-model `M^co` in `K^co`: the same objects and 1-cells,
and the 2-cells `M(σ) : M(s) ⟹ M(t)` read as 2-cells `M(t) ⟹ M(s)` of `K^co`.

Under this correspondence, oplax morphisms of models in `K` are exactly lax morphisms of the
dual models in `K^co` (`UlmerBialgebras.OplaxData.toLax`, `UlmerBialgebras.OplaxMor.toLax`), which
is the paper's "dually, we define an oplax morphism" (Definition 3.10).

## Main results

* `UlmerBialgebras.TwoSig.co`: the dual 2-signature `Σ^co`.
* `UlmerBialgebras.Model.co`: the dual `Σ^co`-model `M^co` in `K^co` (Definition 3.8).
* `UlmerBialgebras.OplaxData.toLax`: oplax data in `K` as lax data of the dual models
  (Definition 3.10).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 3.8 and 3.10
-/

@[expose] public section

universe u v w uᵥ

namespace UlmerBialgebras

open CategoryTheory

/-- The dual of a 2-signature: the source and target of each transformation symbol swapped. -/
@[implicit_reducible]
def TwoSig.co (Sg : TwoSig) : TwoSig :=
  { Sg with trsrc := Sg.trtgt, trtgt := Sg.trsrc }

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  {Sg : TwoSig}

/-- A pre-model in `K` as a pre-model in `K^co`. -/
@[implicit_reducible]
def PreModel.co (M : PreModel Sg Obj) : PreModel Sg.co (Co Obj) where
  obj c := Co.op (M.obj c)
  fn B := M.fn B

/-- Terms are interpreted in `K^co` by the same recursion as in `K`. -/
lemma PreModel.co_interp (M : PreModel Sg Obj) {V : Type uᵥ} {vty : V → Sg.Cat}
    {x : Co Obj} (ρ : ∀ v, x ⟶ M.co.obj (vty v)) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    M.co.interp ρ t = M.interp (fun v => ρ v) t := by
  induction t with
  | var v => rfl
  | app B args ih =>
      unfold PreModel.interp
      simp only [ih]
      with_unfolding_all
      rfl

/-- A model in `K` as a model of the dual signature in `K^co`. Its 2-cells are those of `M`, read
in `K^co`. Their types match because terms are interpreted in `K^co` by the same recursion as in
`K` (`PreModel.co_interp`). -/
@[implicit_reducible]
def Model.co (M : Model Sg Obj) : Model Sg.co (Co Obj) where
  toPreModel := M.toPreModel.co
  tr a :=
    Co.cell
      (@eqToHom ((M.Pctx a).pt ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := Co.op (M.Pctx a).pt) (M.Pctx a).π (Sg.trsrc a)) ≫
        M.tr a ≫
        @eqToHom ((M.Pctx a).pt ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := Co.op (M.Pctx a).pt) (M.Pctx a).π (Sg.trtgt a)).symm)

/-- The transformation 2-cell of `M^co` is `M.tr a` up to `PreModel.co_interp`. -/
lemma Model.co_tr (M : Model Sg Obj) (a : Sg.Tr) :
    Co.uncell (M.co.tr a) =
      @eqToHom ((M.Pctx a).pt ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := Co.op (M.Pctx a).pt) (M.Pctx a).π (Sg.trsrc a)) ≫
        M.tr a ≫
        @eqToHom ((M.Pctx a).pt ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := Co.op (M.Pctx a).pt) (M.Pctx a).π (Sg.trtgt a)).symm :=
  rfl

/-- Oplax data between pre-models in `K` are lax data between the dual pre-models in `K^co`:
the same 1-cells, and the structure 2-cells `F_d M(B) ⟹ N(B) F_c̄` read in `K^co`. -/
@[implicit_reducible]
def OplaxData.toLax {M N : PreModel Sg Obj} (F : OplaxData M N) : LaxData M.co N.co where
  cell c := F.cell c
  str B := F.str B

end UlmerBialgebras
