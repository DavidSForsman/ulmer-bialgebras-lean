module

public import UlmerBialgebras.Syntax.CoTheory
public import UlmerBialgebras.Models.OplaxComp
public import UlmerBialgebras.Models.LaxComp

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Oplax morphisms are lax morphisms in `K^co`

An oplax morphism `F : M → N` of `Σ`-models in `K` has structure 2-cells
`F_d M(B) ⟹ N(B) F_c̄`. Read in `K^co`, these point the other way, and `F` becomes a lax
morphism `M^co → N^co` of `Σ^co`-models. Under this identification the comparison 2-cells `η_t`
agree, the compatibility with transformation symbols becomes the lax one, and composition of
oplax morphisms becomes composition of lax morphisms. This is the "dually" of Definition 3.10 and
Proposition 3.11.

## Main results

* `UlmerBialgebras.OplaxData.toLax_eta`: the comparison 2-cells `η_t` of `F` and of `F.toLax` agree.
* `UlmerBialgebras.OplaxData.tr_compat_iff_co`: the oplax compatibility with a transformation symbol
  is equivalent to the lax one of the dual data.
* `UlmerBialgebras.OplaxMor.toLax`: an oplax morphism in `K` as a lax morphism of the dual models in
  `K^co` (Definition 3.10).
* `UlmerBialgebras.OplaxMor.comp`: the composite of oplax morphisms of models (Proposition 3.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10 and Proposition 3.11
-/

universe u v w uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  {Sg : TwoSig}

namespace OplaxData

variable {M N : PreModel Sg Obj} (F : OplaxData M N)

/-- The structure 2-cells at arbitrary arguments agree. -/
lemma toLax_strAt (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (F.toLax.strAt (x := Co.op x) B g :
      (((M.P B).lift g ≫ M.fn B) ≫ F.cell (Sg.fcod B)) ⟶
        ((N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B)) = F.strAt B g := by
  simp only [LaxData.strAt, OplaxData.strAt, Co.comp_eq, Co.eqToHom_eq, Category.assoc]
  rfl

private lemma strAt_eq_of_eq (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (h : g = g') :
    F.strAt B g = eqToHom (by rw [h]) ≫ F.strAt B g' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

private lemma appCell_conj (Pm : PreModel Sg Obj) (B : Sg.Fun) {x : Obj}
    {g₁ g₂ g₁' g₂' : ∀ i, x ⟶ Pm.obj (Sg.art B i)}
    (h : g₁ = g₂) (h' : g₁' = g₂') (δ : ∀ i, g₂ i ⟶ g₂' i) :
    Pm.appCell B (fun i => eqToHom (congr_fun h i) ≫ δ i ≫ eqToHom (congr_fun h' i).symm) =
      eqToHom (by rw [h]) ≫ Pm.appCell B δ ≫ eqToHom (by rw [h']) := by
  subst h h'
  simp

/-- The comparison 2-cells `η_t` agree. -/
lemma toLax_eta {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    Co.uncell (F.toLax.eta (x := Co.op x) ρ t) =
      eqToHom (congrArg (· ≫ F.cell c) (M.co_interp (x := Co.op x) ρ t)) ≫ F.eta ρ t ≫
        eqToHom (N.co_interp (x := Co.op x) (fun v => ρ v ≫ F.toLax.cell (vty v)) t).symm := by
  induction t with
  | var v =>
    dsimp only [Co.uncell]
    rw [LaxData.eta_var, OplaxData.eta_var]
    simp only [eqToHom_refl, Category.comp_id]
    rfl
  | app B args ih =>
    rw [LaxData.eta_app, OplaxData.eta_app, Co.comp_eq, toLax_strAt]
    have hm : (fun i => M.co.interp (x := Co.op x) ρ (args i)) =
        (fun i => M.interp ρ (args i)) :=
      funext fun i => M.co_interp (x := Co.op x) ρ (args i)
    have hn : (fun i => N.co.interp (x := Co.op x) (fun v => ρ v ≫ F.toLax.cell (vty v)) (args i)) =
        (fun i => N.interp (fun v => ρ v ≫ F.cell (vty v)) (args i)) :=
      funext fun i => N.co_interp (x := Co.op x) (fun v => ρ v ≫ F.toLax.cell (vty v)) (args i)
    have hmc (i) : M.co.interp (x := Co.op x) ρ (args i) ≫ F.cell (Sg.art B i) =
        M.interp ρ (args i) ≫ F.cell (Sg.art B i) := congr($(funext_iff.mp hm i) ≫ F.cell _)
    have hstr : F.strAt B (fun i => M.co.interp (x := Co.op x) ρ (args i)) =
        eqToHom (by rw [hm]) ≫ F.strAt B (fun i => M.interp ρ (args i)) ≫
          eqToHom (congrArg (fun g =>
            (N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B) hm.symm) :=
      F.strAt_eq_of_eq B hm
    have hcell : (N.co.appCell (x := Co.op x) B
        (fun i => F.toLax.eta (x := Co.op x) ρ (args i)) : _) =
        N.appCell B (fun i => eqToHom (hmc i) ≫
          F.eta ρ (args i) ≫ eqToHom (congr_fun hn i).symm) := by
      refine (PreModel.appCell_co N B _).trans ?_
      exact N.appCell_congr B ih
    dsimp only [Co.uncell] at hstr hcell ⊢
    rw [hcell]
    have hcomp := hstr =≫ N.appCell B (fun i =>
      eqToHom (hmc i) ≫ F.eta ρ (args i) ≫ eqToHom (congr_fun hn i).symm)
    refine hcomp.trans ?_
    rw [appCell_conj N B (funext hmc) hn]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end OplaxData

namespace OplaxData

variable {M N : Model Sg Obj} (F : OplaxData M.toPreModel N.toPreModel)

/-- The compatibility of oplax data with a transformation symbol is the lax compatibility of the
dual data. -/
lemma tr_compat_iff_co (a : Sg.Tr) :
    ((M.tr a ▷ F.cell (Sg.trty a)) ≫ F.eta (M.Pctx a).π (Sg.trtgt a)
      = F.eta (M.Pctx a).π (Sg.trsrc a) ≫
        N.trAt a (fun i => (M.Pctx a).π i ≫ F.cell (Sg.trt a i))) ↔
    ((N.co.trAt a (fun i => (M.co.Pctx a).π i ≫ F.toLax.cell (Sg.co.trt a i))) ≫
        F.toLax.eta (M.co.Pctx a).π (Sg.co.trtgt a)
      = F.toLax.eta (M.co.Pctx a).π (Sg.co.trsrc a) ≫
        (M.co.tr a ▷ F.toLax.cell (Sg.co.trty a))) := by
  have htr := N.trAt_co a (fun i => (M.co.Pctx a).π i ≫ F.toLax.cell (Sg.co.trt a i))
  have hm := M.co_tr a
  have heta₁ := F.toLax_eta (M.co.Pctx a).π (Sg.co.trtgt a)
  have heta₂ := F.toLax_eta (M.co.Pctx a).π (Sg.co.trsrc a)
  dsimp only [Co.uncell] at htr hm heta₁ heta₂
  rw [Co.comp_eq, Co.comp_eq, Co.whiskerRight_eq, hm, htr, heta₁, heta₂]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [eq_comm, eqToHom_comp_iff, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← Category.assoc, ← Category.assoc, comp_eqToHom_iff, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  rfl

end OplaxData

/-- An oplax morphism in `K` as a lax morphism of the dual models in `K^co`. -/
@[implicit_reducible]
def OplaxMor.toLax {M N : Model Sg Obj} (F : OplaxMor M N) : LaxMor M.co N.co where
  toLaxData := F.toOplaxData.toLax
  tr_compat a := (F.toOplaxData.tr_compat_iff_co a).1 (F.tr_compat a)

/-- Composition of oplax data is composition of the dual lax data. -/
lemma OplaxData.comp_toLax {M N P : PreModel Sg Obj} (F : OplaxData M N) (G : OplaxData N P) :
    (F.comp G).toLax = F.toLax.comp G.toLax := by
  have h : ∀ B, (F.toLax.comp G.toLax).str B = (F.comp G).toLax.str B := by
    intro B
    simp only [LaxData.comp, OplaxData.comp, OplaxData.toLax, Co.comp_eq, Co.eqToHom_eq,
      Category.assoc]
    exact congrArg (fun t => eqToHom _ ≫ F.str B ▷ G.cell _ ≫ t ≫ eqToHom _)
      (G.toLax_strAt B _)
  exact congr(LaxData.mk (M := M.co) (N := P.co) (fun c => F.cell c ≫ G.cell c)
    $(funext fun B => (h B).symm))

/-- **Proposition 3.11**, oplax form: the composite of oplax morphisms of models is an oplax
morphism. This is the lax case in `K^co`. -/
def OplaxMor.comp {M N P : Model Sg Obj} (F : OplaxMor M N) (G : OplaxMor N P) : OplaxMor M P where
  toOplaxData := F.toOplaxData.comp G.toOplaxData
  tr_compat a := ((F.toOplaxData.comp G.toOplaxData).tr_compat_iff_co a).2 (by
    rw [OplaxData.comp_toLax]
    exact (F.toLax.comp G.toLax).tr_compat a)

end UlmerBialgebras
