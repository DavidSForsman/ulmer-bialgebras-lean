module

public import UlmerBialgebras.Models.Lax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Proposition 3.11: identities and composites of lax morphisms

Let `(F, η) : M → N` and `(G, θ) : N → P` be lax morphisms of Σ-models.  Their composite is
a lax morphism, whose structure 2-cell at a functor symbol `B : c̄ → d` is

`ϕ^B : P(B) ∘ (GF)_c̄ ⟹ G_d ∘ N(B) ∘ F_c̄ ⟹ (GF)_d ∘ M(B)`,

the first 2-cell being `θ^B` whiskered by `F_c̄` and the second `G_d` whiskered by `η^B`.
The identity data is a lax morphism, and strong morphisms (those whose structure 2-cells are
invertible) are closed under identities and composition.

The main technical statement is `UlmerBialgebras.LaxData.eta_comp`, the corresponding factorization
of the comparison 2-cells `η_t` of a composite,

`ϕ_t : P_x̄(t) ∘ (GF)_x̄ ⟹ G_c ∘ N_x̄(t) ∘ F_x̄ ⟹ (GF)_c ∘ M_x̄(t)`,

which is what makes the compatibility with the transformation symbols (Definition 3.10 (3))
of the composite follow from that of the two factors.

## Main results

* `UlmerBialgebras.LaxData.comp`: the composite of lax data (Proposition 3.11).
* `UlmerBialgebras.LaxData.comp_str_isIso`: the composite of strong data has invertible structure
  2-cells.
* `UlmerBialgebras.LaxData.eta_comp`: the factorization of the comparison 2-cells `η_t` of a
  composite.
* `UlmerBialgebras.LaxMor.comp`: lax morphisms of Σ-models are closed under composition
  (Proposition 3.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Proposition 3.11
-/

universe u v w uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

namespace LaxData

/-! ## The identity lax morphism -/

/-! ## Composition -/

variable {M N Pm : PreModel Sg Obj}

/-- Reassociates the composite 1-cell projections in `LaxData.comp`. -/
lemma comp_prod_lift_eq (F : LaxData M N) (G : LaxData N Pm) (B : Sg.Fun) :
    (Pm.P B).lift (fun i => (M.P B).π i ≫ F.cell (Sg.art B i) ≫ G.cell (Sg.art B i)) ≫
        Pm.fn B =
      (Pm.P B).lift (fun i => ((M.P B).π i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) ≫
        Pm.fn B := by
  rw [show (fun i => (M.P B).π i ≫ (F.cell (Sg.art B i) ≫ G.cell (Sg.art B i))) =
    (fun i => ((M.P B).π i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) from
    funext fun i => (Category.assoc _ _ _).symm]

/-- The composite of two lax morphisms of Σ-models (Proposition 3.11). -/
def comp (F : LaxData M N) (G : LaxData N Pm) : LaxData M Pm where
  cell c := F.cell c ≫ G.cell c
  str B :=
    eqToHom (comp_prod_lift_eq F G B) ≫
    G.strAt B (fun i => (M.P B).π i ≫ F.cell (Sg.art B i)) ≫
    (F.str B ▷ G.cell (Sg.fcod B)) ≫
    eqToHom (Category.assoc (M.fn B) (F.cell (Sg.fcod B)) (G.cell (Sg.fcod B)))
/-- The 1-cell of the composite `F.comp G` at `c` is `F.cell c ≫ G.cell c`. -/
@[simp] lemma comp_cell (F : LaxData M N) (G : LaxData N Pm) (c : Sg.Cat) :
    (F.comp G).cell c = F.cell c ≫ G.cell c := rfl


/-- Unfolding of the structure 2-cell of `F.comp G` at `B`: `G.strAt` then `F.str B ▷ G.cell`,
up to `eqToHom`s. -/
lemma comp_str (F : LaxData M N) (G : LaxData N Pm) (B : Sg.Fun) :
    (F.comp G).str B =
      eqToHom (by
        rw [show (fun i => (M.P B).π i ≫ (F.comp G).cell (Sg.art B i)) =
          (fun i => ((M.P B).π i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) from
          funext fun i => (Category.assoc _ _ _).symm]) ≫
      G.strAt B (fun i => (M.P B).π i ≫ F.cell (Sg.art B i)) ≫
      (F.str B ▷ G.cell (Sg.fcod B)) ≫
      eqToHom (by simp only [comp_cell, Category.assoc]) := rfl

/-- The structure 2-cells of a composite of lax morphisms are invertible when those of both
factors are. -/
instance comp_str_isIso (F : LaxData M N) (G : LaxData N Pm) (B : Sg.Fun)
    [IsIso (F.str B)] [IsIso (G.str B)] : IsIso ((F.comp G).str B) := by
  rw [comp_str]; infer_instance

/-- The structure 2-cell of a composite, at an arbitrary family of arguments. -/
lemma comp_strAt (F : LaxData M N) (G : LaxData N Pm) (B : Sg.Fun) {x : Obj}
    (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (F.comp G).strAt B g
      = eqToHom (by
          rw [show (fun i => g i ≫ (F.comp G).cell (Sg.art B i)) =
            (fun i => (g i ≫ F.cell (Sg.art B i)) ≫ G.cell (Sg.art B i)) from
            funext fun i => (Category.assoc _ _ _).symm]) ≫
        G.strAt B (fun i => g i ≫ F.cell (Sg.art B i)) ≫
        (F.strAt B g ▷ G.cell (Sg.fcod B)) ≫
        eqToHom (by simp only [comp_cell, Category.assoc]) := by
  rw [strAt, comp_str]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [G.strAt_precomp B (fun i => (M.P B).π i ≫ F.cell (Sg.art B i)) ((M.P B).lift g),
    G.strAt_congr B (g := fun i => g i ≫ F.cell (Sg.art B i))
      (fun i => by rw [← Category.assoc, (M.P B).lift_π]),
    Bicategory.Strict.whisker_assoc]
  simp only [strAt, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc]
  simp only [eqToHom_trans_assoc, eqToHom_trans]

/-- **Proposition 3.11**: the comparison 2-cells of a composite factor through the comparison
2-cells of the two factors. -/
lemma eta_comp (F : LaxData M N) (G : LaxData N Pm) {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj}
    (ρ : ∀ v, x ⟶ M.obj (vty v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    (F.comp G).eta ρ t
      = eqToHom (by
          rw [show (fun v => ρ v ≫ (F.comp G).cell (vty v)) =
            (fun v => (ρ v ≫ F.cell (vty v)) ≫ G.cell (vty v)) from
            funext fun v => (Category.assoc _ _ _).symm]) ≫
        G.eta (fun v => ρ v ≫ F.cell (vty v)) t ≫
        (F.eta ρ t ▷ G.cell c) ≫
        eqToHom (by simp only [comp_cell, Category.assoc]) := by
  induction t with
  | var v =>
      rw [eta_var, eta_var, eta_var, Bicategory.id_whiskerRight, Category.id_comp,
        Category.id_comp]
      exact ((eqToHom_trans _ _).trans (eqToHom_refl _ _)).symm
  | app B args ih =>
      rw [eta_app, eta_app, eta_app, Pm.appCell_congr B ih, comp_strAt,
        ← Pm.appCell_comp, ← Pm.appCell_comp, ← Pm.appCell_comp]
      simp only [Pm.appCell_eqToHom, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp, Bicategory.comp_whiskerRight]
      rw [reassoc_of% (G.strAt_nat B (fun i => F.eta ρ (args i)))]

end LaxData

namespace LaxMor

variable {M N Pm : Model Sg Obj}

/-- The composite of the underlying data of two lax morphisms is compatible with the
transformation symbols. -/
lemma comp_tr_compat (F : LaxMor M N) (G : LaxMor N Pm) (a : Sg.Tr) :
    Pm.trAt a (fun i => (M.Pctx a).π i ≫ (F.toLaxData.comp G.toLaxData).cell (Sg.trt a i)) ≫
        (F.toLaxData.comp G.toLaxData).eta (M.Pctx a).π (Sg.trtgt a)
      = (F.toLaxData.comp G.toLaxData).eta (M.Pctx a).π (Sg.trsrc a) ≫
        (M.tr a ▷ (F.toLaxData.comp G.toLaxData).cell (Sg.trty a)) := by
  rw [LaxData.eta_comp, LaxData.eta_comp]
  rw [Pm.trAt_congr a (ρ := fun i => ((M.Pctx a).π i ≫ F.cell (Sg.trt a i)) ≫ G.cell (Sg.trt a i))
    (fun i => by rw [LaxData.comp_cell, Category.assoc])]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [reassoc_of% (G.tr_compat_at a (fun i => (M.Pctx a).π i ≫ F.cell (Sg.trt a i)))]
  slice_lhs 3 4 => rw [← Bicategory.comp_whiskerRight, F.tr_compat a, Bicategory.comp_whiskerRight]
  have htr : eqToHom (by simp only [LaxData.comp_cell, Category.assoc]) ≫
      (M.tr a ▷ (F.toLaxData.comp G.toLaxData).cell (Sg.trty a)) =
      ((M.tr a ▷ F.cell (Sg.trty a)) ▷ G.cell (Sg.trty a)) ≫
        eqToHom (by simp only [LaxData.comp_cell, Category.assoc]) := by
    change eqToHom (Category.assoc _ _ _) ≫
        (M.tr a ▷ (F.cell (Sg.trty a) ≫ G.cell (Sg.trty a))) =
      ((M.tr a ▷ F.cell (Sg.trty a)) ▷ G.cell (Sg.trty a)) ≫
        eqToHom (Category.assoc _ _ _)
    simp [Bicategory.Strict.associator_eqToIso]
  rw [htr]
  simp only [Category.assoc]

/-- **Proposition 3.11**: lax morphisms of Σ-models are closed under composition. -/
def comp (F : LaxMor M N) (G : LaxMor N Pm) : LaxMor M Pm where
  toLaxData := F.toLaxData.comp G.toLaxData
  tr_compat := F.comp_tr_compat G

end LaxMor

end UlmerBialgebras
