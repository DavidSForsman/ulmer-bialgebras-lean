module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import UlmerBialgebras.Models.Semantics

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Oplax morphisms of Σ-models

Definition 3.10 of *A Syntactic Approach to Ulmer's Bialgebras* for **oplax** morphisms: the
structure 2-cells point in the direction opposite to the lax ones,

`η^B : F_d ∘ M(B) ⇒ N(B) ∘ F_c̄`,

and so do the comparison 2-cells `η_t : F_c M(t) ⇒ N(t) F₀`.

Only the definitions and the compatibility of `η` with precomposition live here. The results
about oplax morphisms are obtained from the lax ones by duality: an oplax morphism in `K` is a lax
morphism of the dual models in `K^co` (`UlmerBialgebras/Models/CoMor.lean`).

## Main results

* `UlmerBialgebras.OplaxData`, `UlmerBialgebras.OplaxMor`: oplax morphisms of Σ-models
  (Definition 3.10).
* `UlmerBialgebras.OplaxData.eta`: the comparison 2-cell `η_t : F_c M(t) ⇒ N(t) F₀` at an
  environment.
* `UlmerBialgebras.OplaxData.eta_precomp`: compatibility of `η` with precomposition (Lemma 3.18,
  dual form).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Lemma 3.18
-/

universe u v w uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig}

/-- The data of an oplax morphism: a 1-cell for each category symbol and a structure 2-cell
for each functor symbol, pointing in the direction opposite to the lax one. -/
structure OplaxData (M N : PreModel Sg Obj) where
  /-- The 1-cell attached to a category symbol. -/
  cell : ∀ c : Sg.Cat, M.obj c ⟶ N.obj c
  /-- The structure 2-cell `η^B : F_d ∘ M(B) ⇒ N(B) ∘ F_c̄` attached to a functor symbol. -/
  str : ∀ B : Sg.Fun,
    (M.fn B ≫ cell (Sg.fcod B)) ⟶
      ((N.P B).lift (fun i => (M.P B).π i ≫ cell (Sg.art B i)) ≫ N.fn B)

namespace OplaxData

variable {M N : PreModel Sg Obj} (F : OplaxData M N)

/-- The 1-cell `F_c̄ : M_c̄ → N_c̄` on the product of an arity. -/
abbrev prodCell (B : Sg.Fun) : (M.P B).pt ⟶ (N.P B).pt :=
  (N.P B).lift (fun i => (M.P B).π i ≫ F.cell (Sg.art B i))

/-- Composing a lift into the product `M(c̄)` with `F_{c̄}` is the lift of the composites
`g i ≫ F_{c_i}`. -/
lemma lift_comp_prodCell (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (M.P B).lift g ≫ F.prodCell B = (N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) := by
  rw [(N.P B).comp_lift]
  exact congrArg _ (funext fun i => by rw [← Category.assoc, (M.P B).lift_π])

/-- The target of `OplaxData.strAt`: `⟨g⟩ ≫ F_{c̄} ≫ N(B)` is `⟨g_i ≫ F_{c_i}⟩ ≫ N(B)`. -/
lemma strAt_tgt_eq (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (M.P B).lift g ≫ F.prodCell B ≫ N.fn B =
      (N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B := by
  rw [← Category.assoc, F.lift_comp_prodCell]

/-- The structure 2-cell of an oplax morphism, at an arbitrary family of arguments. -/
def strAt (B : Sg.Fun) {x : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) :
    (((M.P B).lift g ≫ M.fn B) ≫ F.cell (Sg.fcod B)) ⟶
      ((N.P B).lift (fun i => g i ≫ F.cell (Sg.art B i)) ≫ N.fn B) :=
  eqToHom (Category.assoc ((M.P B).lift g) (M.fn B) (F.cell (Sg.fcod B))) ≫
    ((M.P B).lift g ◁ F.str B) ≫ eqToHom (strAt_tgt_eq F B g)

/-- The comparison 2-cell `η_{t}` of Definition 3.10 (2) for an oplax morphism, at an
arbitrary environment. -/
def eta {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v)) :
    ∀ {c : Sg.Cat} (t : Trm Sg.toFunSig vty c),
      M.interp ρ t ≫ F.cell c ⟶ N.interp (fun v => ρ v ≫ F.cell (vty v)) t
  | _, .var _ => 𝟙 _
  | _, .app B args =>
      F.strAt B (fun i => M.interp ρ (args i)) ≫ N.appCell B (fun i => eta ρ (args i))

/-- The comparison 2-cell `η_v` of an oplax morphism at a variable is the identity. -/
@[simp] lemma eta_var {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (v : V) : F.eta ρ (Trm.var v) = 𝟙 _ := by simp [eta]

/-- The comparison 2-cell of an oplax morphism at `B(args)` is the structure 2-cell `η^B`
followed by `N(B)` applied to the comparison 2-cells at the arguments. -/
@[simp] lemma eta_app {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (B : Sg.Fun) (args : ∀ i, Trm Sg.toFunSig vty (Sg.art B i)) :
    F.eta ρ (Trm.app B args) =
      F.strAt B (fun i => M.interp ρ (args i)) ≫ N.appCell B (fun i => F.eta ρ (args i)) := by
  simp [eta]

/-- Transporting `strAt` along an equality of the family of arguments. -/
lemma strAt_congr (B : Sg.Fun) {x : Obj} {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (e : ∀ i, g i = g' i) :
    F.strAt B g' = eqToHom (by rw [funext e]) ≫ F.strAt B g ≫ eqToHom (by rw [funext e]) := by
  have hgg : g = g' := funext e
  subst hgg
  simp

/-- `strAt` is compatible with precomposition. -/
lemma strAt_precomp (B : Sg.Fun) {x y : Obj} (g : ∀ i, x ⟶ M.obj (Sg.art B i)) (h : y ⟶ x) :
    h ◁ (F.strAt B g) = eqToHom (by rw [← Category.assoc, ← Category.assoc, (M.P B).comp_lift]) ≫
      F.strAt B (fun i => h ≫ g i) ≫
      eqToHom (by
        rw [show (fun i => (h ≫ g i) ≫ F.cell (Sg.art B i)) =
              (fun i => h ≫ (g i ≫ F.cell (Sg.art B i))) from funext fun i => Category.assoc _ _ _,
          ← (N.P B).comp_lift, ← Category.assoc]) := by
  rw [strAt, strAt]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [Bicategory.Strict.comp_whiskerLeft' h ((M.P B).lift g) (F.str B),
    Bicategory.whiskerLeft_congr ((M.P B).comp_lift h g).symm (F.str B)]
  simp

/-- Equation (3.3) of Lemma 3.18 (auxiliary form), dual form: compatibility of `η` with
precomposition. -/
lemma eta_precomp {V : Type uᵥ} {vty : V → Sg.Cat} {x y : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    (h : y ⟶ x) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    F.eta (fun v => h ≫ ρ v) t =
      eqToHom (by rw [← Category.assoc, ← M.interp_comp]) ≫
      (h ◁ F.eta ρ t) ≫
      eqToHom (by
        rw [show (fun v => (h ≫ ρ v) ≫ F.cell (vty v)) =
          (fun v => h ≫ (ρ v ≫ F.cell (vty v))) from funext fun v => Category.assoc _ _ _,
          N.interp_comp]) := by
  induction t with
  | var v => simp
  | app B args ih =>
      rw [eta_app, eta_app, N.appCell_congr B ih,
        F.strAt_congr B (g := fun i => h ≫ M.interp ρ (args i))
          (fun i => (M.interp_comp h ρ (args i)).symm),
        ← N.appCell_comp, ← N.appCell_comp, Bicategory.whiskerLeft_comp,
        N.whiskerLeft_appCell B (fun i => F.eta ρ (args i)) h,
        F.strAt_precomp B (fun i => M.interp ρ (args i)) h]
      simp

end OplaxData

/-- An oplax morphism of Σ-models (the dual of Definition 3.10). -/
structure OplaxMor (M N : Model Sg Obj) extends OplaxData M.toPreModel N.toPreModel where
  /-- Compatibility with the transformation symbols, Definition 3.10 (3), dual form. -/
  tr_compat : ∀ a : Sg.Tr,
    (M.tr a ▷ toOplaxData.cell (Sg.trty a)) ≫ toOplaxData.eta (M.Pctx a).π (Sg.trtgt a)
      = toOplaxData.eta (M.Pctx a).π (Sg.trsrc a) ≫
        (N.trAt a (fun i => (M.Pctx a).π i ≫ toOplaxData.cell (Sg.trt a i)))

end UlmerBialgebras
