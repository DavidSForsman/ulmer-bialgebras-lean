module

public import UlmerBialgebras.Models.CoModel
public import UlmerBialgebras.Syntax.PathOps
public import UlmerBialgebras.Models.Bialgebra

/-!
# Dual 1-signatures and theories

For a 1-signature `σ` relative to `Σ`, the dual `σ^co` relative to `Σ^co` has the same sorts and
function symbols, with the domain and codomain of each function symbol swapped. Every arrow of
the term graph of `σ` reverses to an arrow of the term graph of `σ^co`, and paths reverse
accordingly. A `σ`-theory `T` gives a `σ^co`-theory `T^co` with the domain and codomain of each
equation swapped and both of its paths reversed. The dual of an algebraic theory is
coalgebraic, and conversely.

Together with `UlmerBialgebras.Model.co` this realises the paper's duality between the lax and the
oplax forms of Lemma 3.21, Theorem 3.22 and Corollary 3.23: the object of `T`-bialgebras of `M` in
`K` is the object of `T^co`-bialgebras of `M^co` in `K^co`.

## Main results

* `UlmerBialgebras.OneSig.co`: the dual 1-signature `σ^co`.
* `UlmerBialgebras.OneSig.Path.co`: the reverse of a path of the term graph of `σ`, a path of the
  term graph of `σ^co`.
* `UlmerBialgebras.Theory.co`: the dual theory `T^co`.
* `UlmerBialgebras.Theory.IsCoalgebraic.co`: the dual of a coalgebraic theory is algebraic.
* `UlmerBialgebras.Model.pathCell_co`: evaluating the reverse of a path in `M^co` gives the 2-cell
  of the path in `M` (Definition 3.14).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 3.7, 3.14, Lemma 3.21, Theorem 3.22 and Corollary 3.23
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory
open scoped CategoryTheory.Bicategory

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- The dual of a 1-signature: the domain and codomain of each function symbol swapped. -/
@[implicit_reducible]
def OneSig.co (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) : OneSig Sg.co where
  Srt := sg.Srt
  sty := sg.sty
  Fn := sg.Fn
  fnty := sg.fnty
  fndom := sg.fncod
  fncod := sg.fndom

namespace OneSig

variable {sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg}

/-- The reverse of an arrow of the term graph of `σ`, an arrow of the term graph of `σ^co`. -/
def Arr.co : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Arr t t' → sg.co.Arr t' t
  | _, _, _, .fn f => .fn (sg := sg.co) f
  | _, _, _, .tr a sub => .tr (sg := sg.co) a sub
  | _, _, _, .app B i args args' hne g =>
      .app (sg := sg.co) B i args' args (fun j hj => (hne j hj).symm) g.co

/-- The reverse of a path of the term graph of `σ`, a path of the term graph of `σ^co`. -/
def Path.co : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Path t t' → sg.co.Path t' t
  | _, _, _, .nil t => .nil (sg := sg.co) t
  | _, _, _, .cons g p => p.co.comp (.cons g.co (.nil _))

/-- The reverse of the arrow `Arr.app B i args args' hne g` is the arrow `Arr.app` of `σ^co`
from `args'` to `args` in slot `i`, with `g.co`. -/
@[simp] lemma Arr.co_app (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i)) :
    (Arr.app B i args args' hne g).co =
      .app (sg := sg.co) B i args' args (fun j hj => (hne j hj).symm) g.co := rfl

end OneSig

/-- The dual of a theory: the domain and codomain of each equation swapped, and both of its
paths reversed. -/
def Theory.co {sg : OneSig Sg} (T : Theory sg) : Theory sg.co where
  Eqn := T.Eqn
  eqty := T.eqty
  dom := T.cod
  cod := T.dom
  lhs r := (T.lhs r).co
  rhs r := (T.rhs r).co

/-- The dual of a coalgebraic theory is algebraic. -/
lemma Theory.IsCoalgebraic.co {sg : OneSig Sg} {T : Theory sg} (h : T.IsCoalgebraic) :
    T.co.IsAlgebraic := h

section Semantics

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]

/-- Applying a functor symbol to 2-cells in `K^co` is applying it in `K`. -/
theorem PreModel.appCell_co (M : PreModel Sg Obj) (B : Sg.Fun) {x : Obj}
    {g g' : ∀ i, x ⟶ M.obj (Sg.art B i)} (γ : ∀ i, g' i ⟶ g i) :
    (M.co.appCell (x := Co.op x) B (g := g) (g' := g') γ :
      (M.P B).lift g' ≫ M.fn B ⟶ (M.P B).lift g ≫ M.fn B) = M.appCell B γ := by
  simp only [PreModel.appCell, Co.comp_eq, Co.eqToHom_eq, Category.assoc]
  rfl

/-- Closed terms are interpreted over `M₀` in `K^co` as in `K`. -/
lemma Model.tm_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] {c : Sg.Cat} (t : sg.CTrm c) :
    M.co.tm sg.co t = M.tm sg t :=
  M.toPreModel.co_interp (x := Co.op (M.P0 sg).pt) (M.P0 sg).π t

/-- The arity 1-cell of `M^co` for `σ^co` is the coarity 1-cell of `M` for `σ`. -/
lemma Model.domCell_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj] :
    M.co.domCell sg.co = M.codCell sg := by
  simp only [Model.domCell, Model.codCell]
  congr 1
  funext f
  exact M.tm_co sg (sg.fncod f)

/-- The coarity 1-cell of `M^co` for `σ^co` is the arity 1-cell of `M` for `σ`. -/
lemma Model.codCell_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj] :
    M.co.codCell sg.co = M.domCell sg := by
  simp only [Model.domCell, Model.codCell]
  congr 1
  funext f
  exact M.tm_co sg (sg.fndom f)

variable [HasChosenInserters.{u, v, w} Obj]

/-- **Duality for objects of operations**: `(M^co)^{σ^co}` in `K^co` is `M^σ` in `K`. -/
lemma Model.sigObj_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj] :
    Co.unop (M.co.sigObj sg.co) = M.sigObj sg :=
  congrArg₂ (fun (d c : (M.P0 sg).pt ⟶ (M.Pfn sg).pt) =>
      (HasChosenInserters.ins (Obj := Obj) d c).pt)
    (M.codCell_co sg) (M.domCell_co sg)

/-- The canonical 1-cell `u` of `M^co` for `σ^co` agrees with `u` of `M` for `σ` up to
`sigObj_co`. -/
lemma Model.u_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj] :
    (M.co.u sg.co : Co.unop (M.co.sigObj sg.co) ⟶ (M.P0 sg).pt) =
      eqToHom (M.sigObj_co sg) ≫ M.u sg := by
  have key : ∀ (d c : (M.P0 sg).pt ⟶ (M.Pfn sg).pt)
      (hd : d = M.domCell sg) (hc : c = M.codCell sg),
      (HasChosenInserters.ins (Obj := Obj) d c).u =
        eqToHom (congrArg₂ (fun (d' c' : (M.P0 sg).pt ⟶ (M.Pfn sg).pt) =>
            (HasChosenInserters.ins (Obj := Obj) d' c').pt) hd hc) ≫
          (M.sigIns sg).u := by
    intro d c hd hc; subst hd; subst hc; simp; rfl
  exact key _ _ (M.codCell_co sg) (M.domCell_co sg)

/-- Evaluating a closed term on `(M^co)^{σ^co}` agrees with `M^σ(t)` up to `sigObj_co`. -/
lemma Model.sigTm_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    {c : Sg.Cat} (t : sg.CTrm c) :
    (show Co.unop (M.co.sigObj sg.co) ⟶ M.obj c from M.co.sigTm sg.co t) =
      eqToHom (M.sigObj_co sg) ≫ M.sigTm sg t := by
  rw [Model.sigTm_eq, Model.sigTm_eq, M.tm_co sg t, M.u_co sg]
  exact Bicategory.Strict.assoc _ _ _

omit [HasChosenInserters.{u, v, w} Obj] in
/-- Transformation symbols are interpreted in `K^co` as in `K`, up to `PreModel.co_interp`. -/
lemma Model.trAt_co (M : Model Sg Obj) (a : Sg.Tr) {x : Co Obj}
    (ρ : ∀ i, x ⟶ M.co.obj (Sg.co.trt a i)) :
    Co.uncell (M.co.trAt (x := x) a ρ) =
      @eqToHom (Co.unop x ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := x) ρ (Sg.trsrc a)) ≫
        M.trAt a ρ ≫
        @eqToHom (Co.unop x ⟶ M.obj (Sg.trty a)) _ _ _
          (M.toPreModel.co_interp (x := x) ρ (Sg.trtgt a)).symm := by
  dsimp only [Co.uncell]
  rw [Model.trAt, Model.trAt]
  simp only [Co.comp_eq, Co.eqToHom_eq, Co.whiskerLeft_eq, Category.assoc]
  have htr_co := M.co_tr a
  dsimp only [Co.uncell] at htr_co ⊢
  rw [htr_co]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]
  congr 2

/-- Evaluation of an arrow `OneSig.Arr.fn f` in `M.co` reduces to `M.arrCell` up to `eqToHom`. -/
private lemma Model.arrCell_co_fn (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (f : sg.Fn) :
    Co.uncell (M.co.arrCell sg.co (OneSig.Arr.fn f).co) =
      eqToHom (M.sigTm_co sg (sg.fndom f)) ≫
        (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg (OneSig.Arr.fn f)) ≫
        eqToHom (M.sigTm_co sg (sg.fncod f)).symm := by
  rw [OneSig.Arr.co, Model.arrCell_fn, Model.arrCell_fn]
  simp only [Co.comp_eq, Co.eqToHom_eq, Category.assoc]
  have key : ∀ (d c : (M.P0 sg).pt ⟶ (M.Pfn sg).pt)
      (hd : d = M.domCell sg) (hc : c = M.codCell sg)
      (hx : (HasChosenInserters.ins (Obj := Obj) d c).pt = M.sigObj sg),
      (HasChosenInserters.ins (Obj := Obj) d c).φ =
        eqToHom (by subst hd hc; cases hx; exact (Bicategory.Strict.id_comp _).symm) ≫
          (eqToHom hx ◁ (M.sigIns sg).φ) ≫
          eqToHom (by subst hd hc; cases hx; exact Bicategory.Strict.id_comp _) := by
    intro d c hd hc hx; subst hd hc; cases hx
    change (M.sigIns sg).φ = eqToHom _ ≫ (𝟙 _ ◁ (M.sigIns sg).φ) ≫ eqToHom _
    rw [Bicategory.Strict.id_whiskerLeft]
    simp only [Category.assoc]
    rw [← Category.assoc (eqToHom _), eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hphi := key _ _ (M.codCell_co sg) (M.domCell_co sg) (M.sigObj_co sg)
  dsimp only [Co.uncell]
  change _ ≫ ((HasChosenInserters.ins (Obj := Obj) (M.co.codCell sg.co)
      (M.co.domCell sg.co)).φ ▷ (M.Pfn sg).π f) ≫ _ = _
  rw [hphi]
  simp only [Bicategory.comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
  rw [Bicategory.Strict.whisker_assoc]
  simp

/-- Evaluation of `OneSig.Arr.tr a sub` in `M.co` reduces to `M.arrCell` up to `eqToHom`. -/
private lemma Model.arrCell_co_tr (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
    Co.uncell (M.co.arrCell sg.co (OneSig.Arr.tr a sub).co) =
      eqToHom (M.sigTm_co sg ((Sg.trsrc a).subst sub)) ≫
        (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg (OneSig.Arr.tr a sub)) ≫
        eqToHom (M.sigTm_co sg ((Sg.trtgt a).subst sub)).symm := by
  -- Both sides are `trAt a` at the environment `sigTm (sub i)`; `trAt_co` computes the left
  -- side in `K`, and `key` moves its environment, `eqToHom (sigObj_co) ≫ sigTm (sub i)`, out
  -- as a whiskering by `eqToHom (sigObj_co)` (by `cases` on the object).
  rw [OneSig.Arr.co, Model.arrCell_tr, Model.arrCell_tr]
  simp only [Co.comp_eq, Co.eqToHom_eq, Category.assoc]
  change _ ≫ Co.uncell (M.co.trAt (x := M.co.sigObj sg.co) a
      (fun i => M.co.sigTm sg.co (sub i))) ≫ _ = _
  rw [M.trAt_co a (x := M.co.sigObj sg.co) (fun i => M.co.sigTm sg.co (sub i))]
  have key : ∀ (x : Co Obj) (hx : Co.unop x = M.sigObj sg)
      (σ : ∀ i, x ⟶ M.co.obj (Sg.co.trt a i))
      (hσ : ∀ i, (σ i : Co.unop x ⟶ M.obj (Sg.trt a i)) = eqToHom hx ≫ M.sigTm sg (sub i)),
      ∃ (hsrc : M.toPreModel.interp (x := x.unop) σ (Sg.trsrc a) =
          eqToHom hx ≫ M.toPreModel.interp (fun i => M.sigTm sg (sub i)) (Sg.trsrc a))
        (htgt : eqToHom hx ≫ M.toPreModel.interp (fun i => M.sigTm sg (sub i)) (Sg.trtgt a) =
          M.toPreModel.interp (x := x.unop) σ (Sg.trtgt a)),
        M.trAt a σ =
          eqToHom hsrc ≫ (eqToHom hx ◁ M.trAt a (fun i => M.sigTm sg (sub i))) ≫
            eqToHom htgt := by
    intro x hx σ hσ
    cases x with
    | op x =>
      dsimp only [Co.unop] at hx; subst hx
      have hσ' : σ = fun i => M.sigTm sg (sub i) :=
        funext fun i => by simpa [Bicategory.Strict.id_comp] using hσ i
      subst hσ'
      simp only [eqToHom_refl]
      refine ⟨(Bicategory.Strict.id_comp _).symm, Bicategory.Strict.id_comp _, ?_⟩
      rw [Bicategory.Strict.id_whiskerLeft]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
        Category.id_comp, Category.comp_id]
  obtain ⟨_, _, htr⟩ := key (M.co.sigObj sg.co) (M.sigObj_co sg)
    (fun i => M.co.sigTm sg.co (sub i)) (fun i => M.sigTm_co sg (sub i))
  rw [htr]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]

/-- Evaluation of an arrow `OneSig.Arr.app` in `M.co` reduces to `M.arrCell` up to `eqToHom`. -/
private lemma Model.arrCell_co_app (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i))
    (ih : Co.uncell (M.co.arrCell sg.co g.co) =
      eqToHom (M.sigTm_co sg (args i)) ≫ (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg g) ≫
        eqToHom (M.sigTm_co sg (args' i)).symm) :
    Co.uncell (M.co.arrCell sg.co (OneSig.Arr.app B i args args' hne g).co) =
      eqToHom (M.sigTm_co sg (.app B args)) ≫
        (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg (OneSig.Arr.app B i args args' hne g)) ≫
        eqToHom (M.sigTm_co sg (.app B args')).symm := by
  -- `appCell` is `lift₂ (…) ▷ fn B`. The lifts into the product along `sigTm` in `K^co` and in
  -- `K` differ by `eqToHom (sigObj_co)` (`hlift_eq`); component by component (`cell_ext`) the
  -- `i`-th cell is `ih` and the others are `eqToHom`s.
  rw [OneSig.Arr.co_app, Model.arrCell_app, Model.arrCell_app]
  refine (PreModel.appCell_co M.toPreModel B _).trans ?_
  simp only [PreModel.appCell]
  have hlift_eq : ∀ (ts : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j)),
      (M.P B).lift (fun j => M.co.sigTm sg.co (ts j)) =
        eqToHom (M.sigObj_co sg) ≫ (M.P B).lift (fun j => M.sigTm sg (ts j)) := by
    intro ts
    refine Eq.trans ?_ ((M.P B).lift_uniq
      (eqToHom (M.sigObj_co sg) ≫ (M.P B).lift fun j => M.sigTm sg (ts j)))
    congr 1; funext j
    rw [Bicategory.Strict.assoc, Product.lift_π]
    exact M.sigTm_co sg (ts j)
  have hwa : ∀ {a b c d : Obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) (k : c ⟶ d),
      (f ◁ η) ▷ k = eqToHom (Bicategory.Strict.assoc f g k) ≫ (f ◁ (η ▷ k)) ≫
        eqToHom (Bicategory.Strict.assoc f h k).symm := by
    intro a b c d f g h η k
    rw [Bicategory.Strict.whisker_assoc]
    simp [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl]
  refine Eq.trans (congrArg (· ▷ M.fn B) (show _ = eqToHom (hlift_eq args) ≫
      (eqToHom (M.sigObj_co sg) ◁ (M.P B).lift₂ (fun j =>
        eqToHom (Product.lift_π _ _ j) ≫
          (if hj : j = i then
            cast (congrArg (fun k => M.sigTm sg (args k) ⟶ M.sigTm sg (args' k)) hj.symm)
              (M.arrCell sg g)
          else eqToHom (by rw [hne j hj])) ≫
          eqToHom (Product.lift_π (M.P B) (fun k => M.sigTm sg (args' k)) j).symm)) ≫
      eqToHom (hlift_eq args').symm from by
    apply (M.P B).cell_ext
    intro j
    rw [(M.P B).lift₂_π, Bicategory.comp_whiskerRight, Bicategory.comp_whiskerRight]
    rw [hwa, (M.P B).lift₂_π]
    simp only [Bicategory.whiskerLeft_comp, Category.assoc]
    by_cases hj : j = i
    · subst hj
      simp only [cast_eq, ↓reduceDIte]
      dsimp only [Co.uncell] at ih
      rw [ih]
      simp
    · simp only [dite_eq_right hj, Co.eqToHom_eq]
      conv_lhs => rw [eqToHom_trans_assoc, eqToHom_trans]
      simp)) ?_
  simp only [Bicategory.comp_whiskerRight]
  rw [hwa]
  simp

/-- Evaluation of an arrow `g.co` in `M.co` reduces to `M.arrCell sg g` up to `eqToHom`. -/
theorem Model.arrCell_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    {c : Sg.Cat}
    {t t' : sg.CTrm c}
    (g : sg.Arr t t') :
    Co.uncell (M.co.arrCell sg.co g.co) =
      eqToHom (M.sigTm_co sg t) ≫ (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg g) ≫
        eqToHom (M.sigTm_co sg t').symm := by
  induction g with
  | fn f => exact M.arrCell_co_fn sg f
  | tr a sub => exact M.arrCell_co_tr sg a sub
  | app B i args args' hne g ih => exact M.arrCell_co_app sg B i args args' hne g ih

/-- Evaluation of a concatenation of paths. -/
lemma Model.pathCell_comp (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    {c : Sg.Cat}
    {t t' t'' : sg.CTrm c} (p : sg.Path t t') (q : sg.Path t' t'') :
    M.pathCell sg (p.comp q) = M.pathCell sg p ≫ M.pathCell sg q := by
  induction p with
  | nil t => simp [OneSig.Path.comp]
  | cons g p ih => simp [OneSig.Path.comp, ih]

/-- Evaluating the reverse of a path in the dual model gives the path's 2-cell. -/
theorem Model.pathCell_co (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    {c : Sg.Cat}
    {t t' : sg.CTrm c}
    (p : sg.Path t t') :
    Co.uncell (M.co.pathCell sg.co p.co) =
      eqToHom (M.sigTm_co sg t) ≫ (eqToHom (M.sigObj_co sg) ◁ M.pathCell sg p) ≫
        eqToHom (M.sigTm_co sg t').symm := by
  induction p with
  | nil t =>
    rw [OneSig.Path.co, Model.pathCell_nil, Model.pathCell_nil]
    simp
    rfl
  | cons g p ih =>
    rw [OneSig.Path.co, Model.pathCell_comp, Model.pathCell_cons, Model.pathCell_nil,
      Model.pathCell_cons]
    simp only [Co.comp_eq, Category.assoc]
    dsimp only [Co.uncell]
    refine (Category.id_comp _).trans ?_
    have h1 : Co.uncell (M.co.arrCell sg.co g.co) =
        eqToHom (M.sigTm_co sg _) ≫ (eqToHom (M.sigObj_co sg) ◁ M.arrCell sg g) ≫
          eqToHom (M.sigTm_co sg _).symm := M.arrCell_co sg g
    have h2 : Co.uncell (M.co.pathCell sg.co p.co) =
        eqToHom (M.sigTm_co sg _) ≫ (eqToHom (M.sigObj_co sg) ◁ M.pathCell sg p) ≫
          eqToHom (M.sigTm_co sg _).symm := ih
    dsimp only [Co.uncell] at h1 h2
    rw [h1, h2]
    simp [Bicategory.whiskerLeft_comp]

end Semantics

end UlmerBialgebras
