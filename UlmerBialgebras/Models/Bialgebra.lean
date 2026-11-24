module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.ZeroLEOne
public import UlmerBialgebras.Models.Lax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The objects `M^σ` of operations and `M^T` of bialgebras

Definitions 3.13 and 3.14 of *A Syntactic Approach to Ulmer's Bialgebras*; together
they give the bialgebraic datum of Proposition 3.15.

## Main results

* `UlmerBialgebras.Model.sigIns`: the inserter defining the object of operations `M^σ`
  (Definition 3.13).
* `UlmerBialgebras.Model.pathCell`: the evaluation `p̄_M` of a path of the term graph
  (Definition 3.14).
* `UlmerBialgebras.Model.thyEquif`: the equifier defining the object `M^T` of `T`-bialgebras
  (Definition 3.14), with `UlmerBialgebras.Model.thyObj` its vertex and `UlmerBialgebras.Model.e`
  its 1-cell.
* `UlmerBialgebras.Model.sigTm_subst`: the term 1-cells of `M^σ` commute with substitution.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 3.13, 3.14 and Proposition 3.15
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras]
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- An equifier of `η, θ` is an equifier of any `η' = η` and `θ' = θ`, with the same vertex and
1-cell. -/
def Equifier.ofEq {a b : Obj} {f g : a ⟶ b} {η θ η' θ' : f ⟶ g} (E : Equifier η θ)
    (h₁ : η = η') (h₂ : θ = θ') : Equifier η' θ' where
  pt := E.pt
  e := E.e
  cond := h₁ ▸ h₂ ▸ E.cond
  lift h H := E.lift h (h₁ ▸ h₂ ▸ H)
  lift_e h _ := E.lift_e h _
  lift_uniq k h _ hk := E.lift_uniq k h _ hk
  full β := E.full β
  faithful α β := E.faithful α β

namespace Model

/-! ### Evaluation of the term graph

`arrCellAlg` and `pathCellAlg` evaluate the arrows and the paths of the term graph at an
environment and a choice of 2-cells for the function symbols. -/

section Eval

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

omit [Bicategory Obj] [Bicategory.Strict Obj] [HasChosenFinProducts Obj] in
/-- Equality helper for off-coordinate terms in `arrCellAlg` and `arrCell`. -/
lemma arrCell_ne_eq {α : Type*} {B : Sg.Fun} {i : Fin (Sg.arn B)}
    {args args' : ∀ j, sg.CTrm (Sg.art B j)} (hne : ∀ j ≠ i, args j = args' j)
    (j : Fin (Sg.arn B)) (hj : j ≠ i) (F : sg.CTrm (Sg.art B j) → α) :
    F (args j) = F (args' j) := by
  rw [hne j hj]

/-- The evaluation of an arrow of the term graph at an environment `ρ : ∀ s, a ⟶ M_{c_s}` and a
choice of 2-cells `ψ f : M(t₁)(ρ) ⟶ M(t₂)(ρ)` for the function symbols `f : t₁ → t₂`. On `M^σ`,
with the inserter 2-cells, it is `Model.arrCellOf`. -/
def arrCellAlg {a : Obj} (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f)) :
    ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Arr t t' → (M.interp ρ t ⟶ M.interp ρ t')
  | _, _, _, .fn f => ψ f
  | _, _, _, .tr a sub =>
      eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trsrc a)) ≫
        M.trAt a (fun i => M.interp ρ (sub i)) ≫
        eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trtgt a)).symm
  | _, _, _, .app B i args args' hne g =>
      M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.interp ρ (args k) ⟶ M.interp ρ (args' k))) hj.symm)
            (arrCellAlg ρ ψ g)
        else eqToHom (arrCell_ne_eq sg hne j hj (M.interp ρ)))

/-- The evaluation of a path of the term graph at an environment and a choice of 2-cells for the
function symbols (see `Model.arrCellAlg`). -/
def pathCellAlg {a : Obj} (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
    (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f)) :
    ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Path t t' → (M.interp ρ t ⟶ M.interp ρ t')
  | _, _, _, .nil _ => 𝟙 _
  | _, _, _, .cons g p => M.arrCellAlg sg ρ ψ g ≫ pathCellAlg ρ ψ p

section AlgLemmas

variable {a : Obj} (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
  (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))

/-- `pathCellAlg` sends the empty path to the identity 2-cell. -/
@[simp] lemma pathCellAlg_nil {c : Sg.Cat} (t : sg.CTrm c) :
    M.pathCellAlg sg ρ ψ (OneSig.Path.nil t) = 𝟙 _ := by
  simp only [pathCellAlg]

/-- `pathCellAlg` of `cons g p` is the vertical composite of `arrCellAlg g` and `pathCellAlg p`. -/
@[simp] lemma pathCellAlg_cons {c : Sg.Cat} {t t' t'' : sg.CTrm c} (g : sg.Arr t t')
    (p : sg.Path t' t'') :
    M.pathCellAlg sg ρ ψ (OneSig.Path.cons g p) =
      M.arrCellAlg sg ρ ψ g ≫ M.pathCellAlg sg ρ ψ p := by
  simp only [pathCellAlg]

/-- `arrCellAlg` on a function-symbol arrow `fn f` is the chosen 2-cell `ψ f`. -/
lemma arrCellAlg_fn (f : sg.Fn) : M.arrCellAlg sg ρ ψ (OneSig.Arr.fn f) = ψ f := by
  simp [arrCellAlg]

/-- `arrCellAlg` on a transformation arrow `tr a sub` is `trAt a`, conjugated by the
substitution equalities `interp_subst`. -/
lemma arrCellAlg_tr (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
    M.arrCellAlg sg ρ ψ (OneSig.Arr.tr a sub) =
      eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trsrc a)) ≫
        M.trAt a (fun i => M.interp ρ (sub i)) ≫
        eqToHom (M.toPreModel.interp_subst ρ sub (Sg.trtgt a)).symm := by
  simp [arrCellAlg]

/-- `arrCellAlg` on an arrow `app B i …` is `appCell B` of `arrCellAlg g` at `i` and identities
elsewhere. -/
lemma arrCellAlg_app (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i)) :
    M.arrCellAlg sg ρ ψ (OneSig.Arr.app B i args args' hne g)
      = M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.interp ρ (args k) ⟶ M.interp ρ (args' k))) hj.symm)
            (M.arrCellAlg sg ρ ψ g)
        else eqToHom (by rw [hne j hj])) := by
  simp [arrCellAlg]

end AlgLemmas

end Eval

section Of

/-! ### `M^σ` and `M^T` from given limits

The objects `M^σ` and `M^T` need only five specific limits: the product `P₀` of the sorts, the
product `P_fn` over the function symbols, an inserter of the domain and codomain 1-cells, the
product `P_eq` over the equations, and an equifier of the two equation 2-cells. Here they are given
as data; the chosen versions below (`Model.thyObj`) take them from the chosen limits of `K`. -/

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

variable (P₀ : Product (fun s : sg.Srt => M.obj (sg.sty s)))

/-- The 1-cell `M(t) : P₀ → M_c` attached to a closed term, for a given product `P₀` of the
sorts. -/
@[implicit_reducible]
def tmOf {c : Sg.Cat} (t : sg.CTrm c) : P₀.pt ⟶ M.obj c := M.interp P₀.π t

variable (Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)))

/-- The 1-cell `(M(t₁))_f : P₀ → P_fn` of arities, for given products. -/
@[implicit_reducible]
def domCellOf : P₀.pt ⟶ Pfn.pt := Pfn.lift (fun f => M.tmOf sg P₀ (sg.fndom f))

/-- The 1-cell `(M(t₂))_f : P₀ → P_fn` of coarities, for given products. -/
@[implicit_reducible]
def codCellOf : P₀.pt ⟶ Pfn.pt := Pfn.lift (fun f => M.tmOf sg P₀ (sg.fncod f))

variable (I : Inserter (M.domCellOf sg P₀ Pfn) (M.codCellOf sg P₀ Pfn))

/-- The 1-cell `t ↦ M(t) ∘ u` on a given inserter `I` (the object `M^σ` of operations). -/
@[implicit_reducible]
def sigTmOf {c : Sg.Cat} (t : sg.CTrm c) : I.pt ⟶ M.obj c :=
  M.interp (fun s => I.u ≫ P₀.π s) t

/-- `sigTmOf t` is the inserter 1-cell `I.u` followed by `tmOf t`. -/
lemma sigTmOf_eq {c : Sg.Cat} (t : sg.CTrm c) :
    M.sigTmOf sg P₀ Pfn I t = I.u ≫ M.tmOf sg P₀ t :=
  M.toPreModel.interp_comp _ _ t

/-- `sigTmOf` of the domain of `f` is `I.u ≫ domCellOf` followed by the projection at `f`. -/
lemma sigTmOf_fndom (f : sg.Fn) :
    M.sigTmOf sg P₀ Pfn I (sg.fndom f) = (I.u ≫ M.domCellOf sg P₀ Pfn) ≫ Pfn.π f := by
  rw [sigTmOf_eq, Category.assoc]
  exact congr(I.u ≫ $((Pfn.lift_π (fun f => M.tmOf sg P₀ (sg.fndom f)) f).symm))

/-- `sigTmOf` of the codomain of `f` is `I.u ≫ codCellOf` followed by the projection at `f`. -/
lemma sigTmOf_fncod (f : sg.Fn) :
    M.sigTmOf sg P₀ Pfn I (sg.fncod f) = (I.u ≫ M.codCellOf sg P₀ Pfn) ≫ Pfn.π f := by
  rw [sigTmOf_eq, Category.assoc]
  exact congr(I.u ≫ $((Pfn.lift_π (fun f => M.tmOf sg P₀ (sg.fncod f)) f).symm))

/-- `sigTmOf` of a substituted term `t.subst sub` interprets `t` at the 1-cells
`sigTmOf (sub v)`. -/
lemma sigTmOf_subst {V : Type uᵥ} {vty : V → Sg.Cat} {c : Sg.Cat} (t : Trm Sg.toFunSig vty c)
    (sub : ∀ v : V, sg.CTrm (vty v)) :
    M.sigTmOf sg P₀ Pfn I (t.subst sub) = M.interp (fun v => M.sigTmOf sg P₀ Pfn I (sub v)) t :=
  M.toPreModel.interp_subst _ _ t

/-- The 2-cell of a function symbol `f` on a given inserter: the inserter 2-cell at `f`. -/
def insCellOf (f : sg.Fn) :
    M.sigTmOf sg P₀ Pfn I (sg.fndom f) ⟶ M.sigTmOf sg P₀ Pfn I (sg.fncod f) :=
  eqToHom (M.sigTmOf_fndom sg P₀ Pfn I f) ≫ (I.φ ▷ Pfn.π f) ≫
    eqToHom (M.sigTmOf_fncod sg P₀ Pfn I f).symm

/-- The evaluation `p̄_M` of an arrow of the term graph, on a given inserter (Definition 3.14). -/
def arrCellOf {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    M.sigTmOf sg P₀ Pfn I t ⟶ M.sigTmOf sg P₀ Pfn I t' :=
  M.arrCellAlg sg (fun s => I.u ≫ P₀.π s) (M.insCellOf sg P₀ Pfn I) g

/-- The evaluation `p̄_M` of a path of the term graph, on a given inserter (Definition 3.14). -/
def pathCellOf {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    M.sigTmOf sg P₀ Pfn I t ⟶ M.sigTmOf sg P₀ Pfn I t' :=
  M.pathCellAlg sg (fun s => I.u ≫ P₀.π s) (M.insCellOf sg P₀ Pfn I) p

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
variable (Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)))

/-- The 2-cell `(p̄_M)_{(p,q)}` of the left-hand sides of the equations, for given limits. -/
def lhsCellOf : (Peq.lift (fun r => M.sigTmOf sg P₀ Pfn I (T.dom r))) ⟶
    (Peq.lift (fun r => M.sigTmOf sg P₀ Pfn I (T.cod r))) :=
  Peq.lift₂ (fun r =>
    eqToHom (Peq.lift_π (fun r => M.sigTmOf sg P₀ Pfn I (T.dom r)) r) ≫
      M.pathCellOf sg P₀ Pfn I (T.lhs r) ≫
      eqToHom (Peq.lift_π (fun r => M.sigTmOf sg P₀ Pfn I (T.cod r)) r).symm)

/-- The 2-cell `(q̄_M)_{(p,q)}` of the right-hand sides of the equations, for given limits. -/
def rhsCellOf : (Peq.lift (fun r => M.sigTmOf sg P₀ Pfn I (T.dom r))) ⟶
    (Peq.lift (fun r => M.sigTmOf sg P₀ Pfn I (T.cod r))) :=
  Peq.lift₂ (fun r =>
    eqToHom (Peq.lift_π (fun r => M.sigTmOf sg P₀ Pfn I (T.dom r)) r) ≫
      M.pathCellOf sg P₀ Pfn I (T.rhs r) ≫
      eqToHom (Peq.lift_π (fun r => M.sigTmOf sg P₀ Pfn I (T.cod r)) r).symm)

variable (Q : Equifier (M.lhsCellOf sg P₀ Pfn I T Peq) (M.rhsCellOf sg P₀ Pfn I T Peq))

/-- **The object `M^T` built from given limits**: the vertex of the equifier `Q`. `Model.thyObj`
is this object at the chosen limits of `K` (`Model.thyObj_eq_thyObjOf`). -/
abbrev thyObjOf : Obj := Q.pt

/-- The 1-cell `e : M^T → M^σ` of `M^T` built from given limits. -/
abbrev eOf : M.thyObjOf sg P₀ Pfn I T Peq Q ⟶ I.pt := Q.e

end Of

/-! ### `M^σ` and `M^T` at the chosen limits of `K` -/

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- The object `M₀ = ∏_{s ∈ S} M_{c_s}`. -/
abbrev P0 : Product (fun s : sg.Srt => M.obj (sg.sty s)) :=
    HasChosenProductsOfSize.prod (ι := sg.Srt) _

/-- The 1-cell `M(t) : M₀ → M_c` attached to a closed term. -/
@[implicit_reducible]
def tm {c : Sg.Cat} (t : sg.CTrm c) : (M.P0 sg).pt ⟶ M.obj c := M.interp (M.P0 sg).π t

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The product `∏_{f} M_{c_f}` over the function symbols of `σ`. -/
abbrev Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)) :=
    HasChosenProductsOfSize.prod (ι := sg.Fn) _

/-- The 1-cell `(M(t₁))_f : M₀ → ∏_f M_{c_f}` of arities. -/
@[implicit_reducible]
def domCell : (M.P0 sg).pt ⟶ (M.Pfn sg).pt := (M.Pfn sg).lift (fun f => M.tm sg (sg.fndom f))

/-- The 1-cell `(M(t₂))_f : M₀ → ∏_f M_{c_f}` of coarities. -/
@[implicit_reducible]
def codCell : (M.P0 sg).pt ⟶ (M.Pfn sg).pt := (M.Pfn sg).lift (fun f => M.tm sg (sg.fncod f))

variable [HasChosenInserters.{u, v, w} Obj]

/-- The inserter defining the object of operations `M^σ` (Definition 3.13). -/
@[implicit_reducible]
def sigIns : Inserter (M.domCell sg) (M.codCell sg) := HasChosenInserters.ins _ _

/-- The object `M^σ` of operations. -/
abbrev sigObj : Obj := (M.sigIns sg).pt

/-- The canonical 1-cell `u_M : M^σ → M₀`. -/
abbrev u : M.sigObj sg ⟶ (M.P0 sg).pt := (M.sigIns sg).u

/-- The environment `s ↦ u_M ≫ π_s` used to interpret terms over `M^σ`. -/
abbrev sigEnv (s : sg.Srt) : M.sigObj sg ⟶ M.obj (sg.sty s) := M.u sg ≫ (M.P0 sg).π s

/-- The 1-cell `M^σ(t) = M(t) ∘ u_M`. -/
@[implicit_reducible]
def sigTm {c : Sg.Cat} (t : sg.CTrm c) : M.sigObj sg ⟶ M.obj c := M.interp (M.sigEnv sg) t

/-- The evaluation `M^σ(t)` of a closed term on `M^σ` factors as `u_M ≫ M(t)`. -/
lemma sigTm_eq {c : Sg.Cat} (t : sg.CTrm c) : M.sigTm sg t = M.u sg ≫ M.tm sg t :=
  M.toPreModel.interp_comp _ _ t

/-- The evaluation `M^σ(fndom f)` of the domain of `f` is `(u_M ≫ domCell) ≫ π_f`. -/
lemma sigTm_fndom (f : sg.Fn) :
    M.sigTm sg (sg.fndom f) = (M.u sg ≫ M.domCell sg) ≫ (M.Pfn sg).π f := by
  rw [Category.assoc, domCell, (M.Pfn sg).lift_π, sigTm_eq]

/-- The evaluation `M^σ(fncod f)` of the codomain of `f` is `(u_M ≫ codCell) ≫ π_f`. -/
lemma sigTm_fncod (f : sg.Fn) :
    M.sigTm sg (sg.fncod f) = (M.u sg ≫ M.codCell sg) ≫ (M.Pfn sg).π f := by
  rw [Category.assoc, codCell, (M.Pfn sg).lift_π, sigTm_eq]

/-- Substitution lemma for `M^σ(-)`: evaluating `t[sub]` on `M^σ` is interpreting `t` in the
environment `v ↦ M^σ(sub v)` (cf. Lemma 3.18 of [forsman2026syntactic]). -/
lemma sigTm_subst {V : Type uᵥ} {vty : V → Sg.Cat} {c : Sg.Cat} (t : Trm Sg.toFunSig vty c)
    (sub : ∀ v : V, sg.CTrm (vty v)) :
    M.sigTm sg (t.subst sub) = M.interp (fun v => M.sigTm sg (sub v)) t :=
  M.toPreModel.interp_subst _ _ t

/-- The evaluation `p̄_M` of an arrow of the term graph (Definition 3.14). -/
def arrCell : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Arr t t' → (M.sigTm sg t ⟶ M.sigTm sg t')
  | _, _, _, .fn f =>
      eqToHom (M.sigTm_fndom sg f) ≫ ((M.sigIns sg).φ ▷ (M.Pfn sg).π f) ≫
        eqToHom (M.sigTm_fncod sg f).symm
  | _, _, _, .tr a sub =>
      eqToHom (M.sigTm_subst sg (Sg.trsrc a) sub) ≫
        M.trAt a (fun i => M.sigTm sg (sub i)) ≫
        eqToHom (M.sigTm_subst sg (Sg.trtgt a) sub).symm
  | _, _, _, .app B i args args' hne g =>
      M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.sigTm sg (args k) ⟶ M.sigTm sg (args' k))) hj.symm)
            (arrCell g)
        else eqToHom (arrCell_ne_eq sg hne j hj (M.sigTm sg)))

/-- The evaluation of the term-graph arrow of a function symbol `f` is the whiskering
`φ ▷ π_f` of the inserter 2-cell, up to `eqToHom` (Definition 3.14 of [forsman2026syntactic]). -/
lemma arrCell_fn (f : sg.Fn) :
    M.arrCell sg (OneSig.Arr.fn f)
      = eqToHom (M.sigTm_fndom sg f) ≫ ((M.sigIns sg).φ ▷ (M.Pfn sg).π f) ≫
        eqToHom (M.sigTm_fncod sg f).symm := by
  simp [arrCell]

/-- The evaluation of the term-graph arrow of a transformation symbol `a` at `sub` is
`trAt a`, up to `eqToHom` (Definition 3.14 of [forsman2026syntactic]). -/
lemma arrCell_tr (a : Sg.Tr) (sub : ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i)) :
    M.arrCell sg (OneSig.Arr.tr a sub)
      = eqToHom (M.sigTm_subst sg (Sg.trsrc a) sub) ≫
        M.trAt a (fun i => M.sigTm sg (sub i)) ≫
        eqToHom (M.sigTm_subst sg (Sg.trtgt a) sub).symm := by
  simp [arrCell]

/-- The evaluation of a term-graph arrow applied inside argument `i` of `B` is `appCell B` of
the evaluated arrow at `i` and identities elsewhere (Definition 3.14 of [forsman2026syntactic]). -/
lemma arrCell_app (B : Sg.Fun) (i : Fin (Sg.arn B))
    (args args' : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j))
    (hne : ∀ j, j ≠ i → args j = args' j) (g : sg.Arr (args i) (args' i)) :
    M.arrCell sg (OneSig.Arr.app B i args args' hne g)
      = M.appCell B (fun j => if hj : j = i then
          cast (congrArg (fun k => (M.sigTm sg (args k) ⟶ M.sigTm sg (args' k))) hj.symm)
            (M.arrCell sg g)
        else eqToHom (by rw [hne j hj])) := by
  simp [arrCell]

/-- The evaluation `p̄_M` of a path of the term graph (Definition 3.14). -/
def pathCell : ∀ {c : Sg.Cat} {t t' : sg.CTrm c}, sg.Path t t' → (M.sigTm sg t ⟶ M.sigTm sg t')
  | _, _, _, .nil _ => 𝟙 _
  | _, _, _, .cons g p => M.arrCell sg g ≫ pathCell p

/-- The evaluation of the empty path is the identity 2-cell. -/
@[simp] lemma pathCell_nil {c : Sg.Cat} (t : sg.CTrm c) :
    M.pathCell sg (UlmerBialgebras.OneSig.Path.nil t) = 𝟙 _ := by simp [pathCell]

/-- The evaluation of a path `g · p` is the vertical composite of the evaluations of `g` and `p`. -/
@[simp] lemma pathCell_cons {c : Sg.Cat} {t t' t'' : sg.CTrm c} (g : sg.Arr t t')
    (p : sg.Path t' t'') :
    M.pathCell sg (UlmerBialgebras.OneSig.Path.cons g p) = M.arrCell sg g ≫ M.pathCell sg p := by
  simp [pathCell]

/-- `Model.arrCell` is `Model.arrCellOf` at the chosen limits of `K`. -/
lemma arrCell_eq_arrCellOf {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    M.arrCell sg g = M.arrCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) g := by
  induction g with
  | fn f =>
    rw [arrCell_fn, arrCellOf, arrCellAlg_fn]
    rfl
  | tr a sub =>
    rw [arrCell_tr, arrCellOf, arrCellAlg_tr]
    rfl
  | app B i args args' hne g ih =>
    rw [arrCell_app, arrCellOf, arrCellAlg_app]
    simp only [ih]
    rfl

/-- `Model.pathCell` is `Model.pathCellOf` at the chosen limits of `K`. -/
lemma pathCell_eq_pathCellOf {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    M.pathCell sg p = M.pathCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) p := by
  induction p with
  | nil t =>
    rw [pathCell_nil, pathCellOf, pathCellAlg_nil]
    rfl
  | cons g p ih =>
    rw [pathCell_cons, pathCellOf, pathCellAlg_cons, ih, arrCell_eq_arrCellOf]
    rfl

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- The product `∏_{(p,q)} M_c` over the equations of the theory. -/
abbrev Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)) :=
    HasChosenProductsOfSize.prod (ι := T.Eqn) _

/-- The 2-cell `(p̄_M)_{(p,q)}` given by the left-hand sides of the equations. -/
def lhsCell : ((M.Peq sg T).lift (fun r => M.sigTm sg (T.dom r))) ⟶
    ((M.Peq sg T).lift (fun r => M.sigTm sg (T.cod r))) :=
  (M.Peq sg T).lift₂ (fun r =>
    eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.dom r)) r) ≫
      M.pathCell sg (T.lhs r) ≫
      eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.cod r)) r).symm)

/-- The 2-cell `(q̄_M)_{(p,q)}` given by the right-hand sides of the equations. -/
def rhsCell : ((M.Peq sg T).lift (fun r => M.sigTm sg (T.dom r))) ⟶
    ((M.Peq sg T).lift (fun r => M.sigTm sg (T.cod r))) :=
  (M.Peq sg T).lift₂ (fun r =>
    eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.dom r)) r) ≫
      M.pathCell sg (T.rhs r) ≫
      eqToHom ((M.Peq sg T).lift_π (fun r => M.sigTm sg (T.cod r)) r).symm)

/-- `u_M ∘ ⟨M(t_r)⟩_r = ⟨M^σ(t_r)⟩_r` into `∏_{r ∈ E} M_{c_r}`, for a family of closed terms `t_r`
indexed by the equations of `T` (the arity and coarity 1-cells of `M^T`). -/
lemma sigCell_eq (h : ∀ r : T.Eqn, sg.CTrm (T.eqty r)) :
    M.u sg ≫ (M.Peq sg T).lift (fun r => M.tm sg (h r))
      = (M.Peq sg T).lift (fun r => M.sigTm sg (h r)) := by
  rw [(M.Peq sg T).comp_lift]
  congr 1
  funext r
  exact (M.sigTm_eq sg (h r)).symm

/-- Equifying the product of equation cells is equivalent to equifying each interpreted
parallel pair of paths. -/
lemma whisker_lhsCell_eq_iff {a : Obj} (d : a ⟶ M.sigObj sg) :
    d ◁ M.lhsCell sg T = d ◁ M.rhsCell sg T ↔
      ∀ r : T.Eqn, d ◁ M.pathCell sg (T.lhs r) = d ◁ M.pathCell sg (T.rhs r) := by
  constructor
  · intro h r
    have h2 : d ◁ ((M.lhsCell sg T) ▷ (M.Peq sg T).π r) =
        d ◁ ((M.rhsCell sg T) ▷ (M.Peq sg T).π r) := by
      rw [Bicategory.Strict.whisker_assoc, Bicategory.Strict.whisker_assoc, h]
    rw [lhsCell, rhsCell, (M.Peq sg T).lift₂_π, (M.Peq sg T).lift₂_π] at h2
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom] at h2
    exact (cancel_mono (eqToHom (by rw [(M.Peq sg T).lift_π
      (fun r => M.sigTm sg (T.cod r)) r]))).1 ((cancel_epi (eqToHom (by
        rw [(M.Peq sg T).lift_π (fun r => M.sigTm sg (T.dom r)) r]))).1 h2)
  · intro h
    apply (M.Peq sg T).cell_ext
    intro r
    rw [Bicategory.Strict.whisker_assoc', Bicategory.Strict.whisker_assoc',
      lhsCell, rhsCell, (M.Peq sg T).lift₂_π, (M.Peq sg T).lift₂_π]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [h r]

/-- `Model.lhsCell` is `Model.lhsCellOf` at the chosen limits of `K`. -/
lemma lhsCell_eq_lhsCellOf :
    M.lhsCell sg T = M.lhsCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) T (M.Peq sg T) := by
  simp only [lhsCell, lhsCellOf, pathCell_eq_pathCellOf]

/-- `Model.rhsCell` is `Model.rhsCellOf` at the chosen limits of `K`. -/
lemma rhsCell_eq_rhsCellOf :
    M.rhsCell sg T = M.rhsCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) T (M.Peq sg T) := by
  simp only [rhsCell, rhsCellOf, pathCell_eq_pathCellOf]

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- The equifier defining the object `M^T` of `T`-bialgebras (Definition 3.14). -/
def thyEquif : Equifier (M.lhsCell sg T) (M.rhsCell sg T) := HasChosenEquifiers.equif _ _

/-- The object `M^T` of `T`-bialgebras. -/
abbrev thyObj : Obj := (M.thyEquif sg T).pt

/-- The canonical 1-cell `e_M : M^T → M^σ`. -/
abbrev e : M.thyObj sg T ⟶ M.sigObj sg := (M.thyEquif sg T).e

/-- The defining property of `M^T`: the two paths of an equation of `T` become equal after
whiskering with `e_M`. -/
lemma e_pathCell (r : T.Eqn) :
    (M.e sg T) ◁ (M.pathCell sg (T.lhs r)) = (M.e sg T) ◁ (M.pathCell sg (T.rhs r)) :=
  (M.whisker_lhsCell_eq_iff sg T (M.e sg T)).mp (M.thyEquif sg T).cond r

/-! ### Agreement with the construction from given limits -/

/-- The chosen equifier `Model.thyEquif`, as an equifier of `Model.lhsCellOf` and
`Model.rhsCellOf` at the chosen limits. It has the same vertex and 1-cell. -/
def thyEquifOf :
    Equifier (M.lhsCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) T (M.Peq sg T))
      (M.rhsCellOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) T (M.Peq sg T)) :=
  (M.thyEquif sg T).ofEq (M.lhsCell_eq_lhsCellOf sg T) (M.rhsCell_eq_rhsCellOf sg T)

/-- `M^T` is `Model.thyObjOf` at the chosen limits of `K`, by definition. -/
lemma thyObj_eq_thyObjOf :
    M.thyObj sg T = M.thyObjOf sg (M.P0 sg) (M.Pfn sg) (M.sigIns sg) T (M.Peq sg T)
      (M.thyEquifOf sg T) := rfl

/-- `e_M` is the 1-cell of `Model.thyEquifOf`, by definition. -/
lemma e_eq_thyEquifOf_e : M.e sg T = (M.thyEquifOf sg T).e := rfl

end Model

end UlmerBialgebras
