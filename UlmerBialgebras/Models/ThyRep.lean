module

public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Basic.ConjEq

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# `T`-algebras over an object, and the universal property of `M^T`

For a `Σ`-model `M` in a strict 2-category `K`, a relative 1-signature `σ` and a theory `T`, a
`T`-algebra of `M` over an object `a` (`Model.Alg`) is an environment `ρ_s : a → M_{c_s}` of the
sorts with a 2-cell `ψ_f : M(t₁)(ρ) ⇒ M(t₂)(ρ)` for each function symbol `f : t₁ → t₂`, such
that the two paths of every equation of `T` evaluate to the same 2-cell. These are the objects of
`K(a, M)^T` of Remark 3.17 of [forsman2026syntactic], read in `K`.

Precomposition with `h : x → a` (`Model.Alg.precomp`) sends `T`-algebras over `a` to `T`-algebras
over `x`. An algebra `A` over `E` is *universal* (`Model.Alg.IsUniversal`) when every algebra over
`x` is `A.precomp h` for a unique `h : x → E`, and every 2-cell between `A.precomp h₁` and
`A.precomp h₂` is `A`'s whiskering of a unique `θ : h₁ ⇒ h₂`. This is the paper's (1) and (2) of
Remark 3.17 for a general theory.

## Main definitions

* `UlmerBialgebras.Model.Alg`: `T`-algebras over an object.
* `UlmerBialgebras.Model.Alg.precomp`: precomposition with a 1-cell.
* `UlmerBialgebras.Model.Alg.Hom`: 2-cells between `T`-algebras over the same object.
* `UlmerBialgebras.Model.Alg.IsUniversal`: the universal property.

## Main results

* `UlmerBialgebras.Model.pathCellAlg_precomp`: path evaluation commutes with precomposition.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj]

/-! ### Two facts about `ConjEq` -/

/-- A 2-cell `α` is `ConjEq` to the 2-cell induced by its whiskerings with the projections,
conjugated along equalities of the endpoints. -/
lemma _root_.UlmerBialgebras.Product.lift₂_conjEq {ι : Type*} {c : ι → Obj} (P : Product c)
    {x : Obj} {f f' k k' : x ⟶ P.pt} (hf : f = k) (hf' : f' = k') (α : k ⟶ k')
    (p : ∀ i, f ≫ P.π i = k ≫ P.π i) (q : ∀ i, k' ≫ P.π i = f' ≫ P.π i) :
    ConjEq (P.lift₂ (fun i => eqToHom (p i) ≫ α ▷ P.π i ≫ eqToHom (q i))) α := by
  subst hf hf'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, P.lift₂_uniq]
  exact ConjEq.of_eq rfl

/-- Right whiskering by equal 1-cells gives `ConjEq` 2-cells. -/
lemma _root_.UlmerBialgebras.ConjEq.whiskerRight_congr' {a b c : Obj} {f g : a ⟶ b}
    (α : f ⟶ g) {h h' : b ⟶ c} (e : h = h') : ConjEq (α ▷ h) (α ▷ h') := by
  subst e
  exact ConjEq.of_eq rfl

variable [Bicategory.Strict Obj] [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace PreModel

variable (M : PreModel Sg Obj)

/-- `appCell B` respects `ConjEq` of the families of 2-cells, over equal families of 1-cells. -/
lemma appCell_conjEq (B : Sg.Fun) {x : Obj} {g₁ g₁' g₂ g₂' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (e : g₁ = g₂) (e' : g₁' = g₂') {γ₁ : ∀ i, g₁ i ⟶ g₁' i} {γ₂ : ∀ i, g₂ i ⟶ g₂' i}
    (h : ∀ i, ConjEq (γ₁ i) (γ₂ i)) : ConjEq (M.appCell B γ₁) (M.appCell B γ₂) := by
  subst e e'
  exact ConjEq.of_eq (M.appCell_congr B fun i => (h i).eq)

end PreModel

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

/-- `trAt` respects equal environments, up to `ConjEq`. -/
lemma trAt_conjEq (a : Sg.Tr) {x : Obj} {ρ ρ' : ∀ i, x ⟶ M.obj (Sg.trt a i)}
    (e : ∀ i, ρ i = ρ' i) : ConjEq (M.trAt a ρ) (M.trAt a ρ') := by
  have hρ : ρ = ρ' := funext e
  subst hρ
  exact ConjEq.of_eq rfl

/-! ### Precomposition -/

section Precomp

variable {a x : Obj} (h : x ⟶ a) (ρ : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s))
  (ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f))

/-- The 2-cells `ψ` whiskered by `h : x → a`, at the environment `h ≫ ρ`. -/
def precompCells (f : sg.Fn) :
    M.interp (fun s => h ≫ ρ s) (sg.fndom f) ⟶ M.interp (fun s => h ≫ ρ s) (sg.fncod f) :=
  eqToHom (M.toPreModel.interp_comp h ρ _) ≫ h ◁ ψ f ≫
    eqToHom (M.toPreModel.interp_comp h ρ _).symm

/-- The evaluation of a term-graph arrow commutes with precomposition: at `h ≫ ρ` and the
whiskered 2-cells it is the whiskering by `h` of the evaluation at `ρ`. -/
lemma arrCellAlg_precomp {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    ConjEq (M.arrCellAlg sg (fun s => h ≫ ρ s) (M.precompCells sg h ρ ψ) g)
      (h ◁ M.arrCellAlg sg ρ ψ g) := by
  induction g with
  | fn f => exact ConjEq.conj _ _ _
  | tr a sub =>
      simp only [arrCellAlg, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
      refine (ConjEq.conj _ _ _).trans (ConjEq.trans ?_ (ConjEq.conj _ _ _).symm)
      rw [M.trAt_precomp]
      exact (M.trAt_conjEq a fun i => M.toPreModel.interp_comp h ρ (sub i)).trans
        (ConjEq.conj _ _ _).symm
  | app B i args args' hne g ih =>
      simp only [arrCellAlg]
      rw [M.toPreModel.whiskerLeft_appCell]
      refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
      refine M.toPreModel.appCell_conjEq B
        (funext fun j => M.toPreModel.interp_comp h ρ (args j))
        (funext fun j => M.toPreModel.interp_comp h ρ (args' j)) fun j => ?_
      by_cases hj : j = i
      · subst hj
        simpa using ih
      · simp only [hj, dite_false, Bicategory.whiskerLeft_eqToHom]
        exact ConjEq.eqToHom_eqToHom _ _ (M.toPreModel.interp_comp h ρ (args j))

/-- The evaluation of a path commutes with precomposition (see `Model.arrCellAlg_precomp`). -/
lemma pathCellAlg_precomp {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    ConjEq (M.pathCellAlg sg (fun s => h ≫ ρ s) (M.precompCells sg h ρ ψ) p)
      (h ◁ M.pathCellAlg sg ρ ψ p) := by
  induction p with
  | nil t =>
      simp only [pathCellAlg, Bicategory.whiskerLeft_id]
      have e := M.toPreModel.interp_comp h ρ t
      exact ⟨e, e.symm, by simp⟩
  | cons g p ih =>
      simp only [pathCellAlg, Bicategory.whiskerLeft_comp]
      exact ConjEq.comp (M.arrCellAlg_precomp sg h ρ ψ g) ih

end Precomp

/-- Path evaluation respects equal environments and `ConjEq` 2-cells. -/
lemma pathCellAlg_congr {a : Obj} {ρ ρ' : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s)} (e : ρ = ρ')
    {ψ : ∀ f : sg.Fn, M.interp ρ (sg.fndom f) ⟶ M.interp ρ (sg.fncod f)}
    {ψ' : ∀ f : sg.Fn, M.interp ρ' (sg.fndom f) ⟶ M.interp ρ' (sg.fncod f)}
    (hψ : ∀ f, ConjEq (ψ f) (ψ' f)) {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    ConjEq (M.pathCellAlg sg ρ ψ p) (M.pathCellAlg sg ρ' ψ' p) := by
  subst e
  have : ψ = ψ' := funext fun f => (hψ f).eq
  subst this
  exact ConjEq.of_eq rfl

/-- Whiskering the interpretation of a term on the right by a 2-cell `α : h ⇒ h'` is the
interpretation of the whiskered environment. -/
lemma whiskerRight_interp_env {V : Type uᵥ} {vty : V → Sg.Cat} {a y : Obj}
    (ρ : ∀ v, a ⟶ M.obj (vty v)) {h h' : y ⟶ a} (α : h ⟶ h') {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    ConjEq (α ▷ M.interp ρ t) (M.interpCell (fun v => α ▷ ρ v) t) := by
  induction t with
  | var v => exact ConjEq.of_eq rfl
  | app B args ih =>
      refine (ConjEq.whiskerRight_comp₁ α _ _).trans ?_
      refine ((ConjEq.of_eq (M.toPreModel.appCell_whiskerRight B α _)).trans
        (ConjEq.conj _ _ _)).symm.trans ?_
      exact M.toPreModel.appCell_conjEq B
        (funext fun i => (M.toPreModel.interp_comp h ρ (args i)).symm)
        (funext fun i => (M.toPreModel.interp_comp h' ρ (args i)).symm) ih

/-- Left whiskering commutes with the interpretation of a family of 2-cells. -/
lemma whiskerLeft_interpCell {V : Type uᵥ} {vty : V → Sg.Cat} {x y : Obj}
    {ρ ρ' : ∀ v, x ⟶ M.obj (vty v)} (γ : ∀ v, ρ v ⟶ ρ' v) (k : y ⟶ x) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    ConjEq (M.interpCell (fun v => k ◁ γ v) t) (k ◁ M.interpCell γ t) := by
  induction t with
  | var v => exact ConjEq.of_eq rfl
  | app B args ih =>
      refine (M.toPreModel.appCell_conjEq B
        (funext fun i => M.toPreModel.interp_comp k ρ (args i))
        (funext fun i => M.toPreModel.interp_comp k ρ' (args i)) ih).trans ?_
      change ConjEq _ (k ◁ M.appCell B fun i => M.interpCell γ (args i))
      rw [M.toPreModel.whiskerLeft_appCell]
      exact (ConjEq.conj _ _ _).symm

/-! ### `T`-algebras over an object -/

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

/-- **A `T`-algebra of `M` over an object `a`**: an environment `ρ_s : a → M_{c_s}` of the sorts,
a 2-cell `ψ_f : M(t₁)(ρ) ⇒ M(t₂)(ρ)` for each function symbol `f : t₁ → t₂`, such that the two
paths of each equation of `T` evaluate to the same 2-cell. An object of `K(a, M)^T` (Remark 3.17
of [forsman2026syntactic]), read in `K`. -/
structure Alg (a : Obj) where
  /-- The environment of the sorts. -/
  env : ∀ s : sg.Srt, a ⟶ M.obj (sg.sty s)
  /-- The 2-cells of the function symbols. -/
  cell : ∀ f : sg.Fn, M.interp env (sg.fndom f) ⟶ M.interp env (sg.fncod f)
  eqn : ∀ r : T.Eqn, M.pathCellAlg sg env cell (T.lhs r) = M.pathCellAlg sg env cell (T.rhs r)

namespace Alg

variable {M sg T}

/-- Two `T`-algebras with equal environments and `ConjEq` 2-cells are equal. -/
lemma ext' {a : Obj} {A B : M.Alg sg T a} (he : A.env = B.env)
    (hc : ∀ f, ConjEq (A.cell f) (B.cell f)) : A = B := by
  obtain ⟨ρ, ψ, h⟩ := A
  obtain ⟨ρ', ψ', h'⟩ := B
  subst he
  have : ψ = ψ' := funext fun f => (hc f).eq
  subst this
  rfl

/-- **Precomposition of a `T`-algebra with `h : x → a`**: the environment `h ≫ ρ` and the
2-cells `h ◁ ψ`. -/
def precomp {a x : Obj} (A : M.Alg sg T a) (h : x ⟶ a) : M.Alg sg T x where
  env s := h ≫ A.env s
  cell := M.precompCells sg h A.env A.cell
  eqn r := ((M.pathCellAlg_precomp sg h A.env A.cell (T.lhs r)).trans
    ((ConjEq.of_eq (congrArg (h ◁ ·) (A.eqn r))).trans
      (M.pathCellAlg_precomp sg h A.env A.cell (T.rhs r)).symm)).eq

/-- Precomposing twice is precomposing with the composite. -/
lemma precomp_precomp {a x y : Obj} (A : M.Alg sg T a) (h : x ⟶ a) (k : y ⟶ x) :
    (A.precomp h).precomp k = A.precomp (k ≫ h) := by
  refine ext' (funext fun s => (Category.assoc k h (A.env s)).symm) fun f => ?_
  refine (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft k (ConjEq.conj _ _ _)).trans ?_)
  exact (ConjEq.whiskerLeft_comp₁ k h (A.cell f)).symm.trans (ConjEq.conj _ _ _).symm

/-- A 2-cell between `T`-algebras over the same object: 2-cells `θ_s : ρ_s ⇒ ρ'_s` of the
environments, compatible with the 2-cells of the function symbols. A morphism of `K(a, M)^T`. -/
structure Hom {a : Obj} (A B : M.Alg sg T a) where
  /-- The components at the sorts. -/
  app : ∀ s : sg.Srt, A.env s ⟶ B.env s
  comm : ∀ f : sg.Fn,
    A.cell f ≫ M.interpCell app (sg.fncod f) = M.interpCell app (sg.fndom f) ≫ B.cell f

/-- **The universal property of a `T`-algebra `A` over `E`, at an object `x`** (Remark 3.17 (1)
and (2) of [forsman2026syntactic]):
1. every `T`-algebra over `x` is `A.precomp h` for a unique `h : x → E`;
2. every 2-cell `β` from `A.precomp h₁` to `A.precomp h₂` is `θ ▷ ρ_A` for a unique
   `θ : h₁ ⇒ h₂`. -/
def IsUniversalAt {E : Obj} (A : M.Alg sg T E) (x : Obj) : Prop :=
  (∀ B : M.Alg sg T x, ∃! h : x ⟶ E, A.precomp h = B) ∧
    ∀ (h₁ h₂ : x ⟶ E) (β : Hom (A.precomp h₁) (A.precomp h₂)),
      ∃! θ : h₁ ⟶ h₂, ∀ s, θ ▷ A.env s = β.app s

/-- **The universal property of a `T`-algebra `A` over `E`**: `Model.Alg.IsUniversalAt` at every
object. -/
def IsUniversal {E : Obj} (A : M.Alg sg T E) : Prop := ∀ x : Obj, A.IsUniversalAt x

/-- The 2-cell `θ ▷ ρ_A` from `A.precomp h₁` to `A.precomp h₂` given by `θ : h₁ ⇒ h₂`. -/
def whiskerHom {E x : Obj} (A : M.Alg sg T E) {h₁ h₂ : x ⟶ E} (θ : h₁ ⟶ h₂) :
    Hom (A.precomp h₁) (A.precomp h₂) where
  app s := θ ▷ A.env s
  comm f := by
    refine (ConjEq.eq_iff (ConjEq.comp (ConjEq.conj _ _ _)
      (M.whiskerRight_interp_env A.env θ _).symm) (ConjEq.comp
        (M.whiskerRight_interp_env A.env θ _).symm (ConjEq.conj _ _ _))).mpr ?_
    exact Bicategory.whisker_exchange θ (A.cell f)

/-- Two 2-cells between `T`-algebras with equal components are equal. -/
@[ext] lemma Hom.ext {a : Obj} {A B : M.Alg sg T a} {β β' : Hom A B} (h : β.app = β'.app) :
    β = β' := by
  cases β; cases β'
  subst h
  rfl

end Alg

/-- `interpCell` respects `ConjEq` families over equal environments. -/
lemma _root_.UlmerBialgebras.PreModel.interpCell_conjEq (N : PreModel Sg Obj) {V : Type uᵥ}
    {vty : V → Sg.Cat} {x : Obj} {ρ₁ ρ₁' ρ₂ ρ₂' : ∀ v, x ⟶ N.obj (vty v)} (e : ρ₁ = ρ₂)
    (e' : ρ₁' = ρ₂') {γ₁ : ∀ v, ρ₁ v ⟶ ρ₁' v} {γ₂ : ∀ v, ρ₂ v ⟶ ρ₂' v}
    (h : ∀ v, ConjEq (γ₁ v) (γ₂ v)) {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    ConjEq (N.interpCell γ₁ t) (N.interpCell γ₂ t) := by
  subst e e'
  have : γ₁ = γ₂ := funext fun v => (h v).eq
  subst this
  exact ConjEq.of_eq rfl

/-- Whiskering the interpretation of a term on the right is the interpretation of the
whiskered environment. -/
lemma _root_.UlmerBialgebras.PreModel.whiskerRight_interp_conjEq (N : PreModel Sg Obj)
    {V : Type uᵥ} {vty : V → Sg.Cat} (P : Product (fun v => N.obj (vty v))) {x : Obj}
    {k k' : x ⟶ P.pt} (α : k ⟶ k') {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    ConjEq (α ▷ N.interp P.π t) (N.interpCell (fun v => α ▷ P.π v) t) := by
  rw [N.interpCell_whisker P]
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  refine ConjEq.whiskerRight ?_ _
  exact (P.lift₂_conjEq (P.lift_uniq k) (P.lift_uniq k') α _ _).symm

/-! ### The canonical algebra on `M^T` built from given limits -/

section Canonical

variable (P₀ : Product (fun s : sg.Srt => M.obj (sg.sty s)))
  (Pfn : Product (fun f : sg.Fn => M.obj (sg.fnty f)))
  (I : Inserter (M.domCellOf sg P₀ Pfn) (M.codCellOf sg P₀ Pfn))
  (Peq : Product (fun r : T.Eqn => M.obj (T.eqty r)))

/-- Equifying the equation 2-cells is equifying each interpreted pair of paths. -/
lemma whisker_lhsCellOf_eq_iff {a : Obj} (d : a ⟶ I.pt) :
    d ◁ M.lhsCellOf sg P₀ Pfn I T Peq = d ◁ M.rhsCellOf sg P₀ Pfn I T Peq ↔
      ∀ r : T.Eqn, d ◁ M.pathCellOf sg P₀ Pfn I (T.lhs r) =
        d ◁ M.pathCellOf sg P₀ Pfn I (T.rhs r) := by
  constructor
  · intro h r
    have h2 : d ◁ ((M.lhsCellOf sg P₀ Pfn I T Peq) ▷ Peq.π r) =
        d ◁ ((M.rhsCellOf sg P₀ Pfn I T Peq) ▷ Peq.π r) := by
      rw [Bicategory.Strict.whisker_assoc, Bicategory.Strict.whisker_assoc, h]
    rw [lhsCellOf, rhsCellOf, Peq.lift₂_π, Peq.lift₂_π] at h2
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom] at h2
    exact (cancel_mono (eqToHom (by rw [Peq.lift_π
      (fun r => M.sigTmOf sg P₀ Pfn I (T.cod r)) r]))).1 ((cancel_epi (eqToHom (by
        rw [Peq.lift_π (fun r => M.sigTmOf sg P₀ Pfn I (T.dom r)) r]))).1 h2)
  · intro h
    apply Peq.cell_ext
    intro r
    rw [Bicategory.Strict.whisker_assoc', Bicategory.Strict.whisker_assoc',
      lhsCellOf, rhsCellOf, Peq.lift₂_π, Peq.lift₂_π]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [h r]

/-- The inserter 2-cell at `f`, whiskered by `k`, is `(k ◁ φ) ▷ π_f`. -/
lemma whiskerLeft_insCellOf {x : Obj} (k : x ⟶ I.pt) (f : sg.Fn) :
    ConjEq (k ◁ M.insCellOf sg P₀ Pfn I f) ((k ◁ I.φ) ▷ Pfn.π f) := by
  simp only [insCellOf, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  exact (ConjEq.conj _ _ _).trans (ConjEq.whiskerLeft_whiskerRight k I.φ (Pfn.π f))

variable (Q : Equifier (M.lhsCellOf sg P₀ Pfn I T Peq) (M.rhsCellOf sg P₀ Pfn I T Peq))

/-- **The canonical `T`-algebra over `M^T`** built from given limits: the environment
`e ≫ u ≫ π_s` and the inserter 2-cells whiskered by `e`. -/
def canonAlg : M.Alg sg T Q.pt where
  env s := Q.e ≫ (I.u ≫ P₀.π s)
  cell := M.precompCells sg Q.e (fun s => I.u ≫ P₀.π s) (M.insCellOf sg P₀ Pfn I)
  eqn r := ((M.pathCellAlg_precomp sg Q.e _ _ (T.lhs r)).trans
    ((ConjEq.of_eq ((M.whisker_lhsCellOf_eq_iff sg T P₀ Pfn I Peq Q.e).mp Q.cond r)).trans
      (M.pathCellAlg_precomp sg Q.e _ _ (T.rhs r)).symm)).eq

section Lift

variable {x : Obj} (B : M.Alg sg T x)

/-- The 1-cell `x → P₀` of the environment of `B`. -/
def algP0 : x ⟶ P₀.pt := P₀.lift B.env

/-- `algP0 B` followed by the domain 1-cell and `π_f` is the interpretation of the domain of `f`. -/
lemma algP0_dom (f : sg.Fn) :
    (M.algP0 sg T P₀ B ≫ M.domCellOf sg P₀ Pfn) ≫ Pfn.π f = M.interp B.env (sg.fndom f) := by
  rw [Category.assoc, domCellOf, Pfn.lift_π, tmOf, algP0, ← M.toPreModel.interp_comp]
  exact M.toPreModel.interp_congr (fun s => P₀.lift_π B.env s) _

/-- `algP0 B` followed by the codomain 1-cell and `π_f` interprets the codomain of `f`. -/
lemma algP0_cod (f : sg.Fn) :
    (M.algP0 sg T P₀ B ≫ M.codCellOf sg P₀ Pfn) ≫ Pfn.π f = M.interp B.env (sg.fncod f) := by
  rw [Category.assoc, codCellOf, Pfn.lift_π, tmOf, algP0, ← M.toPreModel.interp_comp]
  exact M.toPreModel.interp_congr (fun s => P₀.lift_π B.env s) _

/-- The inserter 2-cell of `B`: the 2-cells of the function symbols, collected by `P_fn`. -/
def algCell : M.algP0 sg T P₀ B ≫ M.domCellOf sg P₀ Pfn ⟶
    M.algP0 sg T P₀ B ≫ M.codCellOf sg P₀ Pfn :=
  Pfn.lift₂ fun f => eqToHom (M.algP0_dom sg T P₀ Pfn B f) ≫ B.cell f ≫
    eqToHom (M.algP0_cod sg T P₀ Pfn B f).symm

/-- The 1-cell `x → M^σ` of `B`. -/
def algIns : x ⟶ I.pt := I.lift (M.algP0 sg T P₀ B) (M.algCell sg T P₀ Pfn B)

/-- `algIns B` followed by `u ≫ π_s` recovers the environment `B.env s`. -/
lemma algIns_env (s : sg.Srt) : M.algIns sg T P₀ Pfn I B ≫ (I.u ≫ P₀.π s) = B.env s := by
  rw [← Category.assoc, algIns, I.lift_u, algP0, P₀.lift_π]

/-- `algIns B` whiskered with the inserter 2-cell at `f` is `B.cell f`, up to `ConjEq`. -/
lemma algIns_cell (f : sg.Fn) :
    ConjEq (M.algIns sg T P₀ Pfn I B ◁ M.insCellOf sg P₀ Pfn I f) (B.cell f) := by
  refine (M.whiskerLeft_insCellOf sg P₀ Pfn I _ f).trans ?_
  rw [algIns, I.lift_φ]
  refine (ConjEq.whiskerRight (ConjEq.conj _ _ _) _).trans ?_
  rw [algCell, Pfn.lift₂_π]
  exact ConjEq.conj _ _ _

/-- `algIns B` equifies `lhsCellOf` and `rhsCellOf`, since `B` satisfies the equations of `T`. -/
lemma algIns_cond :
    M.algIns sg T P₀ Pfn I B ◁ M.lhsCellOf sg P₀ Pfn I T Peq =
      M.algIns sg T P₀ Pfn I B ◁ M.rhsCellOf sg P₀ Pfn I T Peq := by
  refine (M.whisker_lhsCellOf_eq_iff sg T P₀ Pfn I Peq _).mpr fun r => ?_
  have hc : ∀ f, ConjEq (M.precompCells sg (M.algIns sg T P₀ Pfn I B) (fun s => I.u ≫ P₀.π s)
      (M.insCellOf sg P₀ Pfn I) f) (B.cell f) := fun f =>
    (ConjEq.conj _ _ _).trans (M.algIns_cell sg T P₀ Pfn I B f)
  have he := funext (M.algIns_env sg T P₀ Pfn I B)
  exact (ConjEq.eq_iff
    ((M.pathCellAlg_precomp sg _ _ _ (T.lhs r)).symm.trans (M.pathCellAlg_congr sg he hc _))
    ((M.pathCellAlg_precomp sg _ _ _ (T.rhs r)).symm.trans (M.pathCellAlg_congr sg he hc _))).mpr
    (B.eqn r)

/-- The 1-cell `x → M^T` of `B`. -/
def algLift : x ⟶ Q.pt := Q.lift (M.algIns sg T P₀ Pfn I B) (M.algIns_cond sg T P₀ Pfn I Peq B)

/-- Precomposing the canonical algebra with `algLift B` recovers the algebra `B`. -/
lemma canonAlg_precomp_algLift :
    (M.canonAlg sg T P₀ Pfn I Peq Q).precomp (M.algLift sg T P₀ Pfn I Peq Q B) = B := by
  refine Alg.ext' (funext fun s => ?_) fun f => ?_
  · change _ ≫ (Q.e ≫ _) = _
    rw [← Category.assoc, algLift, Q.lift_e, algIns_env]
  · refine (ConjEq.conj _ _ _).trans ?_
    refine (ConjEq.whiskerLeft _ (ConjEq.conj _ _ _)).trans ?_
    refine (ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans ?_
    refine (ConjEq.whiskerLeft_congr' (Q.lift_e _ _) _).trans ?_
    exact M.algIns_cell sg T P₀ Pfn I B f

end Lift

/-- The 2-dimensional part of `canonAlg_isUniversal`: every morphism `β` between the
precompositions of the canonical algebra along `h₁` and `h₂` is `θ ▷ env` for a unique
`θ : h₁ ⟶ h₂`. -/
private lemma canonAlg_isUniversal_full_faithful {x : Obj} {h₁ h₂ : x ⟶ Q.pt}
    (β : Alg.Hom ((M.canonAlg sg T P₀ Pfn I Peq Q).precomp h₁)
      ((M.canonAlg sg T P₀ Pfn I Peq Q).precomp h₂)) :
    ∃! θ : h₁ ⟶ h₂, ∀ s, θ ▷ (M.canonAlg sg T P₀ Pfn I Peq Q).env s = β.app s := by
  -- Assemble the components of `β` into a 2-cell `α₀` into the product `P₀`; it is compatible
  -- with the structure cell of the inserter `I` (`H`, from `β.comm`), so it lifts through `I`,
  -- and then through the equifier `Q` (full and faithful on 2-cells), giving `θ`.
  let A := M.canonAlg sg T P₀ Pfn I Peq Q
  have hassoc : ∀ (h : x ⟶ Q.pt) (s : sg.Srt),
      ((h ≫ Q.e) ≫ I.u) ≫ P₀.π s = h ≫ (Q.e ≫ (I.u ≫ P₀.π s)) := fun h s => by
    simp only [Category.assoc]
  let α₀ : (h₁ ≫ Q.e) ≫ I.u ⟶ (h₂ ≫ Q.e) ≫ I.u :=
    P₀.lift₂ fun s => eqToHom (hassoc h₁ s) ≫ β.app s ≫ eqToHom (hassoc h₂ s).symm
  have hα₀ : ∀ s, ConjEq (α₀ ▷ P₀.π s) (β.app s) := fun s => by
    simp only [α₀, P₀.lift₂_π]; exact ConjEq.conj _ _ _
  have hcell : ∀ (h : x ⟶ Q.pt) (f : sg.Fn),
      ConjEq (((h ≫ Q.e) ◁ I.φ) ▷ Pfn.π f) ((A.precomp h).cell f) := fun h f =>
    (M.whiskerLeft_insCellOf sg P₀ Pfn I _ f).symm.trans ((ConjEq.whiskerLeft_comp₁ _ _ _).trans
      ((ConjEq.whiskerLeft _ (ConjEq.conj _ _ _).symm).trans (ConjEq.conj _ _ _).symm))
  have hdom : ∀ f, ConjEq ((α₀ ▷ M.domCellOf sg P₀ Pfn) ▷ Pfn.π f)
      (M.interpCell β.app (sg.fndom f)) := fun f =>
    (ConjEq.whiskerRight_comp₁ _ _ _).symm.trans
      ((ConjEq.whiskerRight_congr' _ (Pfn.lift_π _ f)).trans
        ((M.toPreModel.whiskerRight_interp_conjEq P₀ α₀ _).trans
          (M.toPreModel.interpCell_conjEq (funext (hassoc h₁)) (funext (hassoc h₂)) hα₀ _)))
  have hcod : ∀ f, ConjEq ((α₀ ▷ M.codCellOf sg P₀ Pfn) ▷ Pfn.π f)
      (M.interpCell β.app (sg.fncod f)) := fun f =>
    (ConjEq.whiskerRight_comp₁ _ _ _).symm.trans
      ((ConjEq.whiskerRight_congr' _ (Pfn.lift_π _ f)).trans
        ((M.toPreModel.whiskerRight_interp_conjEq P₀ α₀ _).trans
          (M.toPreModel.interpCell_conjEq (funext (hassoc h₁)) (funext (hassoc h₂)) hα₀ _)))
  have H : I.phiAt (h₁ ≫ Q.e) ≫ (α₀ ▷ M.codCellOf sg P₀ Pfn) =
      (α₀ ▷ M.domCellOf sg P₀ Pfn) ≫ I.phiAt (h₂ ≫ Q.e) := by
    apply Pfn.cell_ext
    intro f
    simp only [Bicategory.comp_whiskerRight]
    refine (ConjEq.eq_iff (ConjEq.comp ?_ (hcod f)) (ConjEq.comp (hdom f) ?_)).mpr (β.comm f)
    · exact (ConjEq.whiskerRight (ConjEq.conj _ _ _) _).trans (hcell h₁ f)
    · exact (ConjEq.whiskerRight (ConjEq.conj _ _ _) _).trans (hcell h₂ f)
  obtain ⟨θ, hθ⟩ := Q.full (I.lift₂' α₀ H)
  have key : ∀ θ' : h₁ ⟶ h₂, ∀ s, ConjEq (θ' ▷ A.env s) (((θ' ▷ Q.e) ▷ I.u) ▷ P₀.π s) :=
    fun θ' s => (ConjEq.whiskerRight_comp₁ _ _ _).trans (ConjEq.whiskerRight_comp₁ _ _ _)
  refine ⟨θ, fun s => ?_, fun θ' hθ' => Q.faithful _ _ (I.lift₂_uniq _ _ ?_)⟩
  · refine ((key θ s).trans ?_).eq
    rw [hθ, I.lift₂'_u]
    exact hα₀ s
  · rw [hθ, I.lift₂'_u]
    apply P₀.cell_ext
    intro s
    exact ((key θ' s).symm.trans ((ConjEq.of_eq (hθ' s)).trans (hα₀ s).symm)).eq

/-- **The canonical algebra on `M^T` is universal** (Remark 3.17 (1) and (2) of
[forsman2026syntactic], for `M^T` built from given limits). -/
theorem canonAlg_isUniversal : (M.canonAlg sg T P₀ Pfn I Peq Q).IsUniversal := by
  intro x
  refine ⟨fun B => ⟨M.algLift sg T P₀ Pfn I Peq Q B,
    M.canonAlg_precomp_algLift sg T P₀ Pfn I Peq Q B, fun h' hh => ?_⟩,
    fun h₁ h₂ β => M.canonAlg_isUniversal_full_faithful sg T P₀ Pfn I Peq Q β⟩
  subst hh
  refine Q.lift_uniq _ _ _ (I.lift_uniq _ _ _ ?_ ?_)
  · exact P₀.hom_ext fun s => by
      rw [algP0, P₀.lift_π]
      simp only [Category.assoc]
      rfl
  · apply Pfn.cell_ext
    intro f
    have hL : ConjEq (((h' ≫ Q.e) ◁ I.φ) ▷ Pfn.π f)
        (((M.canonAlg sg T P₀ Pfn I Peq Q).precomp h').cell f) :=
      (M.whiskerLeft_insCellOf sg P₀ Pfn I _ f).symm.trans
        ((ConjEq.whiskerLeft_comp₁ _ _ _).trans
          ((ConjEq.whiskerLeft _ (ConjEq.conj _ _ _).symm).trans (ConjEq.conj _ _ _).symm))
    refine (hL.trans ?_).eq
    refine ((ConjEq.whiskerRight (ConjEq.conj _ _ _) _).trans ?_).symm
    rw [algCell, Pfn.lift₂_π]
    exact ConjEq.conj _ _ _

end Canonical

end Model

end UlmerBialgebras
