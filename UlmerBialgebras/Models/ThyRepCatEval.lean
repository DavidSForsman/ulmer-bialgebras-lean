module

public import UlmerBialgebras.Models.ThyRep
public import UlmerBialgebras.Models.HomModel
public import UlmerBialgebras.Models.CatCells

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The model `K(x, M)` in `CAT`, componentwise

For a `Σ`-model `M` in a strict 2-category `K` and an object `x`, the model `K(x, M)` in `CAT`
(`Model.homModel`) interprets everything componentwise. This file proves that path evaluation in
`K(x, M)`, at an environment of functors `ε_s : D ⥤ K(x, M_{c_s})` and natural transformations
`χ_f`, has as its component at `d : D` the path evaluation in `M` at the environment `ε_s(d)` and
the 2-cells `χ_f(d)` (`Model.homPathCellAlg_app`). It is the bridge between `T`-algebras of
`K(x, M)` in `CAT` and `T`-algebras of `M` in `K` (Remark 3.17 of [forsman2026syntactic]).

## Main results

* `UlmerBialgebras.Model.homAppCell_app`, `UlmerBialgebras.Model.homInterpCell_app`,
  `UlmerBialgebras.Model.homInterp_map`: components of the 2-cells of `K(x, M)`.
* `UlmerBialgebras.Model.homPathCellAlg_app`: components of evaluated paths.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-- Components of `ConjEq` 2-cells of `CAT` are `ConjEq`. -/
lemma ConjEq.app {A B : Cat.{w, v}} {F G F' G' : A ⟶ B} {α : F ⟶ G} {β : F' ⟶ G'}
    (h : ConjEq α β) (d : A) : ConjEq (α.toNatTrans.app d) (β.toNatTrans.app d) := by
  obtain ⟨p, q, rfl⟩ := h
  subst p q
  exact ConjEq.of_eq (by simp)

namespace Model

variable (M : Model Sg Obj) (x : Obj)

/-- The component of the image under `B` of a family of 2-cells of `K(x, M)`. -/
lemma homAppCell_app (B : Sg.Fun) {D : Cat.{w, v}}
    {g g' : ∀ i, D ⟶ (M.homModel x).obj (Sg.art B i)} (γ : ∀ i, g i ⟶ g' i) (d : D) :
    ConjEq (((M.homModel x).appCell B γ).toNatTrans.app d)
      (M.appCell B (fun i => (γ i).toNatTrans.app d)) := by
  change ConjEq (M.appCell B (fun i => (eqToHom _ ≫ γ i ≫ eqToHom _).toNatTrans.app d)) _
  exact M.toPreModel.appCell_conjEq B rfl rfl fun i => ConjEq.app (ConjEq.conj _ _ _) d

/-- The component of the interpretation of a family of 2-cells of `K(x, M)`. -/
lemma homInterpCell_app {D : Cat.{w, v}} {V : Type uᵥ} {vty : V → Sg.Cat}
    {ε ε' : ∀ v, D ⟶ (M.homModel x).obj (vty v)} (γ : ∀ v, ε v ⟶ ε' v) (d : D) {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    ConjEq (((M.homModel x).interpCell γ t).toNatTrans.app d)
      (M.interpCell (fun v => (γ v).toNatTrans.app d) t) := by
  induction t with
  | var v => exact ConjEq.of_eq rfl
  | app B args ih =>
      refine (M.homAppCell_app x B _ d).trans ?_
      exact M.toPreModel.appCell_conjEq B
        (funext fun i => M.toPreModel.homPreModel_interp_obj_env x ε d (args i))
        (funext fun i => M.toPreModel.homPreModel_interp_obj_env x ε' d (args i)) ih

/-- The interpretation of a term in `K(x, M)` on a morphism of `D`. -/
lemma homInterp_map {D : Cat.{w, v}} {V : Type uᵥ} {vty : V → Sg.Cat}
    (ε : ∀ v, D ⟶ (M.homModel x).obj (vty v)) {d d' : D} (φ : d ⟶ d') {c : Sg.Cat}
    (t : Trm Sg.toFunSig vty c) :
    ConjEq (((M.homModel x).interp ε t).toFunctor.map φ)
      (M.interpCell (fun v => (ε v).toFunctor.map φ) t) := by
  induction t with
  | var v => exact ConjEq.of_eq rfl
  | app B args ih =>
      exact M.toPreModel.appCell_conjEq B
        (funext fun i => M.toPreModel.homPreModel_interp_obj_env x ε d (args i))
        (funext fun i => M.toPreModel.homPreModel_interp_obj_env x ε d' (args i)) ih

variable (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

section Eval

variable {D : Cat.{w, v}} (ε : ∀ s : sg.Srt, D ⟶ (M.homModel x).obj (sg.sty s))
  (χ : ∀ f : sg.Fn, (M.homModel x).interp ε (sg.fndom f) ⟶ (M.homModel x).interp ε (sg.fncod f))

/-- The environment in `M` at an object `d` of `D`: the components `ε_s(d)`. -/
def evalEnv (d : D) (s : sg.Srt) : x ⟶ M.obj (sg.sty s) := (ε s).toFunctor.obj d

/-- The interpretation of a closed term in `K(x, M)` at `ε`, evaluated at `d : D`, is its
interpretation in `M` at the environment `evalEnv ε d` of components. -/
lemma homInterp_obj (d : D) {c : Sg.Cat} (t : sg.CTrm c) :
    ((M.homModel x).interp ε t).toFunctor.obj d = M.interp (M.evalEnv x sg ε d) t :=
  M.toPreModel.homPreModel_interp_obj_env x ε d t

/-- The 2-cells in `M` at an object `d` of `D`: the components `χ_f(d)`. -/
def evalCells (d : D) (f : sg.Fn) :
    M.interp (M.evalEnv x sg ε d) (sg.fndom f) ⟶ M.interp (M.evalEnv x sg ε d) (sg.fncod f) :=
  eqToHom (M.homInterp_obj x sg ε d _).symm ≫ (χ f).toNatTrans.app d ≫
    eqToHom (M.homInterp_obj x sg ε d _)

/-- The component at `d` of an evaluated arrow of `K(x, M)` is the evaluated arrow of `M` at the
components. -/
lemma homArrCellAlg_app (d : D) {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    ConjEq (((M.homModel x).arrCellAlg sg ε χ g).toNatTrans.app d)
      (M.arrCellAlg sg (M.evalEnv x sg ε d) (M.evalCells x sg ε χ d) g) := by
  induction g with
  | fn f => exact (ConjEq.conj _ _ _).symm
  | tr a sub =>
      simp only [arrCellAlg, Cat.Hom₂.comp_app, Cat.eqToHom_app]
      refine (ConjEq.conj _ _ _).trans (ConjEq.trans ?_ (ConjEq.conj _ _ _).symm)
      simp only [Model.trAt, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app]
      refine (ConjEq.conj _ _ _).trans ?_
      change ConjEq (eqToHom _ ≫ M.trAt a _ ≫ eqToHom _) _
      refine (ConjEq.conj _ _ _).trans (M.trAt_conjEq a fun i => ?_)
      exact (Product.cat_lift_π_obj _ _ i d).trans (M.homInterp_obj x sg ε d (sub i))
  | app B i args args' hne g ih =>
      simp only [arrCellAlg]
      refine (M.homAppCell_app x B _ d).trans ?_
      refine M.toPreModel.appCell_conjEq B
        (funext fun j => M.homInterp_obj x sg ε d (args j))
        (funext fun j => M.homInterp_obj x sg ε d (args' j)) fun j => ?_
      by_cases hj : j = i
      · subst hj
        simp only [dite_true, cast_eq]
        exact ih
      · simp only [hj, dite_false, Cat.eqToHom_app]
        exact ConjEq.eqToHom_eqToHom _ _ (M.homInterp_obj x sg ε d (args j))

/-- The component at `d` of an evaluated path of `K(x, M)` is the evaluated path of `M` at the
components. -/
lemma homPathCellAlg_app (d : D) {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    ConjEq (((M.homModel x).pathCellAlg sg ε χ p).toNatTrans.app d)
      (M.pathCellAlg sg (M.evalEnv x sg ε d) (M.evalCells x sg ε χ d) p) := by
  induction p with
  | nil t =>
      simp only [pathCellAlg, Cat.Hom₂.id_app]
      exact ConjEq.id_id (M.homInterp_obj x sg ε d t)
  | cons g p ih =>
      simp only [pathCellAlg, Cat.Hom₂.comp_app]
      exact ConjEq.comp (M.homArrCellAlg_app x sg ε χ d g) ih

end Eval

/-! ### `T`-algebras of `K(x, M)` and of `M` -/

section Alg

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

/-- The `T`-algebra of `M` over `x` at an object `d` of `D`, of a `T`-algebra of `K(x, M)` over
`D`: the components at `d`. -/
def evalAlgAt {D : Cat.{w, v}} (Y : (M.homModel x).Alg sg T D) (d : D) : M.Alg sg T x where
  env := M.evalEnv x sg Y.env d
  cell := M.evalCells x sg Y.env Y.cell d
  eqn r := (ConjEq.eq_iff (M.homPathCellAlg_app x sg Y.env Y.cell d (T.lhs r))
    (M.homPathCellAlg_app x sg Y.env Y.cell d (T.rhs r))).mp
      (congrArg (fun α => α.toNatTrans.app d) (Y.eqn r))

/-- Evaluating a precomposed algebra at `d'` is evaluating at `G(d')`. -/
lemma evalAlgAt_precomp {D D' : Cat.{w, v}} (Y : (M.homModel x).Alg sg T D) (G : D' ⟶ D)
    (d' : D') : M.evalAlgAt x sg T (Y.precomp G) d' = M.evalAlgAt x sg T Y (G.toFunctor.obj d') :=
  Alg.ext' rfl fun f => by
    refine (ConjEq.conj _ _ _).trans ((ConjEq.app (ConjEq.conj _ _ _) d').trans ?_)
    exact (ConjEq.of_eq rfl).trans (ConjEq.conj _ _ _).symm

variable {E : Obj} (A : M.Alg sg T E)

/-- The interpretation in `K(x, M)` at the functors `h ↦ h ≫ ρ_s`, on a 2-cell `α : h ⇒ h'`, is
the whiskering `α ▷ M(t)(ρ)`. -/
lemma postcompInterp_map {h h' : x ⟶ E} (α : h ⟶ h') {c : Sg.Cat} (t : sg.CTrm c) :
    ConjEq (((M.homModel x).interp (fun s => (postcomp x (A.env s)).toCatHom) t).toFunctor.map
      (X := h) (Y := h') α) (α ▷ M.interp A.env t) :=
  (M.homInterp_map x (D := Cat.of (x ⟶ E)) (fun s => (postcomp x (A.env s)).toCatHom)
    (d := h) (d' := h') α t).trans (M.whiskerRight_interp_env A.env α t).symm

/-- Naturality of `evalCell A f` in `h : x ⟶ E`. -/
lemma evalCell_naturality (f : sg.Fn) {h h' : x ⟶ E} (α : h ⟶ h') :
    ((M.homModel x).interp (fun s => (postcomp x (A.env s)).toCatHom)
        (sg.fndom f)).toFunctor.map α ≫
      (eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h' _) ≫
        (A.precomp h').cell f ≫
        eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h' _).symm) =
    (eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h _) ≫
        (A.precomp h).cell f ≫
        eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h _).symm) ≫
      ((M.homModel x).interp (fun s => (postcomp x (A.env s)).toCatHom)
        (sg.fncod f)).toFunctor.map α := by
  refine (ConjEq.eq_iff (ConjEq.comp (M.postcompInterp_map x sg T A α _)
    ((ConjEq.conj _ _ _).trans (ConjEq.conj _ _ _)))
    (ConjEq.comp ((ConjEq.conj _ _ _).trans (ConjEq.conj _ _ _))
      (M.postcompInterp_map x sg T A α _))).mpr ?_
  exact (Bicategory.whisker_exchange α (A.cell f)).symm

/-- The 2-cell of `K(x, M)` given by the 2-cell `ψ_f` of `A`: at `h : x → E`, the 2-cell of
`A.precomp h`. -/
def evalCell (f : sg.Fn) :
    (M.homModel x).interp (fun s => (postcomp x (A.env s)).toCatHom) (sg.fndom f) ⟶
      (M.homModel x).interp (fun s => (postcomp x (A.env s)).toCatHom) (sg.fncod f) :=
  NatTrans.toCatHom₂
    { app := fun h =>
        eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h _) ≫
          (A.precomp h).cell f ≫
          eqToHom (M.homInterp_obj x sg (fun s => (postcomp x (A.env s)).toCatHom) h _).symm
      naturality := fun _ _ α => M.evalCell_naturality x sg T A f α }

/-- The component of `evalCell A f` at `h : x ⟶ E` is the 2-cell `(A.precomp h).cell f`, up to
`ConjEq`. -/
lemma evalCell_app (f : sg.Fn) (h : x ⟶ E) :
    ConjEq ((M.evalCell x sg T A f).toNatTrans.app h) ((A.precomp h).cell f) :=
  ConjEq.conj _ _ _

/-- The evaluation 2-cells satisfy the equations of `T`: for each equation `r`, the path cells of
its two sides agree. -/
lemma evalAlg_eqn (r : T.Eqn) :
    (M.homModel x).pathCellAlg sg (fun s => (postcomp x (A.env s)).toCatHom)
        (M.evalCell x sg T A) (T.lhs r) =
      (M.homModel x).pathCellAlg sg (fun s => (postcomp x (A.env s)).toCatHom)
        (M.evalCell x sg T A) (T.rhs r) := by
  ext h
  have hc : ∀ f, ConjEq (M.evalCells x sg (fun s => (postcomp x (A.env s)).toCatHom)
      (M.evalCell x sg T A) h f) ((A.precomp h).cell f) := fun f =>
    (ConjEq.conj _ _ _).trans (M.evalCell_app x sg T A f h)
  exact (ConjEq.eq_iff
    ((M.homPathCellAlg_app x sg _ _ h (T.lhs r)).trans (M.pathCellAlg_congr sg rfl hc _))
    ((M.homPathCellAlg_app x sg _ _ h (T.rhs r)).trans (M.pathCellAlg_congr sg rfl hc _))).mpr
    ((A.precomp h).eqn r)

/-- **The `T`-algebra of `K(x, M)` over `K(x, E)` given by a `T`-algebra `A` of `M` over `E`**:
the functors `h ↦ h ≫ ρ_s` and the natural transformations `h ↦ h ◁ ψ_f`. -/
def evalAlg : (M.homModel x).Alg sg T (Cat.of (x ⟶ E)) where
  env s := (postcomp x (A.env s)).toCatHom
  cell := M.evalCell x sg T A
  eqn r := M.evalAlg_eqn x sg T A r

/-- The evaluation algebra of `A`, at `h : x → E`, is `A.precomp h`. -/
lemma evalAlgAt_evalAlg (h : x ⟶ E) : M.evalAlgAt x sg T (M.evalAlg x sg T A) h = A.precomp h :=
  Alg.ext' rfl fun f => (ConjEq.conj _ _ _).trans (M.evalCell_app x sg T A f h)

end Alg

/-! ### The terminal category -/

/-- The constant 1-cell `One ⟶ C` at an object `c`. -/
abbrev oneConst {C : Cat.{w, v}} (c : C) : One.{w, v} ⟶ C := ((Functor.const _).obj c).toCatHom

/-- `One` has a single object. -/
lemma one_eq (a : One.{w, v}) : a = One.star := by cases a; rfl

/-- `One` has only identity morphisms. -/
lemma one_hom_eq {a b : One.{w, v}} (φ φ' : a ⟶ b) : φ = φ' := rfl

/-- 1-cells out of `One` are determined by their value at the object. -/
lemma one_hom_ext {C : Cat.{w, v}} {F G : One.{w, v} ⟶ C}
    (h : F.toFunctor.obj One.star = G.toFunctor.obj One.star) : F = G := by
  refine Cat.Hom.ext (CategoryTheory.Functor.ext (fun a => by rw [one_eq a]; exact h)
    fun a b φ => ?_)
  have ha := one_eq a
  have hb := one_eq b
  subst ha hb
  rw [one_hom_eq φ (𝟙 _)]
  simp

/-- 2-cells between 1-cells out of `One` are determined by their component at the object. -/
lemma one_hom₂_ext {C : Cat.{w, v}} {F G : One.{w, v} ⟶ C} {α β : F ⟶ G}
    (h : α.toNatTrans.app One.star = β.toNatTrans.app One.star) : α = β :=
  Cat.Hom₂.ext (NatTrans.ext (funext fun a => by
    have ha := one_eq a
    subst ha
    exact h))

/-- The 2-cell between 1-cells out of `One` with a given component. -/
noncomputable def oneCell {C : Cat.{w, v}} {F G : One.{w, v} ⟶ C}
    (c : F.toFunctor.obj One.star ⟶ G.toFunctor.obj One.star) : F ⟶ G :=
  ⟨(oneEval C).preimage c⟩

/-- The component of `oneCell c` at the object of `One` is `c`. -/
lemma oneCell_app {C : Cat.{w, v}} {F G : One.{w, v} ⟶ C}
    (c : F.toFunctor.obj One.star ⟶ G.toFunctor.obj One.star) :
    (oneCell c).toNatTrans.app One.star = c :=
  (oneEval C).map_preimage c

section One

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

/-- Equal `T`-algebras have `ConjEq` 2-cells. -/
lemma _root_.UlmerBialgebras.Model.Alg.cell_conjEq_of_eq {N : Model Sg Obj}
    {a : Obj} {A B : N.Alg sg T a} (h : A = B) (f : sg.Fn) : ConjEq (A.cell f) (B.cell f) := by
  subst h
  exact ConjEq.of_eq rfl

/-- The constant environment of `K(x, M)` over `One` at an environment of `M` over `x`. -/
abbrev constEnv (ρ : ∀ s : sg.Srt, x ⟶ M.obj (sg.sty s)) (s : sg.Srt) :
    One.{w, v} ⟶ (M.homModel x).obj (sg.sty s) :=
  oneConst (C := (M.homModel x).obj (sg.sty s)) (ρ s)

/-- The 2-cell of `K(x, M)` over `One` given by a 2-cell of `M`. -/
noncomputable def constCell (B : M.Alg sg T x) (f : sg.Fn) :
    (M.homModel x).interp (M.constEnv x sg B.env) (sg.fndom f) ⟶
      (M.homModel x).interp (M.constEnv x sg B.env) (sg.fncod f) :=
  oneCell (eqToHom (M.homInterp_obj x sg (M.constEnv x sg B.env) One.star _) ≫ B.cell f ≫
    eqToHom (M.homInterp_obj x sg (M.constEnv x sg B.env) One.star _).symm)

/-- The component of `constCell B f` at the object of `One` is the 2-cell `B.cell f`, up to
`ConjEq`. -/
lemma constCell_app (B : M.Alg sg T x) (f : sg.Fn) :
    ConjEq ((M.constCell x sg T B f).toNatTrans.app One.star) (B.cell f) := by
  rw [constCell, oneCell_app]
  exact ConjEq.conj _ _ _

/-- The `T`-algebra of `K(x, M)` over `One` given by a `T`-algebra of `M` over `x`. -/
noncomputable def constAlg (B : M.Alg sg T x) : (M.homModel x).Alg sg T One.{w, v} where
  env := M.constEnv x sg B.env
  cell := M.constCell x sg T B
  eqn r := one_hom₂_ext (by
    have hc : ∀ f, ConjEq (M.evalCells x sg (M.constEnv x sg B.env) (M.constCell x sg T B)
        One.star f) (B.cell f) := fun f =>
      (ConjEq.conj _ _ _).trans (M.constCell_app x sg T B f)
    exact (ConjEq.eq_iff
      ((M.homPathCellAlg_app x sg _ _ One.star (T.lhs r)).trans (M.pathCellAlg_congr sg rfl hc _))
      ((M.homPathCellAlg_app x sg _ _ One.star (T.rhs r)).trans
        (M.pathCellAlg_congr sg rfl hc _))).mpr (B.eqn r))

/-- Evaluating the constant algebra `constAlg B` at the object of `One` gives back `B`. -/
lemma evalAlgAt_constAlg (B : M.Alg sg T x) :
    M.evalAlgAt x sg T (M.constAlg x sg T B) One.star = B :=
  Alg.ext' rfl fun f => (ConjEq.conj _ _ _).trans (M.constCell_app x sg T B f)

/-- `T`-algebras of `K(x, M)` over `One` are determined by their evaluation at the object. -/
lemma alg_one_ext {Y Y' : (M.homModel x).Alg sg T One.{w, v}}
    (h : M.evalAlgAt x sg T Y One.star = M.evalAlgAt x sg T Y' One.star) : Y = Y' := by
  obtain ⟨ε, χ, hY⟩ := Y
  obtain ⟨ε', χ', hY'⟩ := Y'
  have he : ε = ε' := funext fun s => one_hom_ext congr(($(h)).env s)
  subst he
  have : χ = χ' := funext fun f => one_hom₂_ext (by
    have hc := Alg.cell_conjEq_of_eq sg T h f
    exact ((ConjEq.conj _ _ _).symm.trans (hc.trans (ConjEq.conj _ _ _))).eq)
  subst this
  rfl

end One

/-! ### The comparison functor `K(x, E) ⥤ K(x, M)^T` -/

section Comparison

variable [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- The canonical `T`-algebra of `K(x, M)` over `K(x, M)^T`. -/
abbrev homCanon : (M.homModel x).Alg sg T ((M.homModel x).thyObj sg T) :=
  (M.homModel x).canonAlg sg T ((M.homModel x).P0 sg) ((M.homModel x).Pfn sg)
    ((M.homModel x).sigIns sg) ((M.homModel x).Peq sg T) ((M.homModel x).thyEquifOf sg T)

/-- The canonical `T`-algebra of `K(x, M)` over `K(x, M)^T` is universal. -/
lemma homCanon_isUniversal : (M.homCanon x sg T).IsUniversal :=
  (M.homModel x).canonAlg_isUniversal sg T _ _ _ _ _

variable {E : Obj} (A : M.Alg sg T E)

/-- **The comparison functor `K(x, E) ⥤ K(x, M)^T`** of a `T`-algebra `A` of `M` over `E`:
`h ↦ A.precomp h`, induced by the universal property of `K(x, M)^T` in `CAT`. For `A` the
canonical algebra on `M^T`, it is `h ↦ (h ≫ e_M ≫ u_M, (h ≫ e_M) ◁ φ_M)`. -/
def algComparison : Cat.of (x ⟶ E) ⟶ (M.homModel x).thyObj sg T :=
  (M.homModel x).algLift sg T ((M.homModel x).P0 sg) ((M.homModel x).Pfn sg)
    ((M.homModel x).sigIns sg) ((M.homModel x).Peq sg T) ((M.homModel x).thyEquifOf sg T)
    (M.evalAlg x sg T A)

/-- Precomposing the canonical algebra over `K(x, M)^T` with the comparison functor of `A` gives the
evaluation algebra `evalAlg A`. -/
lemma homCanon_precomp_algComparison :
    (M.homCanon x sg T).precomp (M.algComparison x sg T A) = M.evalAlg x sg T A :=
  (M.homModel x).canonAlg_precomp_algLift sg T _ _ _ _ _ _

/-- The `T`-algebra of `M` over `x` given by an object of `K(x, M)^T`. -/
abbrev homPsi (y : (M.homModel x).thyObj sg T) : M.Alg sg T x :=
  M.evalAlgAt x sg T (M.homCanon x sg T) y

/-- The `T`-algebra of `M` over `x` given by the image of `h : x ⟶ E` under the comparison functor
is `A.precomp h`. -/
lemma homPsi_algComparison (h : x ⟶ E) :
    M.homPsi x sg T ((M.algComparison x sg T A).toFunctor.obj h) = A.precomp h := by
  rw [homPsi, ← evalAlgAt_precomp, homCanon_precomp_algComparison, evalAlgAt_evalAlg]

/-- **Objects of `K(x, M)^T` are the `T`-algebras of `M` over `x`.** -/
lemma homPsi_bijective : Function.Bijective (M.homPsi x sg T) := by
  refine ⟨fun y y' hyy => ?_, fun B => ?_⟩
  · have e : (M.homCanon x sg T).precomp (oneConst y) =
        (M.homCanon x sg T).precomp (oneConst y') :=
      M.alg_one_ext x sg T (by rw [evalAlgAt_precomp, evalAlgAt_precomp]; exact hyy)
    have := ((M.homCanon_isUniversal x sg T One.{w, v}).1
      ((M.homCanon x sg T).precomp (oneConst y))).unique rfl e.symm
    exact Functor.congr_obj (Cat.Hom.ext_iff.mp this) One.star
  · obtain ⟨k, hk, -⟩ := (M.homCanon_isUniversal x sg T One.{w, v}).1 (M.constAlg x sg T B)
    exact ⟨k.toFunctor.obj One.star, by
      rw [homPsi, ← evalAlgAt_precomp, hk, evalAlgAt_constAlg]⟩

/-- The comparison functor is bijective on objects iff `A` has property (1) of Remark 3.17 at
`x`. -/
theorem algComparison_obj_bijective_iff :
    Function.Bijective (M.algComparison x sg T A).toFunctor.obj ↔
      ∀ B : M.Alg sg T x, ∃! h : x ⟶ E, A.precomp h = B := by
  rw [← Function.bijective_iff_existsUnique,
    ← (M.homPsi_bijective x sg T).of_comp_iff' (M.algComparison x sg T A).toFunctor.obj]
  exact iff_of_eq congr(Function.Bijective $(funext (M.homPsi_algComparison x sg T A)))

end Comparison

/-! ### Morphisms -/

section Hom

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)

/-- Transport of a 2-cell of `T`-algebras along equalities of its endpoints. -/
def _root_.UlmerBialgebras.Model.Alg.Hom.transport {N : Model Sg Obj} {a : Obj}
    {A A' B B' : N.Alg sg T a} (hA : A = A') (hB : B = B') (β : Alg.Hom A B) : Alg.Hom A' B' :=
  hA ▸ hB ▸ β

/-- Transporting a 2-cell of `T`-algebras along equalities of its endpoints leaves its components
unchanged, up to `ConjEq`. -/
lemma _root_.UlmerBialgebras.Model.Alg.Hom.transport_app {N : Model Sg Obj} {a : Obj}
    {A A' B B' : N.Alg sg T a} (hA : A = A') (hB : B = B') (β : Alg.Hom A B) (s : sg.Srt) :
    ConjEq ((Alg.Hom.transport sg T hA hB β).app s) (β.app s) := by
  subst hA hB
  exact ConjEq.of_eq rfl

omit [Bicategory.Strict Obj] [HasChosenFinProducts Obj] in
/-- Equal functors send a morphism to `ConjEq` morphisms. -/
lemma map_conjEq_of_eq {C D : Cat.{w, v}} {F G : C ⟶ D} (h : F = G) {a b : C} (θ : a ⟶ b) :
    ConjEq (F.toFunctor.map θ) (G.toFunctor.map θ) := by
  subst h
  exact ConjEq.of_eq rfl

/-- The 2-cell between the evaluations at `d` and `d'` of a `T`-algebra of `K(x, M)`, given by a
morphism `φ : d ⟶ d'`. -/
def evalHomAt {D : Cat.{w, v}} (Y : (M.homModel x).Alg sg T D) {d d' : D} (φ : d ⟶ d') :
    Alg.Hom (M.evalAlgAt x sg T Y d) (M.evalAlgAt x sg T Y d') where
  app s := (Y.env s).toFunctor.map φ
  comm f := (ConjEq.eq_iff (ConjEq.comp (ConjEq.conj _ _ _).symm (M.homInterp_map x Y.env φ _))
      (ConjEq.comp (M.homInterp_map x Y.env φ _) (ConjEq.conj _ _ _).symm)).mp
    ((Y.cell f).toNatTrans.naturality φ).symm

/-- The component at `d'` of a 2-cell of `Y.precomp G` is the component of the corresponding 2-cell
of `Y` at `G d'`, up to `ConjEq`. -/
lemma precomp_cell_app {D D' : Cat.{w, v}} (Y : (M.homModel x).Alg sg T D) (G : D' ⟶ D)
    (d' : D') (f : sg.Fn) :
    ConjEq (((Y.precomp G).cell f).toNatTrans.app d')
      ((Y.cell f).toNatTrans.app (G.toFunctor.obj d')) :=
  ConjEq.app (ConjEq.conj _ _ _) d'

end Hom

section HomComparison

variable [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- The 2-cell of `T`-algebras of `M` over `x` given by a morphism of `K(x, M)^T`. -/
abbrev homPsiHom {y y' : (M.homModel x).thyObj sg T} (g : y ⟶ y') :
    Alg.Hom (M.homPsi x sg T y) (M.homPsi x sg T y') :=
  M.evalHomAt x sg T (M.homCanon x sg T) g

/-- **Morphisms of `K(x, M)^T` are the 2-cells of `T`-algebras of `M` over `x`.** -/
lemma homPsiHom_bijective (y y' : (M.homModel x).thyObj sg T) :
    Function.Bijective (M.homPsiHom x sg T (y := y) (y' := y')) := by
  let A := M.homCanon x sg T
  have R2 := (M.homCanon_isUniversal x sg T One.{w, v}).2 (oneConst y) (oneConst y')
  refine ⟨fun g g' hgg => ?_, fun β => ?_⟩
  · let θ : ∀ g : y ⟶ y', (oneConst y : One.{w, v} ⟶ _) ⟶ oneConst y' := fun g => oneCell g
    have hθ : ∀ g s, ((θ g ▷ A.env s).toNatTrans.app One.star) = (A.env s).toFunctor.map g :=
      fun g s => by simp only [Cat.whiskerRight_app, θ, oneCell_app]
    have e := (R2 (A.whiskerHom (θ g))).unique (fun s => rfl) (fun s => one_hom₂_ext
      ((hθ g' s).trans ((funext_iff.mp (Alg.Hom.ext_iff.mp hgg) s).symm.trans (hθ g s).symm)))
    have e' : (θ g).toNatTrans.app One.star = (θ g').toNatTrans.app One.star :=
      NatTrans.congr_app (Cat.Hom₂.ext_iff.mp e) One.star
    simp only [θ, oneCell_app] at e'
    exact e'
  · let β₁ : Alg.Hom (A.precomp (oneConst y)) (A.precomp (oneConst y')) :=
      { app := fun s => oneCell (β.app s)
        comm := fun f => one_hom₂_ext (by
          simp only [Cat.Hom₂.comp_app]
          have hi : ∀ t : sg.CTrm (sg.fnty f), ConjEq (((M.homModel x).interpCell
              (fun s => (oneCell (β.app s) : (A.precomp (oneConst y)).env s ⟶
                (A.precomp (oneConst y')).env s)) t).toNatTrans.app One.star)
              (M.interpCell β.app t) := fun t =>
            (M.homInterpCell_app x _ One.star t).trans
              (M.toPreModel.interpCell_conjEq rfl rfl (fun s => ConjEq.of_eq (oneCell_app _)) t)
          exact (ConjEq.eq_iff
            (ConjEq.comp ((M.precomp_cell_app x sg T A (oneConst y) One.star f).trans
              (ConjEq.conj _ _ _).symm) (hi _))
            (ConjEq.comp (hi _) ((M.precomp_cell_app x sg T A (oneConst y') One.star f).trans
              (ConjEq.conj _ _ _).symm))).mpr (β.comm f)) }
    obtain ⟨θ, hθ, -⟩ := R2 β₁
    refine ⟨θ.toNatTrans.app One.star, Alg.Hom.ext (funext fun s => ?_)⟩
    exact (NatTrans.congr_app (Cat.Hom₂.ext_iff.mp (hθ s)) One.star).trans (oneCell_app _)

variable {E : Obj} (A : M.Alg sg T E)

/-- The 2-cell of `T`-algebras given by the image of `θ : h₁ ⟶ h₂` under the comparison functor has
components `θ ▷ ρ_s`, up to `ConjEq`. -/
lemma homPsiHom_algComparison {h₁ h₂ : x ⟶ E} (θ : h₁ ⟶ h₂) (s : sg.Srt) :
    ConjEq ((M.homPsiHom x sg T ((M.algComparison x sg T A).toFunctor.map θ)).app s)
      (θ ▷ A.env s) :=
  map_conjEq_of_eq congr(($(M.homCanon_precomp_algComparison x sg T A)).env s) θ

/-- The comparison functor is full and faithful iff `A` has property (2) of Remark 3.17 at `x`. -/
theorem algComparison_fullyFaithful_iff :
    ((M.algComparison x sg T A).toFunctor.Full ∧ (M.algComparison x sg T A).toFunctor.Faithful) ↔
      ∀ (h₁ h₂ : x ⟶ E) (β : Alg.Hom (A.precomp h₁) (A.precomp h₂)),
        ∃! θ : h₁ ⟶ h₂, ∀ s, θ ▷ A.env s = β.app s := by
  let H := (M.algComparison x sg T A).toFunctor
  have hP := M.homPsi_algComparison x sg T A
  constructor
  · rintro ⟨hfull, hfaith⟩ h₁ h₂ β
    let β' := Alg.Hom.transport sg T (hP h₁).symm (hP h₂).symm β
    obtain ⟨g, hg⟩ := (M.homPsiHom_bijective x sg T _ _).2 β'
    obtain ⟨θ, rfl⟩ := hfull.map_surjective g
    refine ⟨θ, fun s => ((M.homPsiHom_algComparison x sg T A θ s).symm.trans
      ((ConjEq.of_eq (funext_iff.mp (Alg.Hom.ext_iff.mp hg) s)).trans
        (Alg.Hom.transport_app sg T _ _ β s))).eq, fun θ' hθ' => hfaith.map_injective ?_⟩
    refine (M.homPsiHom_bijective x sg T _ _).1 (Alg.Hom.ext (funext fun s => ?_))
    exact ((M.homPsiHom_algComparison x sg T A θ' s).trans ((ConjEq.of_eq (hθ' s)).trans
      ((Alg.Hom.transport_app sg T _ _ β s).symm.trans
        (ConjEq.of_eq (funext_iff.mp (Alg.Hom.ext_iff.mp hg) s).symm)))).eq
  · intro R2
    refine ⟨⟨fun {h₁ h₂} g => ?_⟩, ⟨fun {h₁ h₂} θ θ' hθθ => ?_⟩⟩
    · let β := Alg.Hom.transport sg T (hP h₁) (hP h₂) (M.homPsiHom x sg T g)
      obtain ⟨θ, hθ, -⟩ := R2 h₁ h₂ β
      refine ⟨θ, (M.homPsiHom_bijective x sg T _ _).1 (Alg.Hom.ext (funext fun s => ?_))⟩
      refine ((M.homPsiHom_algComparison x sg T A θ s).trans ?_).eq
      rw [hθ s]
      exact Alg.Hom.transport_app sg T _ _ _ s
    · have hw : ∀ s, θ ▷ A.env s = θ' ▷ A.env s := fun s =>
        ((M.homPsiHom_algComparison x sg T A θ s).symm.trans
          ((ConjEq.of_eq (by rw [hθθ])).trans (M.homPsiHom_algComparison x sg T A θ' s))).eq
      exact (R2 h₁ h₂ (A.whiskerHom θ)).unique (fun s => rfl) (fun s => (hw s).symm)

/-- **The comparison functor `K(x, E) ⥤ K(x, M)^T` is an isomorphism of categories** (bijective on
objects, full and faithful) **iff `A` has the universal property of Remark 3.17 at `x`**. -/
theorem algComparison_iso_iff :
    (Function.Bijective (M.algComparison x sg T A).toFunctor.obj ∧
      (M.algComparison x sg T A).toFunctor.Full ∧
        (M.algComparison x sg T A).toFunctor.Faithful) ↔ A.IsUniversalAt x := by
  rw [Alg.IsUniversalAt, ← M.algComparison_obj_bijective_iff x sg T A,
    ← M.algComparison_fullyFaithful_iff x sg T A]

end HomComparison

end Model

end UlmerBialgebras
