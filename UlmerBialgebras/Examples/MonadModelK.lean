module

public import UlmerBialgebras.Examples.LaxPathCalc
public import UlmerBialgebras.Examples.SignatureEx
public import UlmerBialgebras.Models.ThyRep
public import Mathlib.Tactic.FinCases

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# A monad in a 2-category as a `Σ_Mnd`-model, and its `T_Lax`-algebras

For a monad `(t : c → c, m : tt ⇒ t, e : id_c ⇒ t)` in a strict 2-category `K` with chosen finite
products:
* `UlmerBialgebras.MndK.model`: the `Σ_Mnd`-model of the monad, with `M(T) = π₀ ≫ t` on the chosen
  unary product and `μ`, `η` interpreted by `m`, `e`;
* `UlmerBialgebras.MndK.IsAlg`: a pair `(h' : x → c, ψ : t h' ⇒ h')` satisfies
  `ψ • m h' = ψ • t ψ` and `ψ • e h' = id`;
* `UlmerBialgebras.MndK.eqn_iff_isAlg`: an environment and a 2-cell for `T` satisfy the equations of
  the lax-limit theory `T_Lax` iff they satisfy the two algebra equations;
* `UlmerBialgebras.MndK.emAlg`: the `T_Lax`-algebra of a pair satisfying them.

Composition of 1-cells is diagrammatic, so `t h'` is `h' ≫ t` and `m h'` is `h' ◁ m`. The monad
laws are not needed and are not assumed.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17,
  Examples 3.20 (4)
* [R. Street, *The formal theory of monads*][STREET1972149]
-/

universe u v w

namespace UlmerBialgebras.MndK

open CategoryTheory SigEx

/-- A morphism `ConjEq` to an identity can be absorbed on the left. -/
lemma comp_of_conjEq_id {C : Type*} [Category C] {X Y Z X' Z' : C} {u : X ⟶ Y} {v : Y ⟶ Z}
    {v' : X' ⟶ Z'} {W : C} (hu : ConjEq u (𝟙 W)) (hv : ConjEq v v') : ConjEq (u ≫ v) v' := by
  obtain ⟨p, q, rfl⟩ := hu
  simpa using hv.eqToHom_comp (p.trans q)

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
  {c : Obj} (t : c ⟶ c) (m : t ≫ t ⟶ t) (e : 𝟙 c ⟶ t)

/-- The interpretation of the functor symbol `T` of `Σ_Mnd`: `t` after the projection of the
chosen unary product. -/
def preModel : PreModel mndSig Obj where
  obj _ := c
  fn _ := (HasChosenFinProducts.finProd (fun _ : Fin 1 => c)).π 0 ≫ t

/-- The interpretation of `T(s₀)` is `t` after the interpretation of `s₀`. -/
lemma preModel_interp_app {V : Type} {vty : V → Unit} {x : Obj}
    (ρ : ∀ v, x ⟶ (preModel t).obj (vty v)) (args : Fin 1 → Trm mndFunSig vty ()) :
    (preModel t).interp ρ (Trm.app MndFun.T args) = (preModel t).interp ρ (args 0) ≫ t :=
  -- `T(s)` is interpreted by the lift of `s` to the unary product, then `π 0 ≫ t`.
  (Category.assoc _ _ _).symm.trans
    congr($((HasChosenFinProducts.finProd (fun _ : Fin 1 => c)).lift_π
      (fun i => (preModel t).interp ρ (args i)) 0) ≫ t)

/-- The interpretation of `T s` is `t` after the interpretation of `s`. -/
lemma preModel_interp_mndT {V : Type} {vty : V → Unit} {x : Obj}
    (ρ : ∀ v, x ⟶ (preModel t).obj (vty v)) (s : Trm mndFunSig vty ()) :
    (preModel t).interp ρ (mndT s) = (preModel t).interp ρ s ≫ t :=
  preModel_interp_app t ρ ![s]

/-- The interpretation of `μ` and `η` by `m` and `e`, at the projection of the context product. -/
def modelCell : ∀ a : MndTr,
    (preModel t).interp ((preModel t).Pctx a).π (mndSig.trsrc a) ⟶
      (preModel t).interp ((preModel t).Pctx a).π (mndSig.trtgt a)
    | .mu => eqToHom (by
          rw [preModel_interp_mndT, preModel_interp_mndT]
          exact Category.assoc _ _ _) ≫
        ((preModel t).Pctx MndTr.mu).π 0 ◁ m ≫
          eqToHom (by exact (preModel_interp_mndT t ((preModel t).Pctx MndTr.mu).π (.var 0)).symm)
    | .eta => eqToHom (Category.comp_id _).symm ≫
        ((preModel t).Pctx MndTr.eta).π 0 ◁ e ≫
          eqToHom (by exact (preModel_interp_mndT t ((preModel t).Pctx MndTr.eta).π (.var 0)).symm)

/-- **A monad in `K` as a `Σ_Mnd`-model** (cf. Examples 3.19). -/
def model : Model mndSig Obj where
  toPreModel := preModel t
  tr := modelCell t m e

/-- `(h', ψ : t h' ⇒ h')` satisfies `ψ • m h' = ψ • t ψ` and `ψ • e h' = id_{h'}`. -/
def IsAlg {x : Obj} (h' : x ⟶ c) (ψ : h' ≫ t ⟶ h') : Prop :=
  (h' ◁ m ≫ ψ = eqToHom (Category.assoc h' t t).symm ≫ ψ ▷ t ≫ ψ) ∧
    (h' ◁ e ≫ ψ = eqToHom (Category.comp_id h'))


/-! ### Calculations in the model of the monad -/

/-- The 1-signature `σ_Lax` of `Σ_Mnd`. -/
abbrev σL : OneSig mndSig := LaxEx.oneSig mndSig

/-- The theory `T_Lax` of `Σ_Mnd`. -/
abbrev TL : Theory σL := LaxEx.theory mndSig

/-- The image of a 2-cell under the functor symbol `T` is its whiskering by `t`. -/
lemma appCell_T_conjEq {x : Obj} {g g' : ∀ i, x ⟶ (model t m e).obj (mndSig.art MndFun.T i)}
    (γ : ∀ i, g i ⟶ g' i) :
    ConjEq ((model t m e).appCell MndFun.T γ) (γ 0 ▷ t) := by
  let P := (model t m e).P MndFun.T
  change ConjEq ((P.lift₂ (fun i => eqToHom (P.lift_π g i) ≫ γ i ≫
    eqToHom (P.lift_π g' i).symm)) ▷ (P.π 0 ≫ t)) (γ 0 ▷ t)
  refine (ConjEq.whiskerRight_comp₁ _ _ _).trans (ConjEq.whiskerRight ?_ t)
  rw [P.lift₂_π]
  exact ConjEq.conj _ _ _

/-- The interpretation of `μ` at an environment `ρ` is `ρ₀ ◁ m`. -/
lemma trAt_mu_conjEq {x : Obj} (ρ : ∀ i, x ⟶ (model t m e).obj (mndSig.trt MndTr.mu i)) :
    ConjEq ((model t m e).trAt MndTr.mu ρ) (ρ 0 ◁ m) := by
  let P := (model t m e).Pctx MndTr.mu
  have h1 : ConjEq ((model t m e).tr MndTr.mu) (P.π 0 ◁ m) := ConjEq.conj _ _ _
  exact (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft (P.lift ρ) h1).trans
    ((ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans (ConjEq.whiskerLeft_congr' (P.lift_π ρ 0) m)))

/-- The interpretation of `η` at an environment `ρ` is `ρ₀ ◁ e`. -/
lemma trAt_eta_conjEq {x : Obj} (ρ : ∀ i, x ⟶ (model t m e).obj (mndSig.trt MndTr.eta i)) :
    ConjEq ((model t m e).trAt MndTr.eta ρ) (ρ 0 ◁ e) := by
  let P := (model t m e).Pctx MndTr.eta
  have h1 : ConjEq ((model t m e).tr MndTr.eta) (P.π 0 ◁ e) := ConjEq.conj _ _ _
  exact (ConjEq.conj _ _ _).trans ((ConjEq.whiskerLeft (P.lift ρ) h1).trans
    ((ConjEq.whiskerLeft_comp₁ _ _ _).symm.trans (ConjEq.whiskerLeft_congr' (P.lift_π ρ 0) e)))

/-- The term `T(x₀)[s̄]` of the equations of `T_Lax` is `T(s)`. -/
lemma subst_mndT_var (a : MndTr) :
    (mndT (Trm.var 0)).subst (LaxEx.subS mndSig a) =
      (Trm.app MndFun.T (fun _ => Trm.var ()) : σL.CTrm ()) := by
  rw [Trm.subst]
  congr 1
  funext i
  fin_cases i
  rfl

/-- The term `T(T(x₀))[s̄]` of the equation `μ` is `T(T(s))`. -/
lemma subst_mndT_mndT_var :
    (mndT (mndT (Trm.var 0))).subst (LaxEx.subS mndSig MndTr.mu) =
      (Trm.app MndFun.T (fun _ => Trm.app MndFun.T (fun _ => Trm.var ())) : σL.CTrm ()) := by
  rw [Trm.subst]
  congr 1
  funext i
  fin_cases i
  exact subst_mndT_var MndTr.mu

/-! ### `T_Lax`-algebras of the monad -/

section Alg

variable {t m e} {x : Obj} (ρ : ∀ s : σL.Srt, x ⟶ (model t m e).obj (σL.sty s))
  (ψ : ∀ f : σL.Fn, (model t m e).interp ρ (σL.fndom f) ⟶ (model t m e).interp ρ (σL.fncod f))

/-- The domain `T(x₀)` of the function symbol `T` is interpreted as `ρ () ≫ t`. -/
lemma interp_fndom_T : (model t m e).interp ρ (σL.fndom MndFun.T) = ρ () ≫ t :=
  preModel_interp_app t ρ (fun _ => Trm.var ())

/-- The 2-cell `ψ : t h' ⇒ h'` of an environment with a 2-cell for `T`. -/
def psiAlg : ρ () ≫ t ⟶ ρ () := eqToHom (interp_fndom_T ρ).symm ≫ ψ MndFun.T

/-- The 2-cell `ψ MndFun.T` is `ConjEq` to its retyped form `psiAlg ρ ψ`. -/
lemma psi_conjEq : ConjEq (ψ MndFun.T) (psiAlg ρ ψ) :=
  ((ConjEq.of_eq rfl).eqToHom_comp _).symm

/-- The canonical path of `T(s)` evaluates to the 2-cell of `T`. -/
lemma termPath_T_alg (s₀ : σL.CTrm ()) (h : s₀ = Trm.app MndFun.T (fun _ => Trm.var ())) :
    ConjEq ((model t m e).pathCellAlg σL ρ ψ (LaxEx.termPath s₀)) (ψ MndFun.T) := by
  subst h
  rw [LaxEx.pathCellAlg_termPath]
  have hfun : (fun _ : Fin 1 => (model t m e).pathCellAlg σL ρ ψ
      (LaxEx.termPath (Trm.var ()))) = fun _ => 𝟙 _ :=
    funext fun _ => LaxEx.pathCellAlg_termPath_var _ _ _ _
  rw [hfun, PreModel.appCell_id]
  exact comp_of_conjEq_id (ConjEq.of_eq rfl) (ConjEq.of_eq rfl)

/-- The left side of the equation `μ` evaluates to `m h'` followed by `ψ`, up to `ConjEq`. -/
lemma lhs_mu_alg : ConjEq ((model t m e).pathCellAlg σL ρ ψ (TL.lhs MndTr.mu))
    (ρ () ◁ m ≫ psiAlg ρ ψ) := by
  simp only [TL, LaxEx.theory, LaxEx.pathCellAlg_comp, Model.pathCellAlg_cons,
    Model.pathCellAlg_nil, Category.comp_id, Model.arrCellAlg_tr]
  refine ConjEq.comp ((ConjEq.conj _ _ _).trans (trAt_mu_conjEq t m e _)) ?_
  exact (termPath_T_alg ρ ψ _ (subst_mndT_var _)).trans (psi_conjEq ρ ψ)

/-- The canonical path of `T(T(s))` is `ψ • t ψ`. -/
lemma termPath_TT_alg (s₀ : σL.CTrm ())
    (h : s₀ = Trm.app MndFun.T (fun _ => Trm.app MndFun.T (fun _ => Trm.var ()))) :
    ConjEq ((model t m e).pathCellAlg σL ρ ψ (LaxEx.termPath s₀))
      (eqToHom (Category.assoc (ρ ()) t t).symm ≫ psiAlg ρ ψ ▷ t ≫ psiAlg ρ ψ) := by
  subst h
  rw [LaxEx.pathCellAlg_termPath]
  have p1 := (appCell_T_conjEq t m e (fun _ => (model t m e).pathCellAlg σL ρ ψ
      (LaxEx.termPath (Trm.app MndFun.T (fun _ => Trm.var ()))))).trans
    (ConjEq.whiskerRight ((termPath_T_alg ρ ψ _ rfl).trans (psi_conjEq ρ ψ)) t)
  exact (ConjEq.comp p1 (psi_conjEq ρ ψ)).trans ((ConjEq.of_eq rfl).eqToHom_comp _).symm

/-- The right side of the equation `μ` evaluates to `ψ • t ψ`, up to `ConjEq`. -/
lemma rhs_mu_alg : ConjEq ((model t m e).pathCellAlg σL ρ ψ (TL.rhs MndTr.mu))
    (eqToHom (Category.assoc (ρ ()) t t).symm ≫ psiAlg ρ ψ ▷ t ≫ psiAlg ρ ψ) :=
  termPath_TT_alg ρ ψ _ subst_mndT_mndT_var

/-- The left side of the equation `η` evaluates to `e h'` followed by `ψ`, up to `ConjEq`. -/
lemma lhs_eta_alg : ConjEq ((model t m e).pathCellAlg σL ρ ψ (TL.lhs MndTr.eta))
    (ρ () ◁ e ≫ psiAlg ρ ψ) := by
  simp only [TL, LaxEx.theory, LaxEx.pathCellAlg_comp, Model.pathCellAlg_cons,
    Model.pathCellAlg_nil, Category.comp_id, Model.arrCellAlg_tr]
  refine ConjEq.comp ((ConjEq.conj _ _ _).trans (trAt_eta_conjEq t m e _)) ?_
  exact (termPath_T_alg ρ ψ _ (subst_mndT_var _)).trans (psi_conjEq ρ ψ)

/-- The right side of the equation `η` evaluates to the identity 2-cell, up to `ConjEq`. -/
lemma rhs_eta_alg : ConjEq ((model t m e).pathCellAlg σL ρ ψ (TL.rhs MndTr.eta))
    (eqToHom (Category.comp_id (ρ ()))) := by
  have h0 : (model t m e).pathCellAlg σL ρ ψ (TL.rhs MndTr.eta) = 𝟙 _ :=
    LaxEx.pathCellAlg_termPath_var _ _ _ _
  rw [h0]
  exact ConjEq.eqToHom_eqToHom rfl _ (Category.comp_id (ρ ())).symm

/-- **The equations of `T_Lax` for a monad**: an environment with a 2-cell for `T` satisfies
the two equations of `T_Lax` iff `(h', ψ)` satisfies `ψ • m h' = ψ • t ψ` and
`ψ • e h' = id`. -/
theorem eqn_iff_isAlg :
    (∀ r, (model t m e).pathCellAlg σL ρ ψ (TL.lhs r) =
      (model t m e).pathCellAlg σL ρ ψ (TL.rhs r)) ↔ IsAlg t m e (ρ ()) (psiAlg ρ ψ) := by
  constructor
  · intro h
    exact ⟨(ConjEq.eq_iff (lhs_mu_alg ρ ψ) (rhs_mu_alg ρ ψ)).1 (h MndTr.mu),
      (ConjEq.eq_iff (lhs_eta_alg ρ ψ) (rhs_eta_alg ρ ψ)).1 (h MndTr.eta)⟩
  · rintro ⟨h₁, h₂⟩ r
    cases r
    · exact (ConjEq.eq_iff (lhs_mu_alg ρ ψ) (rhs_mu_alg ρ ψ)).2 h₁
    · exact (ConjEq.eq_iff (lhs_eta_alg ρ ψ) (rhs_eta_alg ρ ψ)).2 h₂

end Alg

omit [HasChosenFinProducts Obj] in
/-- `IsAlg` is invariant under equal 1-cells and `ConjEq` 2-cells. -/
lemma isAlg_congr {x : Obj} {h₁ h₂ : x ⟶ c} {ψ₁ : h₁ ≫ t ⟶ h₁} {ψ₂ : h₂ ≫ t ⟶ h₂}
    (hh : h₁ = h₂) (hψ : ConjEq ψ₁ ψ₂) : IsAlg t m e h₁ ψ₁ ↔ IsAlg t m e h₂ ψ₂ := by
  subst hh
  obtain rfl := hψ.eq
  rfl

/-- **The `T_Lax`-algebra of a pair `(u : d → c, η : t u ⇒ u)`** satisfying the two algebra
equations: the environment `u` and the 2-cell `η` for `T`. -/
def emAlg {d : Obj} (u : d ⟶ c) (η : u ≫ t ⟶ u) (hη : IsAlg t m e u η) :
    (model t m e).Alg σL TL d where
  env _ := u
  cell f := match f with
    | MndFun.T => eqToHom (interp_fndom_T (t := t) (m := m) (e := e) fun _ => u) ≫ η
  eqn := (eqn_iff_isAlg _ _).mpr ((isAlg_congr t m e rfl (by
    exact ((ConjEq.of_eq (rfl : η = η)).eqToHom_comp _).eqToHom_comp _)).mpr hη)

end UlmerBialgebras.MndK
