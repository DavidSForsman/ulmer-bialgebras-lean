module

public import UlmerBialgebras.Models.Bialgebra

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The Induced Functor of Algebras Theorem

Lemma 3.21, Theorem 3.22 and Corollary 3.23 of *A Syntactic Approach to Ulmer's
Bialgebras*: a lax morphism `(F, η) : M → N` of Σ-models induces a morphism
`F^T : M^T → N^T` between the objects of `T`-bialgebras, provided that `η_t` is invertible
at the function coarity terms and monic (after whiskering with `u_M e_M`) at the equational
coarity terms.

## Main results

* `UlmerBialgebras.LaxMor.sigMor`: the 1-cell `F^σ : M^σ → N^σ` with `F^σ u_N = u_M F₀` (Lemma 3.21
  (1)).
* `UlmerBialgebras.LaxMor.theta_path`: the compatibility (3.5) of `F^σ` with the evaluation of paths
  (Lemma 3.21 (2)).
* `UlmerBialgebras.LaxMor.exists_unique_thyMor`: if `η_t` is invertible at the function coarity
  terms and `η_t` whiskered by `u_M e_M` is monic at the equational coarity terms, there is a unique
  `F^T : M^T → N^T` with `F^T e_N = e_M F^σ` (Theorem 3.22).
* `UlmerBialgebras.LaxMor.exists_unique_thyMor_of_algebraic`: the same for an algebraic theory
  (Corollary 3.23 (1)).
* `UlmerBialgebras.LaxMor.exists_unique_thyMor_of_strong`: the same for a strong morphism
  (Corollary 3.23 (3)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 3.21, Theorem 3.22 and Corollary 3.23
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace LaxMor

noncomputable section

variable {M N : Model Sg Obj} (F : LaxMor M N) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The 1-cell `F₀ : M₀ → N₀`. -/
abbrev prod0 : (M.P0 sg).pt ⟶ (N.P0 sg).pt :=
  (N.P0 sg).lift (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s))

/-- The comparison 2-cell `η_t : N(t) F₀ ⇒ F_c M(t)`. -/
abbrev etaTm {c : Sg.Cat} (t : sg.CTrm c) :
    N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t ⟶ M.tm sg t ≫ F.cell c :=
  F.toLaxData.eta (M.P0 sg).π t

omit [HasChosenProductsOfSize.{s₂, u, v, w} Obj] in
/-- `F₀ ≫ N(t)` is the interpretation of `t` in `N` in the environment `π_s ≫ F_{c_s}`. -/
lemma prod0_comp_tm {c : Sg.Cat} (t : sg.CTrm c) :
    F.prod0 sg ≫ N.tm sg t = N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t := by
  rw [Model.tm, ← N.toPreModel.interp_comp]
  exact N.toPreModel.interp_congr (fun s => (N.P0 sg).lift_π _ s) t

variable [HasChosenInserters.{u, v, w} Obj]

/-- The source of `η_t ∗ u_M`, rewritten: `(u_M ≫ F₀) ≫ N(t) = u_M ≫ N(t)[π_s ≫ F_{c_s}]`. -/
lemma sig_src_eq {c : Sg.Cat} (t : sg.CTrm c) :
    (M.u sg ≫ F.prod0 sg) ≫ N.tm sg t
      = M.u sg ≫ N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t := by
  rw [Category.assoc, F.prod0_comp_tm]

/-- The target of `LaxMor.Psi`: `u_M ≫ M(t) ≫ F_c` is `M^σ(t) ≫ F_c`. -/
lemma sig_tgt_eq {c : Sg.Cat} (t : sg.CTrm c) :
    M.u sg ≫ M.tm sg t ≫ F.cell c = M.sigTm sg t ≫ F.cell c := by
  rw [← Category.assoc, ← Model.sigTm_eq]

/-- The 2-cell `η_t ∗ u_M`, with its source and target rewritten. -/
def Psi {c : Sg.Cat} (t : sg.CTrm c) :
    ((M.u sg ≫ F.prod0 sg) ≫ N.tm sg t) ⟶ (M.sigTm sg t ≫ F.cell c) :=
  eqToHom (F.sig_src_eq sg t) ≫ (M.u sg ◁ F.etaTm sg t) ≫
    eqToHom (F.sig_tgt_eq sg t)

/-- `Ψ_t` is invertible when the comparison 2-cell `η_t` is. -/
instance psi_isIso {c : Sg.Cat} (t : sg.CTrm c) [IsIso (F.etaTm sg t)] :
    IsIso (F.Psi sg t) := by
  rw [Psi]; infer_instance

/-- `Ψ_t` is the comparison 2-cell of `F` at the environment of `M^σ`. -/
lemma psi_eq_eta {c : Sg.Cat} (t : sg.CTrm c) :
    F.Psi sg t = eqToHom (by
      rw [F.sig_src_eq, show (fun s => M.sigEnv sg s ≫ F.cell (sg.sty s)) =
        (fun s => M.u sg ≫ ((M.P0 sg).π s ≫ F.cell (sg.sty s))) from
        funext fun s => Category.assoc _ _ _, N.toPreModel.interp_comp]) ≫
      F.toLaxData.eta (M.sigEnv sg) t := by
  rw [Psi, F.toLaxData.eta_precomp (M.P0 sg).π (M.u sg) t]
  simp [etaTm]

/-- Rewriting `(u_M ≫ F₀) ≫ N(dom) ≫ π_f` as `(u_M ≫ F₀) ≫ N(dom f)`. -/
lemma sigStr_dom_eq (f : sg.Fn) :
    ((M.u sg ≫ F.prod0 sg) ≫ N.domCell sg) ≫ (N.Pfn sg).π f
      = (M.u sg ≫ F.prod0 sg) ≫ N.tm sg (sg.fndom f) := by
  rw [Category.assoc (M.u sg ≫ F.prod0 sg) (N.domCell sg) ((N.Pfn sg).π f), Model.domCell,
    (N.Pfn sg).lift_π]

/-- Rewriting `(u_M ≫ F₀) ≫ N(cod) ≫ π_f` as `(u_M ≫ F₀) ≫ N(cod f)`. -/
lemma sigStr_cod_eq (f : sg.Fn) :
    ((M.u sg ≫ F.prod0 sg) ≫ N.codCell sg) ≫ (N.Pfn sg).π f
      = (M.u sg ≫ F.prod0 sg) ≫ N.tm sg (sg.fncod f) := by
  rw [Category.assoc (M.u sg ≫ F.prod0 sg) (N.codCell sg) ((N.Pfn sg).π f), Model.codCell,
    (N.Pfn sg).lift_π]

section

variable (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fncod f)))

/-- The 2-cell of equation (3.4) used to induce `F^σ` from the inserter `N^σ`. -/
def sigStr : ((M.u sg ≫ F.prod0 sg) ≫ N.domCell sg) ⟶
    ((M.u sg ≫ F.prod0 sg) ≫ N.codCell sg) :=
  (N.Pfn sg).lift₂ (fun f =>
    haveI : IsIso (F.etaTm sg (sg.fncod f)) := hiso f
    eqToHom (F.sigStr_dom_eq sg f) ≫
      F.Psi sg (sg.fndom f) ≫
      (M.arrCell sg (OneSig.Arr.fn f) ▷ F.cell (sg.fnty f)) ≫
      inv (F.Psi sg (sg.fncod f)) ≫
      eqToHom (F.sigStr_cod_eq sg f).symm)

/-- The induced morphism `F^σ : M^σ → N^σ` of Lemma 3.21 (1). -/
def sigMor : M.sigObj sg ⟶ N.sigObj sg :=
  (N.sigIns sg).lift (M.u sg ≫ F.prod0 sg) (F.sigStr sg hiso)

/-- `F^σ ≫ u_N = u_M ≫ F₀` (Lemma 3.21 (1) of [forsman2026syntactic]). -/
lemma sigMor_u : F.sigMor sg hiso ≫ N.u sg = M.u sg ≫ F.prod0 sg :=
  (N.sigIns sg).lift_u _ _

/-- `F^σ ≫ N^σ(t) = (u_M ≫ F₀) ≫ N(t)` for a closed term `t`. -/
lemma sigMor_sigTm {c : Sg.Cat} (t : sg.CTrm c) :
    F.sigMor sg hiso ≫ N.sigTm sg t = (M.u sg ≫ F.prod0 sg) ≫ N.tm sg t := by
  rw [Model.sigTm_eq, ← Category.assoc, F.sigMor_u]

/-- The comparison 2-cell `Θ_t : F^σ ≫ N^σ(t) ⟶ M^σ(t) ≫ F_c`. -/
def Theta {c : Sg.Cat} (t : sg.CTrm c) :
    (F.sigMor sg hiso ≫ N.sigTm sg t) ⟶ (M.sigTm sg t ≫ F.cell c) :=
  eqToHom (F.sigMor_sigTm sg hiso t) ≫ F.Psi sg t

/-- `Θ_t` is the comparison 2-cell of `F` at the environment of `M^σ`. -/
lemma theta_eq_eta {c : Sg.Cat} (t : sg.CTrm c) :
    F.Theta sg hiso t = eqToHom (by
      rw [F.sigMor_sigTm sg hiso, F.sig_src_eq,
        show (fun s => M.sigEnv sg s ≫ F.cell (sg.sty s)) =
          (fun s => M.u sg ≫ ((M.P0 sg).π s ≫ F.cell (sg.sty s))) from
          funext fun s => Category.assoc _ _ _, N.toPreModel.interp_comp]) ≫
      F.toLaxData.eta (M.sigEnv sg) t := by
  rw [Theta, F.psi_eq_eta]
  simp

/-- `Θ` at a term headed by a functor symbol. -/
lemma theta_app (B : Sg.Fun) (args : ∀ j : Fin (Sg.arn B), sg.CTrm (Sg.art B j)) :
    F.Theta sg hiso (Trm.app B args)
      = eqToHom (by
        rw [show N.sigTm sg (Trm.app B args)
              = (N.P B).lift (fun j => N.sigTm sg (args j)) ≫ N.fn B from rfl,
          ← Category.assoc, (N.P B).comp_lift]) ≫
        N.appCell B (fun j => F.Theta sg hiso (args j)) ≫
        F.toLaxData.strAt B (fun j => M.sigTm sg (args j)) := by
  rw [F.theta_eq_eta sg hiso (Trm.app B args),
    N.toPreModel.appCell_congr B (fun j => F.theta_eq_eta sg hiso (args j)),
    ← N.toPreModel.appCell_comp, LaxData.eta_app]
  simp [Model.sigTm]

/-- `Θ` at a substituted term. -/
lemma theta_subst {V : Type uᵥ} {vty : V → Sg.Cat} {c : Sg.Cat} (t : Trm Sg.toFunSig vty c)
    (sub : ∀ v : V, sg.CTrm (vty v)) :
    F.Theta sg hiso (t.subst sub)
      = eqToHom (by rw [Model.sigTm_subst, ← N.toPreModel.interp_comp]) ≫
        N.toPreModel.interpCell (fun v => F.Theta sg hiso (sub v)) t ≫
        F.toLaxData.eta (fun v => M.sigTm sg (sub v)) t ≫
        eqToHom (by rw [Model.sigTm_subst]) := by
  rw [F.theta_eq_eta sg hiso (t.subst sub), F.toLaxData.eta_subst (M.sigEnv sg) sub t,
    N.toPreModel.interpCell_congr
      (fun v => (eqToHom_comp_iff _ _ _).1 (F.theta_eq_eta sg hiso (sub v)).symm) t,
    ← N.toPreModel.interpCell_comp]
  simp [Model.sigTm]

/-- `Θ` commutes with the identifications of equal terms. -/
lemma theta_eqToHom {c : Sg.Cat} {t t' : sg.CTrm c} (e : t = t') :
    (F.sigMor sg hiso ◁ eqToHom (by rw [e])) ≫ F.Theta sg hiso t'
      = F.Theta sg hiso t ≫ (eqToHom (by rw [e]) ▷ F.cell c) := by
  subst e; simp

/-- Equation (3.5) of Lemma 3.21 (2), for the arrows of the term graph. -/
lemma theta_arr {c : Sg.Cat} {t t' : sg.CTrm c} (g : sg.Arr t t') :
    (F.sigMor sg hiso ◁ N.arrCell sg g) ≫ F.Theta sg hiso t'
      = F.Theta sg hiso t ≫ (M.arrCell sg g ▷ F.cell c) := by
  -- By the arrow: a function symbol (the structure cell of `F^σ`), a transformation symbol
  -- (`F.tr_compat_at` and the naturality of `trAt`), and an arrow under a functor symbol
  -- (the induction hypothesis, through `appCell`).
  induction g with
  | fn f =>
      have : IsIso (F.etaTm sg (sg.fncod f)) := hiso f
      have hφ : F.sigMor sg hiso ◁ (N.sigIns sg).φ
          = eqToHom (by rw [← Category.assoc, F.sigMor_u]) ≫ F.sigStr sg hiso ≫
            eqToHom (by rw [← Category.assoc, F.sigMor_u]) :=
        (N.sigIns sg).lift_φ _ _
      have hstr : F.sigStr sg hiso ▷ (N.Pfn sg).π f
          = eqToHom (F.sigStr_dom_eq sg f) ≫ F.Psi sg (sg.fndom f) ≫
            (M.arrCell sg (OneSig.Arr.fn f) ▷ F.cell (sg.fnty f)) ≫
            inv (F.Psi sg (sg.fncod f)) ≫ eqToHom (F.sigStr_cod_eq sg f).symm := by
        rw [sigStr, (N.Pfn sg).lift₂_π]
      rw [Model.arrCell_fn]
      simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
      rw [Bicategory.Strict.whisker_assoc, hφ]
      simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc]
      rw [hstr, Theta, Theta]
      simp
  | tr a sub =>
      have hnat := N.trAt_nat a (ρ := fun i => F.sigMor sg hiso ≫ N.sigTm sg (sub i))
        (ρ' := fun i => M.sigTm sg (sub i) ≫ F.cell (Sg.trt a i))
        (fun i => F.Theta sg hiso (sub i))
      have hcompat := F.tr_compat_at a (fun i => M.sigTm sg (sub i))
      have hpre := N.trAt_precomp a (fun i => N.sigTm sg (sub i)) (F.sigMor sg hiso)
      rw [Model.arrCell_tr, Model.arrCell_tr, F.theta_subst sg hiso (Sg.trtgt a) sub,
        F.theta_subst sg hiso (Sg.trsrc a) sub]
      simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
        Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [hpre]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← reassoc_of% hnat, reassoc_of% hcompat]
  | app B i args args' hne g ih =>
      have comp : ∀ j : Fin (Sg.arn B),
          (F.sigMor sg hiso ◁ (if hj : j = i then
              cast (congrArg (fun k => (N.sigTm sg (args k) ⟶ N.sigTm sg (args' k))) hj.symm)
                (N.arrCell sg g)
            else eqToHom (by rw [hne j hj]))) ≫ F.Theta sg hiso (args' j)
          = F.Theta sg hiso (args j) ≫ ((if hj : j = i then
              cast (congrArg (fun k => (M.sigTm sg (args k) ⟶ M.sigTm sg (args' k))) hj.symm)
                (M.arrCell sg g)
            else eqToHom (by rw [hne j hj])) ▷ F.cell (Sg.art B j)) := by
        intro j
        by_cases hj : j = i
        · subst hj
          simpa using ih
        · simp only [dite_eq_right hj]
          exact F.theta_eqToHom sg hiso (hne j hj)
      rw [Model.arrCell_app, Model.arrCell_app, N.toPreModel.whiskerLeft_appCell,
        F.theta_app sg hiso B args', F.theta_app sg hiso B args]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      slice_lhs 2 3 => rw [N.toPreModel.appCell_comp]
      rw [N.toPreModel.appCell_congr B comp, ← N.toPreModel.appCell_comp]
      simp only [Category.assoc]
      rw [F.toLaxData.strAt_nat]

/-- Equation (3.5) of Lemma 3.21 (2), for the paths of the term graph. -/
lemma theta_path {c : Sg.Cat} {t t' : sg.CTrm c} (p : sg.Path t t') :
    (F.sigMor sg hiso ◁ N.pathCell sg p) ≫ F.Theta sg hiso t'
      = F.Theta sg hiso t ≫ (M.pathCell sg p ▷ F.cell c) := by
  induction p with
  | nil t => simp
  | cons g p ih =>
      rw [Model.pathCell_cons, Model.pathCell_cons, Bicategory.whiskerLeft_comp, Category.assoc, ih,
        ← Category.assoc, F.theta_arr sg hiso g, Category.assoc, ← Bicategory.comp_whiskerRight]

variable [HasChosenEquifiers.{u, v, w} Obj] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- **The Induced Functor of Algebras Theorem** (Theorem 3.22 of [forsman2026syntactic]).

Let `(F, η) : M → N` be a lax morphism of Σ-models in a PIE-complete 2-category.  Assume
that `η_t` is an isomorphism for every function coarity term `t`, and that `η_t ∗ u_M e_M`
is monic for every equational coarity term `t`.  Then there is a unique morphism
`F^T : M^T → N^T` with `F^T ≫ e_N = e_M ≫ F^σ`. -/
theorem exists_unique_thyMor
    (hmono : ∀ r : T.Eqn, Mono ((M.e sg T ≫ M.u sg) ◁ F.etaTm sg (T.cod r))) :
    ∃! G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T = M.e sg T ≫ F.sigMor sg hiso := by
  have hmonoTheta : ∀ r : T.Eqn, Mono (M.e sg T ◁ F.Theta sg hiso (T.cod r)) := by
    intro r
    have := hmono r
    rw [Theta, Psi]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
    rw [Bicategory.Strict.comp_whiskerLeft' (M.e sg T) (M.u sg) (F.etaTm sg (T.cod r))]
    infer_instance
  have key : ∀ r : T.Eqn,
      M.e sg T ◁ (F.sigMor sg hiso ◁ N.pathCell sg (T.lhs r))
        = M.e sg T ◁ (F.sigMor sg hiso ◁ N.pathCell sg (T.rhs r)) := by
    intro r
    have := hmonoTheta r
    have w1 := congr(M.e sg T ◁ $(F.theta_path sg hiso (T.lhs r)))
    have w2 := congr(M.e sg T ◁ $(F.theta_path sg hiso (T.rhs r)))
    simp only [Bicategory.whiskerLeft_comp] at w1 w2
    rw [Bicategory.Strict.whisker_assoc, M.e_pathCell sg T r, ← Bicategory.Strict.whisker_assoc,
      ← w2] at w1
    exact (cancel_mono _).1 w1
  have H : (M.e sg T ≫ F.sigMor sg hiso) ◁ N.lhsCell sg T
      = (M.e sg T ≫ F.sigMor sg hiso) ◁ N.rhsCell sg T := by
    refine (N.Peq sg T).cell_ext (fun r => ?_)
    rw [Bicategory.Strict.whisker_assoc', Bicategory.Strict.whisker_assoc', Model.lhsCell,
      Model.rhsCell,
      (N.Peq sg T).lift₂_π, (N.Peq sg T).lift₂_π]
    simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
    rw [Bicategory.Strict.comp_whiskerLeft, Bicategory.Strict.comp_whiskerLeft, key r]
  refine ⟨(N.thyEquif sg T).lift _ H, (N.thyEquif sg T).lift_e _ H, ?_⟩
  intro G hG
  exact (N.thyEquif sg T).lift_uniq G _ H hG

end

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- **Corollary 3.23 (1)**: for an *algebraic* theory `T` every lax morphism of Σ-models
induces a morphism of the objects of `T`-bialgebras. -/
theorem exists_unique_thyMor_of_algebraic (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj] (halg : T.IsAlgebraic) :
    ∃! G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T
        = M.e sg T ≫ F.sigMor sg (fun f => F.toLaxData.eta_isVar _ (halg.1 f)) := by
  refine F.exists_unique_thyMor sg _ T (fun r => ?_)
  have := F.toLaxData.eta_isVar (M.P0 sg).π (halg.2 r)
  infer_instance

/-- **Corollary 3.23 (3)**: a *strong* morphism of Σ-models induces a morphism of the objects
of `T`-bialgebras for every bialgebraic theory `T`. -/
theorem exists_unique_thyMor_of_strong (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (hstrong : ∀ B : Sg.Fun, IsIso (F.str B)) :
    ∃! G : M.thyObj sg T ⟶ N.thyObj sg T,
      G ≫ N.e sg T
        = M.e sg T ≫ F.sigMor sg
            (fun f => F.toLaxData.eta_isIso_of_strong hstrong _ (sg.fncod f)) := by
  refine F.exists_unique_thyMor sg _ T (fun r => ?_)
  have := F.toLaxData.eta_isIso_of_strong hstrong (M.P0 sg).π (T.cod r)
  infer_instance

end

end LaxMor

end UlmerBialgebras
