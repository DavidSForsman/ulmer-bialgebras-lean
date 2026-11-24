module

public import UlmerBialgebras.Factorization.SubTheoryExact
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2

/-!
# Extensions of 1-signatures, translations of theories, and Corollary 6.9

In `UlmerBialgebras/Factorization/SubTheory.lean` and
`UlmerBialgebras/Factorization/SubTheoryExact.lean`,
the forgetful 1-cell `M^{T₂} → M^{T₁}` and its regularity/exactness inheritance (**Corollary 6.9**
of the paper, numbered 5.11 in an earlier version) are formalized for a sub-theory
`T₁ = T₂.restrict j` over the *same* 1-signature `σ₁ = σ₂`.

This file generalizes that machinery to **sub-1-signatures `σ₁ ⊆ σ₂` and the corresponding
sub-theories**, using `UlmerBialgebras.OneSig.restrictFn` and `UlmerBialgebras.Theory.restrictSig`
from `UlmerBialgebras/Paper/Sec3Defs2.lean`:

* `UlmerBialgebras.Model.PfnSub`, `UlmerBialgebras.Model.sigSubCell` — the projections and 2-cells
  restricting the interpretation of function symbols along `jFn : Fn₁ → sg.Fn`;
* `UlmerBialgebras.Model.sigSubForget`, `UlmerBialgebras.Model.thySubSigForget` — the canonical
  forgetful 1-cells `M^{σ₂} → M^{σ₁}` and `M^{T₂} → M^{T₁}`, which lie over the identity of `M₀`
  (`UlmerBialgebras.Model.thySubSigForget_thyForget`); this is the morphism of bialgebraic data to
  which `cor_6_9` in `UlmerBialgebras/Proofs/Sec6/Sec6Proofs.lean` applies Corollary 6.8.

## Main results

* `UlmerBialgebras.Model.thySubSigForget`: the forgetful 1-cell `M^T → M^{T₁}` for a sub-theory `T₁`
  of `T` over a sub-1-signature.
* `UlmerBialgebras.Model.thySubSigForget_thyForget`: it commutes with the forgetful 1-cells to
  `M₀`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.9
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Sg : TwoSig.{u₁, u₂, u₃}}

/-! ## Morphisms of 1-signatures and translation of the term graph -/

/-! ## Sub-theories over a sub-1-signature and the forgetful 1-cells -/

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) {Fn₁ : Type s₂}
  (jFn : Fn₁ → sg.Fn)

section Terms

variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- Restricting the function symbols does not change `M₀ = ∏_s M_{c_s}`. -/
@[simp] lemma p0_restrictFn : M.P0 (sg.restrictFn jFn) = M.P0 sg := rfl

/-- Restricting the function symbols does not change the 1-cell `M(t) : M₀ → M_c` of a closed
    term. -/
@[simp] lemma tm_restrictFn {c : Sg.Cat} (t : sg.CTrm c) :
    M.tm (sg.restrictFn jFn) t = M.tm sg t := rfl

end Terms

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The projection `∏_{f : sg.Fn} M_{c_f} → ∏_{f₁ : Fn₁} M_{c_{jFn f₁}}`. -/
def PfnSub : (M.Pfn sg).pt ⟶ (M.Pfn (sg.restrictFn jFn)).pt :=
  (M.Pfn (sg.restrictFn jFn)).lift (fun f₁ => (M.Pfn sg).π (jFn f₁))

/-- The `f₁`-th projection of `PfnSub` is the `jFn f₁`-th projection. -/
@[simp] lemma pfnSub_π (f₁ : Fn₁) :
    M.PfnSub sg jFn ≫ (M.Pfn (sg.restrictFn jFn)).π f₁ = (M.Pfn sg).π (jFn f₁) :=
  (M.Pfn (sg.restrictFn jFn)).lift_π _ f₁

variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- The arity 1-cell of `σ` followed by `PfnSub` is the arity 1-cell of `σ₁ = sg.restrictFn jFn`. -/
lemma domCell_PfnSub :
    M.domCell sg ≫ M.PfnSub sg jFn = M.domCell (sg.restrictFn jFn) := by
  refine (M.Pfn (sg.restrictFn jFn)).hom_ext (fun f₁ => ?_)
  rw [Category.assoc, pfnSub_π, domCell, (M.Pfn sg).lift_π, domCell,
    (M.Pfn (sg.restrictFn jFn)).lift_π]
  rfl

/-- The coarity 1-cell of `σ` followed by `PfnSub` is the coarity 1-cell of `σ₁`. -/
lemma codCell_PfnSub :
    M.codCell sg ≫ M.PfnSub sg jFn = M.codCell (sg.restrictFn jFn) := by
  refine (M.Pfn (sg.restrictFn jFn)).hom_ext (fun f₁ => ?_)
  rw [Category.assoc, pfnSub_π, codCell, (M.Pfn sg).lift_π, codCell,
    (M.Pfn (sg.restrictFn jFn)).lift_π]
  rfl

variable [HasChosenInserters.{u, v, w} Obj]

/-- The 2-cell used to lift `M.u sg` into the inserter `M^{sg.restrictFn jFn}`. -/
def sigSubCell :
    M.u sg ≫ M.domCell (sg.restrictFn jFn) ⟶ M.u sg ≫ M.codCell (sg.restrictFn jFn) :=
  eqToHom (by rw [← M.domCell_PfnSub sg jFn, Category.assoc]) ≫
    ((M.sigIns sg).φ ▷ M.PfnSub sg jFn) ≫
    eqToHom (by rw [Category.assoc, M.codCell_PfnSub sg jFn])

/-- The forgetful 1-cell `M^σ → M^{σ₁}` for a sub-1-signature `σ₁ = sg.restrictFn jFn`. -/
def sigSubForget : M.sigObj sg ⟶ M.sigObj (sg.restrictFn jFn) :=
  (M.sigIns (sg.restrictFn jFn)).lift (M.u sg) (M.sigSubCell sg jFn)

/-- `u_{σ₁} ∘ sigSubForget = u_σ`: the forgetful 1-cell `M^σ → M^{σ₁}` lies over `M₀`. -/
@[simp] lemma sigSubForget_u :
    M.sigSubForget sg jFn ≫ M.u (sg.restrictFn jFn) = M.u sg :=
  (M.sigIns (sg.restrictFn jFn)).lift_u _ _

/-- The structure 2-cell of `M^{σ₁}` whiskered by `sigSubForget` is `sigSubCell`, up to
    `eqToHom`s. -/
@[simp] lemma sigSubForget_φ :
    M.sigSubForget sg jFn ◁ (M.sigIns (sg.restrictFn jFn)).φ =
      eqToHom (by rw [← Category.assoc, M.sigSubForget_u sg jFn]) ≫ M.sigSubCell sg jFn ≫
        eqToHom (by rw [← Category.assoc, M.sigSubForget_u sg jFn]) :=
  (M.sigIns (sg.restrictFn jFn)).lift_φ _ _

/-- `M^{σ₁}(t) ∘ sigSubForget = M^σ(t)` for every closed term `t`. -/
lemma sigSubForget_sigTm {c : Sg.Cat} (t : sg.CTrm c) :
    M.sigSubForget sg jFn ≫ M.sigTm (sg.restrictFn jFn) t = M.sigTm sg t := by
  rw [sigTm_eq, sigTm_eq, ← Category.assoc, sigSubForget_u, tm_restrictFn]

omit [HasChosenInserters.{u, v, w} Obj] [HasChosenProductsOfSize.{s₁, u, v, w} Obj]
  [HasChosenProductsOfSize.{s₂, u, v, w} Obj] in
/-- The image under a functor symbol `B` of a family conjugated by `eqToHom`s is the image of the
    family, conjugated by `eqToHom`s. -/
lemma appCell_congr_hom (B : Sg.Fun) {x : Obj}
    {g₁ g₁' g₂ g₂' : ∀ i, x ⟶ M.obj (Sg.art B i)}
    (e₁ : ∀ i, g₁ i = g₁' i) (e₂ : ∀ i, g₂ i = g₂' i) (γ : ∀ i, g₁' i ⟶ g₂' i) :
    M.appCell B (fun i => eqToHom (e₁ i) ≫ γ i ≫ eqToHom (e₂ i).symm) =
      eqToHom (by rw [funext e₁]) ≫ M.appCell B γ ≫ eqToHom (by rw [funext e₂]) := by
  have h₁ : g₁ = g₁' := funext e₁
  have h₂ : g₂ = g₂' := funext e₂
  subst h₁; subst h₂
  simp

/-- Whiskering the evaluation of an arrow of `sg.restrictFn jFn` with `sigSubForget` gives the
evaluation of the translated arrow in `sg`. -/
lemma sigSubForget_arrCell : ∀ {c : Sg.Cat} {t t' : (sg.restrictFn jFn).CTrm c}
    (g : (sg.restrictFn jFn).Arr t t'),
    M.sigSubForget sg jFn ◁ M.arrCell (sg.restrictFn jFn) g =
      eqToHom (M.sigSubForget_sigTm sg jFn t) ≫
        M.arrCell sg (OneSig.Arr.ofRestrictFn jFn g) ≫
        eqToHom (M.sigSubForget_sigTm sg jFn t').symm
  | _, _, _, .fn f₁ => by
      rw [arrCell_fn, OneSig.Arr.ofRestrictFn, arrCell_fn]
      simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
      rw [Bicategory.Strict.whisker_assoc (M.sigSubForget sg jFn) (M.sigIns (sg.restrictFn jFn)).φ
          ((M.Pfn (sg.restrictFn jFn)).π f₁),
        sigSubForget_φ]
      dsimp only [sigSubCell]
      simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight, Category.assoc,
        eqToHom_trans,
        eqToHom_trans_assoc]
      have hπ : M.PfnSub sg jFn ≫ (M.Pfn (sg.restrictFn jFn)).π f₁ = (M.Pfn sg).π (jFn f₁) :=
        M.pfnSub_π sg jFn f₁
      have hcongr := Bicategory.whiskerRight_congr (M.sigIns sg).φ hπ
      rw [Bicategory.Strict.whiskerRight_comp' (M.sigIns sg).φ (M.PfnSub sg jFn)
          ((M.Pfn (sg.restrictFn jFn)).π f₁)]
      simp [reassoc_of% hcongr]
  | _, _, _, .tr a sub => by
      rw [arrCell_tr, OneSig.Arr.ofRestrictFn, arrCell_tr]
      simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
      rw [M.trAt_precomp a (fun i => M.sigTm (sg.restrictFn jFn) (sub i)) (M.sigSubForget sg jFn)]
      rw [M.trAt_congr a (fun i => M.sigSubForget_sigTm sg jFn (sub i))]
      simp
  | _, _, _, .app B i args args' hne g => by
      have ih := sigSubForget_arrCell g
      rw [arrCell_app, OneSig.Arr.ofRestrictFn, arrCell_app]
      rw [M.toPreModel.whiskerLeft_appCell B _ (M.sigSubForget sg jFn)]
      have harg : (fun j => M.sigSubForget sg jFn ≫ M.sigTm (sg.restrictFn jFn) (args j)) =
          (fun j => M.sigTm sg (args j)) := funext (fun j => M.sigSubForget_sigTm sg jFn (args j))
      have harg' : (fun j => M.sigSubForget sg jFn ≫ M.sigTm (sg.restrictFn jFn) (args' j)) =
          (fun j => M.sigTm sg (args' j)) := funext (fun j => M.sigSubForget_sigTm sg jFn (args' j))
      have h1 : M.appCell B (fun j =>
          M.sigSubForget sg jFn ◁
            if hj : j = i then
              cast (congrArg (fun k => M.sigTm (sg.restrictFn jFn) (args k) ⟶
                M.sigTm (sg.restrictFn jFn) (args' k)) hj.symm)
                (M.arrCell (sg.restrictFn jFn) g)
            else eqToHom (by rw [hne j hj])) =
          eqToHom (by rw [harg]) ≫
          M.appCell B (fun j =>
            if hj : j = i then
              cast (congrArg (fun k => M.sigTm sg (args k) ⟶ M.sigTm sg (args' k)) hj.symm)
                (M.arrCell sg (OneSig.Arr.ofRestrictFn jFn g))
            else eqToHom (by rw [hne j hj])) ≫
          eqToHom (by rw [harg']) := by
        rw [← M.appCell_congr_hom B (fun j => M.sigSubForget_sigTm sg jFn (args j))
          (fun j => M.sigSubForget_sigTm sg jFn (args' j))]
        refine M.appCell_congr B (fun j => ?_)
        by_cases hj : j = i
        · subst hj
          rw [dite_eq_left rfl, dite_eq_left rfl, cast_eq, cast_eq, ih]
        · simp only [dite_eq_right hj, Bicategory.whiskerLeft_eqToHom, eqToHom_trans]
      rw [h1]
      simp

/-- Whiskering the evaluation of a path of `sg.restrictFn jFn` with `sigSubForget` gives the
evaluation of the translated path in `sg`. -/
lemma sigSubForget_pathCell : ∀ {c : Sg.Cat} {t t' : (sg.restrictFn jFn).CTrm c}
    (p : (sg.restrictFn jFn).Path t t'),
    M.sigSubForget sg jFn ◁ M.pathCell (sg.restrictFn jFn) p =
      eqToHom (M.sigSubForget_sigTm sg jFn t) ≫
        M.pathCell sg (OneSig.Path.ofRestrictFn jFn p) ≫
        eqToHom (M.sigSubForget_sigTm sg jFn t').symm
  | _, _, _, .nil t => by
      simp [OneSig.Path.ofRestrictFn]
  | _, _, _, .cons g p => by
      have ih := sigSubForget_pathCell p
      simp only [pathCell_cons, OneSig.Path.ofRestrictFn, Bicategory.whiskerLeft_comp,
        M.sigSubForget_arrCell sg jFn g, ih, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]

section SubSigForget

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
  [HasChosenEquifiers.{u, v, w} Obj] {E : Type s₃} (jEq : E → T.Eqn)
  (lhs₁ rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r)))
  (hlhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (lhs₁ r) = T.lhs (jEq r))
  (hrhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (rhs₁ r) = T.rhs (jEq r))

include hlhs hrhs

/-- The composite `M.e sg T ≫ M.sigSubForget sg jFn` equifies the defining 2-cells of
`T.restrictSig jFn jEq lhs₁ rhs₁`. -/
theorem e_sigSubForget_equifies :
    (M.e sg T ≫ M.sigSubForget sg jFn) ◁
        M.lhsCell (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) =
      (M.e sg T ≫ M.sigSubForget sg jFn) ◁
        M.rhsCell (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) := by
  refine M.whiskerLeft_lhsCell_eq (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) _
    (fun r => ?_)
  dsimp [Theory.restrictSig]
  rw [Bicategory.Strict.comp_whiskerLeft, Bicategory.Strict.comp_whiskerLeft,
    M.sigSubForget_pathCell sg jFn (lhs₁ r), M.sigSubForget_pathCell sg jFn (rhs₁ r),
    hlhs r, hrhs r]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, M.e_pathCell sg T (jEq r)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  congr 1

/-- The forgetful 1-cell `M^T → M^{T₁}` for a sub-theory `T₁ = T.restrictSig jFn jEq lhs₁ rhs₁`
over a sub-1-signature `σ₁ = sg.restrictFn jFn`. -/
def thySubSigForget :
    M.thyObj sg T ⟶ M.thyObj (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) :=
  (M.thyEquif (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁)).lift
    (M.e sg T ≫ M.sigSubForget sg jFn)
    (M.e_sigSubForget_equifies sg jFn T jEq lhs₁ rhs₁ hlhs hrhs)

/-- `e_{T₁} ∘ thySubSigForget = sigSubForget ∘ e_T`: the forgetful 1-cell `M^T → M^{T₁}` is
    compatible with the equifier inclusions into `M^σ` and `M^{σ₁}`. -/
@[simp] lemma thySubSigForget_e :
    M.thySubSigForget sg jFn T jEq lhs₁ rhs₁ hlhs hrhs ≫
        M.e (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) =
      M.e sg T ≫ M.sigSubForget sg jFn :=
  (M.thyEquif (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁)).lift_e _ _

/-- Compatibility of `thySubSigForget` with the forgetful 1-cells to `M₀`:
`U_{T₁} ∘ thySubSigForget = U_T`. -/
@[simp] lemma thySubSigForget_thyForget :
    M.thySubSigForget sg jFn T jEq lhs₁ rhs₁ hlhs hrhs ≫
        M.thyForget (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) =
      M.thyForget sg T := by
  rw [show M.thyForget (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) =
        M.e (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) ≫ M.u (sg.restrictFn jFn)
      from rfl,
    ← Category.assoc, M.thySubSigForget_e, Category.assoc, M.sigSubForget_u]

end SubSigForget

end Model

end UlmerBialgebras
