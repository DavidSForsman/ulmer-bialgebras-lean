module

public import UlmerBialgebras.Models.Induced
public import UlmerBialgebras.Models.Oplax

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The 1-cell `F^σ` induced by an oplax morphism

This is the oplax form of Lemma 3.21 (1) of *A Syntactic Approach to Ulmer's Bialgebras*. Let
`(F, η) : M → N` be an oplax morphism of `Σ`-models. Its comparison 2-cells point the other way,
`η_t : F_c M(t) ⇒ N(t) F₀`. Assume that `η_t` is invertible at the function arity terms. Then the
inserter `N^σ` induces `F^σ : M^σ → N^σ` with `u_N F^σ = F₀ u_M` and
`φ_N F^σ = (η_{t₂} u_M)_f • (∏_f F_c φ_M) • (η_{t₁}⁻¹ u_M)_f`, for the function symbols
`f : t₁ → t₂`.

For a coalgebraic theory the arity terms are sorts, so `η_t` is an identity there.
Corollary 3.23 (2) states that `F` then induces `F^T : M^T → N^T` with `e_N F^T = F^σ e_M`. The
lax `F^σ` is `UlmerBialgebras.LaxMor.sigMor`. `UlmerBialgebras.OplaxMor.toLax_sigMor`
(`CoInduced.lean`) shows that the oplax `F^σ` is the lax `F^σ` of `F` read in `K^co`.

## Main results

* `UlmerBialgebras.OplaxData.eta_isVar`: at a sort, the comparison 2-cell `η_t` is invertible.
* `UlmerBialgebras.OplaxMor.sigStr`: the 2-cell `(η_{t₂} u_M)_f • (∏_f F_c φ_M) • (η_{t₁}⁻¹ u_M)_f`
  used to induce `F^σ` from the inserter `N^σ`.
* `UlmerBialgebras.OplaxMor.sigMor`: the 1-cell `F^σ : M^σ → N^σ` induced by an oplax morphism whose
  `η_t` are invertible at the function arity terms (Lemma 3.21 (1)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 3.21 (1), Corollary 3.23 (2)
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃ uᵥ

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace OplaxData

variable {M N : PreModel Sg Obj} (F : OplaxData M N)

/-- If `t` is a sort (a variable), the comparison 2-cell `η_t` is the identity. -/
lemma eta_isVar {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (ρ : ∀ v, x ⟶ M.obj (vty v))
    {c : Sg.Cat} {t : Trm Sg.toFunSig vty c} (h : t.IsVar) : IsIso (F.eta ρ t) := by
  cases t with
  | var v => rw [eta_var]; infer_instance
  | app B args => exact h.elim

end OplaxData

namespace OplaxMor

noncomputable section

variable {M N : Model Sg Obj} (F : OplaxMor M N) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The 1-cell `F₀ : M₀ → N₀`. -/
abbrev prod0 : (M.P0 sg).pt ⟶ (N.P0 sg).pt :=
  (N.P0 sg).lift (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s))

/-- The comparison 2-cell `η_t : F_c M(t) ⇒ N(t) F₀`. -/
abbrev etaTm {c : Sg.Cat} (t : sg.CTrm c) :
    M.tm sg t ≫ F.cell c ⟶ N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t :=
  F.toOplaxData.eta (M.P0 sg).π t

omit [HasChosenProductsOfSize.{s₂, u, v, w} Obj] in
/-- `F₀ ≫ N(t)` is the interpretation of `t` in `N` in the environment `π_s ≫ F_{c_s}`. -/
lemma prod0_comp_tm {c : Sg.Cat} (t : sg.CTrm c) :
    F.prod0 sg ≫ N.tm sg t = N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t := by
  rw [Model.tm, ← N.toPreModel.interp_comp]
  exact N.toPreModel.interp_congr (fun s => (N.P0 sg).lift_π _ s) t

variable [HasChosenInserters.{u, v, w} Obj]

/-- Rewriting `(u_M ≫ F₀) ≫ N(t)` as `u_M ≫ N(t)[π_s ≫ F_{c_s}]`. -/
lemma sig_src_eq {c : Sg.Cat} (t : sg.CTrm c) :
    (M.u sg ≫ F.prod0 sg) ≫ N.tm sg t
      = M.u sg ≫ N.interp (fun s => (M.P0 sg).π s ≫ F.cell (sg.sty s)) t := by
  rw [Category.assoc, F.prod0_comp_tm]

/-- The source of `OplaxMor.Psi`: `M^σ(t) ≫ F_c` is `u_M ≫ M(t) ≫ F_c` (named after the target
of the lax `LaxMor.Psi`). -/
lemma sig_tgt_eq {c : Sg.Cat} (t : sg.CTrm c) :
    M.sigTm sg t ≫ F.cell c = M.u sg ≫ M.tm sg t ≫ F.cell c := by
  rw [Model.sigTm_eq, Category.assoc]

/-- The 2-cell `η_t ∗ u_M`, with its source and target rewritten. -/
def Psi {c : Sg.Cat} (t : sg.CTrm c) :
    (M.sigTm sg t ≫ F.cell c) ⟶ ((M.u sg ≫ F.prod0 sg) ≫ N.tm sg t) :=
  eqToHom (F.sig_tgt_eq sg t) ≫ (M.u sg ◁ F.etaTm sg t) ≫
    eqToHom (F.sig_src_eq sg t).symm

/-- `Ψ_t` is invertible when the comparison 2-cell `η_t` is. -/
instance psi_isIso {c : Sg.Cat} (t : sg.CTrm c) [IsIso (F.etaTm sg t)] :
    IsIso (F.Psi sg t) := by
  rw [Psi]; infer_instance

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

variable (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fndom f)))

/-- The 2-cell `(η_{t₂} u_M)_f • (∏_f F_c φ_M) • (η_{t₁}⁻¹ u_M)_f` used to induce the oplax
`F^σ` from the inserter `N^σ`. -/
def sigStr : ((M.u sg ≫ F.prod0 sg) ≫ N.domCell sg) ⟶
    ((M.u sg ≫ F.prod0 sg) ≫ N.codCell sg) :=
  (N.Pfn sg).lift₂ (fun f =>
    haveI : IsIso (F.etaTm sg (sg.fndom f)) := hiso f
    eqToHom (F.sigStr_dom_eq sg f) ≫
      inv (F.Psi sg (sg.fndom f)) ≫
      (M.arrCell sg (OneSig.Arr.fn f) ▷ F.cell (sg.fnty f)) ≫
      F.Psi sg (sg.fncod f) ≫
      eqToHom (F.sigStr_cod_eq sg f).symm)

/-- The 1-cell `F^σ : M^σ → N^σ` induced by an oplax morphism whose comparison 2-cells are
invertible at the function arity terms (oplax form of Lemma 3.21 (1)). -/
def sigMor : M.sigObj sg ⟶ N.sigObj sg :=
  (N.sigIns sg).lift (M.u sg ≫ F.prod0 sg) (F.sigStr sg hiso)

end

end

end OplaxMor

end UlmerBialgebras
