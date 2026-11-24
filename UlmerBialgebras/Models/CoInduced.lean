module

public import UlmerBialgebras.Models.OplaxInduced
public import UlmerBialgebras.Models.CoMor
public import UlmerBialgebras.Models.CoHom
public import UlmerBialgebras.Models.CoBialgebra

/-!
# The oplax `F^σ` is the lax `F^σ` in `K^co`

An oplax morphism `F : M → N` in `K` is the lax morphism `F.toLax : M^co → N^co` in `K^co`
(`UlmerBialgebras.OplaxMor.toLax`). Its lax `F^σ` in `K^co`, read as a 1-cell of `K`, is the oplax
`F^σ` of `UlmerBialgebras.OplaxMor.sigMor`: the comparison 2-cells `η_t` agree
(`UlmerBialgebras.OplaxData.toLax_eta`), the inserters agree, and the order of composition of
2-cells is reversed, which exchanges `η_{t₁}⁻¹ ∘ ⋯ ∘ η_{t₂}` and `η_{t₂} ∘ ⋯ ∘ η_{t₁}⁻¹`.

## Main results

* `UlmerBialgebras.OplaxMor.toLax_sigMor`: the lax `F^σ` of `F.toLax` in `K^co` is the oplax `F^σ`
  of `F` (as a heterogeneous equality).
* `UlmerBialgebras.OplaxMor.exists_thyMor_of_co`: a 1-cell `(M^co)^{T^co} → (N^co)^{T^co}` over the
  lax `F^σ` in `K^co` gives a 1-cell `F^T : M^T → N^T` with `F^T e_N = e_M F^σ` (Theorem 3.22).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 3.21 and Theorem 3.22
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Co

/-- The inverse of a 2-cell of `K^co` is its inverse in `K`: if `α` reads in `K` as the
invertible `β`, then `α⁻¹` reads as `β⁻¹`. The instance of `α` is found by unification. -/
lemma inv_eq_of_uncell_eq {a b : Obj} {f g : a ⟶ b} {α : hom f ⟶ hom g} {_ : IsIso α}
    {β : g ⟶ f} [IsIso β] (h : uncell α = β) : inv α = cell (inv β) := by
  subst h
  apply IsIso.inv_eq_of_hom_inv_id
  rw [comp_eq]
  exact IsIso.inv_hom_id (uncell α)

end Co

variable [HasChosenFinProducts.{u, v, w} Obj] {Sg : TwoSig.{u₁, u₂, u₃}}

namespace OplaxMor

variable {M N : Model Sg Obj} (F : OplaxMor M N) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- The comparison 2-cells of `F.toLax` are those of `F`. -/
lemma toLax_etaTm {c : Sg.Cat} (t : sg.CTrm c) :
    Co.uncell (F.toLax.etaTm sg.co t) =
      eqToHom (congrArg (· ≫ F.cell c) (M.tm_co sg t)) ≫ F.etaTm sg t ≫
        eqToHom (N.co_interp (x := Co.op (M.P0 sg).pt)
          (fun s => (M.P0 sg).π s ≫ F.toLax.cell (sg.sty s)) t).symm :=
  F.toOplaxData.toLax_eta (M.P0 sg).π t

/-- If `η_t` is invertible at the function arity terms of `σ`, the comparison 2-cells of
`F.toLax` are invertible at the function coarity terms of `σ^co`. -/
lemma toLax_hiso (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fndom f))) :
    ∀ f : sg.co.Fn, IsIso (F.toLax.etaTm sg.co (sg.co.fncod f)) := fun f => by
  have : IsIso (F.etaTm sg (sg.fndom f)) := hiso f
  have : IsIso (F.etaTm sg (sg.co.fncod f)) := hiso f
  -- The coarity terms of `σ^co` are the arity terms of `σ`.
  have h : IsIso (Co.uncell (F.toLax.etaTm sg.co (sg.fndom f))) := by
    rw [F.toLax_etaTm sg (sg.fndom f)]
    infer_instance
  exact (Co.isIso_cell_iff (Co.uncell (F.toLax.etaTm sg.co (sg.co.fncod f)))).2 h

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]

/-- A closed term evaluated on `(M^co)^{σ^co}`, then `F_c`, is `M^σ(t) ≫ F_c` along
`(M^co)^{σ^co} = M^σ`. -/
private lemma sigTm_co_comp_cell {c : Sg.Cat} (t : sg.CTrm c) :
    (show Co.unop (M.co.sigObj sg.co) ⟶ N.obj c from M.co.sigTm sg.co t ≫ F.toLax.cell c) =
      eqToHom (M.sigObj_co sg) ≫ M.sigTm sg t ≫ F.cell c := by
  have hsig := M.sigTm_co sg t
  dsimp only at hsig
  exact (congrArg (· ≫ F.cell c) hsig).trans (Bicategory.Strict.assoc _ _ _)

/-- The 2-cells `Ψ_t` of `F.toLax` agree with `F.Psi` up to `M.sigObj_co`. -/
private lemma toLax_Psi_eq {c : Sg.Cat} (t : sg.CTrm c) :
    Co.uncell (F.toLax.Psi sg.co t) =
      eqToHom (F.sigTm_co_comp_cell sg t) ≫
        Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg)) (F.Psi sg t) ≫
        eqToHom (by
          rw [M.u_co sg, N.tm_co sg t]
          simp only [← Bicategory.Strict.assoc]
          rfl) := by
  dsimp only [Co.uncell]
  simp only [LaxMor.Psi, OplaxMor.Psi, Co.comp_eq, Co.eqToHom_eq, Co.whiskerLeft_eq,
    Category.assoc]
  have heta := F.toLax_etaTm sg t
  dsimp only [Co.uncell] at heta
  have hwl_eq : ∀ {a b d : Obj} {u₁ u₂ : a ⟶ b} (hu : u₁ = u₂) {k l : b ⟶ d} (η : k ⟶ l),
      Bicategory.whiskerLeft u₁ η =
        eqToHom (by rw [hu]) ≫ Bicategory.whiskerLeft u₂ η ≫ eqToHom (by rw [hu]) := by
    intro _ _ _ _ _ hu _ _ η; subst hu; simp
  have hwl : ∀ {a a' b d : Obj} (h : a = a') (u : a' ⟶ b) {k l : b ⟶ d} (η : k ⟶ l),
      Bicategory.whiskerLeft (eqToHom h ≫ u) η =
        eqToHom (by subst h; exact Bicategory.Strict.assoc _ _ _) ≫
          Bicategory.whiskerLeft (eqToHom h) (Bicategory.whiskerLeft u η) ≫
          eqToHom (by subst h; exact (Bicategory.Strict.assoc _ _ _).symm) := by
    intro _ _ _ _ h u _ _ η; subst h
    rw [Bicategory.Strict.comp_whiskerLeft]
  rw [heta]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [hwl_eq (M.u_co sg) (F.etaTm sg t), hwl (M.sigObj_co sg) (M.u sg)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- The 2-cells `Ψ_t` of `F.toLax` are those of `F`. -/
lemma toLax_Psi {c : Sg.Cat} (t : sg.CTrm c) :
    HEq (Co.uncell (F.toLax.Psi sg.co t)) (F.Psi sg t) :=
  Co.cell_heq_of_eqToHom_whiskerLeft (M.sigObj_co sg)
    (F.sigTm_co_comp_cell sg t)
    (by
      rw [M.u_co sg, N.tm_co sg t]
      simp only [← Bicategory.Strict.assoc]
      rfl)
    (F.toLax_Psi_eq sg t)

/-- The inverse of `Ψ_{t₁}` for `F.toLax` agrees with `inv (F.Psi sg t)` up to `M.sigObj_co`. -/
private lemma toLax_Psi_inv_eq {c : Sg.Cat} (t : sg.CTrm c)
    [IsIso (F.etaTm sg t)] [IsIso (F.toLax.Psi sg.co t)] :
    Co.uncell (inv (F.toLax.Psi sg.co t)) =
      eqToHom (by
        rw [M.u_co sg, N.tm_co sg t]
        simp only [← Bicategory.Strict.assoc]
        rfl) ≫
        Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg)) (inv (F.Psi sg t)) ≫
        eqToHom (F.sigTm_co_comp_cell sg t).symm := by
  have h1 := F.toLax_Psi_eq sg t
  have h1inv : inv (F.toLax.Psi sg.co t) = _ := Co.inv_eq_of_uncell_eq h1
  rw [h1inv]
  dsimp only [Co.uncell]
  apply IsIso.inv_eq_of_hom_inv_id
  have hcomp : Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg)) (F.Psi sg t) ≫
      Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg)) (inv (F.Psi sg t)) = 𝟙 _ := by
    rw [← Bicategory.whiskerLeft_comp, IsIso.hom_inv_id, Bicategory.whiskerLeft_id]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc _ (Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg))
    (inv (F.Psi sg t))), hcomp, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- The structure 2-cell inducing the lax `F^σ` of `F.toLax` is the one inducing the oplax
`F^σ` of `F`. -/
lemma toLax_sigStr (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fndom f))) :
    HEq (Co.uncell (F.toLax.sigStr sg.co (F.toLax_hiso sg hiso))) (F.sigStr sg hiso) := by
  -- Both cells are lifts into `∏_f N_{c_f}`; compare them at each projection `f`, where both are
  -- built from `η_{dom f}`, `ψ_{cod f}⁻¹` and the arrow of `f`, transported along `K^co`.
  refine Co.cell_heq_of_eqToHom_whiskerLeft (M.sigObj_co sg)
    (by
      rw [M.u_co sg, N.codCell_co sg]
      simp only [← Bicategory.Strict.assoc]
      rfl)
    (by
      rw [M.u_co sg, N.domCell_co sg]
      simp only [← Bicategory.Strict.assoc]
      rfl) ?_
  dsimp only [Co.uncell]
  simp only [LaxMor.sigStr, OplaxMor.sigStr]
  change (N.Pfn sg).lift₂ _ = _
  refine (N.Pfn sg).cell_ext (fun f => ?_)
  rw [(N.Pfn sg).lift₂_π]
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  rw [Bicategory.Strict.whisker_assoc', (N.Pfn sg).lift₂_π]
  simp only [Co.comp_eq, Co.eqToHom_eq, Co.whiskerRight_eq, Category.assoc]
  have : IsIso (F.etaTm sg (sg.fndom f)) := hiso f
  have : IsIso (F.etaTm sg (sg.co.fncod f)) := hiso f
  have : IsIso (F.toLax.etaTm sg.co (sg.co.fncod f)) := F.toLax_hiso sg hiso f
  have : IsIso (F.toLax.Psi sg.co (sg.co.fncod f)) := LaxMor.psi_isIso F.toLax sg.co (sg.co.fncod f)
  have h1inv' : Co.uncell (inv (F.toLax.Psi sg.co (sg.co.fncod f))) = _ :=
    F.toLax_Psi_inv_eq sg (sg.co.fncod f)
  have h2 := F.toLax_Psi_eq sg (sg.fncod f)
  have harr : Co.uncell (M.co.arrCell sg.co (OneSig.Arr.fn (sg := sg.co) f)) =
      eqToHom (by
        have hsig := M.sigTm_co sg (sg.fndom f)
        dsimp only at hsig
        exact hsig) ≫
        Bicategory.whiskerLeft (eqToHom (M.sigObj_co sg)) (M.arrCell sg (OneSig.Arr.fn f)) ≫
        eqToHom (by
          have hsig := M.sigTm_co sg (sg.fncod f)
          dsimp only at hsig
          exact hsig.symm) :=
    M.arrCell_co sg (OneSig.Arr.fn (sg := sg) f)
  dsimp only [Co.uncell] at h1inv' h2 harr
  have h2' : F.toLax.Psi sg.co (sg.co.fndom f) = _ := h2
  rw [h1inv', harr, h2']
  simp only [Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight,
    Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc]
  rw [Bicategory.Strict.whisker_assoc]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  repeat congr 2

/-- **Duality for `F^σ`**: the lax `F^σ` of `F.toLax` in `K^co` is the oplax `F^σ` of `F`, along
`(M^co)^{σ^co} = M^σ` and `(N^co)^{σ^co} = N^σ` (`UlmerBialgebras.Model.sigObj_co`). -/
lemma toLax_sigMor (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fndom f))) :
    HEq (F.toLax.sigMor sg.co (F.toLax_hiso sg hiso)) (F.sigMor sg hiso) := by
  have key : ∀ (d c : (N.P0 sg).pt ⟶ (N.Pfn sg).pt)
      (hd : d = N.domCell sg) (hc : c = N.codCell sg)
      (x : Obj) (hx : x = M.sigObj sg)
      (k : x ⟶ (N.P0 sg).pt) (hk : HEq k (M.u sg ≫ F.prod0 sg))
      (w : k ≫ d ⟶ k ≫ c) (hw : HEq w (F.sigStr sg hiso)),
      HEq ((HasChosenInserters.ins (Obj := Obj) d c).lift k w)
        ((N.sigIns sg).lift (M.u sg ≫ F.prod0 sg) (F.sigStr sg hiso)) := by
    intro d c hd hc x hx k hk w hw
    subst hd hc hx hk hw
    rfl
  exact key _ _ (N.codCell_co sg) (N.domCell_co sg) _ (M.sigObj_co sg)
    (M.co.u sg.co ≫ F.toLax.prod0 sg.co)
    (Co.hom_heq_of_eqToHom_comp (M.sigObj_co sg)
      (by rw [M.u_co sg]; exact Bicategory.Strict.assoc _ _ _))
    (Co.uncell (F.toLax.sigStr sg.co (F.toLax_hiso sg hiso)))
    (F.toLax_sigStr sg hiso)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- A 1-cell `G : (M^co)^{T^co} → (N^co)^{T^co}` of `K^co` with `e G = F^σ e` for the lax `F^σ` of
`F.toLax` gives a 1-cell `M^T → N^T` of `K` with `e_N F^T = F^σ e_M` for the oplax `F^σ` of `F`. -/
lemma exists_thyMor_of_co (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
    (hiso : ∀ f : sg.Fn, IsIso (F.etaTm sg (sg.fndom f)))
    (G : M.co.thyObj sg.co T.co ⟶ N.co.thyObj sg.co T.co)
    (hG : G ≫ N.co.e sg.co T.co =
      M.co.e sg.co T.co ≫ F.toLax.sigMor sg.co (F.toLax_hiso sg hiso)) :
    ∃ G' : M.thyObj sg T ⟶ N.thyObj sg T, G' ≫ N.e sg T = M.e sg T ≫ F.sigMor sg hiso := by
  exact exists_comm_of_heq (Obj := Obj) (M.thyObj_co sg T) (N.thyObj_co sg T)
    (M.sigObj_co sg) (N.sigObj_co sg) G (M.e_co_heq sg T) (N.e_co_heq sg T)
    (F.toLax_sigMor sg hiso) hG

end OplaxMor

end UlmerBialgebras
