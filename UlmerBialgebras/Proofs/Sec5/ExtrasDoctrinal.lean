module

public import UlmerBialgebras.Proofs.Sec5.Doctrinal
public import UlmerBialgebras.Paper.Sec3DefsTwoFun
public import UlmerBialgebras.Proofs.Sec3.TwoFunctorOplaxModel
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Solution: doctrinal adjunction for Σ-models

The ingredient behind the proof of Theorem 7.4 of [forsman2026syntactic], stated for Σ-models of
any 2-signature. Let `M, N` be Σ-models in a PIE-complete strict 2-category `K`, `G : M → N` a lax
morphism (Definition 3.10) and `F_c ⊣ G_c` adjunctions in `K` for the category symbols `c`.

* `mate_oplaxMor`: the mates of the structure 2-cells of `G` (`Doctrinal.mateStr`) make the `F_c`
  an **oplax** morphism `N → M`, compatible with every transformation symbol.
* `laxMor_iff_oplaxMor_mate`, `mateStr_bijective`: conversely, for fixed cells `F_c ⊣ G_c`, the
  mate is a bijection between structure 2-cells, and lax structures on the `G_c` correspond to
  oplax structures on the `F_c`.
* `idData_laxMor`: the identity data is a lax morphism (Proposition 3.11).
* `doctrinal_adjunction`: if every mate is invertible, the `F_c` with the inverse mates form a lax
  morphism `F : N → M`, and the units and counits of the `F_c ⊣ G_c` are 2-cells of lax
  morphisms `1 ⇒ G ∘ F` and `F ∘ G ⇒ 1` (`LaxTwoCell`). The triangle laws hold componentwise, so
  `F ⊣ G` is an adjunction in the 2-category of Σ-models and lax morphisms.
* `doctrinal_adjunction_strong`: if `G` is strong too, both 1-cells are strong, so the adjunction
  lives in the 2-category of strong morphisms (the case of Theorem 7.4, where `g_*` is strict).
* `laxNat_mate_oplaxNat`: the case of lax natural transformations (Example 3.12; Houston's
  Proposition 2.35): the mates of the naturality 2-cells of a lax transformation whose components
  have left adjoints form an oplax transformation.

**`G` need not be strong when `F` is.** For `Σ_Mon`, the free abelian group functor
`(Set, ×, 1) → (Ab, ⊗, ℤ)` is strong monoidal, but its right adjoint, the forgetful functor, is
only lax: `ℤ/2 × ℤ/2 → ℤ/2 ⊗ ℤ/2 = ℤ/2` is not injective. So `doctrinal_adjunction` does not make
`G` strong.

## Main results

* `UlmerBialgebras.Paper.mate_oplaxMor`
* `UlmerBialgebras.Paper.laxMor_iff_oplaxMor_mate`
* `UlmerBialgebras.Paper.mateStr_bijective`
* `UlmerBialgebras.Paper.idData_laxMor`
* `UlmerBialgebras.Paper.doctrinal_adjunction`
* `UlmerBialgebras.Paper.doctrinal_adjunction_strong`
* `UlmerBialgebras.Paper.laxNat_mate_oplaxNat`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11, Example 3.12, Theorem 7.4
* [R. Houston, *Linear logic without units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory Doctrinal

section SigmaModels

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj] {Sg : TwoSig}
  {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}

/-- **Mates of a lax morphism form an oplax morphism** (addition beyond
[forsman2026syntactic]): for a lax morphism `G : M → N` of Σ-models and adjunctions
`F_c ⊣ G_c`, the cells `F_c` with the mates of the structure 2-cells of `G` are an oplax morphism
`N → M`. -/
theorem mate_oplaxMor (G : LaxMor M N) (A : ∀ c, TwoAdj (Fc c) (G.cell c)) :
    ∃ F : OplaxMor N M, F.toOplaxData = mateOplaxData G.toLaxData A :=
  ⟨⟨mateOplaxData G.toLaxData A, fun a => (tr_compat_iff G.toLaxData A a).1 (G.tr_compat a)⟩,
    rfl⟩

/-- **Lax structures are oplax structures on the left adjoints** (addition beyond
[forsman2026syntactic]): lax data `G : M → N` with adjunctions `F_c ⊣ G_c` is a lax morphism iff
its mates form an oplax morphism `N → M`. -/
theorem laxMor_iff_oplaxMor_mate (G : LaxData M.toPreModel N.toPreModel)
    (A : ∀ c, TwoAdj (Fc c) (G.cell c)) :
    (∃ G' : LaxMor M N, G'.toLaxData = G) ↔
      ∃ F : OplaxMor N M, F.toOplaxData = mateOplaxData G A := by
  constructor
  · rintro ⟨G', rfl⟩
    exact mate_oplaxMor G' A
  · rintro ⟨F, hF⟩
    refine ⟨⟨G, fun a => (tr_compat_iff G A a).2 ?_⟩, rfl⟩
    have := F.tr_compat a
    rw [hF] at this
    exact this

/-- **The mate correspondence** (addition beyond [forsman2026syntactic]): for adjunctions
`F_c ⊣ G_c`, taking mates is a bijection from the lax structure 2-cells
`G_c̄ ≫ N(B) ⇒ M(B) ≫ G_d` to the oplax ones `N(B) ≫ F_d ⇒ F_c̄ ≫ M(B)`. -/
theorem mateStr_bijective {Gc : ∀ c, M.obj c ⟶ N.obj c} (A : ∀ c, TwoAdj (Fc c) (Gc c))
    (B : Sg.Fun) :
    Function.Bijective (mateStr A B :
      (prodR Gc B ≫ N.fn B ⟶ M.fn B ≫ Gc (Sg.fcod B)) →
        (N.fn B ≫ Fc (Sg.fcod B) ⟶ prodL Fc B ≫ M.fn B)) := by
  rw [show (mateStr A B : (prodR Gc B ≫ N.fn B ⟶ M.fn B ≫ Gc (Sg.fcod B)) → _) =
    (Bicategory.mateEquiv (prodAdj A B) (A (Sg.fcod B))).symm from funext (mateStr_eq A B)]
  exact Equiv.bijective _

/-- **Identity lax morphisms** (Proposition 3.11 of [forsman2026syntactic]): the identity data
of a Σ-model is a lax morphism. -/
theorem idData_laxMor (M : Model Sg Obj) :
    ∃ I : LaxMor M M, I.toLaxData = LaxData.idData M.toPreModel :=
  ⟨⟨LaxData.idData M.toPreModel, idData_tr_compat M⟩, rfl⟩

/-- **Doctrinal adjunction** (addition beyond [forsman2026syntactic]; Kelly): for a lax
morphism `G : M → N` and adjunctions `F_c ⊣ G_c` whose mates are invertible, the `F_c` with the
inverse mates form a lax morphism `F : N → M`, and the units and counits of the `F_c ⊣ G_c` are
2-cells of lax morphisms `1_N ⇒ F ≫ G` and `G ≫ F ⇒ 1_M`. Their triangle laws are those of the
`F_c ⊣ G_c`, so `F ⊣ G` in the 2-category of Σ-models and lax morphisms. -/
theorem doctrinal_adjunction (G : LaxMor M N) (A : ∀ c, TwoAdj (Fc c) (G.cell c))
    [∀ B, IsIso ((mateOplaxData G.toLaxData A).str B)] :
    ∃ F : LaxMor N M, F.toLaxData = invLaxData (mateOplaxData G.toLaxData A) ∧
      ∃ (η : LaxTwoCell (LaxData.idData N.toPreModel)
          (LaxData.comp (invLaxData (mateOplaxData G.toLaxData A)) G.toLaxData))
        (ε : LaxTwoCell (LaxData.comp G.toLaxData (invLaxData (mateOplaxData G.toLaxData A)))
          (LaxData.idData M.toPreModel)),
        (∀ c, η.app c = (A c).unit') ∧ (∀ c, ε.app c = (A c).counit') :=
  ⟨⟨invLaxData (mateOplaxData G.toLaxData A),
      invLaxData_tr_compat (M := N) (N := M) ⟨mateOplaxData G.toLaxData A,
        fun a => (tr_compat_iff G.toLaxData A a).1 (G.tr_compat a)⟩⟩, rfl,
    ⟨fun c => (A c).unit', unit_str_compat G.toLaxData A⟩,
    ⟨fun c => (A c).counit', counit_str_compat G.toLaxData A⟩, fun _ => rfl, fun _ => rfl⟩

/-- **Doctrinal adjunction for strong morphisms** (addition beyond
[forsman2026syntactic]): if moreover `G` is strong, then so is `F`, and the adjunction of
`doctrinal_adjunction` lives in the 2-category of Σ-models and strong morphisms. -/
theorem doctrinal_adjunction_strong (G : LaxMor M N) (hG : ∀ B, IsIso (G.str B))
    (A : ∀ c, TwoAdj (Fc c) (G.cell c)) [∀ B, IsIso ((mateOplaxData G.toLaxData A).str B)] :
    ∃ F : LaxMor N M, F.toLaxData = invLaxData (mateOplaxData G.toLaxData A) ∧
      (∀ B, IsIso (F.str B)) ∧
      ∃ (η : LaxTwoCell (LaxData.idData N.toPreModel)
          (LaxData.comp (invLaxData (mateOplaxData G.toLaxData A)) G.toLaxData))
        (ε : LaxTwoCell (LaxData.comp G.toLaxData (invLaxData (mateOplaxData G.toLaxData A)))
          (LaxData.idData M.toPreModel)),
        (∀ c, η.app c = (A c).unit') ∧ (∀ c, ε.app c = (A c).counit') := by
  have _ := hG
  obtain ⟨⟨D, hD⟩, rfl, η, ε, h₁, h₂⟩ := doctrinal_adjunction G A
  exact ⟨⟨_, hD⟩, rfl, fun B => IsIso.inv_isIso (f := (mateOplaxData G.toLaxData A).str B), η, ε,
    h₁, h₂⟩

end SigmaModels

section LaxNat

open TwoFun
open scoped CategoryTheory.Bicategory

variable {A : Type ua} [Bicategory.{wa, va} A] [Bicategory.Strict A]
variable {K : Type u} [Bicategory.{w, v} K]

/-- Invertibility transfers along a heterogeneous equality of 2-cells whose endpoints are equal. -/
lemma isIso_of_heq {X Y : K} {f g f' g' : X ⟶ Y} {x : f ⟶ g} {y : f' ⟶ g'}
    (hf : f = f') (hg : g = g') (h : HEq x y) (hy : IsIso y) : IsIso x := by
  subst hf hg; obtain rfl := eq_of_heq h; infer_instance

/-- Inverses of heterogeneously equal invertible 2-cells with equal endpoints are heterogeneously
equal. -/
lemma inv_heq_inv {X Y : K} {f g f' g' : X ⟶ Y} {x : f ⟶ g} {y : f' ⟶ g'}
    (hf : f = f') (hg : g = g') (h : HEq x y) (hx : IsIso x) (hy : IsIso y) :
    HEq (inv x) (inv y) := by
  subst hf hg; obtain rfl := eq_of_heq h; rfl

variable [Bicategory.Strict K]

/-- The oplax transformation `G ⇒ F` of mates of a lax transformation `σ : F ⇒ G` along
adjunctions `l_a ⊣ σ_a` (Houston, Proposition 2.35). -/
def laxNatMate {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) : OplaxNat G F where
  app := l
  nat {a b} f := (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)
  nat_cell {a b f g} η := by
    have := congr((Bicategory.mateEquiv (adj a) (adj b)).symm $(σ.nat_cell η))
    rw [Bicategory.mateEquiv_symm_comp_left, Bicategory.mateEquiv_symm_comp_right] at this
    exact this
  nat_comp {a b c} f g := by
    apply eq_of_heq
    have hβ : HEq (σ.nat (f ≫ g))
        (Bicategory.rightAdjointSquare.vcomp (σ.nat f) (σ.nat g)) := by
      rw [σ.nat_comp]
      simp only [Bicategory.rightAdjointSquare.vcomp, AsBicat.associator_hom,
        AsBicat.associator_inv, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
      refine heq_comp rfl rfl ?_ HEq.rfl ?_
      · simp [F.map_comp]
      refine heq_comp rfl rfl ?_ (heq_eqToHom_eqToHom _ _ rfl) ?_
      · simp [F.map_comp]
      exact heq_comp rfl rfl (by simp [F.map_comp]) HEq.rfl
        (heq_eqToHom_eqToHom _ _ rfl)
    have hm := Bicategory.mateEquiv_symm_heq (adj a) (adj c) (G.map_comp f g) (F.map_comp f g) hβ
    rw [Bicategory.mateEquiv_symm_vcomp (adj a) (adj b) (adj c)] at hm
    refine hm.trans ?_
    simp only [Bicategory.leftAdjointSquare.vcomp, AsBicat.associator_hom,
      AsBicat.associator_inv, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
    refine heq_comp rfl rfl ?_ HEq.rfl ?_
    · simp [F.map_comp]
    refine heq_comp rfl rfl ?_ (heq_eqToHom_eqToHom _ _ rfl) ?_
    · simp [F.map_comp]
    exact heq_comp rfl rfl (by simp [F.map_comp]) HEq.rfl
      (heq_eqToHom_eqToHom _ _ rfl)
  nat_id a := by
    apply eq_of_heq
    have hβ : HEq (σ.nat (𝟙 a)) ((ρ_ (σ.app a)).hom ≫ (λ_ (σ.app a)).inv) := by
      rw [σ.nat_id]
      simp only [AsBicat.rightUnitor_hom, AsBicat.leftUnitor_inv, eqToHom_trans]
      exact heq_eqToHom_eqToHom _ _ (by rw [G.map_id])
    have hm := Bicategory.mateEquiv_symm_heq (adj a) (adj a) (G.map_id a) (F.map_id a) hβ
    have e : (Bicategory.mateEquiv (adj a) (adj a)).symm
        ((ρ_ (σ.app a)).hom ≫ (λ_ (σ.app a)).inv) = (λ_ (l a)).hom ≫ (ρ_ (l a)).inv :=
      (Equiv.symm_apply_eq _).2 (Bicategory.mateEquiv_leftUnitor_hom_rightUnitor_inv _).symm
    rw [e] at hm
    refine hm.trans ?_
    simp only [AsBicat.leftUnitor_hom, AsBicat.rightUnitor_inv, eqToHom_trans]
    exact heq_eqToHom_eqToHom _ _ (by rw [G.map_id])

/-- **Mates of a lax transformation** (Houston, Proposition 2.35; the case of `Σ_A`-models of
Example 3.12 of [forsman2026syntactic]): for a lax natural transformation `σ : F ⇒ G` between
strict 2-functors `A → K` and adjunctions `l_a ⊣ σ_a`, the `l_a` with the mates
`G f ≫ l_b ⇒ l_a ≫ F f` of the naturality 2-cells `σ_a ≫ G f ⇒ F f ≫ σ_b` (Mathlib's
`Bicategory.mateEquiv`) form an oplax natural transformation `G ⇒ F`. -/
theorem laxNat_mate_oplaxNat {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) :
    ∃ τ : OplaxNat G F, (∀ a, τ.app a = l a) ∧
      ∀ {a b : A} (f : a ⟶ b),
        HEq (τ.nat f) ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) :=
  ⟨laxNatMate σ l adj, fun _ => rfl, fun _ => HEq.rfl⟩

/-- A lax transformation `G ⇒ F` with the inverse naturality 2-cells of an oplax transformation
whose naturality 2-cells are invertible. -/
noncomputable def TwoFun.OplaxNat.invLax {F G : StrictTwoFunctor K A} (τ : OplaxNat G F)
    [hτ : ∀ {a b : A} (f : a ⟶ b), IsIso (τ.nat f)] : LaxNat G F where
  app := τ.app
  nat f := inv (τ.nat f)
  nat_cell {a b f g} η := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact (τ.nat_cell η).symm
  nat_comp {a b c} f g := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [τ.nat_comp]
    simp [← Bicategory.whiskerLeft_comp_assoc, ← Bicategory.comp_whiskerRight_assoc]
  nat_id a := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [τ.nat_id]
    simp

variable [HasChosenFinProducts.{u, v, w} K]

/-- The mate of a structure 2-cell of `M_σ` along the unary product adjunction is the whiskered
mate of the naturality 2-cell. -/
lemma mateStr_sigOf {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) {a b : A} (f : a ⟶ b)
    (s : prodR (M := F.model.toPreModel) (N := G.model.toPreModel) σ.app (⟨a, b, f⟩ : SigFun A) ≫
        G.model.fn (⟨a, b, f⟩ : SigFun A) ⟶ F.model.fn (⟨a, b, f⟩ : SigFun A) ≫ σ.app b)
    (hs : HEq s ((F.model.P (⟨a, b, f⟩ : SigFun A)).π 0 ◁ σ.nat f)) :
    HEq (mateStr (M := F.model.toPreModel) (N := G.model.toPreModel) adj
        (⟨a, b, f⟩ : SigFun A) s)
      ((G.model.P (⟨a, b, f⟩ : SigFun A)).π 0 ◁
        (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) := by
  rw [mateStr_eq]
  have hv : HEq s (Bicategory.rightAdjointSquare.vcomp
      (eqToHom ((G.model.P (⟨a, b, f⟩ : SigFun A)).lift_π
        (fun i => (F.model.P (⟨a, b, f⟩ : SigFun A)).π i ≫ σ.app a) 0)) (σ.nat f)) := by
    refine hs.trans ?_
    simp [Bicategory.rightAdjointSquare.vcomp]
  have hm := Bicategory.mateEquiv_symm_heq (prodAdj (M := F.model.toPreModel)
    (N := G.model.toPreModel) adj (⟨a, b, f⟩ : SigFun A)) (adj b) rfl rfl hv
  rw [Bicategory.mateEquiv_symm_vcomp (prodAdj (M := F.model.toPreModel)
    (N := G.model.toPreModel) adj (⟨a, b, f⟩ : SigFun A)) (adj a) (adj b), prodAdj_eq,
    mate_proj] at hm
  refine hm.trans ?_
  simp [Bicategory.leftAdjointSquare.vcomp]

/-- Extensionality for `LaxData`: equal cells and heterogeneously equal structure 2-cells. -/
lemma laxData_ext' {Sg : TwoSig} {M N : PreModel Sg K} {L L' : LaxData M N}
    (hc : L.cell = L'.cell) (hs : ∀ B, HEq (L.str B) (L'.str B)) : L = L' := by
  obtain ⟨c, s⟩ := L
  obtain ⟨c', s'⟩ := L'
  dsimp only at hc hs
  subst hc
  have : s = s' := funext fun B => eq_of_heq (hs B)
  subst this
  rfl

/-- **Adjunctions of lax transformations** (Houston, Proposition 2.35, read through the
correspondence of Example 3.12 of [forsman2026syntactic]): let `σ : F ⇒ G` be a lax natural
transformation between strict 2-functors `A → K`, with adjunctions `l_a ⊣ σ_a` whose mates
`G f ≫ l_b ⇒ l_a ≫ F f` of the naturality 2-cells are invertible. Then the `l_a` with the inverse
mates form a lax natural transformation `τ : G ⇒ F`, and under the correspondences `e`, `e'` of
Example 3.12 (`ex_3_12_lax`) between lax transformations and lax morphisms of `Σ_A`-models, the
units and counits of the `l_a ⊣ σ_a` are 2-cells of lax morphisms `1 ⇒ e' τ ≫ e σ` and
`e σ ≫ e' τ ⇒ 1`, that is, modifications. So `τ ⊣ σ`. -/
theorem laxNat_adjunction {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a))
    [∀ {a b : A} (f : a ⟶ b), IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f))]
    (e : LaxNat F G ≃ LaxMor F.model G.model) (he : ∀ σ a, (e σ).cell a = σ.app a)
    (he' : ∀ σ {a b : A} (f : a ⟶ b), HEq ((e σ).str ⟨a, b, f⟩)
      ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.nat f))
    (e' : LaxNat G F ≃ LaxMor G.model F.model) (he₂ : ∀ τ a, (e' τ).cell a = τ.app a)
    (he₂' : ∀ τ {a b : A} (f : a ⟶ b), HEq ((e' τ).str ⟨a, b, f⟩)
      ((HasChosenFinProducts.finProd (fun _ : Fin 1 => G.obj a)).π 0 ◁ τ.nat f)) :
    ∃ τ : LaxNat G F, (∀ a, τ.app a = l a) ∧
      (∀ {a b : A} (f : a ⟶ b),
        HEq (τ.nat f) (inv ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)))) ∧
      ∃ (η : LaxTwoCell (LaxData.idData G.model.toPreModel)
          (LaxData.comp (e' τ).toLaxData (e σ).toLaxData))
        (ε : LaxTwoCell (LaxData.comp (e σ).toLaxData (e' τ).toLaxData)
          (LaxData.idData F.model.toPreModel)),
        (∀ a, HEq (η.app a) (adj a).unit') ∧ (∀ a, HEq (ε.app a) (adj a).counit') := by
  have : ∀ {a b : A} (f : a ⟶ b), IsIso ((laxNatMate σ l adj).nat f) := fun f =>
    inferInstanceAs (IsIso ((Bicategory.mateEquiv _ _).symm (σ.nat f)))
  -- `τ` is the inverse of the mate of `σ`; the given equivalences `e`, `e'` are `laxEquiv`, and
  -- the doctrinal adjunction for `laxEquiv F G σ` gives the unit and counit
  let τ := (laxNatMate σ l adj).invLax
  refine ⟨τ, fun _ => rfl, fun _ => HEq.rfl, ?_⟩
  have h1 : e σ = laxEquiv F G σ := LaxMor.ext' (funext (he σ)) (by
    rintro ⟨a, b, f⟩
    exact (he' σ f).trans (σ.toLaxData_str f).heq.symm)
  have h2 : e' τ = laxEquiv G F τ := LaxMor.ext' (funext (he₂ τ)) (by
    rintro ⟨a, b, f⟩
    exact (he₂' τ f).trans (τ.toLaxData_str f).heq.symm)
  rw [h1, h2]
  -- the mate of `σ` has invertible structure cells
  have hiso : ∀ B, IsIso ((mateOplaxData (laxEquiv F G σ).toLaxData adj).str B) := by
    rintro ⟨a, b, f⟩
    have k := mateStr_sigOf σ l adj f _ (σ.toLaxData_str f).heq
    have hm : IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) := by
      infer_instance
    have : IsIso ((G.model.P ⟨a, b, f⟩).π 0 ◁
        (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) :=
      @Bicategory.whiskerLeft_isIso _ _ _ _ _ _ _ _ _ hm
    exact isIso_of_heq (Category.assoc _ _ _)
      (by simp only [Category.assoc, lift_π_assoc]; rfl) k this
  -- the doctrinal adjunction, and its left adjoint is `τ`
  obtain ⟨F', -, η₀, ε₀, hη, hε⟩ := doctrinal_adjunction (laxEquiv F G σ) adj
  have hL : (laxEquiv G F τ).toLaxData =
      invLaxData (mateOplaxData (laxEquiv F G σ).toLaxData adj) := by
    refine laxData_ext' rfl ?_
    rintro ⟨a, b, f⟩
    have k := mateStr_sigOf σ l adj f _ (σ.toLaxData_str f).heq
    have hm : IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) := by
      infer_instance
    have hw : IsIso ((G.model.P ⟨a, b, f⟩).π 0 ◁
        (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) :=
      @Bicategory.whiskerLeft_isIso _ _ _ _ _ _ _ _ _ hm
    refine (τ.toLaxData_str f).heq.trans ?_
    refine (heq_of_eq (@Bicategory.inv_whiskerLeft _ _ _ _ _ _ _ _ _ hm).symm).trans ?_
    exact inv_heq_inv (Category.assoc _ _ _).symm
      (by simp only [Category.assoc, lift_π_assoc]) k.symm hw (hiso _)
  rw [hL]
  exact ⟨η₀, ε₀, fun a => heq_of_eq (hη a), fun a => heq_of_eq (hε a)⟩


end LaxNat

end UlmerBialgebras.Paper
