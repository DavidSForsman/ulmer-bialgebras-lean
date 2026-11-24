module

public import UlmerBialgebras.Paper.Sec3DefsPsFun
public import UlmerBialgebras.Proofs.Sec5.ExtrasDoctrinal
public import UlmerBialgebras.Proofs.Sec3.PsFunModel
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Doctrinal adjunction for transformations between pseudofunctors

Proofs of the results of `Companion/Statements/ExtrasDoctrinalBicat.lean`, by transport through the
correspondence of Example 3.12 (`PsFun.laxEquiv`, `PsFun.oplaxEquiv`, `PsFun.laxModifEquiv`) from
doctrinal adjunction for `Σ_A`-models (`mate_oplaxMor`, `doctrinal_adjunction`). The vertical
composite and the identity of lax transformations correspond to the composite and the identity of
lax morphisms of models (`PsFun.toLaxData_vComp`, `PsFun.toLaxData_id`).

## Main results

* `UlmerBialgebras.Paper.laxTrans_mate_oplaxTrans`
* `UlmerBialgebras.Paper.laxTrans_adjunction`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.12, Theorem 7.4
* [R. Houston, *Linear logic without units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory Doctrinal PsFun
open scoped CategoryTheory.Bicategory

variable {A : Type ua} [Bicategory.{wa, va} A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K]
  [HasChosenFinProducts.{u, v, w} K]

namespace PsFun

/-- A 2-cell of lax data transported along equalities of its source and target. -/
def laxTwoCellCast {Sg : TwoSig} {M N : PreModel Sg K} {L₁ L₁' L₂ L₂' : LaxData M N}
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (x : LaxTwoCell L₁' L₂') : LaxTwoCell L₁ L₂ := by
  subst h₁ h₂; exact x

/-- Casting a lax 2-cell along equalities of its endpoints does not change its components, up to
heterogeneous equality. -/
lemma laxTwoCellCast_app {Sg : TwoSig} {M N : PreModel Sg K} {L₁ L₁' L₂ L₂' : LaxData M N}
    (h₁ : L₁ = L₁') (h₂ : L₂ = L₂') (x : LaxTwoCell L₁' L₂') (c : Sg.Cat) :
    HEq ((laxTwoCellCast h₁ h₂ x).app c) (x.app c) := by
  subst h₁ h₂; rfl

/-- Composites `u ≫ v` and `u' ≫ eqToHom e ≫ v'` of `ConjEq` morphisms are `ConjEq`. -/
lemma _root_.UlmerBialgebras.ConjEq.comp_eqToHom_comp {C : Type*} [Category C]
    {X Y Z X₁ Y₁ Y₂ Z₁ : C} {u : X ⟶ Y} {v : Y ⟶ Z} {u' : X₁ ⟶ Y₁} {v' : Y₂ ⟶ Z₁}
    (hu : ConjEq u u') (hv : ConjEq v v') (e : Y₁ = Y₂) :
    ConjEq (u ≫ v) (u' ≫ eqToHom e ≫ v') := by
  obtain ⟨p, q, rfl⟩ := hu
  obtain ⟨p', q', rfl⟩ := hv
  subst p q q' e
  exact ⟨rfl, rfl, by simp⟩

/-- Composites `u ≫ eqToHom e ≫ v` and `u' ≫ eqToHom e' ≫ v'` of `ConjEq` morphisms are
`ConjEq`. -/
lemma _root_.UlmerBialgebras.ConjEq.comp_eqToHom_comp' {C : Type*} [Category C]
    {X Y Y' Z X₁ Y₁ Y₂ Z₁ : C} {u : X ⟶ Y} {v : Y' ⟶ Z} {u' : X₁ ⟶ Y₁} {v' : Y₂ ⟶ Z₁}
    (hu : ConjEq u u') (hv : ConjEq v v') (e : Y = Y') (e' : Y₁ = Y₂) :
    ConjEq (u ≫ eqToHom e ≫ v) (u' ≫ eqToHom e' ≫ v') := by
  subst e
  simpa using ConjEq.comp_eqToHom_comp hu hv e'

/-- Whiskering by the projection out of the unary product `∏_{Fin 1} F a` is injective. -/
lemma whiskerLeft_π_injective (F : Pseudofunctor A K) {a b : A} (f : a ⟶ b) {y : K}
    {u u' : F.obj a ⟶ y} {x x' : u ⟶ u'}
    (h : ((model F).P ⟨a, b, f⟩).π 0 ◁ x = ((model F).P ⟨a, b, f⟩).π 0 ◁ x') :
    x = x' :=
  whiskerLeft_cancel_of_section _ _ (lift_id_π F f) h

variable {F G : Pseudofunctor A K}

/-- The identity lax transformation is the identity lax morphism of models. -/
lemma toLaxData_id (F : Pseudofunctor A K) :
    toLaxData (Lax.LaxTrans.id F.toLax) = LaxData.idData (model F).toPreModel := by
  refine laxData_ext' rfl ?_
  rintro ⟨a, b, f⟩
  obtain ⟨e, he⟩ := (toLaxData_str (Lax.LaxTrans.id F.toLax) f).exists_eqToHom_iff.mpr
    ⟨by simp [Lax.LaxTrans.id], by simp [Lax.LaxTrans.id, Bicategory.Strict.leftUnitor_eqToIso,
      Bicategory.Strict.rightUnitor_eqToIso]⟩
  exact heq_of_eq (he.trans rfl)

/-- The vertical composite of lax transformations is the composite of their lax morphisms of
models. -/
lemma toLaxData_vComp {H : Pseudofunctor A K} (τ : Lax.LaxTrans F.toLax G.toLax)
    (σ : Lax.LaxTrans G.toLax H.toLax) :
    toLaxData (τ.vComp σ) = (toLaxData τ).comp (toLaxData σ) := by
  refine laxData_ext' rfl ?_
  rintro ⟨a, b, f⟩
  refine ConjEq.heq ?_
  refine (toLaxData_str (τ.vComp σ) f).trans ?_
  have h₁ := strAt_eq G H (toLaxData σ) f
    (fun i => ((model F).P ⟨a, b, f⟩).π i ≫ τ.app a) (((model F).P ⟨a, b, f⟩).π 0 ≫ τ.app a)
    rfl
  rw [natOf_toLaxData] at h₁
  have h₂ : ConjEq ((toLaxData τ).str ⟨a, b, f⟩ ▷ (toLaxData σ).cell ((sigOf A).fcod ⟨a, b, f⟩))
      ((((model F).P ⟨a, b, f⟩).π 0 ◁ τ.naturality f) ▷ σ.app b) :=
    (toLaxData_str τ f).whiskerRight (σ.app b)
  have e : (((model F).P ⟨a, b, f⟩).π 0 ≫ τ.app a) ≫ G.map f ≫ σ.app b =
      (((model F).P ⟨a, b, f⟩).π 0 ≫ τ.app a ≫ G.map f) ≫ σ.app b := by
    simp only [Category.assoc]
  have hc : ConjEq (((toLaxData τ).comp (toLaxData σ)).str ⟨a, b, f⟩) _ :=
    ConjEq.eqToHom_comp (ConjEq.comp_eqToHom_comp h₁ (h₂.comp_eqToHom _) e) _
  refine ConjEq.trans ?_ hc.symm
  simp only [Lax.LaxTrans.vComp, Lax.LaxTrans.vCompNaturality, Bicategory.Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  exact ConjEq.eqToHom_comp (ConjEq.comp_eqToHom_comp' (ConjEq.whiskerLeft_comp₁ _ _ _).symm
    (ConjEq.comp_eqToHom (ConjEq.whiskerLeft_whiskerRight _ _ _) _) _ e) _

end PsFun

/-- The mate of a structure 2-cell of `M_σ` along the unary product adjunction is the whiskered
mate of the naturality 2-cell. -/
lemma PsFun.mateStr_sigOf {F G : Pseudofunctor A K} (σ : Lax.LaxTrans F.toLax G.toLax)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) {a b : A} (f : a ⟶ b)
    (s : prodR (M := (model F).toPreModel) (N := (model G).toPreModel) σ.app
        (⟨a, b, f⟩ : SigFun A) ≫ (model G).fn (⟨a, b, f⟩ : SigFun A) ⟶
          (model F).fn (⟨a, b, f⟩ : SigFun A) ≫ σ.app b)
    (hs : HEq s (((model F).P (⟨a, b, f⟩ : SigFun A)).π 0 ◁ σ.naturality f)) :
    HEq (mateStr (M := (model F).toPreModel) (N := (model G).toPreModel) adj
        (⟨a, b, f⟩ : SigFun A) s)
      (((model G).P (⟨a, b, f⟩ : SigFun A)).π 0 ◁
        (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)) := by
  rw [mateStr_eq]
  have hv : HEq s (Bicategory.rightAdjointSquare.vcomp
      (eqToHom (((model G).P (⟨a, b, f⟩ : SigFun A)).lift_π
        (fun i => ((model F).P (⟨a, b, f⟩ : SigFun A)).π i ≫ σ.app a) 0)) (σ.naturality f)) := by
    refine hs.trans ?_
    simp [Bicategory.rightAdjointSquare.vcomp]
  have hm := Bicategory.mateEquiv_symm_heq (prodAdj (M := (model F).toPreModel)
    (N := (model G).toPreModel) adj (⟨a, b, f⟩ : SigFun A)) (adj b) rfl rfl hv
  rw [Bicategory.mateEquiv_symm_vcomp (prodAdj (M := (model F).toPreModel)
    (N := (model G).toPreModel) adj (⟨a, b, f⟩ : SigFun A)) (adj a) (adj b), prodAdj_eq,
    mate_proj] at hm
  refine hm.trans ?_
  simp [Bicategory.leftAdjointSquare.vcomp]

/-- **Mates of a lax transformation** (Houston, Proposition 2.35, through Example 3.12 of
[forsman2026syntactic]): for a lax transformation `σ : F ⇒ G` between pseudofunctors `A → K` and
adjunctions `l_a ⊣ σ_a`, the `l_a` with the mates `G f ≫ l_b ⇒ l_a ≫ F f` of the naturality
2-cells `σ_a ≫ G f ⇒ F f ≫ σ_b` (Mathlib's `Bicategory.mateEquiv`) form an oplax
transformation `G ⇒ F`. -/
theorem laxTrans_mate_oplaxTrans {F G : Pseudofunctor A K} (σ : Lax.LaxTrans F.toLax G.toLax)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) :
    ∃ τ : Lax.OplaxTrans G.toLax F.toLax, (∀ a, τ.app a = l a) ∧
      ∀ {a b : A} (f : a ⟶ b),
        HEq (τ.naturality f) ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)) := by
  obtain ⟨⟨D, hD⟩, rfl⟩ := mate_oplaxMor (laxEquiv F G σ) adj
  refine ⟨ofOplaxMor ⟨_, hD⟩, fun _ => rfl, fun {a b} f => heq_of_eq ?_⟩
  refine whiskerLeft_π_injective G f (eq_of_heq ((oplaxStr_eq G F _ f).heq.symm.trans ?_))
  exact PsFun.mateStr_sigOf σ l adj f _ (toLaxData_str σ f).heq

/-- **Adjunctions of lax transformations** (Houston, Proposition 2.35, through Example 3.12 of
[forsman2026syntactic]): let `σ : F ⇒ G` be a lax transformation between pseudofunctors
`A → K`, with adjunctions `l_a ⊣ σ_a` whose mates `G f ≫ l_b ⇒ l_a ≫ F f` of the naturality
2-cells are invertible. Then the `l_a` with the inverse mates form a lax transformation
`τ : G ⇒ F`, and the units and counits of the `l_a ⊣ σ_a` are modifications `𝟙 ⟶ τ ≫ σ` and
`σ ≫ τ ⟶ 𝟙`. So `τ ⊣ σ`. -/
theorem laxTrans_adjunction {F G : Pseudofunctor A K} (σ : Lax.LaxTrans F.toLax G.toLax)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a))
    [∀ {a b : A} (f : a ⟶ b),
      IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f))] :
    ∃ τ : Lax.LaxTrans G.toLax F.toLax, (∀ a, τ.app a = l a) ∧
      (∀ {a b : A} (f : a ⟶ b),
        HEq (τ.naturality f) (inv ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)))) ∧
      ∃ (η : Lax.LaxTrans.Modification (Lax.LaxTrans.id G.toLax) (τ.vComp σ))
        (ε : Lax.LaxTrans.Modification (σ.vComp τ) (Lax.LaxTrans.id F.toLax)),
        (∀ a, HEq (η.app a) (adj a).unit') ∧ (∀ a, HEq (ε.app a) (adj a).counit') := by
  -- The mates of the naturality cells are the structure cells of the mate data of `σ` under
  -- the equivalence with lax morphisms of the doctrine; they are invertible, so the doctrinal
  -- adjunction gives `τ` with the unit and counit. Then `τ` is read back as a lax transformation.
  have hk : ∀ {a b : A} (f : a ⟶ b),
      HEq ((mateOplaxData (laxEquiv F G σ).toLaxData adj).str ⟨a, b, f⟩)
        (((model G).P ⟨a, b, f⟩).π 0 ◁ (Bicategory.mateEquiv (adj a) (adj b)).symm
          (σ.naturality f)) := fun f => PsFun.mateStr_sigOf σ l adj f _ (toLaxData_str σ f).heq
  have hw : ∀ {a b : A} (f : a ⟶ b), IsIso (((model G).P ⟨a, b, f⟩).π 0 ◁
      (Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)) := fun f => inferInstance
  have hiso : ∀ B, IsIso ((mateOplaxData (laxEquiv F G σ).toLaxData adj).str B) := by
    rintro ⟨a, b, f⟩
    exact isIso_of_heq (Category.assoc _ _ _)
      (by simp only [Category.assoc, lift_π_assoc]; rfl) (hk f) (hw f)
  obtain ⟨⟨D, hD⟩, rfl, η₀, ε₀, hη, hε⟩ := doctrinal_adjunction (laxEquiv F G σ) adj
  let τ : Lax.LaxTrans G.toLax F.toLax := ofLaxMor ⟨_, hD⟩
  have hτ : toLaxData τ = invLaxData (mateOplaxData (laxEquiv F G σ).toLaxData adj) :=
    congr(($((laxEquiv G F).right_inv ⟨_, hD⟩)).toLaxData)
  refine ⟨τ, fun _ => rfl, fun {a b} f => heq_of_eq ?_, ?_⟩
  · -- The naturality cells of `τ` are the inverse mates.
    refine whiskerLeft_π_injective G f (eq_of_heq ((laxStr_eq G F _ f).heq.symm.trans ?_))
    refine (inv_heq_inv (Category.assoc _ _ _).symm
      (by simp only [Category.assoc, lift_π_assoc]; rfl) (hk f).symm (hw f) (hiso _)).symm.trans ?_
    exact heq_of_eq (Bicategory.inv_whiskerLeft _ _)
  · -- The unit and counit, cast along the lax data of the composites.
    have hidG : toLaxData (Lax.LaxTrans.id G.toLax) = LaxData.idData (model G).toPreModel :=
      toLaxData_id G
    have hτσ : toLaxData (τ.vComp σ) =
        (invLaxData (mateOplaxData (laxEquiv F G σ).toLaxData adj)).comp (toLaxData σ) :=
      (toLaxData_vComp τ σ).trans (by rw [hτ])
    have hστ : toLaxData (σ.vComp τ) =
        (toLaxData σ).comp (invLaxData (mateOplaxData (laxEquiv F G σ).toLaxData adj)) :=
      (toLaxData_vComp σ τ).trans (by rw [hτ])
    have hidF : toLaxData (Lax.LaxTrans.id F.toLax) = LaxData.idData (model F).toPreModel :=
      toLaxData_id F
    exact ⟨(laxModifEquiv G G _ _).symm (laxTwoCellCast hidG hτσ η₀),
      (laxModifEquiv F F _ _).symm (laxTwoCellCast hστ hidF ε₀),
      fun a => (laxTwoCellCast_app hidG hτσ η₀ a).trans (heq_of_eq (hη a)),
      fun a => (laxTwoCellCast_app hστ hidF ε₀ a).trans (heq_of_eq (hε a))⟩

end UlmerBialgebras.Paper
