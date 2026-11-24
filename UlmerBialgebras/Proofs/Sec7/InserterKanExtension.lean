module

public import UlmerBialgebras.Proofs.Sec5.BiDense
public import UlmerBialgebras.Proofs.Sec4.ExtensionCategories
public import UlmerBialgebras.Proofs.Sec5.ChainCofinality
public import UlmerBialgebras.Proofs.Sec5.EquifJointEpi
public import UlmerBialgebras.Monadicity.BigMonadicity
public import UlmerBialgebras.Kan.ColimKan

/-!
# Helper lemmas for Theorem 7.6 (`thm_7_6`, `thm_7_6_monadic`, and `lem_5_6`)

Helper results for the left Kan extension, cocompleteness and monadicity clauses of
Theorem 7.6 and for Lemma 5.6. The local adjoints come from Theorem 5.5 (1) for the
inserter and Theorem 5.5 (2) for the equifier. Theorem 7.4 then lifts these local adjoints;
the general bialgebraic monadicity criterion gives monadicity. This is the paper's route.

## Main results

* `UlmerBialgebras.Equifier.exists_leftKan_of_isRightAdjoint`: if `postcomp X E.e` has a left
  adjoint, then left Kan extensions along `k : I ⟶ X` lift from `E.e`-underlying diagrams to
  `E.pt`.
* `UlmerBialgebras.hasColimitsOfSize_of_full_faithful_isRightAdjoint`: a category with a fully
  faithful right adjoint into a cocomplete category is cocomplete.
* `UlmerBialgebras.Ins.hasColimitsOfSize_of_rel`: `Ins F G` is cocomplete when `C` is, `G` has an
  `F`-relative left adjoint and `F` preserves `κ`-chain colimits.
* `UlmerBialgebras.Inserter.push_isRightAdjoint_and_exists_leftKan`: the relative-adjoint
  transfinite construction of left Kan extensions into an inserter in a 2-category (used for
  `lem_5_6` and the inserter Kan-extension step of `thm_7_6`).
* `UlmerBialgebras.Paper.BialgDatum.isMonadic2_uB_of_isBiDense`: proof of `thm_7_6_monadic`
  (Theorem 7.6).
* `UlmerBialgebras.Paper.BialgDatum.exists_initial_leftExt_and_isACocomplete`: proof of `thm_7_6`
  (Theorem
  7.6).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 5.6 and
  Theorem 7.6
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w u' v' w₀

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## 1. Cocompleteness of `Ins F G` and `forget_isRightAdjoint_of_rel_binary` -/

section InsColimits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {J : Type w} [Category.{w} J]

/-- The functor from `J` to the terminal category `One.{0, 0}`. -/
def toOneCat (J : Type w) [Category.{w} J] : J ⥤ (One.{0, 0} : Type) where
  obj _ := One.star
  map _ := PUnit.unit

/-- Cocone associated to a left extension along `toOneCat J`. -/
@[simps]
def coconeOfLeftExtension {d : J ⥤ C} (L : Functor.LeftExtension (toOneCat J) d) : Cocone d where
  pt := L.right.obj One.star
  ι :=
    { app := fun j => L.hom.app j
      naturality := fun i j f => by
        have h := L.hom.naturality f
        have h2 : L.right.map ((toOneCat J).map f) = 𝟙 (L.right.obj One.star) :=
          L.right.map_id One.star
        exact h.trans ((L.hom.app i ≫= h2)) }

/-- Left extension along `toOneCat J` associated to a cocone. -/
def leftExtensionOfCocone {d : J ⥤ C} (c : Cocone d) : Functor.LeftExtension (toOneCat J) d :=
  StructuredArrow.mk (Y := (Functor.const (One.{0, 0} : Type)).obj c.pt)
    { app := fun j => c.ι.app j
      naturality := fun i j f => by
        dsimp
        rw [Category.comp_id]
        exact c.w f }

/-- Equivalence of morphisms between left extensions along `toOneCat J` and cocones. -/
def leftExtensionHomEquiv {d : J ⥤ C} (L L' : Functor.LeftExtension (toOneCat J) d) :
    (L ⟶ L') ≃ (coconeOfLeftExtension L ⟶ coconeOfLeftExtension L') where
  toFun a :=
    { hom := a.right.app One.star
      w := fun j => congr_app (StructuredArrow.w a) j }
  invFun m := StructuredArrow.homMk
    { app := fun x => match x with | OneObj.star => m.hom
      naturality := by
        rintro ⟨⟩ ⟨⟩ g
        obtain rfl : g = 𝟙 One.star.{0, 0} := rfl
        exact (L.right.map_id One.star =≫ m.hom).trans
          ((Category.id_comp m.hom).trans ((Category.comp_id m.hom).symm.trans
            ((m.hom ≫= L'.right.map_id One.star).symm))) }
    (by ext j; exact m.w j)
  left_inv a := by
    apply StructuredArrow.hom_ext
    ext x
    cases x
    rfl
  right_inv _ := rfl

/-- A diagram `d : J ⥤ C` has a colimit iff it has a left Kan extension along `toOneCat J`. -/
theorem hasColimit_iff_hasLeftKanExtension_toOneCat (d : J ⥤ C) :
    HasColimit d ↔ (toOneCat J).HasLeftKanExtension d := by
  constructor
  · intro ⟨⟨c, hc⟩⟩
    have hinit : IsInitial (leftExtensionOfCocone c) :=
      IsInitial.ofUniqueHom
        (fun L' => (leftExtensionHomEquiv (leftExtensionOfCocone c) L').symm
          (((Cocone.isColimitEquivIsInitial c) hc).to (coconeOfLeftExtension L')))
        (fun L' m => by
          have hm : leftExtensionHomEquiv (leftExtensionOfCocone c) L' m
              = ((Cocone.isColimitEquivIsInitial c) hc).to _ :=
            ((Cocone.isColimitEquivIsInitial c) hc).hom_ext _ _
          exact (Equiv.eq_symm_apply _).2 hm)
    exact hinit.hasInitial
  · intro h
    let L : Functor.LeftExtension (toOneCat J) d := ⊥_ _
    have hL : IsInitial L := initialIsInitial
    have hc : IsColimit (coconeOfLeftExtension L) :=
      (Cocone.isColimitEquivIsInitial _).symm
        (IsInitial.ofUniqueHom
          (fun c => leftExtensionHomEquiv L (leftExtensionOfCocone c) (hL.to _))
          (fun c m => by
            have hm : (leftExtensionHomEquiv L (leftExtensionOfCocone c)).symm m = hL.to _ :=
              hL.hom_ext _ _
            exact (Equiv.symm_apply_eq _).1 hm))
    exact ⟨⟨_, hc⟩⟩

/-- If `C` is cocomplete, `G` has an `F`-relative left adjoint, and `F` preserves `κ`-chain
colimits, then `Ins F G` is cocomplete. -/
theorem Ins.hasColimitsOfSize_of_rel {F G : C ⥤ D} {L : C ⥤ C} {κ : Cardinal.{w}}
    (hκ : Cardinal.aleph0 ≤ κ) (ra : RelLeftAdjoint F G L) [HasColimitsOfSize.{w, w} C]
    (hF : PreservesColimitsOfShape (Kappa.shape κ) F) :
    HasColimitsOfSize.{w, w} (Ins F G) := by
  have hch : HasChainColimitsLE κ C := fun _ _ _ _ _ => inferInstance
  refine ⟨fun {J} _ => ⟨fun d => ?_⟩⟩
  rw [hasColimit_iff_hasLeftKanExtension_toOneCat]
  have : (toOneCat J).HasLeftKanExtension (d ⋙ Ins.forget F G) :=
    (hasColimit_iff_hasLeftKanExtension_toOneCat _).1 inferInstance
  have : (toOneCat J).HasLeftKanExtension ((d ⋙ Ins.forget F G) ⋙ L) :=
    (hasColimit_iff_hasLeftKanExtension_toOneCat _).1 inferInstance
  exact Ins.hasLeftKanExtension_of_rel hκ ra hch hF d (toOneCat J)

/-- Every nonempty linear order is a connected category. -/
lemma isConnected_of_nonempty_linearOrder (J : Type w) [LinearOrder J] [Nonempty J] :
    IsConnected J := by
  have : IsFilteredOrEmpty J := inferInstance
  have : IsFiltered J := {}
  exact IsFiltered.isConnected J

/-- Variant of `Ins.forget_isRightAdjoint_of_rel` requiring only `[HasBinaryCoproducts C]`
(matching `Ins.forget_isRightAdjoint_of_shape`). -/
theorem Ins.forget_isRightAdjoint_of_rel_binary {F G : C ⥤ D} {L : C ⥤ C}
    {κ : Cardinal.{w}} (hκ : Cardinal.aleph0 ≤ κ)
    (ra : RelLeftAdjoint F G L) [HasBinaryCoproducts C]
    (hch : HasChainColimitsLE κ C)
    (hF : PreservesColimitsOfShape (Kappa.shape κ) F) :
    (Ins.forget F G).IsRightAdjoint := by
  let := Kappa.orderBotOfPos hκ
  have := Cardinal.noMaxOrder hκ
  have := Kappa.hasIterationOfShape_of_chain hκ hch
  have : Nonempty (Kappa.shape κ) := ⟨⊥⟩
  have : IsConnected (Kappa.shape κ) := isConnected_of_nonempty_linearOrder (Kappa.shape κ)
  have := hF
  have : PreservesColimitsOfShape (Kappa.shape κ) L := ra.preservesColimitsOfShape
  refine ra.ins_forget_isRightAdjoint ?_
  exact Ins.forget_isRightAdjoint_of_shape (F := L) (G := 𝟭 C) (L := 𝟭 C) Adjunction.id
    (Kappa.shape κ) (fun j => not_isMax j)

/-- A left adjoint preserves initial objects. -/
def isInitialLeftAdjointObj {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} (hX : IsInitial X) :
    IsInitial (L.obj X) :=
  IsInitial.ofUniqueHom
    (fun Y => (adj.homEquiv X Y).symm (hX.to (R.obj Y)))
    (fun Y m => (adj.homEquiv X Y).injective (by
      rw [Equiv.apply_symm_apply]
      exact hX.hom_ext _ _))

end InsColimits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## 2. Left Adjoints Preserve Left Kan Extensions -/

/-! ## 3. Connected Colimits and Binary Coproducts in `LeftExt` -/

namespace LeftExt

variable {I X c c' : Obj} (k : I ⟶ X) (d : I ⟶ c) (f : c ⟶ c')

/-- The forgetful projection `LeftExt k d ⥤ (X ⟶ c)`. -/
@[simps]
def proj : LeftExt k d ⥤ (X ⟶ c) where
  obj L := L.ext
  map g := LeftExt.homCell g

/-- Canonical functor `LeftExt k d ⥤ StructuredArrow d (precomp k c)`. -/
@[simps]
def toStructuredArrow : LeftExt k d ⥤ StructuredArrow d (precomp k c) where
  obj L := StructuredArrow.mk L.unit
  map g := StructuredArrow.homMk (LeftExt.homCell g) (LeftExt.w g)

/-- Inverse functor `StructuredArrow d (precomp k c) ⥤ LeftExt k d`. -/
@[simps]
def ofStructuredArrow : StructuredArrow d (precomp k c) ⥤ LeftExt k d where
  obj A := LeftExt.mk A.right A.hom
  map g := LeftExt.homMk g.right (StructuredArrow.w g)

/-- Equivalence `LeftExt k d ≌ StructuredArrow d (precomp k c)`. -/
@[simps]
def structuredArrowEquiv : LeftExt k d ≌ StructuredArrow d (precomp k c) where
  functor := toStructuredArrow k d
  inverse := ofStructuredArrow k d
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun g => LeftExt.hom_ext
      ((Category.comp_id (LeftExt.homCell g)).trans (Category.id_comp (LeftExt.homCell g)).symm))
  counitIso := NatIso.ofComponents (fun x => StructuredArrow.isoMk (Iso.refl _)
      (show x.hom ≫ (precomp k c).map (𝟙 x.right) = x.hom by
        rw [CategoryTheory.Functor.map_id, Category.comp_id]))
    (fun g => by ext; exact (Category.comp_id g.right).trans (Category.id_comp g.right).symm)
  functor_unitIso_comp _ := by ext; exact Category.id_comp _

/-- `toStructuredArrow k d : LeftExt k d ⥤ StructuredArrow d (precomp k c)` is an equivalence. -/
instance : (toStructuredArrow k d).IsEquivalence :=
  (structuredArrowEquiv k d).isEquivalence_functor

/-- `toStructuredArrow k d` followed by the structured-arrow projection is `proj k d`
(definitionally). -/
lemma toStructuredArrow_comp_proj :
    toStructuredArrow k d ⋙ StructuredArrow.proj d (precomp k c) = proj k d := rfl

/-- For connected `J`, if `K(X, c)` has `J`-colimits then so does `LeftExt k d`, via its equivalence
with the comma category `StructuredArrow d (precomp k c)`. -/
instance hasColimitsOfShape_of_isConnected {J : Type*} [Category J] [IsConnected J]
    [HasColimitsOfShape J (X ⟶ c)] : HasColimitsOfShape J (LeftExt k d) :=
  Adjunction.hasColimitsOfShape_of_equivalence (toStructuredArrow k d)

/-- For connected `J`, the projection `proj k d : LeftExt k d ⥤ K(X, c)` preserves `J`-colimits. -/
instance preservesColimitsOfShape_proj {J : Type*} [Category J] [IsConnected J] :
    PreservesColimitsOfShape J (proj k d) := by
  rw [← toStructuredArrow_comp_proj k d]
  infer_instance

/-- For connected `J`, the projection `proj k d : LeftExt k d ⥤ K(X, c)` reflects `J`-colimits. -/
instance reflectsColimitsOfShape_proj {J : Type*} [Category J] [IsConnected J] :
    ReflectsColimitsOfShape J (proj k d) := by
  have : ReflectsColimitsOfShape J (StructuredArrow.proj d (precomp k c)) := inferInstance
  rw [← toStructuredArrow_comp_proj k d]
  infer_instance

/-- Pushing extensions forward along `f` commutes with the projections:
`push k d f ⋙ proj = proj ⋙ K(X, f)` (definitionally). -/
lemma push_comp_proj :
    LeftExt.push k d f ⋙ proj k (d ≫ f) = proj k d ⋙ postcomp X f := rfl

/-- For connected `J`, if `K(X, f)` preserves `J`-colimits then so does
`LeftExt.push k d f : LeftExt k d ⥤ LeftExt k (d f)`, since `proj` preserves and reflects them. -/
instance preservesColimitsOfShape_push {J : Type*} [Category J] [IsConnected J]
    [PreservesColimitsOfShape J (postcomp X f)] :
    PreservesColimitsOfShape J (LeftExt.push k d f) := by
  have : PreservesColimitsOfShape J (proj k d ⋙ postcomp X f) := inferInstance
  have : PreservesColimitsOfShape J (LeftExt.push k d f ⋙ proj k (d ≫ f)) := by
    rwa [push_comp_proj k d f]
  exact Limits.preservesColimitsOfShape_of_reflects_of_preserves
    (LeftExt.push k d f) (proj k (d ≫ f))

/-- When `LeftExt k d` has an initial object `L₀` and `X ⟶ c` has pushouts, `LeftExt k d` has
binary coproducts (constructed as pushouts under `L₀.ext`). -/
theorem hasBinaryCoproducts_of_hasInitial (L₀ : LeftExt k d) (hL₀ : IsInitial L₀)
    [HasPushouts (X ⟶ c)] : HasBinaryCoproducts (LeftExt k d) := by
  -- The coproduct of two extensions is the pushout of their maps out of the initial one.
  have : ∀ L₁ L₂ : LeftExt k d, HasBinaryCoproduct L₁ L₂ := fun L₁ L₂ => by
    let f₁ : L₀.ext ⟶ L₁.ext := LeftExt.homCell (hL₀.to L₁)
    let f₂ : L₀.ext ⟶ L₂.ext := LeftExt.homCell (hL₀.to L₂)
    have hf₁ : L₀.unit ≫ (k ◁ f₁) = L₁.unit := LeftExt.w (hL₀.to L₁)
    have hf₂ : L₀.unit ≫ (k ◁ f₂) = L₂.unit := LeftExt.w (hL₀.to L₂)
    let P : LeftExt k d := LeftExt.mk (pushout f₁ f₂) (L₁.unit ≫ (k ◁ pushout.inl f₁ f₂))
    have hP_unit : P.unit = L₂.unit ≫ (k ◁ pushout.inr f₁ f₂) := by
      dsimp [P]
      rw [← hf₁, ← hf₂, Category.assoc (obj := _ ⟶ _), Category.assoc (obj := _ ⟶ _), ←
          Bicategory.whiskerLeft_comp, ← Bicategory.whiskerLeft_comp,
        pushout.condition]
    let inlP : L₁ ⟶ P := LeftExt.homMk (pushout.inl f₁ f₂) rfl
    let inrP : L₂ ⟶ P := LeftExt.homMk (pushout.inr f₁ f₂) hP_unit.symm
    refine HasColimit.mk ⟨BinaryCofan.mk inlP inrP, BinaryCofan.IsColimit.mk _
      (fun {T} g₁ g₂ =>
        LeftExt.homMk (pushout.desc (LeftExt.homCell g₁) (LeftExt.homCell g₂) ?_) ?_)
      ?_ ?_ ?_⟩
    · have h₁ : (LeftExt.homCell (hL₀.to L₁ ≫ g₁)) = LeftExt.homCell (hL₀.to L₂ ≫ g₂) :=
        congr(LeftExt.homCell $(hL₀.hom_ext (hL₀.to L₁ ≫ g₁) (hL₀.to L₂ ≫ g₂)))
      exact h₁
    · dsimp [P]
      rw [Category.assoc (obj := _ ⟶ _), ← Bicategory.whiskerLeft_comp, pushout.inl_desc,
        LeftExt.w g₁]
    · intro T g₁ g₂
      exact LeftExt.hom_ext (pushout.inl_desc _ _ _)
    · intro T g₁ g₂
      exact LeftExt.hom_ext (pushout.inr_desc _ _ _)
    · intro T g₁ g₂ m hm₁ hm₂
      refine LeftExt.hom_ext (pushout.hom_ext ?_ ?_)
      · simp only [LeftExt.homCell_homMk, pushout.inl_desc]
        exact congr(LeftExt.homCell $(hm₁))
      · simp only [LeftExt.homCell_homMk, pushout.inr_desc]
        exact congr(LeftExt.homCell $(hm₂))
  exact hasBinaryCoproducts_of_hasColimit_pair (LeftExt k d)

end LeftExt

/-! ## 4. Lifting Left Kan Extensions into an Inserter (Lemma 5.6 and Inserter Step of Thm 7.6) -/

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b} (I₀ : Inserter f g) {I X : Obj}
variable (k : I ⟶ X) (d : I ⟶ I₀.pt)

-- The functors `twistedPush` (`g_*`) and `leftExtToIns` of Lemma 4.6 (2), and the fact that
-- `leftExtToIns` is an isomorphism of categories over `LE(u d, k)`, are in
-- `UlmerBialgebras/Paper/Sec4DefsExt.lean` and
-- `UlmerBialgebras/Proofs/Sec4/ExtensionCategories.lean`.

variable {l : b ⟶ a} (Adj : TwoAdj l g)
  (L₁ : LeftExt k (d ≫ I₀.u)) (hL₁ : IsInitial L₁)
  (L₂ : LeftExt k ((d ≫ I₀.u) ≫ f)) (hL₂ : IsInitial L₂)

/-- The transpose `L₂.ext ≫ l ⟶ L₁.ext` of the structure cell of `d`. -/
noncomputable def kanBaseHom : L₂.ext ≫ l ⟶ L₁.ext :=
  ((Adj.postcompAdj X).homEquiv L₂.ext L₁.ext).symm (LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁)))

/-- The comparison map `L₂.ext ≫ l ⟶ (S.ext ≫ f) ≫ l` for an extension `S` of `d ≫ u`. -/
noncomputable def kanCompHom (S : LeftExt k (d ≫ I₀.u)) :
    L₂.ext ≫ l ⟶ (S.ext ≫ f) ≫ l :=
  (LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))) ▷ l

/-- `kanCompHom` is natural in the extension `S`: for `α : S ⟶ S'`,
`kanCompHom S ≫ ((α ▷ f) ▷ l) = kanCompHom S'`. -/
lemma kanCompHom_naturality {S S' : LeftExt k (d ≫ I₀.u)} (α : S ⟶ S') :
    kanCompHom I₀ k d L₂ hL₂ S ≫ ((LeftExt.homCell α ▷ f) ▷ l) = kanCompHom I₀ k d L₂ hL₂ S' := by
  dsimp [kanCompHom]
  rw [← Bicategory.comp_whiskerRight]
  congr 1
  exact congr(LeftExt.homCell $(hL₂.hom_ext
    (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S) ≫
      (LeftExt.push k (d ≫ I₀.u) f).map α)
    (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S'))))

/-- For extensions `S, T` of `d u` along `k` and `γ : S f ⟶ T g`, `γ` is a morphism of extensions
`f_* S ⟶ g_* T` (Lemma 4.6 (2)) iff `kanBaseHom ≫ !_T = kanCompHom S ≫ γ♭`, where `!_T` is the map
out of the initial `L₁` and `γ♭ : S f l ⟶ T` is the transpose of `γ` under `l ⊣ g`. -/
lemma kanAdj_compat_iff (S T : LeftExt k (d ≫ I₀.u))
    (γ : S.ext ≫ f ⟶ T.ext ≫ g) :
    (((LeftExt.push k (d ≫ I₀.u) f).obj S).unit ≫ (k ◁ γ) = (kanTarget I₀ k d T).unit) ↔
      kanBaseHom I₀ k d Adj L₁ L₂ hL₂ ≫ LeftExt.homCell (hL₁.to T) =
        kanCompHom I₀ k d L₂ hL₂ S ≫
          ((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext).symm γ := by
  -- Rewrite both sides through the units of the extensions and the initial maps.
  have hpush : (((LeftExt.push k (d ≫ I₀.u) f).obj S).unit ≫ (k ◁ γ) = (kanTarget I₀ k d T).unit) ↔
      L₂.unit ≫ (k ◁ ((LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))) ≫ γ))
        = (kanTarget I₀ k d T).unit := by
    rw [Bicategory.whiskerLeft_comp, ← Category.assoc (obj := _ ⟶ _),
      LeftExt.w (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))]
  have hunitL₁ : (kanTarget I₀ k d L₁).unit ≫ (k ◁ (LeftExt.homCell (hL₁.to T) ▷ g)) =
      (kanTarget I₀ k d T).unit :=
    LeftExt.w ((I₀.twistedPush k d).map (hL₁.to T))
  have hunitL₂ : L₂.unit ≫
      (k ◁ (LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁)) ≫ (LeftExt.homCell (hL₁.to T) ▷ g)))
      = (kanTarget I₀ k d T).unit := by
    have hcomp := (L₂.unit ≫= Bicategory.whiskerLeft_comp k
      (LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁))) (LeftExt.homCell (hL₁.to T) ▷ g))
    have hunit := congrArg (· ≫ (k ◁ (LeftExt.homCell (hL₁.to T) ▷ g)))
      (LeftExt.w (hL₂.to (kanTarget I₀ k d L₁)))
    exact (hcomp.trans ((Category.assoc _ _ _).symm.trans hunit)).trans hunitL₁
  have hcomp₂ :
      (L₂.unit ≫ (k ◁ ((LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))) ≫ γ))
      = (kanTarget I₀ k d T).unit) ↔
        (LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))) ≫ γ
          = LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁)) ≫ (LeftExt.homCell (hL₁.to T) ▷ g) := by
    refine ⟨fun h => congr(LeftExt.homCell $(hL₂.hom_ext (LeftExt.homMk (L' := kanTarget I₀ k d T)
      _ h) (LeftExt.homMk (L' := kanTarget I₀ k d T) _ hunitL₂))), fun h => by rw [h, hunitL₂]⟩
  rw [hpush, hcomp₂, ← ((Adj.postcompAdj X).homEquiv L₂.ext T.ext).symm.injective.eq_iff]
  -- Transpose along the adjunction and compare the two sides.
  have lhs_eq : ((Adj.postcompAdj X).homEquiv L₂.ext T.ext).symm
        ((LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S))) ≫ γ)
      = kanCompHom I₀ k d L₂ hL₂ S ≫
          ((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext).symm γ := by
    apply ((Adj.postcompAdj X).homEquiv L₂.ext T.ext).injective
    rw [Equiv.apply_symm_apply]
    have hnat := (Adj.postcompAdj X).homEquiv_naturality_left
      (LeftExt.homCell (hL₂.to ((LeftExt.push k (d ≫ I₀.u) f).obj S)))
      (((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext).symm γ)
    dsimp [postcomp, kanCompHom] at hnat ⊢
    rw [hnat, Equiv.apply_symm_apply]
  have rhs_eq : ((Adj.postcompAdj X).homEquiv L₂.ext T.ext).symm
        (LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁)) ≫ (LeftExt.homCell (hL₁.to T) ▷ g))
      = kanBaseHom I₀ k d Adj L₁ L₂ hL₂ ≫ LeftExt.homCell (hL₁.to T) := by
    apply ((Adj.postcompAdj X).homEquiv L₂.ext T.ext).injective
    rw [Equiv.apply_symm_apply]
    have hnat := (Adj.postcompAdj X).homEquiv_naturality_right
      (kanBaseHom I₀ k d Adj L₁ L₂ hL₂)
      (LeftExt.homCell (hL₁.to T))
    dsimp [postcomp, kanBaseHom] at hnat ⊢
    have htranspose := ((Adj.postcompAdj X).homEquiv L₂.ext L₁.ext).apply_symm_apply
      (show L₂.ext ⟶ L₁.ext ≫ g from (LeftExt.homCell (hL₂.to (kanTarget I₀ k d L₁))))
    exact (hnat.trans (congrArg (· ≫ (LeftExt.homCell (hL₁.to T) ▷ g)) htranspose)).symm
  rw [lhs_eq, rhs_eq, eq_comm]

variable [HasPushouts (X ⟶ a)]

/-- The relative left adjoint `LeftExt k (d ≫ I₀.u) ⥤ LeftExt k (d ≫ I₀.u)` of
`I₀.twistedPush k d` relative to `LeftExt.push k (d ≫ I₀.u) f`. -/
@[simps]
noncomputable def kanRelLeftAdjoint :
    LeftExt k (d ≫ I₀.u) ⥤ LeftExt k (d ≫ I₀.u) where
  obj S :=
    LeftExt.mk (pushout (kanBaseHom I₀ k d Adj L₁ L₂ hL₂) (kanCompHom I₀ k d L₂ hL₂ S))
      (L₁.unit ≫ (k ◁ pushout.inl _ _))
  map {S₁ S₂} α :=
    LeftExt.homMk (pushout.desc (pushout.inl _ _)
      (((LeftExt.homCell α ▷ f) ▷ l) ≫ pushout.inr _ _)
      (by rw [← Category.assoc (obj := _ ⟶ _), kanCompHom_naturality I₀ k d L₂ hL₂ α,
          pushout.condition]))
      (by
        dsimp
        simp only [Category.assoc (obj := _ ⟶ _), ← Bicategory.whiskerLeft_comp, pushout.inl_desc])
  map_id S := LeftExt.hom_ext (pushout.hom_ext
    (by
      simp only [LeftExt.homCell_homMk, LeftExt.homCell_id, pushout.inl_desc]
      exact (Category.comp_id _).symm)
    (by
      simp only [LeftExt.homCell_homMk, LeftExt.homCell_id, pushout.inr_desc]
      rw [Bicategory.id_whiskerRight, Bicategory.id_whiskerRight, Category.id_comp]
      exact (Category.comp_id _).symm))
  map_comp α β := LeftExt.hom_ext (pushout.hom_ext
    (by
      simp only [LeftExt.homCell_homMk, LeftExt.homCell_comp]
      rw [pushout.inl_desc, ← Category.assoc (obj := _ ⟶ _), pushout.inl_desc, pushout.inl_desc])
    (by
      simp only [LeftExt.homCell_homMk, LeftExt.homCell_comp]
      rw [pushout.inr_desc, ← Category.assoc (obj := _ ⟶ _), pushout.inr_desc, Category.assoc (obj
          := _ ⟶ _), pushout.inr_desc,
        ← Category.assoc (obj := _ ⟶ _), ← Bicategory.comp_whiskerRight,
          ← Bicategory.comp_whiskerRight]))

/-- For a morphism `m : R(S) ⟶ T` out of the pushout extension `R(S)` of `kanRelLeftAdjoint`, the
composite `inl ≫ m` is the unique map `L₁ ⟶ T` out of the initial extension `L₁`. -/
lemma inl_comp_kanRelLeftAdjoint_hom {S T : LeftExt k (d ≫ I₀.u)}
    (m : (kanRelLeftAdjoint I₀ k d Adj L₁ L₂ hL₂).obj S ⟶ T) :
    pushout.inl (kanBaseHom I₀ k d Adj L₁ L₂ hL₂) (kanCompHom I₀ k d L₂ hL₂ S) ≫ LeftExt.homCell m
      = LeftExt.homCell (hL₁.to T) := by
  have hm : L₁.unit ≫
      (k ◁ (pushout.inl (kanBaseHom I₀ k d Adj L₁ L₂ hL₂) (kanCompHom I₀ k d L₂ hL₂ S) ≫
        LeftExt.homCell m))
        = T.unit := by
    exact (L₁.unit ≫= Bicategory.whiskerLeft_comp _ _ _).trans
      ((Category.assoc _ _ _).symm.trans (LeftExt.w m))
  exact congr(LeftExt.homCell $(hL₁.hom_ext (LeftExt.homMk (L' := T) _ hm) (hL₁.to T)))

-- Give the underlying hom its pushout source explicitly for rewriting.
private noncomputable abbrev kanRelLeftAdjointHom {S T : LeftExt k (d ≫ I₀.u)}
    (m : (kanRelLeftAdjoint I₀ k d Adj L₁ L₂ hL₂).obj S ⟶ T) :
    pushout (kanBaseHom I₀ k d Adj L₁ L₂ hL₂) (kanCompHom I₀ k d L₂ hL₂ S) ⟶ T.ext :=
  LeftExt.homCell m

/-- `kanRelLeftAdjoint` is a `LeftExt.push k (d ≫ I₀.u) f`-relative left adjoint of
`I₀.twistedPush k d`. -/
noncomputable def isRelLeftAdjointKanRelLeftAdjoint :
    RelLeftAdjoint (LeftExt.push k (d ≫ I₀.u) f) (I₀.twistedPush k d)
      (kanRelLeftAdjoint I₀ k d Adj L₁ L₂ hL₂) where
  homEquiv S T :=
    { toFun := fun m =>
        LeftExt.homMk (((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext)
          (pushout.inr (kanBaseHom I₀ k d Adj L₁ L₂ hL₂) (kanCompHom I₀ k d L₂ hL₂ S) ≫
            LeftExt.homCell m))
         ((kanAdj_compat_iff I₀ k d Adj L₁ hL₁ L₂ hL₂ S T _).mpr (by
            rw [Equiv.symm_apply_apply]
            exact ((Category.assoc _ _ _).symm.trans ((pushout.condition =≫ _).symm.trans
              ((Category.assoc _ _ _).trans
                (whisker_eq _ (inl_comp_kanRelLeftAdjoint_hom I₀ k d Adj L₁ hL₁ L₂ hL₂ m))))).symm))
      invFun := fun γ =>
        LeftExt.homMk (pushout.desc (LeftExt.homCell (hL₁.to T))
          (((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext).symm (LeftExt.homCell γ))
          ((kanAdj_compat_iff I₀ k d Adj L₁ hL₁ L₂ hL₂ S T (LeftExt.homCell γ)).mp
            (LeftExt.w γ)))
         ((Category.assoc _ _ _).trans ((L₁.unit ≫= (Bicategory.whiskerLeft_comp _ _ _).symm).trans
          (congr(L₁.unit ≫ k ◁ $(pushout.inl_desc _ _ _)).trans
            (LeftExt.w (hL₁.to T)))))
      left_inv := fun m => LeftExt.hom_ext (pushout.hom_ext
        ((pushout.inl_desc _ _ _).trans
          (inl_comp_kanRelLeftAdjoint_hom I₀ k d Adj L₁ hL₁ L₂ hL₂ m).symm)
        ((pushout.inr_desc _ _ _).trans (Equiv.symm_apply_apply _ _)))
      right_inv := fun γ => LeftExt.hom_ext
        (congr((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext $(pushout.inr_desc _ _ _)).trans
          (((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T.ext).apply_symm_apply
            (LeftExt.homCell γ))) }
  homEquiv_naturality_left {S S' T} α m := LeftExt.hom_ext (by
    let m' := kanRelLeftAdjointHom I₀ k d Adj L₁ L₂ hL₂ m
    exact (congr((Adj.postcompAdj X).homEquiv (S'.ext ≫ f) T.ext
      $(((Category.assoc _ _ _).symm.trans (pushout.inr_desc _ _ _ =≫ m')).trans
        (Category.assoc _ _ _)))).trans
      ((Adj.postcompAdj X).homEquiv_naturality_left (LeftExt.homCell α ▷ f) _))
  homEquiv_naturality_right {S T T'} m β := LeftExt.hom_ext (by
    let m' := kanRelLeftAdjointHom I₀ k d Adj L₁ L₂ hL₂ m
    exact (congr((Adj.postcompAdj X).homEquiv (S.ext ≫ f) T'.ext
      $((Category.assoc (pushout.inr _ _) m' (LeftExt.homCell β)).symm)).trans
      ((Adj.postcompAdj X).homEquiv_naturality_right _ (LeftExt.homCell β))))

/-- **Inserter Kan-extension theorem** (generalizing Lemma 5.6 to any `g` with a left adjoint):
if `g` has a left adjoint in `K`, `X ⟶ a` has pushouts and `κ_≤`-chain colimits,
`postcomp X f` preserves `κ`-chain colimits, and `d ≫ I₀.u` and `(d ≫ I₀.u) ≫ f` have
left Kan extensions along `k`, then `LeftExt.push k d I₀.u` has a left adjoint and `d` has a
left Kan extension along `k`. -/
theorem push_isRightAdjoint_and_exists_leftKan
    (hg : ∃ l, Nonempty (TwoAdj l g)) {κ : Cardinal.{w₀}} (hκ : Cardinal.aleph0 ≤ κ)
    (hch : HasChainColimitsLE κ (X ⟶ a))
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp X f))
    (h1 : ∃ L : LeftExt k (d ≫ I₀.u), Nonempty (IsInitial L))
    (h2 : ∃ L : LeftExt k ((d ≫ I₀.u) ≫ f), Nonempty (IsInitial L)) :
    (LeftExt.push k d I₀.u).IsRightAdjoint ∧ ∃ L : LeftExt k d, Nonempty (IsInitial L) := by
  obtain ⟨l, ⟨Adj⟩⟩ := hg
  obtain ⟨L₁, ⟨hL₁⟩⟩ := h1
  obtain ⟨L₂, ⟨hL₂⟩⟩ := h2
  have : HasBinaryCoproducts (LeftExt k (d ≫ I₀.u)) :=
    LeftExt.hasBinaryCoproducts_of_hasInitial k (d ≫ I₀.u) L₁ hL₁
  have hch_ext : HasChainColimitsLE κ (LeftExt k (d ≫ I₀.u)) := by
    intro J _ _ _ hJ
    have : HasColimitsOfShape J (X ⟶ a) := hch J hJ
    have : IsConnected J := isConnected_of_nonempty_linearOrder J
    exact LeftExt.hasColimitsOfShape_of_isConnected k (d ≫ I₀.u)
  have : Nonempty (Kappa.shape κ) :=
    letI := Kappa.orderBotOfPos hκ
    ⟨⊥⟩
  have : IsConnected (Kappa.shape κ) := isConnected_of_nonempty_linearOrder (Kappa.shape κ)
  have : PreservesColimitsOfShape (Kappa.shape κ) (postcomp X f) := hf
  have hF_ext : PreservesColimitsOfShape (Kappa.shape κ) (LeftExt.push k (d ≫ I₀.u) f) :=
    LeftExt.preservesColimitsOfShape_push k (d ≫ I₀.u) f
  let ra := isRelLeftAdjointKanRelLeftAdjoint I₀ k d Adj L₁ hL₁ L₂ hL₂
  have : (Ins.forget (LeftExt.push k (d ≫ I₀.u) f) (I₀.twistedPush k d)).IsRightAdjoint :=
    Ins.forget_isRightAdjoint_of_rel_binary hκ ra hch_ext hF_ext
  have : (leftExtToIns I₀ k d).IsRightAdjoint := inferInstance
  have hadj : (LeftExt.push k d I₀.u).IsRightAdjoint := by
    rw [← leftExtToIns_comp_forget I₀ k d]
    infer_instance
  have := hadj
  let adjPush := Adjunction.ofIsRightAdjoint (LeftExt.push k d I₀.u)
  exact ⟨hadj, ⟨(LeftExt.push k d I₀.u).leftAdjoint.obj L₁,
    ⟨isInitialLeftAdjointObj adjPush hL₁⟩⟩⟩

end Inserter

/-! ## 5. Lifting Left Kan Extensions into an Equifier -/

namespace Equifier

variable {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)

/-- If `postcomp X E.e` has a left adjoint and `d ≫ E.e` has a left Kan extension along
`k : I ⟶ X`, then `d` has a left Kan extension along `k`. -/
theorem exists_leftKan_of_isRightAdjoint {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    [(postcomp X E.e).IsRightAdjoint]
    (hL' : ∃ L' : LeftExt k (d ≫ E.e), Nonempty (IsInitial L')) :
    ∃ L : LeftExt k d, Nonempty (IsInitial L) := by
  -- Transport the initial extension along the left adjoint of `postcomp X E.e`.
  obtain ⟨L', ⟨hL'⟩⟩ := hL'
  let adjE := Adjunction.ofIsRightAdjoint (postcomp X E.e)
  let m₀ : X ⟶ E.pt := (postcomp X E.e).leftAdjoint.obj L'.ext
  let u₀ : L'.ext ⟶ m₀ ≫ E.e := adjE.unit.app L'.ext
  obtain ⟨unit₀, hunit₀⟩ := E.full (k₁ := d) (k₂ := k ≫ m₀)
    (L'.unit ≫ (k ◁ u₀) ≫ eqToHom (Category.assoc k m₀ E.e).symm)
  let L₀ : LeftExt k d := LeftExt.mk m₀ unit₀
  -- `L₀` is initial: maps out of it correspond to maps out of `L'` under the adjunction.
  refine ⟨L₀, ⟨IsInitial.ofUniqueHom
    (fun S => LeftExt.homMk ((adjE.homEquiv L'.ext S.ext).symm
      (LeftExt.homCell (hL'.to ((LeftExt.push k d E.e).obj S)))) ?_)
    (fun S μ => LeftExt.hom_ext ?_)⟩⟩
  · set φ := hL'.to ((LeftExt.push k d E.e).obj S)
    set ψ₀ : m₀ ⟶ S.ext := (adjE.homEquiv L'.ext S.ext).symm (LeftExt.homCell φ)
    have hψ₀ : u₀ ≫ (ψ₀ ▷ E.e) = LeftExt.homCell φ := by
      have h := (adjE.homEquiv L'.ext S.ext).apply_symm_apply (LeftExt.homCell φ)
      rwa [Adjunction.homEquiv_unit] at h
    have hφ : L'.unit ≫ (k ◁ LeftExt.homCell φ) =
        (S.unit ▷ E.e) ≫ eqToHom (Category.assoc k S.ext E.e) := LeftExt.w φ
    refine E.faithful _ _ ?_
    simp only [L₀, LeftExt.mk_unit]
    rw [Bicategory.comp_whiskerRight, hunit₀, Bicategory.Strict.whisker_assoc' k ψ₀ E.e]
    simp only [Category.assoc (obj := _ ⟶ _), eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (obj := _ ⟶ _) (k ◁ u₀), ← Bicategory.whiskerLeft_comp, hψ₀]
    rw [reassoc_of% hφ, eqToHom_trans, eqToHom_refl, Category.comp_id]
  · set φ := hL'.to ((LeftExt.push k d E.e).obj S)
    dsimp only [LeftExt.homCell_homMk]
    apply (adjE.homEquiv L'.ext S.ext).injective
    rw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    have hμ : unit₀ ≫ (k ◁ (LeftExt.homCell μ)) = S.unit := LeftExt.w μ
    have hcompat : L'.unit ≫ (k ◁ (u₀ ≫ (LeftExt.homCell μ ▷ E.e)))
        = (S.unit ▷ E.e) ≫ eqToHom (Category.assoc k S.ext E.e) := by
      have h1 := congrArg (fun α => (α ▷ E.e) ≫ eqToHom (Category.assoc k S.ext E.e)) hμ
      rw [Bicategory.comp_whiskerRight, hunit₀,
        Bicategory.Strict.whisker_assoc' k (LeftExt.homCell μ) E.e] at h1
      simp only [Category.assoc (obj := _ ⟶ _), eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp,
        eqToHom_trans, Category.comp_id] at h1
      rw [Bicategory.whiskerLeft_comp]
      exact h1
    exact congr(LeftExt.homCell $(hL'.hom_ext
      (LeftExt.homMk (L' := (LeftExt.push k d E.e).obj S) (u₀ ≫ (LeftExt.homCell μ ▷ E.e)) hcompat)
      φ))

end Equifier

/-! ## 6. Cocompleteness of a Reflective Full Subcategory -/

section ReflectiveColimits

variable {C' D' : Type*} [Category C'] [Category D']

/-- A category admitting a fully faithful right adjoint into a cocomplete category is
cocomplete. -/
theorem hasColimitsOfSize_of_full_faithful_isRightAdjoint (G : D' ⥤ C')
    [G.Full] [G.Faithful] [G.IsRightAdjoint] [HasColimitsOfSize.{w₀, w₀} C'] :
    HasColimitsOfSize.{w₀, w₀} D' := by
  let L := G.leftAdjoint
  let adj := Adjunction.ofIsRightAdjoint G
  have : IsIso adj.counit := Adjunction.counit_isIso_of_R_fully_faithful adj
  have : PreservesColimitsOfSize.{w₀, w₀} L := adj.leftAdjoint_preservesColimits
  refine ⟨fun {J} _ => ⟨fun K => ?_⟩⟩
  have : HasColimit ((K ⋙ G) ⋙ L) := inferInstance
  exact hasColimit_of_iso (Functor.associator K G L ≪≫
    Functor.isoWhiskerLeft K (asIso adj.counit) ≪≫ K.rightUnitor).symm

end ReflectiveColimits

/-! ## 7. Proof of `thm_7_6` and `thm_7_6_monadic` -/

namespace Paper.BialgDatum

variable (A : ObjectProperty Obj)
variable (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)

/-- For any `a`, if `B.g` has a left adjoint in `K`, `a ⟶ B.c` is cocomplete, and
`postcomp a B.f` preserves `κ`-chain colimits, then `postcomp a B.ins.u` is a right adjoint,
preserves `κ`-chain colimits, and `a ⟶ B.ins.pt` is cocomplete. -/
theorem postcomp_insU_isRightAdjoint_and_cocomplete (hg : ∃ l, Nonempty (TwoAdj l B.g))
    {a : Obj} (hcoc : HasColimitsOfSize.{w₀, w₀} (a ⟶ B.c))
    {κ : Cardinal.{w₀}} (hκ : Cardinal.aleph0 ≤ κ)
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp a B.f)) :
    (postcomp a B.ins.u).IsRightAdjoint ∧
      PreservesColimitsOfShape κ.ord.ToType (postcomp a B.ins.u) ∧
      HasColimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := by
  obtain ⟨l, ⟨adj_g⟩⟩ := hg
  have : HasColimitsOfSize.{w₀, w₀} (a ⟶ B.c) := hcoc
  have : HasFiniteCoproducts (a ⟶ B.c) := inferInstance
  have hch : HasChainColimitsLE κ (a ⟶ B.c) := fun _ _ _ _ _ => inferInstance
  let ra := RelLeftAdjoint.ofAdjunction (adj_g.postcompAdj a) (postcomp a B.f)
  -- Theorem 5.5 (1) supplies the local inserter adjunction.
  let : MonadicRightAdjoint (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
    Ins.monadicRightAdjointForget hκ ra hch hf
  have : (Ins.forget (postcomp a B.f) (postcomp a B.g)).IsRightAdjoint := inferInstance
  have : (Inserter.homFunctor B.ins a).IsRightAdjoint := inferInstance
  have hadj : (postcomp a B.ins.u).IsRightAdjoint := by
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have hpres : PreservesColimitsOfShape κ.ord.ToType (postcomp a B.ins.u) := by
    have := hf
    have : PreservesColimitsOfShape κ.ord.ToType
        (Ins.forget (postcomp a B.f) (postcomp a B.g)) := inferInstance
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have : HasColimitsOfSize.{w₀, w₀} (Ins (postcomp a B.f) (postcomp a B.g)) :=
    Ins.hasColimitsOfSize_of_rel hκ ra hf
  have h_ins_coc : HasColimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) :=
    ⟨fun {J} _ => Adjunction.hasColimitsOfShape_of_equivalence (Inserter.homFunctor B.ins a)⟩
  exact ⟨hadj, hpres, h_ins_coc⟩

/-- If `a ⟶ B.c` is cocomplete, then `postcomp a E.e` and `postcomp a (B.uB E)` are
right adjoints and `a ⟶ E.pt` is cocomplete. -/
theorem postcomp_e_isRightAdjoint_and_cocomplete
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    {a : Obj} (hcoc : HasColimitsOfSize.{w₀, w₀} (a ⟶ B.c))
    {κ : Cardinal.{w₀}} (hκ : Cardinal.aleph0 ≤ κ)
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp a B.f))
    (hf' : PreservesColimitsOfShape κ.ord.ToType (postcomp a B.f')) :
    (postcomp a E.e).IsRightAdjoint ∧ (postcomp a (B.uB E)).IsRightAdjoint ∧
      HasColimitsOfSize.{w₀, w₀} (a ⟶ E.pt) := by
  obtain ⟨l', ⟨adj_g'⟩⟩ := hg'
  obtain ⟨hadj_u, hpres_u, hins_coc⟩ :=
    B.postcomp_insU_isRightAdjoint_and_cocomplete hg hcoc hκ hf
  have := hadj_u
  have := hpres_u
  have := hf'
  have : HasColimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := hins_coc
  have : HasCoequalizers (a ⟶ B.ins.pt) := inferInstance
  have hch_ins : HasChainColimitsLE κ (a ⟶ B.ins.pt) := fun _ _ _ _ _ => inferInstance
  have : (postcomp a B.g').IsRightAdjoint := (adj_g'.postcompAdj a).isRightAdjoint
  have : (postcomp a (B.ins.u ≫ B.g')).IsRightAdjoint := by
    rw [postcomp_comp₁ a B.ins.u B.g']
    infer_instance
  have hpres_uf' : PreservesColimitsOfShape κ.ord.ToType (postcomp a (B.ins.u ≫ B.f')) := by
    rw [postcomp_comp₁ a B.ins.u B.f']
    infer_instance
  let ra' := RelLeftAdjoint.ofAdjunction
    (Adjunction.ofIsRightAdjoint (postcomp a (B.ins.u ≫ B.g')))
    (postcomp a (B.ins.u ≫ B.f'))
  have := hpres_uf'
  have hJE : PreservesJointEpiOfShape κ.ord.ToType (postcomp a (B.ins.u ≫ B.f')) :=
    fun _ _ hc _ _ _ h => (isColimitOfPreserves (postcomp a (B.ins.u ≫ B.f')) hc).hom_ext h
  -- Theorem 5.5 (2), shared with the checked statement in Sec5Proofs.
  let : MonadicRightAdjoint (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
    Equif.monadicRightAdjointForgetOfJointEpi hκ ra' (postcompNat a B.α)
      (postcompNat a B.β) hch_ins hJE
  have : (Equif.forget (postcompNat a B.α) (postcompNat a B.β)).IsRightAdjoint := inferInstance
  have : (Equifier.homFunctor E a).IsRightAdjoint := inferInstance
  have hadj_e : (postcomp a E.e).IsRightAdjoint := by
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  have := hadj_e
  have hadj_uB : (postcomp a (B.uB E)).IsRightAdjoint := by
    rw [postcomp_comp₁ a E.e B.ins.u]
    infer_instance
  have : (postcomp a E.e).Full := by
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  have : (postcomp a E.e).Faithful := by
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  have hE_coc : HasColimitsOfSize.{w₀, w₀} (a ⟶ E.pt) :=
    hasColimitsOfSize_of_full_faithful_isRightAdjoint (postcomp a E.e)
  exact ⟨hadj_e, hadj_uB, hE_coc⟩

/-- Proof of `thm_7_6_monadic`: Theorem 5.5 (2) supplies the local equifier adjunctions;
Theorem 7.4 lifts them, and the bialgebraic monadicity criterion gives monadicity. -/
theorem isMonadic2_uB_of_isBiDense (hA : IsBiDense A)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c) (hRan : HasARightKan A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    IsMonadic2 (B.uB E) :=
  B.isMonadic2_uB_of_isARightAdjoint E hA hg hg' hRan fun a ha =>
    (B.postcomp_e_isRightAdjoint_and_cocomplete E hg hg' (hcoc ha)
      (hκ a ha) (hf a ha) (hf' a ha)).2.1

/-- Proof of `thm_7_6`. -/
theorem exists_initial_leftExt_and_isACocomplete
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt), A X →
      (∃ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L)) →
      (∃ L : LeftExt k ((d ≫ B.uB E) ≫ B.f), Nonempty (IsInitial L)) →
        ∃ L : LeftExt k d, Nonempty (IsInitial L)) ∧
      IsACocomplete.{w₀} A E.pt := by
  refine ⟨fun {I X} k d hX h1 h2 => ?_, fun a ha =>
    (B.postcomp_e_isRightAdjoint_and_cocomplete E hg hg' (hcoc ha)
      (hκ a ha) (hf a ha) (hf' a ha)).2.2⟩
  have : HasColimitsOfSize.{w₀, w₀} (X ⟶ B.c) := hcoc hX
  have : HasPushouts (X ⟶ B.c) := inferInstance
  have hch : HasChainColimitsLE (κ X hX) (X ⟶ B.c) := fun _ _ _ _ _ => inferInstance
  have : (postcomp X E.e).IsRightAdjoint :=
    (B.postcomp_e_isRightAdjoint_and_cocomplete E hg hg' (hcoc hX)
      (hκ X hX) (hf X hX) (hf' X hX)).1
  obtain ⟨L₁, hL₁⟩ := h1
  obtain ⟨L₂, hL₂⟩ := h2
  have h1' : ∃ L : LeftExt k ((d ≫ E.e) ≫ B.ins.u), Nonempty (IsInitial L) :=
    ⟨(LeftExt.reindex k (Category.assoc d E.e B.ins.u).symm).obj L₁, isInitial_reindex k _ hL₁⟩
  have h2' : ∃ L : LeftExt k (((d ≫ E.e) ≫ B.ins.u) ≫ B.f), Nonempty (IsInitial L) :=
    ⟨(LeftExt.reindex k (by rw [Category.assoc d E.e B.ins.u])).obj L₂, isInitial_reindex k _ hL₂⟩
  have hins := (Inserter.push_isRightAdjoint_and_exists_leftKan B.ins k (d ≫ E.e)
    hg (hκ X hX) hch (hf X hX) h1' h2').2
  exact Equifier.exists_leftKan_of_isRightAdjoint E k d hins

end Paper.BialgDatum

end UlmerBialgebras
