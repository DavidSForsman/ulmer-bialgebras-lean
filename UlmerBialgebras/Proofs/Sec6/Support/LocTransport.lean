module

public import UlmerBialgebras.Paper.Sec3DefsLoc
public import UlmerBialgebras.Paper.Sec6DefsLoc
public import UlmerBialgebras.Models.UniverseChangeSig

/-!
# `Mod_R` in `Cat.{u + 1, u + 1}` is the change of universe of `Mod_R` in `Cat.{u, u + 1}`

The `Σ_SMon`-model `Loc.modModel R = smonModel (ModU R)` of Lemma 6.10, where `ModU R` lifts the
morphisms of `ModuleCat.{u} R` with `ULiftHom` and transports the monoidal structure, is the
change of universe `upModel` of the `Σ_SMon`-model `smonModel (ModuleCat.{u} R)` in
`Cat.{u, u + 1}` (`UlmerBialgebras.Paper.Loc.modModel_eq`). The structure 2-cells agree because
the transported associator, unitors and braiding of `ModU R` are the lifted ones.

## Main results

* `UlmerBialgebras.Paper.Loc.modModel_eq`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory UlmerBialgebras.UnivChange
open scoped CategoryTheory.Bicategory

namespace UlmerBialgebras.Paper.Loc

variable (R : Type u) [CommRing R]
/-- An object of `ModuleCat R` as an object of `ModU R`. -/
def upM (X : ModuleCat.{u} R) : ModU R := ULiftHom.objUp X
/-- The inverse associator of `ModU R` is the lifted inverse associator of `ModuleCat R`. -/
lemma l_assocInv (X Y Z : ModuleCat.{u} R) :
    ULift.down (α_ (upM R X) (upM R Y) (upM R Z)).inv = (α_ X Y Z).inv := by
  change (X ◁ 𝟙 (Y ⊗ Z) ≫ (α_ X Y Z).inv ≫ 𝟙 (X ⊗ Y) ▷ Z) = _
  simp
/-- The inverse left unitor of `ModU R` is the lifted inverse left unitor of `ModuleCat R`. -/
lemma l_lunitInv (X : ModuleCat.{u} R) : ULift.down (λ_ (upM R X)).inv = (λ_ X).inv := by
  change 𝟙 X ≫ (λ_ X).inv ≫ 𝟙 (𝟙_ _) ▷ X = _
  simp
/-- The inverse right unitor of `ModU R` is the lifted inverse right unitor of `ModuleCat R`. -/
lemma l_runitInv (X : ModuleCat.{u} R) : ULift.down (ρ_ (upM R X)).inv = (ρ_ X).inv := by
  change 𝟙 X ≫ (ρ_ X).inv ≫ X ◁ 𝟙 (𝟙_ _) = _
  simp
/-- The associator of `ModU R` is the lifted associator of `ModuleCat R`. -/
lemma l_assoc (X Y Z : ModuleCat.{u} R) :
    ULift.down (α_ (upM R X) (upM R Y) (upM R Z)).hom = (α_ X Y Z).hom := by
  change (𝟙 (X ⊗ Y) ▷ Z ≫ (α_ X Y Z).hom ≫ X ◁ 𝟙 (Y ⊗ Z)) = _
  simp
/-- The left unitor of `ModU R` is the lifted left unitor of `ModuleCat R`. -/
lemma l_lunit (X : ModuleCat.{u} R) : ULift.down (λ_ (upM R X)).hom = (λ_ X).hom := by
  change (𝟙 (𝟙_ _) ▷ X ≫ (λ_ X).hom) ≫ 𝟙 X = _
  simp
/-- The right unitor of `ModU R` is the lifted right unitor of `ModuleCat R`. -/
lemma l_runit (X : ModuleCat.{u} R) : ULift.down (ρ_ (upM R X)).hom = (ρ_ X).hom := by
  change (X ◁ 𝟙 (𝟙_ _) ≫ (ρ_ X).hom) ≫ 𝟙 X = _
  simp
/-- The braiding of `ModU R` is the lifted braiding of `ModuleCat R`. -/
lemma l_sym (X Y : ModuleCat.{u} R) :
    ULift.down (β_ (upM R X) (upM R Y)).hom = (β_ X Y).hom := rfl

/-- The `assoc` 2-cell of `modModel R` agrees with that of `upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_assoc : HEq ((modModel R).tr .assoc)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .assoc) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_assoc R _ _ _)

/-- The `assocInv` 2-cell of `modModel R` agrees with that of
`upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_assocInv : HEq ((modModel R).tr .assocInv)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .assocInv) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_assocInv R _ _ _)

/-- The `lunit` 2-cell of `modModel R` agrees with that of `upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_lunit : HEq ((modModel R).tr .lunit)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .lunit) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_lunit R _)

/-- The `lunitInv` 2-cell of `modModel R` agrees with that of
`upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_lunitInv : HEq ((modModel R).tr .lunitInv)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .lunitInv) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_lunitInv R _)

/-- The `runit` 2-cell of `modModel R` agrees with that of `upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_runit : HEq ((modModel R).tr .runit)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .runit) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_runit R _)

/-- The `runitInv` 2-cell of `modModel R` agrees with that of
`upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_runitInv : HEq ((modModel R).tr .runitInv)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .runitInv) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_runitInv R _)

/-- The `sym` 2-cell of `modModel R` agrees with that of `upModel (smonModel (ModuleCat R))`. -/
lemma modModel_tr_sym : HEq ((modModel R).tr .sym)
    ((upModel.{u, u + 1} (smonModel (ModuleCat.{u} R))).tr .sym) := by
  rw [upModel_tr]
  refine ConjEq.heq ?_
  refine ConjEq.trans ?_ (ConjEq.conj _ _ _).symm
  apply ConjEq.of_eq
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext p
  exact ULift.ext (l_sym R _ _)

/-- `modModel R` is equal to the universe-lifted `smonModel (ModuleCat.{u} R)`. -/
theorem modModel_eq : modModel R = upModel.{u, u + 1} (smonModel (ModuleCat.{u} R)) := by
  refine Model.ext_heq ?_ fun a => ?_
  · change PreModel.mk _ _ = PreModel.mk _ _
    congr 1
    funext B
    cases B <;> rfl
  · cases a
    · exact modModel_tr_assoc R
    · exact modModel_tr_assocInv R
    · exact modModel_tr_lunit R
    · exact modModel_tr_lunitInv R
    · exact modModel_tr_runit R
    · exact modModel_tr_runitInv R
    · exact modModel_tr_sym R

/-! ## Lemma 6.10 for `modModel` and for `modCatModel` -/

open Limits UnivChange.Model

section Stmt

variable (sg : OneSig SigEx.smonSig) (T : Theory sg)

/-- The statement of Lemma 6.10 for a model `MR` over `R`, models `Mp p` over `R_p` and 1-cells
`φ p` between the products of the sorts. -/
def Stmt610 (MR : Model SigEx.smonSig Cat.{w, max w (u + 1)})
    (Mp : ∀ (p : Ideal R) [p.IsMaximal], Model SigEx.smonSig Cat.{w, max w (u + 1)})
    (φ : ∀ (p : Ideal R) [p.IsMaximal], (MR.P0 sg).pt ⟶ ((Mp p).P0 sg).pt) : Prop :=
  (∃ L : ∀ (p : Ideal R) [p.IsMaximal], MR.thyObj sg T ⟶ (Mp p).thyObj sg T,
      ∀ (p : Ideal R) [p.IsMaximal], L p ≫ (Mp p).thyForget sg T = MR.thyForget sg T ≫ φ p) ∧
    ∀ L : ∀ (p : Ideal R) [p.IsMaximal], MR.thyObj sg T ⟶ (Mp p).thyObj sg T,
      (∀ (p : Ideal R) [p.IsMaximal], L p ≫ (Mp p).thyForget sg T = MR.thyForget sg T ≫ φ p) →
      (∀ ⦃X Y : (MR.thyObj sg T : Type (max w (u + 1)))⦄ (f : X ⟶ Y),
        (∀ (p : Ideal R) [p.IsMaximal], IsIso ((L p).toFunctor.map f)) → IsIso f) ∧
      (∀ (p : Ideal R) [p.IsMaximal] (J : Type u) [SmallCategory J] [IsSifted J],
        PreservesColimitsOfShape J (L p).toFunctor) ∧
      (IsVonNeumannRegularRing R → ∀ (p : Ideal R) [p.IsMaximal],
        (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsCosifted J],
          PreservesLimitsOfShape J (L p).toFunctor) ∧
        IsField (Localization.AtPrime p))

/-- Congruence of `Stmt610` along model and 1-cell equalities. -/
lemma stmt610_congr {MR MR' : Model SigEx.smonSig Cat.{w, max w (u + 1)}}
    {Mp Mp' : ∀ (p : Ideal R) [p.IsMaximal], Model SigEx.smonSig Cat.{w, max w (u + 1)}}
    {φ : ∀ (p : Ideal R) [p.IsMaximal], (MR.P0 sg).pt ⟶ ((Mp p).P0 sg).pt}
    {φ' : ∀ (p : Ideal R) [p.IsMaximal], (MR'.P0 sg).pt ⟶ ((Mp' p).P0 sg).pt}
    (hR : MR = MR') (hP : Mp = Mp') (hφ : ∀ (p : Ideal R) [p.IsMaximal], HEq (φ p) (φ' p)) :
    Stmt610 R sg T MR Mp φ ↔ Stmt610 R sg T MR' Mp' φ' := by
  subst hR hP
  obtain rfl : φ = φ' := by
    funext p hp
    exact eq_of_heq (hφ p)
  rfl

/-- Lemma 6.10 for a model in `Cat.{u, u + 1}` is equivalent to Lemma 6.10 for its change of
universe. -/
lemma stmt610_up_iff (N : Model SigEx.smonSig Cat.{u, u + 1})
    (N' : ∀ (p : Ideal R) [p.IsMaximal], Model SigEx.smonSig Cat.{u, u + 1})
    (φ : ∀ (p : Ideal R) [p.IsMaximal], (N.P0 sg).pt ⟶ ((N' p).P0 sg).pt) :
    Stmt610 R sg T (upModel.{u, u + 1} N) (fun p _ => upModel.{u, u + 1} (N' p))
        (fun p _ => upP0 (φ p)) ↔
      Stmt610 R sg T N N' φ := by
  constructor
  · rintro ⟨⟨L', hL'⟩, hU⟩
    refine ⟨⟨fun p _ => downThy (L' p), fun p _ => forget_of_upThy ?_⟩, fun L hL => ?_⟩
    · rw [upThy_downThy]
      exact hL' p
    · obtain ⟨hc, hs, hv⟩ := hU (fun p _ => upThy (L p)) (fun p _ => upThy_forget (hL p))
      refine ⟨fun X Y f hf => ?_, fun p _ J _ _ => ?_, fun hR p _ => ?_⟩
      · rw [isIso_iff_thyUp]
        exact hc _ fun p _ => (isIso_map_iff_upThy (L p) f).1 (hf p)
      · exact (preservesColimitsOfShape_upThy_iff J (L p)).1 (hs p J)
      · obtain ⟨h₁, h₂⟩ := hv hR p
        exact ⟨fun J _ _ _ => (preservesLimitsOfShape_upThy_iff J (L p)).1 (h₁ J), h₂⟩
  · rintro ⟨⟨L, hL⟩, hU⟩
    refine ⟨⟨fun p _ => upThy (L p), fun p _ => upThy_forget (hL p)⟩, fun L' hL' => ?_⟩
    have hL₂ : ∀ (p : Ideal R) [p.IsMaximal], downThy (L' p) ≫ (N' p).thyForget sg T =
        N.thyForget sg T ≫ φ p := fun p _ => forget_of_upThy (by
      rw [upThy_downThy]
      exact hL' p)
    obtain ⟨hc, hs, hv⟩ := hU (fun p _ => downThy (L' p)) hL₂
    refine ⟨fun X Y f hf => ?_, fun p _ J _ _ => ?_, fun hR p _ => ?_⟩
    · rw [isIso_iff_thyDown]
      refine hc _ fun p _ => (isIso_upThy_map_iff (downThy (L' p)) f).1 ?_
      rw [upThy_downThy]
      exact hf p
    · rw [← upThy_downThy (L' p), preservesColimitsOfShape_upThy_iff]
      exact hs p J
    · obtain ⟨h₁, h₂⟩ := hv hR p
      refine ⟨fun J _ _ _ => ?_, h₂⟩
      rw [← upThy_downThy (L' p), preservesLimitsOfShape_upThy_iff]
      exact h₁ J

/-- `locSig R sg p` is heterogeneous-equal to the universe-lifted `locSigCat R sg p`. -/
lemma locSig_heq (p : Ideal R) [p.IsPrime] :
    HEq (locSig R sg p) (upP0.{u, u + 1} (N := modCatModel R)
      (N' := modCatModel (Localization.AtPrime p)) (locSigCat R sg p)) :=
  heq_of_eq rfl

/-- **Lemma 6.10 for `modModel` and for `modCatModel` are equivalent.** -/
theorem stmt610_modModel_iff :
    Stmt610 R sg T (modModel R) (fun p _ => modModel (Localization.AtPrime p))
        (fun p _ => locSig R sg p) ↔
      Stmt610 R sg T (modCatModel R) (fun p _ => modCatModel (Localization.AtPrime p))
        (fun p _ => locSigCat R sg p) :=
  (stmt610_congr R sg T (modModel_eq R) (funext fun _ => funext fun _ => modModel_eq _)
    fun p _ => locSig_heq R sg p).trans (stmt610_up_iff R sg T _ _ _)

end Stmt

end UlmerBialgebras.Paper.Loc
