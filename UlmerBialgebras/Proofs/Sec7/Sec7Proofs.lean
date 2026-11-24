module

public import UlmerBialgebras.Proofs.Sec6.Sec6Proofs

/-! # Solution: Section 7

Proofs on density, monadicity and local presentability.

## Main results

* `UlmerBialgebras.Paper.yoneda_biDense`: Section 7.1: the class of all objects is bi-dense.
* `UlmerBialgebras.Paper.thm_7_4`: Theorem 7.4: for bi-dense `A`, if `d` has and `g : d ⟶ c`
  preserves right Kan extensions along 1-cells between objects of `A`, and `g` is an `A`-right
  adjoint, then `g` is a right adjoint.
* `UlmerBialgebras.Paper.cor_7_5`: Corollary 7.5: an `A`-accessible 1-cell `g : d ⟶ c` is a right
  adjoint if `d` is right `𝒜`-locally presentable and `g` is `𝒜`-continuous, and a left adjoint if
  `d` is left `𝒜`-locally presentable and `g` is `𝒜`-cocontinuous.
* `UlmerBialgebras.Paper.thm_7_6`, `UlmerBialgebras.Paper.thm_7_6_monadic`: Theorem 7.6: under its
  hypotheses, `u_B` is monadic, a 1-cell `d : I ⟶ Bialg(B)` has a left Kan extension along
  `k : I ⟶ X` with `X` in `A` whenever `d ≫ u_B` and `d ≫ u_B ≫ f` do, and `Bialg(B)` is
  `A`-cocomplete, in any strict 2-category.
* `UlmerBialgebras.Paper.thm_7_7`, `UlmerBialgebras.Paper.thm_7_7_monadic`: Theorem 7.7: for
  `A`-accessible `f, f', g, g'`, if `c` has and `g, g'` preserve `𝒜`-limits, then `u_B` is
  `A`-accessible and monadic and `Bialg(B)` is right `𝒜`-locally presentable; if `c` has and `f, f'`
  preserve `𝒜`-colimits, then `u_B` is `A`-accessible and comonadic and `Bialg(B)` is left
  `𝒜`-locally presentable, in any strict 2-category.

The checked statements hold in any strict 2-category, without PIE completeness, which goes beyond
the paper.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 7.1,
  Theorem 7.4, Corollary 7.5 and Theorems 7.6 and 7.7
-/

@[expose] public section

universe u v w u' v' w₀ w₁ u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 7: monadicity and local presentability in 2-categories -/

section Sec7

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Section 7.1** ([forsman2026syntactic]): by the bicategorical Yoneda lemma, the class of all
objects is bi-dense. -/
theorem yoneda_biDense : IsBiDense (⊤ : ObjectProperty Obj) :=
  -- Argument: every object is a retract of itself, and the extra
  -- field `nat₂` of `PsFamily` is exactly `AHomFamily.IsCellCompatible`.
  ⟨isACellDense_of_aRetractive aRetractive_true, fun d _ G =>
    ⟨G.toAHomFamily.retractRepresentation trivial (Retract.refl d) G.nat₂⟩⟩

/-- **Theorem 7.4** ([forsman2026syntactic]): if `A` is bi-dense, `d` has and `g` preserves all
right Kan extensions along 1-cells of `𝒜`, and `g` is an `A`-right adjoint, then `g` is a right
adjoint. -/
theorem thm_7_4 (A : ObjectProperty Obj) (hA : IsBiDense A) {c d : Obj} (g : d ⟶ c)
    (hd : HasARightKan A d)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesRightKan k e g)
    (hadj : IsARightAdjoint A g) :
    ∃ f : c ⟶ d, Nonempty (TwoAdj f g) :=
  exists_leftAdjoint_of_isARightAdjoint A hA g hd hg hadj

/-- An equivalence of categories is an accessible functor (it preserves all colimits). -/
lemma isAccessible_of_isEquivalence {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (F : C ⥤ D) [F.IsEquivalence] : Functor.IsAccessible.{w₀} F := by
  have : Fact Cardinal.aleph0.{w₀}.IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : F.IsCardinalAccessible Cardinal.aleph0.{w₀} := ⟨fun J _ _ => inferInstance⟩
  exact Functor.isAccessible_of_isCardinalAccessible F Cardinal.aleph0.{w₀}

/-- An accessible category with `w₀`-small limits has `w₀`-small colimits, for any hom
universe. -/
theorem hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits_general {C : Type u₁}
    [Category.{v₁} C] [IsAccessibleCategory.{w₀} C] [HasLimitsOfSize.{w₀, w₀} C] :
    HasColimitsOfSize.{w₀, w₀} C := by
  let e := ShrinkHoms.equivalence.{w₀} C
  have := e.isAccessibleCategory.{w₀}
  have : HasLimitsOfSize.{w₀, w₀} (ShrinkHoms C) := Adjunction.has_limits_of_equivalence e.inverse
  have := hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits (ShrinkHoms C)
  exact Adjunction.has_colimits_of_equivalence e.functor

/-- An accessible category with `w₀`-small colimits is locally presentable, for any hom
universe. -/
theorem isLocallyPresentable_of_hasColimits_general {C : Type u₁} [Category.{v₁} C]
    [IsAccessibleCategory.{w₀} C] [HasColimitsOfSize.{w₀, w₀} C] :
    IsLocallyPresentable.{w₀} C := by
  let e := ShrinkHoms.equivalence.{w₀} C
  have := e.isAccessibleCategory.{w₀}
  have : HasColimitsOfSize.{w₀, w₀} (ShrinkHoms C) :=
    Adjunction.has_colimits_of_equivalence e.inverse
  have : IsLocallyPresentable.{w₀} (ShrinkHoms C) := isLocallyPresentable_of_hasColimits _
  exact e.symm.isLocallyPresentable

/-- **Theorem 5.10 (2)** ([forsman2026syntactic]) for categories with hom-types in any universe:
only local `w₀`-smallness is used. -/
theorem isRightAdjoint_of_isAccessible_general {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [IsLocallyPresentable.{w₀} C] [IsAccessibleCategory.{w₀} D] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w₀, w₀} F] [Functor.IsAccessible.{w₀} F] : F.IsRightAdjoint := by
  let eC := ShrinkHoms.equivalence.{w₀} C
  let eD := ShrinkHoms.equivalence.{w₀} D
  have := eC.isLocallyPresentable.{w₀}
  have := eD.isAccessibleCategory.{w₀}
  have := isAccessible_of_isEquivalence.{w₀} eC.inverse
  have := isAccessible_of_isEquivalence.{w₀} eD.functor
  have : (eC.inverse ⋙ F ⋙ eD.functor).IsRightAdjoint := thm_5_10_2 (eC.inverse ⋙ F ⋙ eD.functor)
  have e2 : F ⋙ (eD.functor ⋙ eD.inverse) ≅ F :=
    Functor.isoWhiskerLeft F eD.unitIso.symm ≪≫ Functor.rightUnitor F
  have e1 : F ≅ (eC.functor ⋙ eC.inverse) ⋙ F :=
    (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight eC.unitIso F
  exact Functor.isRightAdjoint_of_iso
    ((Functor.isoWhiskerLeft (eC.functor ⋙ eC.inverse) e2 ≪≫ e1.symm :
      eC.functor ⋙ (eC.inverse ⋙ F ⋙ eD.functor) ⋙ eD.inverse ≅ F))

/-- **Theorem 5.10 (1)** ([forsman2026syntactic]) for categories with hom-types in any universe. -/
theorem isLeftAdjoint_of_preservesColimits_general {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] [IsLocallyPresentable.{w₀} C] [LocallySmall.{w₀} D] (F : C ⥤ D)
    [PreservesColimitsOfSize.{w₀, w₀} F] : F.IsLeftAdjoint := by
  let eC := ShrinkHoms.equivalence.{w₀} C
  have := eC.isLocallyPresentable.{w₀}
  have : (eC.inverse ⋙ F).IsLeftAdjoint := thm_5_10_1 (eC.inverse ⋙ F)
  exact Functor.isLeftAdjoint_of_iso
    ((Functor.isoWhiskerRight eC.unitIso.symm F ≪≫ Functor.leftUnitor F :
      eC.functor ⋙ (eC.inverse ⋙ F) ≅ F))

/-- **Corollary 7.5** ([forsman2026syntactic]): an `A`-accessible 1-cell out of a right `𝒜`-locally
presentable object that is `𝒜`-continuous is a right adjoint; dually for left adjoints. -/
theorem cor_7_5 (A : ObjectProperty Obj) (hA : IsBiDense A) {c d : Obj} (g : d ⟶ c)
    (hacc : IsAAccessibleMor'.{w₀} A g) :
    (IsRightALocPres.{w₀} A d → IsCalAContinuous.{w₀} A g →
        ∃ f : c ⟶ d, Nonempty (TwoAdj f g)) ∧
      (IsLeftALocPres.{w₀} A d → IsCalACocontinuous.{w₀} A g →
        ∃ h : c ⟶ d, Nonempty (TwoAdj g h)) := by
  constructor
  · rintro ⟨hd_acc, hd_comp, hd_kan⟩ ⟨hg_cont, hg_kan⟩
    refine thm_7_4 A hA g hd_kan hg_kan (fun a ha => ?_)
    have : IsAccessibleCategory.{w₀} (a ⟶ d) := hd_acc ha
    have : IsAccessibleCategory.{w₀} (a ⟶ c) := (hacc ha).2.1
    have : Functor.IsAccessible.{w₀} (postcomp a g) := (hacc ha).2.2
    have : HasLimitsOfSize.{w₀, w₀} (a ⟶ d) := hd_comp ha
    have : HasColimitsOfSize.{w₀, w₀} (a ⟶ d) :=
      hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits_general
    have : IsLocallyPresentable.{w₀} (a ⟶ d) := isLocallyPresentable_of_hasColimits_general
    have : PreservesLimitsOfSize.{w₀, w₀} (postcomp a g) := hg_cont ha
    exact isRightAdjoint_of_isAccessible_general (postcomp a g)
  · rintro ⟨hd_acc, hd_cocomp, hd_kan⟩ ⟨hg_cocont, hg_kan⟩
    refine exists_rightAdjoint_of_isALeftAdjoint A hA g hd_kan hg_kan (fun a ha => ?_)
    have : IsAccessibleCategory.{w₀} (a ⟶ d) := hd_acc ha
    have : IsAccessibleCategory.{w₀} (a ⟶ c) := (hacc ha).2.1
    have : HasColimitsOfSize.{w₀, w₀} (a ⟶ d) := hd_cocomp ha
    have : IsLocallyPresentable.{w₀} (a ⟶ d) := isLocallyPresentable_of_hasColimits_general
    have : LocallySmall.{w₀} (a ⟶ c) := inferInstance
    have : PreservesColimitsOfSize.{w₀, w₀} (postcomp a g) := hg_cocont ha
    exact isLeftAdjoint_of_preservesColimits_general (postcomp a g)

/-! ### Theorems 7.6 and 7.7 -/

/-- **Theorem 7.6** ([forsman2026syntactic]) (Kan extension and cocompleteness clauses; the
monadicity clause is `thm_7_6_monadic`). -/
theorem thm_7_6 (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt), A X →
      (∃ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L)) →
      (∃ L : LeftExt k ((d ≫ B.uB E) ≫ B.f), Nonempty (IsInitial L)) →
        ∃ L : LeftExt k d, Nonempty (IsInitial L)) ∧
      IsACocomplete.{w₀} A E.pt :=
  B.exists_initial_leftExt_and_isACocomplete A E hg hg' hcoc κ hκ hf hf'

/-- **Theorem 7.6** ([forsman2026syntactic]), monadicity clause: under the hypotheses of `thm_7_6`,
`u_B` is monadic. -/
theorem thm_7_6_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c) (hRan : HasARightKan A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    IsMonadic2 (B.uB E) :=
  B.isMonadic2_uB_of_isBiDense A E hA hg hg' hcoc hRan κ hκ hf hf'

/-- **Theorem 7.7** ([forsman2026syntactic]) (local presentability and accessibility clauses; the
(co)monadicity clauses are `thm_7_7_monadic`). -/
theorem thm_7_7 (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₁} A B.c → IsCalAContinuous.{w₁} A B.g → IsCalAContinuous.{w₁} A B.g' →
      IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt ∧
        IsCalAComplete.{w₁} A E.pt) ∧
    (IsCalACocomplete.{w₁} A B.c → IsCalACocontinuous.{w₁} A B.f →
      IsCalACocontinuous.{w₁} A B.f' →
      IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt ∧
        IsCalACocomplete.{w₁} A E.pt) := by
  obtain ⟨huB_acc, hE_acc⟩ := B.uB_isAAccessibleMor' E hf hf' hg hg'
  refine ⟨fun ⟨hc_lim, hc_kan⟩ ⟨hg_lim, hg_kan⟩ ⟨hg'_lim, hg'_kan⟩ => ?_,
    fun ⟨hc_colim, hc_kan⟩ ⟨hf_colim, hf_kan⟩ ⟨hf'_colim, hf'_kan⟩ => ?_⟩
  · exact ⟨huB_acc, hE_acc,
      (B.uB_isAComplete_and_continuous E hc_lim hg_lim hg'_lim).1,
      (B.uB_hasAndPreservesARightKan E hc_kan hg_kan hg'_kan).1⟩
  · exact ⟨huB_acc, hE_acc,
      (B.uB_isACocomplete_and_cocontinuous E hc_colim hf_colim hf'_colim).1,
      (B.uB_hasAndPreservesALeftKan E hc_kan hf_kan hf'_kan).1⟩

/-- **Theorem 7.7** ([forsman2026syntactic]), (co)monadicity clauses: (1) if `c` has and `g, g'`
preserve `𝒜`-limits, `u_B` is monadic; (2) if `c` has and `f, f'` preserve `𝒜`-colimits, `u_B` is
comonadic. -/
theorem thm_7_7_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₀} A B.c → IsCalAContinuous.{w₀} A B.g → IsCalAContinuous.{w₀} A B.g' →
      IsMonadic2 (B.uB E)) ∧
    (IsCalACocomplete.{w₀} A B.c → IsCalACocontinuous.{w₀} A B.f → IsCalACocontinuous.{w₀} A B.f' →
      IsComonadic2 (B.uB E)) := by
  obtain ⟨huB_acc, hE_acc⟩ := B.uB_isAAccessibleMor' E hf hf' hg hg'
  refine ⟨fun ⟨hc_lim, hc_kan⟩ ⟨hg_lim, hg_kan⟩ ⟨hg'_lim, hg'_kan⟩ => ?_,
    fun ⟨hc_colim, hc_kan⟩ ⟨hf_colim, hf_kan⟩ ⟨hf'_colim, hf'_kan⟩ => ?_⟩
  · obtain ⟨hE_lim, huB_lim⟩ := B.uB_isAComplete_and_continuous E hc_lim hg_lim hg'_lim
    obtain ⟨hE_kan, huB_kan⟩ := B.uB_hasAndPreservesARightKan E hc_kan hg_kan hg'_kan
    exact B.isMonadic2_uB_of_twoAdj E
      ((cor_7_5 A hA (B.uB E) huB_acc).1 ⟨hE_acc, hE_lim, hE_kan⟩ ⟨huB_lim, huB_kan⟩)
  · obtain ⟨hE_colim, huB_colim⟩ :=
      B.uB_isACocomplete_and_cocontinuous E hc_colim hf_colim hf'_colim
    obtain ⟨hE_kan, huB_kan⟩ := B.uB_hasAndPreservesALeftKan E hc_kan hf_kan hf'_kan
    exact B.isComonadic2_uB_of_twoAdj E
      ((cor_7_5 A hA (B.uB E) huB_acc).2 ⟨hE_acc, hE_colim, hE_kan⟩ ⟨huB_colim, huB_kan⟩)

end Sec7


end UlmerBialgebras.Paper
