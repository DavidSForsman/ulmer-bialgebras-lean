module

public import UlmerBialgebras.Proofs.Sec5.CatTwoBridge
public import UlmerBialgebras.Proofs.Sec5.Sec7Sharp
public import UlmerBialgebras.Kan.KanId

/-!
# Theorem 5.11 as the case `K = CAT`, `A = {1}` of the sharpened Theorem 7.7

The class `{1}` is bi-dense in `Cat.{v, u}` (`UlmerBialgebras.Paper.isBiDense_one`), and the
`{1}`-properties of objects and 1-cells of `CAT` are the ordinary ones
(`UlmerBialgebras/Proofs/Sec5/CatTwoBridge.lean`; accessibility and joint (co)monicness are
transported here). The
Kan-extension parts of `𝒜`-(co)completeness and `𝒜`-(co)continuity are automatic, since the only
1-cell `1 ⟶ 1` is the identity and Kan extensions along an identity are the extensions with
invertible (co)unit. So the sharpened Theorem 7.7
(`UlmerBialgebras.Paper.isAAccessible_bialg_of_jointMono`,
`UlmerBialgebras.Paper.isMonadic2_uB_of_jointMono`) specialises to Theorem 5.11
(`UlmerBialgebras.Paper.uB_comonadic_monadic_of_jointMono_cat`), with the same hypotheses and
conclusions as the checked `UlmerBialgebras.Paper.thm_5_11`.

## Main results

* `UlmerBialgebras.Paper.CatTwo.hasARightKan_one`, `UlmerBialgebras.Paper.CatTwo.hasALeftKan_one`,
  `UlmerBialgebras.Paper.CatTwo.preservesRightKan_one`,
  `UlmerBialgebras.Paper.CatTwo.preservesLeftKan_one`: Kan extensions along `{1}` in `CAT` exist and
  are preserved.
* `UlmerBialgebras.Paper.CatTwo.isAAccessibleObj_one_iff`,
  `UlmerBialgebras.Paper.CatTwo.isAAccessibleMor'_one_iff`: `{1}`-accessibility is accessibility.
* `UlmerBialgebras.Paper.CatTwo.isAJointMonoMor_one`,
  `UlmerBialgebras.Paper.CatTwo.isAJointEpiMor_one`: joint (co)monicness transported to `CAT(1, -)`.
* `UlmerBialgebras.Paper.uB_comonadic_monadic_of_jointMono_cat`: Theorem 5.11, derived from the
  sharpened Theorem 7.7.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.11,
  Theorem 7.7, Definition 7.1 and Section 7.1 (the case `K = CAT`, `A = {1}`)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.CatTwo

open CategoryTheory UlmerBialgebras Limits

/-! ## Kan extensions along the identity of `1` -/

section Kan

variable {X c : Cat.{v, u}} {e : X ⟶ c}

/-- Right Kan extensions along the 1-cells of `{1}` exist in `CAT`. -/
theorem hasARightKan_one (c : Cat.{v, u}) :
    HasARightKan (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) c := by
  intro i x hi hx k d
  subst hi; subst hx
  obtain rfl := eq_id₁_of_one k
  have : IsIso (RightExt.idExt d).counit := inferInstanceAs (IsIso (𝟙 d))
  exact ⟨_, ⟨RightExt.isTerminalOfIsIsoCounit (RightExt.idExt d)⟩⟩

/-- Left Kan extensions along the 1-cells of `{1}` exist in `CAT`. -/
theorem hasALeftKan_one (c : Cat.{v, u}) :
    HasALeftKan (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) c := by
  intro i x hi hx k d
  subst hi; subst hx
  obtain rfl := eq_id₁_of_one k
  have : IsIso (LeftExt.idExt d).unit := inferInstanceAs (IsIso (𝟙 d))
  exact ⟨_, ⟨LeftExt.isInitialOfIsIsoUnit (LeftExt.idExt d)⟩⟩

/-- Every 1-cell of `CAT` preserves the right Kan extensions along the 1-cells of `{1}`. -/
theorem preservesRightKan_one {c c' : Cat.{v, u}} (g : c ⟶ c') :
    ∀ ⦃i x : Cat.{v, u}⦄, i = One.{v, u} → x = One.{v, u} → ∀ (k : i ⟶ x) (e : i ⟶ c),
      PreservesRightKan k e g := by
  intro i x hi hx k e
  subst hi; subst hx
  obtain rfl := eq_id₁_of_one k
  exact preservesRightKan_id g

/-- Every 1-cell of `CAT` preserves the left Kan extensions along the 1-cells of `{1}`. -/
theorem preservesLeftKan_one {c c' : Cat.{v, u}} (f : c ⟶ c') :
    ∀ ⦃i x : Cat.{v, u}⦄, i = One.{v, u} → x = One.{v, u} → ∀ (k : i ⟶ x) (e : i ⟶ c),
      PreservesLeftKan k e f := by
  intro i x hi hx k e
  subst hi; subst hx
  obtain rfl := eq_id₁_of_one k
  exact preservesLeftKan_id f

end Kan

/-! ## Accessibility and joint (co)monicness along `CAT(1, C) ≃ C` -/

section Transport

variable {c d : Cat.{v, u}}

/-- Accessibility of functors is invariant under natural isomorphism. -/
lemma isAccessible_of_natIso.{w₀, u₁, v₁, u₂, v₂} {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] {F G : C₁ ⥤ C₂} (e : F ≅ G)
    [Functor.IsAccessible.{w₀} F] : Functor.IsAccessible.{w₀} G := by
  obtain ⟨κ, hκ, hF⟩ := Functor.IsAccessible.exists_cardinal (F := F)
  exact ⟨κ, hκ, Functor.isCardinalAccessible_of_natIso e κ⟩

/-- An object of `CAT` is `{1}`-accessible if and only if it is accessible. -/
theorem isAAccessibleObj_one_iff.{w₀} (c : Cat.{v, u}) :
    IsAAccessibleObj.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) c ↔
      IsAccessibleCategory.{w₀} c := by
  refine ⟨fun h => ?_, fun h a ha => ?_⟩
  · have : IsAccessibleCategory.{w₀} (One.{v, u} ⟶ c) := h rfl
    exact isAccessibleCategory_of_isEquivalence' (homOneEval c).asEquivalence.inverse
  · subst ha
    exact isAccessibleCategory_of_isEquivalence' (homOneEval c)

/-- A 1-cell of `CAT` is `{1}`-accessible if and only if it is an accessible functor between
accessible categories. -/
theorem isAAccessibleMor'_one_iff.{w₀} (f : c ⟶ d) :
    IsAAccessibleMor'.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) f ↔
      IsAccessibleCategory.{w₀} c ∧ IsAccessibleCategory.{w₀} d ∧
        Functor.IsAccessible.{w₀} f.toFunctor := by
  refine ⟨fun h => ?_, fun ⟨hc, hd, hf⟩ a ha => ?_⟩
  · obtain ⟨hc, hd, hf⟩ := h rfl
    refine ⟨isAccessibleCategory_of_isEquivalence' (homOneEval c).asEquivalence.inverse,
      isAccessibleCategory_of_isEquivalence' (homOneEval d).asEquivalence.inverse, ?_⟩
    have : Functor.IsAccessible.{w₀} (homOneEval c ⋙ f.toFunctor) := by
      rw [← postcomp_one_comp_homOneEval]; infer_instance
    exact isAccessible_of_natIso
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (homOneEval c).asEquivalence.counitIso f.toFunctor ≪≫
        Functor.leftUnitor _ :
        (homOneEval c).asEquivalence.inverse ⋙ (homOneEval c ⋙ f.toFunctor) ≅ _)
  · subst ha
    refine ⟨isAccessibleCategory_of_isEquivalence' (homOneEval c),
      isAccessibleCategory_of_isEquivalence' (homOneEval d), ?_⟩
    have : Functor.IsAccessible.{w₀} (postcomp One.{v, u} f ⋙ homOneEval d) := by
      rw [postcomp_one_comp_homOneEval]; infer_instance
    exact isAccessible_of_natIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (homOneEval d).asEquivalence.unitIso.symm ≪≫
        Functor.rightUnitor _ :
        (postcomp One.{v, u} f ⋙ homOneEval d) ⋙ (homOneEval d).asEquivalence.inverse ≅ _)

/-- If `g` preserves the joint monicness of small limiting cones, so does `CAT(1, g)`. -/
lemma postcomp_one_preservesJointMonoOfShape {J : Type*} [Category J] (g : c ⟶ d)
    (hg : PreservesJointMonoOfShape J g.toFunctor) :
    PreservesJointMonoOfShape J (postcomp One.{v, u} g) := by
  intro Kd s hs y p q hpq
  refine natTrans_one_ext ?_
  exact hg (Kd ⋙ homOneEval c) _ (isLimitOfPreserves (homOneEval c) hs) _ _ fun j =>
    congr(($(hpq j)).toNatTrans.app One.star)

/-- If `f` preserves the joint epicness of small colimiting cocones, so does `CAT(1, f)`. -/
lemma postcomp_one_preservesJointEpiOfShape {J : Type*} [Category J] (f : c ⟶ d)
    (hf : PreservesJointEpiOfShape J f.toFunctor) :
    PreservesJointEpiOfShape J (postcomp One.{v, u} f) := by
  intro Kd s hs y p q hpq
  refine natTrans_one_ext ?_
  exact hf (Kd ⋙ homOneEval c) _ (isColimitOfPreserves (homOneEval c) hs) _ _ fun j =>
    congr(($(hpq j)).toNatTrans.app One.star)

/-- A functor preserving the joint monicness of small limiting cones satisfies the hypotheses
`IsAJointMonoMor` of the sharpened Theorem 7.7 for `{1}` in `CAT`. -/
theorem isAJointMonoMor_one.{w₀} (g : c ⟶ d)
    (hg : ∀ (J : Type w₀) [SmallCategory J], PreservesJointMonoOfShape J g.toFunctor) :
    IsAJointMonoMor.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) g := by
  refine ⟨fun a ha J _ => ?_, fun i x hi hx k e R hR =>
    subterminal_of_isTerminal (preservesRightKan_one g hi hx k e R hR).some⟩
  subst ha
  exact postcomp_one_preservesJointMonoOfShape g (hg J)

/-- A functor preserving the joint epicness of small colimiting cocones satisfies the hypotheses
`IsAJointEpiMor` of the sharpened Theorem 7.7 for `{1}` in `CAT`. -/
theorem isAJointEpiMor_one.{w₀} (f : c ⟶ d)
    (hf : ∀ (J : Type w₀) [SmallCategory J], PreservesJointEpiOfShape J f.toFunctor) :
    IsAJointEpiMor.{w₀} (Obj := Cat.{v, u}) (fun X => X = One.{v, u}) f := by
  refine ⟨fun a ha J _ => ?_, fun i x hi hx k e L hL =>
    quotientInitial_of_isInitial (preservesLeftKan_one f hi hx k e L hL).some⟩
  subst ha
  exact postcomp_one_preservesJointEpiOfShape f (hf J)

end Transport

end UlmerBialgebras.Paper.CatTwo

namespace UlmerBialgebras.Paper

open CategoryTheory UlmerBialgebras Limits CatTwo

/-- **Theorem 5.11** ([forsman2026syntactic]), derived from the sharpened Theorem 7.7
(`isAAccessible_bialg_of_jointMono`, `isMonadic2_uB_of_jointMono`) with `K = Cat.{w, u}` and the
bi-dense class `A = {1}` (`isBiDense_one`). The statement is that of the checked `thm_5_11`. -/
theorem uB_comonadic_monadic_of_jointMono_cat (B : BialgDatum (Obj := Cat.{w, u}))
    (E : Equifier B.α B.β)
    [IsLocallyPresentable.{w} (B.c : Type u)]
    [IsAccessibleCategory.{w} (B.x : Type u)] [IsAccessibleCategory.{w} (B.y : Type u)]
    [Functor.IsAccessible.{w} (B.f).toFunctor]
    [Functor.IsAccessible.{w} (B.g).toFunctor]
    [Functor.IsAccessible.{w} (B.f').toFunctor]
    [Functor.IsAccessible.{w} (B.g').toFunctor] :
    (IsAccessibleCategory.{w} (E.pt : Type u) ∧
      Functor.IsAccessible.{w} (B.uB E).toFunctor) ∧
    ((PreservesLimitsOfSize.{w, w} (B.g).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointMonoOfShape J (B.g').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (MonadicRightAdjoint (B.uB E).toFunctor)) ∧
    ((PreservesColimitsOfSize.{w, w} (B.f).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointEpiOfShape J (B.f').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (ComonadicLeftAdjoint (B.uB E).toFunctor)) := by
  have hacc : ∀ {a b : Cat.{w, u}} (h : a ⟶ b) [IsAccessibleCategory.{w} a]
      [IsAccessibleCategory.{w} b] [Functor.IsAccessible.{w} h.toFunctor],
      IsAAccessibleMor'.{w} (fun X => X = One.{w, u}) h :=
    by
      intro a b h _ _ _
      exact (isAAccessibleMor'_one_iff h).2 ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨huB, hE⟩, h1, h2⟩ :=
    isAAccessible_bialg_of_jointMono _ B E (hacc B.f) (hacc B.f') (hacc B.g) (hacc B.g')
  obtain ⟨m1, m2⟩ := isMonadic2_uB_of_jointMono _ isBiDense_one B E
    (hacc B.f) (hacc B.f') (hacc B.g) (hacc B.g')
  have hEacc : IsAccessibleCategory.{w} (E.pt : Type u) :=
    (isAAccessibleObj_one_iff E.pt).1 hE
  refine ⟨⟨hEacc, ((isAAccessibleMor'_one_iff _).1 huB).2.2⟩, fun ⟨hg, hg'⟩ => ?_,
    fun ⟨hf, hf'⟩ => ?_⟩
  · have hc : IsCalAComplete.{w} (fun X => X = One.{w, u}) B.c :=
      ⟨(isAComplete_one_iff B.c).2 (hasLimitsOfSize_of_isLocallyPresentable _),
        hasARightKan_one B.c⟩
    have hgc : IsCalAContinuous.{w} (fun X => X = One.{w, u}) B.g :=
      ⟨(isAContinuous_one_iff B.g).2 hg, preservesRightKan_one B.g⟩
    have hg'm := isAJointMonoMor_one B.g' hg'
    obtain ⟨⟨-, hElim, -⟩, -⟩ := h1 hc hgc hg'm
    have : HasLimitsOfSize.{w, w} (E.pt : Type u) := (isAComplete_one_iff E.pt).1 hElim
    exact ⟨isLocallyPresentable_of_isAccessibleCategory _ (Or.inl this),
      (isMonadic2_iff _).1 (m1 hc hgc hg'm)⟩
  · have hc : IsCalACocomplete.{w} (fun X => X = One.{w, u}) B.c :=
      ⟨(isACocomplete_one_iff B.c).2 (hasColimitsOfSize_of_isLocallyPresentable _),
        hasALeftKan_one B.c⟩
    have hfc : IsCalACocontinuous.{w} (fun X => X = One.{w, u}) B.f :=
      ⟨(isACocontinuous_one_iff B.f).2 hf, preservesLeftKan_one B.f⟩
    have hf'm := isAJointEpiMor_one B.f' hf'
    obtain ⟨⟨-, hEcolim, -⟩, -⟩ := h2 hc hfc hf'm
    have : HasColimitsOfSize.{w, w} (E.pt : Type u) := (isACocomplete_one_iff E.pt).1 hEcolim
    exact ⟨isLocallyPresentable_of_isAccessibleCategory _ (Or.inr this),
      (isComonadic2_iff _).1 (m2 hc hfc hf'm)⟩

end UlmerBialgebras.Paper
