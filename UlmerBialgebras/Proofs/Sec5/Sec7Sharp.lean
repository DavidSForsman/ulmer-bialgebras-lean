module

public import UlmerBialgebras.Proofs.Sec7.Sec7Proofs

/-!
# A sharpened Theorem 7.7: joint monicness instead of continuity of `g'`

Theorem 7.7 of [forsman2026syntactic] asks the equational coarity support `g'` to be
`𝒜`-continuous (dually, the equational arity support `f'` to be `𝒜`-cocontinuous). The proof only
uses that the hom-functors `K(a, g')`, `a ∈ A`, preserve the joint monicness of limiting cones,
and that `g'` sends right Kan extensions along `𝒜` to subterminal extensions: these are the
conditions under which the equifier `Bialg(B)` is closed under limits in the inserter (the
hom-level form of Corollary 4.8 and of the argument of Theorem 5.11). This file proves Theorem 7.7
under these weaker hypotheses, in any strict 2-category with a class `A` (bi-dense for the
(co)monadicity clauses); Theorem 5.11 is its case `K = CAT`, `A = {1}`
(`UlmerBialgebras/Proofs/Sec5/CatAccessibleMonadicity.lean`).

## Main results

* `UlmerBialgebras.Paper.equifCreatesLimitOfJointMono`,
  `UlmerBialgebras.Paper.equifCreatesColimitOfJointEpi`: an equifier of `η, θ : F ⟶ G` is closed
  under the limits jointly detected by `G` (colimits jointly detected by `F`).
* `UlmerBialgebras.Paper.BialgDatum.uB_isAComplete_and_continuous_of_jointMono` and its dual: the
  hom-level completeness of `Bialg(B)` and continuity of `u_B`.
* `UlmerBialgebras.Paper.isAAccessible_bialg_of_jointMono`: accessibility of `u_B` and right (left)
  `𝒜`-local presentability
  of `Bialg(B)` under the sharpened hypotheses.
* `UlmerBialgebras.Paper.isMonadic2_uB_of_jointMono`: if `A` is bi-dense, `u_B` is monadic
  (comonadic) under the
  sharpened hypotheses.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.7,
  Corollary 4.8 and Theorem 5.11
-/

@[expose] public section

universe u v w w₀

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Equifiers closed under jointly detected (co)limits -/

section Equif

variable {C : Type*} [Category C] {D : Type*} [Category D] {F G : C ⥤ D} {η θ : F ⟶ G}

/-- The equifier of `η, θ : F ⟶ G` is closed under the limits whose image under `G` is jointly
monic. -/
@[instance_reducible]
noncomputable def equifCreatesLimitOfJointMono {J : Type w₀} [Category J]
    (hG : PreservesJointMonoOfShape J G) (K : J ⥤ Equif η θ)
    [HasLimit (K ⋙ Equif.forget η θ)] : CreatesLimit K (Equif.forget η θ) :=
  createsLimitFullSubcategoryInclusion' K (limit.isLimit _) (by
    refine hG _ _ (limit.isLimit (K ⋙ Equif.forget η θ)) _ _ fun j => ?_
    have h : η.app (K.obj j).obj = θ.app (K.obj j).obj := (K.obj j).property
    have h1 := η.naturality (limit.π (K ⋙ Equif.forget η θ) j)
    have h2 := θ.naturality (limit.π (K ⋙ Equif.forget η θ) j)
    dsimp at h1 h2 h ⊢
    rw [← h1, ← h2, h])

/-- The equifier of `η, θ : F ⟶ G` is closed under the colimits whose image under `F` is jointly
epic. -/
@[instance_reducible]
noncomputable def equifCreatesColimitOfJointEpi {J : Type w₀} [Category J]
    (hF : PreservesJointEpiOfShape J F) (K : J ⥤ Equif η θ)
    [HasColimit (K ⋙ Equif.forget η θ)] : CreatesColimit K (Equif.forget η θ) :=
  createsColimitFullSubcategoryInclusion' K (colimit.isColimit _) (by
    refine hF _ _ (colimit.isColimit (K ⋙ Equif.forget η θ)) _ _ fun j => ?_
    have h : η.app (K.obj j).obj = θ.app (K.obj j).obj := (K.obj j).property
    have h1 := η.naturality (colimit.ι (K ⋙ Equif.forget η θ) j)
    have h2 := θ.naturality (colimit.ι (K ⋙ Equif.forget η θ) j)
    dsimp at h1 h2 h ⊢
    rw [h1, h2, h])

end Equif

/-- Joint monicness of limiting cones is preserved by precomposition with a functor that
preserves the limits. -/
lemma preservesJointMonoOfShape_comp {J : Type w₀} [Category J] {C₁ : Type*} [Category C₁]
    {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃] (P : C₁ ⥤ C₂) (Q : C₂ ⥤ C₃)
    [PreservesLimitsOfShape J P] (hQ : PreservesJointMonoOfShape J Q) :
    PreservesJointMonoOfShape J (P ⋙ Q) :=
  fun Kd _ hc _ p q h => hQ (Kd ⋙ P) _ (isLimitOfPreserves P hc) p q h

/-- Joint epicness of colimiting cocones is preserved by precomposition with a functor that
preserves the colimits. -/
lemma preservesJointEpiOfShape_comp {J : Type w₀} [Category J] {C₁ : Type*} [Category C₁]
    {C₂ : Type*} [Category C₂] {C₃ : Type*} [Category C₃] (P : C₁ ⥤ C₂) (Q : C₂ ⥤ C₃)
    [PreservesColimitsOfShape J P] (hQ : PreservesJointEpiOfShape J Q) :
    PreservesJointEpiOfShape J (P ⋙ Q) :=
  fun Kd _ hc _ p q h => hQ (Kd ⋙ P) _ (isColimitOfPreserves P hc) p q h

/-! ## The hom-level statements -/

namespace BialgDatum

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)

/-- `E.pt` is `A`-complete and `B.uB E` is `A`-continuous when `B.c` is `A`-complete, `B.g` is
`A`-continuous and each `K(a, g')`, `a ∈ A`, preserves the joint monicness of small limiting
cones. -/
theorem uB_isAComplete_and_continuous_of_jointMono {A : ObjectProperty Obj}
    (hc : IsAComplete.{w₀} A B.c) (hg : IsAContinuous.{w₀} A B.g)
    (hg' : ∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₀) [SmallCategory J],
      PreservesJointMonoOfShape J (postcomp a B.g')) :
    IsAComplete.{w₀} A E.pt ∧ IsAContinuous.{w₀} A (B.uB E) := by
  -- Hom-wise at `a ∈ A`: `K(a, Ins)` has the limits and `K(a, u)` preserves them; the equifier
  -- `K(a, E)` is closed under them by joint monicness (`equifCreatesLimitOfJointMono`).
  have hins_lim : ∀ ⦃a : Obj⦄, A a → HasLimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := by
    intro a ha
    have := hc ha
    have := hg ha
    refine ⟨fun J _ => ?_⟩
    have : HasLimitsOfShape J (Ins (postcomp a B.f) (postcomp a B.g)) := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence (Inserter.homFunctor B.ins a)
  have hu_cont : UlmerBialgebras.IsAContinuousMor.{w₀} A B.ins.u := by
    intro a ha
    have := hc ha
    have := hg ha
    refine ⟨fun {J} _ => ?_⟩
    have : PreservesLimitsOfShape J (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
      inferInstance
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have key : ∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₀) [SmallCategory J]
      (D : J ⥤ Equif (postcompNat a B.α) (postcompNat a B.β)),
      Nonempty (CreatesLimit D (Equif.forget (postcompNat a B.α) (postcompNat a B.β))) ∧
        HasLimit (D ⋙ Equif.forget (postcompNat a B.α) (postcompNat a B.β)) := by
    intro a ha J _ D
    have := hins_lim ha
    have := hu_cont ha
    have hG : PreservesJointMonoOfShape J (postcomp a (B.ins.u ≫ B.g')) := by
      rw [postcomp_comp₁ a B.ins.u B.g']
      exact preservesJointMonoOfShape_comp _ _ (hg' ha J)
    exact ⟨⟨equifCreatesLimitOfJointMono hG D⟩, inferInstance⟩
  have hequif_lim : ∀ ⦃a : Obj⦄, A a →
      HasLimitsOfSize.{w₀, w₀} (Equif (postcompNat a B.α) (postcompNat a B.β)) :=
    fun a ha => ⟨fun J _ => ⟨fun D => by
      obtain ⟨⟨hcr⟩, hl⟩ := key ha J D
      exact hasLimit_of_created D (Equif.forget _ _)⟩⟩
  have hE_lim : IsAComplete.{w₀} A E.pt := by
    intro a ha
    have := hequif_lim ha
    exact ⟨fun J _ => Adjunction.hasLimitsOfShape_of_equivalence (Equifier.homFunctor E a)⟩
  have he_cont : UlmerBialgebras.IsAContinuousMor.{w₀} A E.e := by
    intro a ha
    have : PreservesLimitsOfSize.{w₀, w₀}
        (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      ⟨fun {J} _ => ⟨fun {D} => by
        obtain ⟨⟨hcr⟩, hl⟩ := key ha J D
        infer_instance⟩⟩
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  exact ⟨hE_lim, he_cont.comp hu_cont⟩

/-- `E.pt` is `A`-cocomplete and `B.uB E` is `A`-cocontinuous when `B.c` is `A`-cocomplete,
`B.f` is `A`-cocontinuous and each `K(a, f')`, `a ∈ A`, preserves the joint epicness of small
colimiting cocones. -/
theorem uB_isACocomplete_and_cocontinuous_of_jointEpi {A : ObjectProperty Obj}
    (hc : IsACocomplete.{w₀} A B.c) (hf : IsACocontinuous.{w₀} A B.f)
    (hf' : ∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₀) [SmallCategory J],
      PreservesJointEpiOfShape J (postcomp a B.f')) :
    IsACocomplete.{w₀} A E.pt ∧ IsACocontinuous.{w₀} A (B.uB E) := by
  -- Hom-wise at `a ∈ A`: `K(a, Ins)` has the colimits and `K(a, u)` preserves them; the equifier
  -- `K(a, E)` is closed under them by joint epicness (`equifCreatesColimitOfJointEpi`).
  have hins_colim : ∀ ⦃a : Obj⦄, A a → HasColimitsOfSize.{w₀, w₀} (a ⟶ B.ins.pt) := by
    intro a ha
    have := hc ha
    have := hf ha
    refine ⟨fun J _ => ?_⟩
    have : HasColimitsOfShape J (Ins (postcomp a B.f) (postcomp a B.g)) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence (Inserter.homFunctor B.ins a)
  have hu_cocont : UlmerBialgebras.IsACocontinuousMor.{w₀} A B.ins.u := by
    intro a ha
    have := hc ha
    have := hf ha
    refine ⟨fun {J} _ => ?_⟩
    have : PreservesColimitsOfShape J (Ins.forget (postcomp a B.f) (postcomp a B.g)) :=
      inferInstance
    rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  have key : ∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₀) [SmallCategory J]
      (D : J ⥤ Equif (postcompNat a B.α) (postcompNat a B.β)),
      Nonempty (CreatesColimit D (Equif.forget (postcompNat a B.α) (postcompNat a B.β))) ∧
        HasColimit (D ⋙ Equif.forget (postcompNat a B.α) (postcompNat a B.β)) := by
    intro a ha J _ D
    have := hins_colim ha
    have := hu_cocont ha
    have hF : PreservesJointEpiOfShape J (postcomp a (B.ins.u ≫ B.f')) := by
      rw [postcomp_comp₁ a B.ins.u B.f']
      exact preservesJointEpiOfShape_comp _ _ (hf' ha J)
    exact ⟨⟨equifCreatesColimitOfJointEpi hF D⟩, inferInstance⟩
  have hequif_colim : ∀ ⦃a : Obj⦄, A a →
      HasColimitsOfSize.{w₀, w₀} (Equif (postcompNat a B.α) (postcompNat a B.β)) :=
    fun a ha => ⟨fun J _ => ⟨fun D => by
      obtain ⟨⟨hcr⟩, hl⟩ := key ha J D
      exact hasColimit_of_created D (Equif.forget _ _)⟩⟩
  have hE_colim : IsACocomplete.{w₀} A E.pt := by
    intro a ha
    have := hequif_colim ha
    exact ⟨fun J _ => Adjunction.hasColimitsOfShape_of_equivalence (Equifier.homFunctor E a)⟩
  have he_cocont : UlmerBialgebras.IsACocontinuousMor.{w₀} A E.e := by
    intro a ha
    have : PreservesColimitsOfSize.{w₀, w₀}
        (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      ⟨fun {J} _ => ⟨fun {D} => by
        obtain ⟨⟨hcr⟩, hl⟩ := key ha J D
        infer_instance⟩⟩
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  exact ⟨hE_colim, he_cocont.comp hu_cocont⟩

/-- If `B.c` has right Kan extensions along `𝒜`, `B.g` preserves them and `B.g'` sends them to
subterminal extensions, then `E.pt` has right Kan extensions along `𝒜` and `B.uB E` preserves
them. -/
theorem uB_hasAndPreservesARightKan_of_subterminal {A : ObjectProperty Obj} (hc : HasARightKan A
  B.c)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesRightKan k e B.g)
    (hg' : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c) (R : RightExt k e),
      Nonempty (IsTerminal R) → Subterminal ((RightExt.push k e B.g').obj R)) :
    HasARightKan A E.pt ∧
      ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ E.pt),
        PreservesRightKan k e (B.uB E) := by
  refine ⟨fun i x hi hx k d => ?_, fun i x hi hx k d => ?_⟩
  · obtain ⟨R₀, hR₀⟩ := hc hi hx k (d ≫ B.uB E)
    obtain ⟨⟨R, hRR, -⟩, hterm⟩ := cor_4_8_right B E k d (hg hi hx k _) (hg' hi hx k _) R₀ hR₀
    exact ⟨R, hterm R hRR⟩
  · obtain ⟨R₀, hR₀⟩ := hc hi hx k (d ≫ B.uB E)
    exact preservesTerminal_of_strictlyCreatesTerminal _
      (cor_4_8_right B E k d (hg hi hx k _) (hg' hi hx k _)) hR₀

/-- If `B.c` has left Kan extensions along `𝒜`, `B.f` preserves them and `B.f'` sends them to
quotient-initial extensions, then `E.pt` has left Kan extensions along `𝒜` and `B.uB E`
preserves them. -/
theorem uB_hasAndPreservesALeftKan_of_quotientInitial {A : ObjectProperty Obj} (hc : HasALeftKan A
  B.c)
    (hf : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c), PreservesLeftKan k e B.f)
    (hf' : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ B.c) (L : LeftExt k e),
      Nonempty (IsInitial L) → QuotientInitial ((LeftExt.push k e B.f').obj L)) :
    HasALeftKan A E.pt ∧
      ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ E.pt),
        PreservesLeftKan k e (B.uB E) := by
  refine ⟨fun i x hi hx k d => ?_, fun i x hi hx k d => ?_⟩
  · obtain ⟨L₀, hL₀⟩ := hc hi hx k (d ≫ B.uB E)
    obtain ⟨⟨L, hLL, -⟩, hinit⟩ := cor_4_8_left B E k d (hf hi hx k _) (hf' hi hx k _) L₀ hL₀
    exact ⟨L, hinit L hLL⟩
  · obtain ⟨L₀, hL₀⟩ := hc hi hx k (d ≫ B.uB E)
    exact preservesInitial_of_strictlyCreatesInitial _
      (cor_4_8_left B E k d (hf hi hx k _) (hf' hi hx k _)) hL₀

end BialgDatum

/-! ## The sharpened Theorem 7.7 -/

section Sharp

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- The hypotheses on the equational coarity support `g'` in the sharpened Theorem 7.7 (1): each
`K(a, g')`, `a ∈ A`, preserves the joint monicness of small limiting cones, and `g'` sends right
Kan extensions along `𝒜` to subterminal extensions. -/
def IsAJointMonoMor.{w₁, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c y : Obj} (g' : c ⟶ y) : Prop :=
  (∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₁) [SmallCategory J],
      PreservesJointMonoOfShape J (postcomp a g')) ∧
    ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ c) (R : RightExt k e),
      Nonempty (IsTerminal R) → Subterminal ((RightExt.push k e g').obj R)

/-- The hypotheses on the equational arity support `f'` in the sharpened Theorem 7.7 (2): each
`K(a, f')`, `a ∈ A`, preserves the joint epicness of small colimiting cocones, and `f'` sends left
Kan extensions along `𝒜` to quotient-initial extensions. -/
def IsAJointEpiMor.{w₁, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c y : Obj} (f' : c ⟶ y) : Prop :=
  (∀ ⦃a : Obj⦄, A a → ∀ (J : Type w₁) [SmallCategory J],
      PreservesJointEpiOfShape J (postcomp a f')) ∧
    ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ c) (L : LeftExt k e),
      Nonempty (IsInitial L) → QuotientInitial ((LeftExt.push k e f').obj L)

/-- **Theorem 7.7, sharpened** ([forsman2026syntactic], Theorem 7.7 with the hypotheses of
Theorem 5.11), in any strict 2-category: if `f, f', g, g'` are `A`-accessible, then `u_B` is
`A`-accessible and `Bialg(B)` is `A`-accessible; (1) if `c` is `𝒜`-complete, `g` is `𝒜`-continuous
and `g'` satisfies `IsAJointMonoMor`, then `Bialg(B)` is right `𝒜`-locally presentable and `u_B` is
`𝒜`-continuous; (2) dually, with `IsAJointEpiMor` for `f'`. -/
theorem isAAccessible_bialg_of_jointMono (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt) ∧
    (IsCalAComplete.{w₀} A B.c → IsCalAContinuous.{w₀} A B.g → IsAJointMonoMor.{w₀} A B.g' →
      IsRightALocPres.{w₀} A E.pt ∧ IsCalAContinuous.{w₀} A (B.uB E)) ∧
    (IsCalACocomplete.{w₀} A B.c → IsCalACocontinuous.{w₀} A B.f → IsAJointEpiMor.{w₀} A B.f' →
      IsLeftALocPres.{w₀} A E.pt ∧ IsCalACocontinuous.{w₀} A (B.uB E)) := by
  obtain ⟨huB_acc, hE_acc⟩ := B.uB_isAAccessibleMor' E hf hf' hg hg'
  refine ⟨⟨huB_acc, hE_acc⟩, fun ⟨hc_lim, hc_kan⟩ ⟨hg_lim, hg_kan⟩ ⟨hg'_mono, hg'_kan⟩ => ?_,
    fun ⟨hc_colim, hc_kan⟩ ⟨hf_colim, hf_kan⟩ ⟨hf'_epi, hf'_kan⟩ => ?_⟩
  · obtain ⟨hE_lim, huB_lim⟩ :=
      B.uB_isAComplete_and_continuous_of_jointMono E hc_lim hg_lim hg'_mono
    obtain ⟨hE_kan, huB_kan⟩ := B.uB_hasAndPreservesARightKan_of_subterminal E hc_kan hg_kan hg'_kan
    exact ⟨⟨hE_acc, hE_lim, hE_kan⟩, huB_lim, huB_kan⟩
  · obtain ⟨hE_colim, huB_colim⟩ :=
      B.uB_isACocomplete_and_cocontinuous_of_jointEpi E hc_colim hf_colim hf'_epi
    obtain ⟨hE_kan, huB_kan⟩ :=
      B.uB_hasAndPreservesALeftKan_of_quotientInitial E hc_kan hf_kan hf'_kan
    exact ⟨⟨hE_acc, hE_colim, hE_kan⟩, huB_colim, huB_kan⟩

/-- **Theorem 7.7, sharpened, (co)monadicity clauses** ([forsman2026syntactic], Theorem 7.7 with
the hypotheses of Theorem 5.11): if `A` is bi-dense and `f, f', g, g'` are `A`-accessible, then
(1) if `c` is `𝒜`-complete, `g` is `𝒜`-continuous and `g'` satisfies `IsAJointMonoMor`, `u_B` is
monadic; (2) dually, with `IsAJointEpiMor` for `f'`, `u_B` is comonadic. -/
theorem isMonadic2_uB_of_jointMono (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₀} A B.c → IsCalAContinuous.{w₀} A B.g → IsAJointMonoMor.{w₀} A B.g' →
      IsMonadic2 (B.uB E)) ∧
    (IsCalACocomplete.{w₀} A B.c → IsCalACocontinuous.{w₀} A B.f → IsAJointEpiMor.{w₀} A B.f' →
      IsComonadic2 (B.uB E)) := by
  obtain ⟨⟨huB_acc, -⟩, h1, h2⟩ := isAAccessible_bialg_of_jointMono A B E hf hf' hg hg'
  refine ⟨fun hc hg hg' => ?_, fun hc hf hf' => ?_⟩
  · obtain ⟨hE, huB⟩ := h1 hc hg hg'
    exact B.isMonadic2_uB_of_twoAdj E ((cor_7_5 A hA (B.uB E) huB_acc).1 hE huB)
  · obtain ⟨hE, huB⟩ := h2 hc hf hf'
    exact B.isComonadic2_uB_of_twoAdj E ((cor_7_5 A hA (B.uB E) huB_acc).2 hE huB)

end Sharp

end UlmerBialgebras.Paper
