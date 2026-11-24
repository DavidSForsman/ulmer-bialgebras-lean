module

public import UlmerBialgebras.Proofs.Sec6.Sec6Bialgebra
public import Foundations.CategoryTheory.Category.ThinShape
public import Mathlib.CategoryTheory.Category.ULift

/-! # Solution: Factorization and exactness of theories

## Main results

* `UlmerBialgebras.Paper.cor_6_7`: Corollary 6.7: given orthogonal factorization systems on the
  `M_c`, the lifted system is the unique one on `M^T` preserved by `U` when `T` is algebraic and
  each `M(B)` preserves the left classes componentwise, when `T` is coalgebraic and each `M(B)`
  preserves the right classes componentwise, or when each `M(B)` preserves both classes
  componentwise.
* `UlmerBialgebras.Paper.uB_reflectsIsomorphisms`: `U_B : Bialg(B) → c` reflects isomorphisms.
* `UlmerBialgebras.Paper.cor_6_8`: Corollary 6.8 (exactness reflection principle): under its
  hypotheses, `Bialg(B₁)` has pullbacks and reflexive coequalizers, `Fb` preserves them and reflects
  isomorphisms, and `Bialg(B₁)` is Barr-exact if `Bialg(B₂)` is and `Bialg(B₁)` has a terminal
  object.
* `UlmerBialgebras.Paper.cor_6_9`: Corollary 6.9: under its hypotheses, `M^{T₂}` is Barr-exact if
  `M^{T₁}` is, for algebraic theories `T₁ ⊆ T₂` over 1-signatures `σ₁ ⊆ σ₂`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollaries 6.7, 6.8 and 6.9
-/

@[expose] public section

universe u v w u' v' w₀ u₁ v₁ u₂ v₂ u₃ s s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- **Corollary 6.7** ([forsman2026syntactic]): let each `M_c` carry an orthogonal factorization
system. (1) If `T` is algebraic and each `M(B)` preserves the left classes componentwise, or `T` is
coalgebraic and each `M(B)` preserves the right classes componentwise, then
`(U⁻¹∏ₛE_{c_s}, U⁻¹∏ₛM_{c_s})` is the unique OFS on `M^T` preserved by `U`; (2) the same holds for
any `T` if each `M(B)` preserves both classes componentwise. -/
theorem cor_6_7 {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    (S : ∀ c : Sg.Cat, OFS (M.obj c : Type (max u v))) :
    (T.IsAlgebraic → (∀ B, PreservesLeftClassComponentwise M S B) →
        HasUniqueLiftedOFS M S sg T) ∧
      (T.IsCoalgebraic → (∀ B, PreservesRightClassComponentwise M S B) →
        HasUniqueLiftedOFS M S sg T) ∧
      ((∀ B, PreservesLeftClassComponentwise M S B) →
        (∀ B, PreservesRightClassComponentwise M S B) → HasUniqueLiftedOFS M S sg T) := by
  refine ⟨fun halg hBE => ?_, fun hco hBM => ?_, fun hBE hBM => ?_⟩
  · have hB := fun B => fn_repPreservesLeft M S B (hBE B)
    exact hasUniqueLiftedOFS_of_rep M S sg T
      (fun f => M.tm_repPreservesLeft sg _ hB (sg.fndom f))
      (fun f => tm_repPreservesRight_of_isVar M sg _ (sg.fncod f) (halg.1 f))
      (fun r => M.tm_repPreservesLeft sg _ hB (T.dom r))
      (fun r => tm_repPreservesRight_of_isVar M sg _ (T.cod r) (halg.2 r))
  · have hB := fun B => fn_repPreservesRight M S B (hBM B)
    exact hasUniqueLiftedOFS_of_rep M S sg T
      (fun f => tm_repPreservesLeft_of_isVar M sg _ (sg.fndom f) (hco.1 f))
      (fun f => M.tm_repPreservesRight sg _ hB (sg.fncod f))
      (fun r => tm_repPreservesLeft_of_isVar M sg _ (T.dom r) (hco.2 r))
      (fun r => M.tm_repPreservesRight sg _ hB (T.cod r))
  · have hL := fun B => fn_repPreservesLeft M S B (hBE B)
    have hR := fun B => fn_repPreservesRight M S B (hBM B)
    exact hasUniqueLiftedOFS_of_rep M S sg T
      (fun f => M.tm_repPreservesLeft sg _ hL (sg.fndom f))
      (fun f => M.tm_repPreservesRight sg _ hR (sg.fncod f))
      (fun r => M.tm_repPreservesLeft sg _ hL (T.dom r))
      (fun r => M.tm_repPreservesRight sg _ hR (T.cod r))

/-- The factorization system (isomorphisms, all morphisms). -/
noncomputable def isoOFS (C : Type*) [Category C] : OFS C :=
  OFS.mk' (MorphismProperty.isomorphisms C) ⊤
    (fun _ _ f => ⟨_, 𝟙 _, f, MorphismProperty.isomorphisms.infer_property _, trivial, by simp⟩)
    (fun _ _ _ _ e m he _ => by
      have : IsIso e := he
      exact leftOrth_of_isIso ⊤ e m trivial)
    inferInstance ⟨fun _ _ => trivial⟩

/-- `U_B` reflects isomorphisms (Theorem 6.6 (1) for the factorization system
(isomorphisms, all morphisms)). -/
theorem uB_reflectsIsomorphisms (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β) :
    (B.uB E).toFunctor.ReflectsIsomorphisms := by
  obtain ⟨P, hPE, hPM, -⟩ := thm_6_6_1 B E (isoOFS (B.c : Type (max u v)))
    (fun _ _ _ _ e m he _ => by
      have : IsIso e := he
      exact leftOrth_of_isIso ⊤ _ _ trivial)
    (fun _ _ _ _ e m he _ f g _ h h' h1 _ h1' _ => by
      have : IsIso e := he
      exact (cancel_epi _).1 (h1.trans h1'.symm))
  have hPM' : P.M = ⊤ := by ext x y f; exact iff_of_true ((hPM f).2 trivial) trivial
  constructor
  intro x y f hf
  have h1 : P.E f := (hPE f).2 hf
  rw [P.E_eq, hPM'] at h1
  obtain ⟨k, ⟨k1, k2⟩, -⟩ := h1 f trivial (𝟙 _) (𝟙 _) (by simp)
  exact ⟨k, k1, k2⟩



/-- `U_B` strictly creates colimits of reflexive pairs when `F` preserves them and `F'` maps
regular epis to epis (Corollary 4.8). -/
theorem uB_strictlyCreates_reflexive (B : BialgDatum (Obj := Cat.{v, max u v}))
    (E : Equifier B.α B.β)
    [PreservesColimitsOfShape WalkingReflexivePair (B.f).toFunctor]
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    (J : Cat.{v, max u v}) (e : WalkingReflexivePair ≌ (J : Type (max u v)))
    (d : J ⟶ E.pt) :
    StrictlyCreatesLeftKan (toOne J) d (B.uB E) := by
  have : PreservesColimitsOfShape (J : Type (max u v)) (B.f).toFunctor :=
    preservesColimitsOfShape_of_equiv e (B.f).toFunctor
  refine cor_4_8_left B E (toOne J) d (preservesLeftKan_of_preservesColimitsOfShape B.f _) ?_
  intro L hL
  let one' : (J : Type (max u v)) := e.functor.obj WalkingReflexivePair.zero
  have hc := (isColimitCoconeOfLeftExt hL.some).whiskerEquivalence e
  have hc2 :=
      (Functor.Final.isColimitWhiskerEquiv WalkingParallelPair.inclusionWalkingReflexivePair _).symm
      hc
  have hreg := regularEpi_of_isColimit_walkingParallelPair _ _ hc2
  have hepi : Epi ((B.f').toFunctor.map (L.unit.toNatTrans.app one')) := hF' _ hreg
  have heq : ((LeftExt.push (toOne J) (d ≫ B.uB E) B.f').obj L).unit.toNatTrans.app one' =
      (B.f').toFunctor.map (L.unit.toNatTrans.app one') := by
    simp
  have : Epi (((LeftExt.push (toOne J) (d ≫ B.uB E) B.f').obj L).unit.toNatTrans.app one') := by
    rw [heq]; exact hepi
  exact quotientInitial_of_epi_unit _ one'

/-- If `C` has reflexive coequalizers, `f` preserves them and `f'` sends regular epis to epis, then
`Bialg(B)` has reflexive coequalizers and `U_B` preserves them (it creates them, Corollary 4.8). -/
theorem uB_reflexiveCoequalizers (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [HasReflexiveCoequalizers (B.c : Type (max u v))]
    [PreservesColimitsOfShape WalkingReflexivePair (B.f).toFunctor]
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e)) :
    HasColimitsOfShape WalkingReflexivePair (E.pt : Type (max u v)) ∧
      PreservesColimitsOfShape WalkingReflexivePair (B.uB E).toFunctor := by
  let U₁ : (E.pt : Type (max u v)) ⥤ (B.c : Type (max u v)) := (B.uB E).toFunctor
  have : HasColimitsOfShape WalkingReflexivePair (B.c : Type (max u v)) :=
    hasReflexiveCoequalizers_iff.2 inferInstance
  have : HasColimitsOfShape (reflexivePairShapeCat.{u, v} : Type (max u v))
      (B.c : Type (max u v)) :=
    hasColimitsOfShape_of_equivalence (reflexivePairShapeCat.equivalence.{u, v})
  have hcolE : ∀ K : WalkingReflexivePair ⥤ (E.pt : Type (max u v)), HasColimit K ∧
      PreservesColimit K U₁ := by
    intro K
    let d : reflexivePairShapeCat.{u, v} ⟶ E.pt :=
      (reflexivePairShapeCat.equivalence.symm.functor ⋙ K).toCatHom
    have hcr := uB_strictlyCreates_reflexive B E hF'
      reflexivePairShapeCat.{u, v} reflexivePairShapeCat.equivalence.{u, v} d
    have : HasColimit (reflexivePairShapeCat.equivalence.symm.functor ⋙ K ⋙ U₁) :=
      hasColimit_equivalence_comp (reflexivePairShapeCat.equivalence.symm)
    have : HasColimit (d ≫ B.uB E).toFunctor :=
      inferInstanceAs (HasColimit (reflexivePairShapeCat.equivalence.symm.functor ⋙ K ⋙ U₁))
    have : HasColimit d.toFunctor :=
      hasColimit_of_strictlyCreatesLeftKan d (B.uB E) hcr
    have : PreservesColimit d.toFunctor U₁ :=
      preservesColimit_of_strictlyCreatesLeftKan d (B.uB E) hcr
    have : HasColimit (reflexivePairShapeCat.equivalence.symm.functor ⋙ K) :=
      inferInstanceAs (HasColimit d.toFunctor)
    have : PreservesColimit (reflexivePairShapeCat.equivalence.symm.functor ⋙ K) U₁ :=
      inferInstanceAs (PreservesColimit d.toFunctor U₁)
    exact ⟨hasColimit_of_equivalence_comp (reflexivePairShapeCat.equivalence.symm),
      preservesColimit_of_equiv (reflexivePairShapeCat.equivalence.symm) K U₁⟩
  exact ⟨⟨fun K => (hcolE K).1⟩, ⟨fun {K} => (hcolE K).2⟩⟩

section Square

variable {B₁ B₂ : BialgDatum (Obj := Cat.{v, max u v})} {E₁ : Equifier B₁.α B₁.β}
  {E₂ : Equifier B₂.α B₂.β} {F : B₁.c ⟶ B₂.c} {Fb : E₁.pt ⟶ E₂.pt}
  (hsq : Fb ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F)
include hsq

/-- In a square `Fb ≫ U₂ = U₁ ≫ F`, `Fb` preserves the pullbacks that `U₁ ≫ F` preserves, since
`U₂` creates pullbacks (Corollary 4.8). -/
theorem preservesPullbacks_of_bialgSquare
    [PreservesLimitsOfShape WalkingCospan (B₁.uB E₁).toFunctor]
    [PreservesLimitsOfShape WalkingCospan F.toFunctor]
    [PreservesLimitsOfShape WalkingCospan (B₂.g).toFunctor]
    (hG'₂ : PreservesJointMonoOfShape WalkingCospan (B₂.g').toFunctor) :
    PreservesLimitsOfShape WalkingCospan Fb.toFunctor := by
  have hsq' : Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor = (B₁.uB E₁).toFunctor ⋙ F.toFunctor :=
    congr(($hsq).toFunctor)
  constructor
  intro K
  have : PreservesLimit K (Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor) := by rw [hsq']; infer_instance
  exact preservesLimit_of_reflect K Fb (B₂.uB E₂) cospanShapeCat cospanShapeCat.equivalence
    (uB_strictlyCreates_of_equiv B₂ E₂ hG'₂ cospanShapeCat cospanShapeCat.equivalence
      ((cospanShapeCat.equivalence.inverse ⋙ K ⋙ Fb.toFunctor).toCatHom))

/-- In a square `Fb ≫ U₂ = U₁ ≫ F`, `Fb` preserves the reflexive coequalizers that `U₁ ≫ F`
preserves, since `U₂` creates them (Corollary 4.8). -/
theorem preservesReflexiveCoequalizers_of_bialgSquare
    [PreservesColimitsOfShape WalkingReflexivePair (B₁.uB E₁).toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair F.toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair (B₂.f).toFunctor]
    (hF'₂ : ∀ ⦃a b : (B₂.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₂.f').toFunctor.map e)) :
    PreservesColimitsOfShape WalkingReflexivePair Fb.toFunctor := by
  have hsq' : Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor = (B₁.uB E₁).toFunctor ⋙ F.toFunctor :=
    congr(($hsq).toFunctor)
  constructor
  intro K
  have : PreservesColimit K (Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor) := by
    rw [hsq']; infer_instance
  exact preservesColimit_of_reflect K Fb (B₂.uB E₂) reflexivePairShapeCat
    reflexivePairShapeCat.equivalence
    (uB_strictlyCreates_reflexive B₂ E₂ hF'₂ reflexivePairShapeCat
      reflexivePairShapeCat.equivalence
      ((reflexivePairShapeCat.equivalence.inverse ⋙ K ⋙ Fb.toFunctor).toCatHom))

/-- In a square `Fb ≫ U₂ = U₁ ≫ F` with `U₁` and `F` conservative, `Fb` is conservative. -/
theorem reflectsIsomorphisms_of_bialgSquare [(B₁.uB E₁).toFunctor.ReflectsIsomorphisms]
    [F.toFunctor.ReflectsIsomorphisms] : Fb.toFunctor.ReflectsIsomorphisms := by
  have hsq' : Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor = (B₁.uB E₁).toFunctor ⋙ F.toFunctor :=
    congr(($hsq).toFunctor)
  constructor
  intro x y f hf
  have h1 : IsIso ((Fb.toFunctor ⋙ (B₂.uB E₂).toFunctor).map f) := by
    change IsIso ((B₂.uB E₂).toFunctor.map (Fb.toFunctor.map f)); infer_instance
  rw [hsq'] at h1
  have : IsIso (F.toFunctor.map ((B₁.uB E₁).toFunctor.map f)) := h1
  have : IsIso ((B₁.uB E₁).toFunctor.map f) := isIso_of_reflects_iso _ F.toFunctor
  exact isIso_of_reflects_iso f (B₁.uB E₁).toFunctor

end Square

/-- A conservative functor that preserves kernel pairs reflects monomorphisms. -/
theorem mono_of_mono_map_of_reflectsIsomorphisms {A D : Type*} [Category A] [Category D]
    [HasPullbacks A] (G : A ⥤ D) [PreservesLimitsOfShape WalkingCospan G]
    [G.ReflectsIsomorphisms] {x y : A} (f : x ⟶ y) (hf : Mono (G.map f)) : Mono f := by
  have hk : IsKernelPair f (pullback.fst f f) (pullback.snd f f) := IsPullback.of_hasPullback f f
  have : IsIso (G.map (pullback.fst f f)) := IsKernelPair.isIso_of_mono (hk.map G)
  have : IsIso (pullback.fst f f) := isIso_of_reflects_iso _ G
  exact IsKernelPair.mono_of_isIso_fst hk

/-- Working form of `cor_6_8`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Corollary 6.8** ([forsman2026syntactic]) (exactness reflection principle). -/
theorem exactness_reflection_of_bialgMor (B₁ B₂ : BialgDatum (Obj := Cat.{v, max u v}))
    (E₁ : Equifier B₁.α B₁.β)
    (E₂ : Equifier B₂.α B₂.β) (F : B₁.c ⟶ B₂.c) (Fb : E₁.pt ⟶ E₂.pt)
    (hsq : Fb ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F)
    [HasPullbacks (B₁.c : Type (max u v))] [HasReflexiveCoequalizers (B₁.c : Type (max u v))]
    [PreservesLimitsOfShape WalkingCospan F.toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair F.toFunctor]
    [F.toFunctor.ReflectsIsomorphisms]
    [PreservesColimitsOfShape WalkingReflexivePair (B₁.f).toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair (B₂.f).toFunctor]
    (hF'₁ : ∀ ⦃a b : (B₁.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₁.f').toFunctor.map e))
    (hF'₂ : ∀ ⦃a b : (B₂.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₂.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B₁.g).toFunctor]
    [PreservesLimitsOfShape WalkingCospan (B₂.g).toFunctor]
    (hG'₁ : PreservesJointMonoOfShape WalkingCospan (B₁.g').toFunctor)
    (hG'₂ : PreservesJointMonoOfShape WalkingCospan (B₂.g').toFunctor) :
    HasPullbacks (E₁.pt : Type (max u v)) ∧ HasReflexiveCoequalizers (E₁.pt : Type (max u v)) ∧
      Nonempty (PreservesLimitsOfShape WalkingCospan Fb.toFunctor) ∧
      Nonempty (PreservesColimitsOfShape WalkingReflexivePair Fb.toFunctor) ∧
      Fb.toFunctor.ReflectsIsomorphisms ∧
      (IsExactCat (E₂.pt : Type (max u v)) → HasTerminal (E₁.pt : Type (max u v)) →
        IsExactCat (E₁.pt : Type (max u v))) := by
  let U₁ : (E₁.pt : Type (max u v)) ⥤ (B₁.c : Type (max u v)) := (B₁.uB E₁).toFunctor
  let U₂ : (E₂.pt : Type (max u v)) ⥤ (B₂.c : Type (max u v)) := (B₂.uB E₂).toFunctor
  let Fb' : (E₁.pt : Type (max u v)) ⥤ (E₂.pt : Type (max u v)) := Fb.toFunctor
  let F' : (B₁.c : Type (max u v)) ⥤ (B₂.c : Type (max u v)) := F.toFunctor
  have hsq' : Fb' ⋙ U₂ = U₁ ⋙ F' := congr(($hsq).toFunctor)
  have := uB_preservesPullbacks B₁ E₁ hG'₁
  have hpb : HasPullbacks (E₁.pt : Type (max u v)) := uB_hasPullbacks B₁ E₁ hG'₁
  have := uB_reflectsIsomorphisms B₁ E₁
  obtain ⟨_, _⟩ := uB_reflexiveCoequalizers B₁ E₁ hF'₁
  have hrefl : HasReflexiveCoequalizers (E₁.pt : Type (max u v)) := hasReflexiveCoequalizers_iff.1
      inferInstance
  have hFbpb : PreservesLimitsOfShape WalkingCospan Fb' :=
    preservesPullbacks_of_bialgSquare hsq hG'₂
  have hFbco : PreservesColimitsOfShape WalkingReflexivePair Fb' :=
    preservesReflexiveCoequalizers_of_bialgSquare hsq hF'₂
  have hcons : Fb'.ReflectsIsomorphisms := reflectsIsomorphisms_of_bialgSquare hsq
  refine ⟨(hpb : HasPullbacks (E₁.pt : Type (max u v))),
    (hrefl : HasReflexiveCoequalizers (E₁.pt : Type (max u v))),
    (⟨hFbpb⟩ : Nonempty (PreservesLimitsOfShape WalkingCospan Fb.toFunctor)),
    (⟨hFbco⟩ : Nonempty (PreservesColimitsOfShape WalkingReflexivePair Fb.toFunctor)),
    (hcons : Fb.toFunctor.ReflectsIsomorphisms), fun hex₂ hterm₁ => ?_⟩
  have := hterm₁
  have : HasFiniteLimits (E₁.pt : Type (max u v)) := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have hmono : ∀ ⦃x y : (E₁.pt : Type (max u v))⦄ (f : x ⟶ y), Mono (Fb'.map f) → Mono f :=
    fun _ _ f hf => mono_of_mono_map_of_reflectsIsomorphisms Fb' f hf
  exact regular_exact_transfer_of_preservesPullbacks_exact Fb' hmono
    (by
      intro R x r s hrs
      have : IsReflexivePair r s := hrs.isReflexivePair
      exact ⟨inferInstance, preservesColimit_parallelPair_of_reflexive Fb' r s⟩)
    hcons hex₂

/-- **Corollary 6.8** ([forsman2026syntactic]), the exactness reflection principle. Let
`F : c₁ ⥤ c₂` and `Fb : E₁ ⥤ E₂` be functors between the categories and the categories of
bialgebras of two bialgebraic data, with `Fb ⋙ U₂ = U₁ ⋙ F`. Suppose that `c₁` has pullbacks and
reflexive coequalizers; that `F` preserves them and reflects isomorphisms; that the functors `f` of
both data preserve reflexive coequalizers and their `f'` send regular epimorphisms to
epimorphisms; and that the functors `g` preserve pullbacks and their `g'` preserve jointly monic
cones over cospans. Then `E₁` has pullbacks and reflexive coequalizers, `Fb` preserves them and
reflects isomorphisms, and `E₁` is Barr-exact when `E₂` is and `E₁` has a terminal object. -/
theorem cor_6_8 (B₁ B₂ : BialgDatum (Obj := Cat.{v, max u v})) (E₁ : Equifier B₁.α B₁.β)
    (E₂ : Equifier B₂.α B₂.β) (F : B₁.c ⟶ B₂.c) (Fb : E₁.pt ⟶ E₂.pt)
    (hsq : Fb ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F)
    [HasPullbacks (B₁.c : Type (max u v))] [HasReflexiveCoequalizers (B₁.c : Type (max u v))]
    [PreservesLimitsOfShape WalkingCospan F.toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair F.toFunctor]
    [F.toFunctor.ReflectsIsomorphisms]
    [PreservesColimitsOfShape WalkingReflexivePair (B₁.f).toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair (B₂.f).toFunctor]
    (hF'₁ : ∀ ⦃a b : (B₁.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₁.f').toFunctor.map e))
    (hF'₂ : ∀ ⦃a b : (B₂.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₂.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B₁.g).toFunctor]
    [PreservesLimitsOfShape WalkingCospan (B₂.g).toFunctor]
    (hG'₁ : PreservesJointMonoOfShape WalkingCospan (B₁.g').toFunctor)
    (hG'₂ : PreservesJointMonoOfShape WalkingCospan (B₂.g').toFunctor) :
    HasPullbacks (E₁.pt : Type (max u v)) ∧ HasReflexiveCoequalizers (E₁.pt : Type (max u v)) ∧
      Nonempty (PreservesLimitsOfShape WalkingCospan Fb.toFunctor) ∧
      Nonempty (PreservesColimitsOfShape WalkingReflexivePair Fb.toFunctor) ∧
      Fb.toFunctor.ReflectsIsomorphisms ∧
      (BarrExact (E₂.pt : Type (max u v)) → HasTerminal (E₁.pt : Type (max u v)) →
        BarrExact (E₁.pt : Type (max u v))) := by
  obtain ⟨hpb, hcoeq, hlim, hcolim, hrefl, hexact⟩ :=
    exactness_reflection_of_bialgMor B₁ B₂ E₁ E₂ F Fb hsq hF'₁ hF'₂ hG'₁ hG'₂
  exact ⟨hpb, hcoeq, hlim, hcolim, hrefl, fun h ht =>
    isExactCat_iff_barrExact.1 (hexact (isExactCat_iff_barrExact.2 h) ht)⟩

attribute [local instance] uliftCategory in
/-- The reflexive-pair shape at the size of `Cat.{v, max u v}`: objects in `Type (max u v)`,
morphisms in `Type v`. -/
abbrev walkingReflexivePairCat' : Cat.{v, max u v} :=
  Cat.of (ULiftHom.{v} (ULift.{max u v} WalkingReflexivePair))

attribute [local instance] uliftCategory in
/-- The lifted reflexive-pair shape is equivalent to `WalkingReflexivePair`. -/
noncomputable def walkingReflexivePairCatEquiv' :
    WalkingReflexivePair ≌ (walkingReflexivePairCat'.{u, v} : Type (max u v)) :=
  ULift.equivalence.trans ULiftHom.equiv

/-- A functor preserving reflexive coequalizers sends regular epimorphisms to epimorphisms, in a
category with kernel pairs: a regular epimorphism is the coequalizer of its kernel pair, which is
a reflexive pair. -/
theorem epi_map_of_regularEpi {C D : Type*} [Category C] [Category D] [HasPullbacks C]
    (G : C ⥤ D) [PreservesColimitsOfShape WalkingReflexivePair G] {a b : C} (e : a ⟶ b)
    (he : Nonempty (RegularEpi e)) : Epi (G.map e) := by
  obtain ⟨r⟩ := he
  have k : IsKernelPair e (pullback.fst e e) (pullback.snd e e) := IsPullback.of_hasPullback e e
  have : IsReflexivePair (pullback.fst e e) (pullback.snd e e) :=
    ⟨⟨pullback.lift (𝟙 a) (𝟙 a) rfl, by simp, by simp⟩⟩
  have := preservesColimit_parallelPair_of_reflexive G (pullback.fst e e) (pullback.snd e e)
  have l := isColimitCoforkMapOfIsColimit G _ (k.toCoequalizer r)
  exact ⟨fun u v h => Cofork.IsColimit.hom_ext l h⟩

/-- A functor preserving `J`-limits preserves the joint monicness of `J`-limit projections. -/
theorem preservesJointMonoOfShape_of_preservesLimitsOfShape {J C D : Type*} [Category J]
    [Category C] [Category D] (G : C ⥤ D) [PreservesLimitsOfShape J G] :
    PreservesJointMonoOfShape J G :=
  fun _ _ hc _ _ _ h => (isLimitOfPreserves G hc).hom_ext h

section ModelDatum

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}]
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]

/-- For an algebraic theory over finitely complete `M_c`, the coarity data of `modelDatum` preserve
pullbacks: `G = (M(t₂))_f` preserves them and `G' = (M(t₂'))_r` preserves the joint monicness of
pullback projections, both being products of projections. -/
theorem modelDatum_coarity (hlim : ∀ c : Sg.Cat, HasFiniteLimits (M.obj c : Type (max u v)))
    (halg : T.IsAlgebraic) :
    PreservesLimitsOfShape WalkingCospan (modelDatum M sg T).g.toFunctor ∧
      PreservesJointMonoOfShape WalkingCospan (modelDatum M sg T).g'.toFunctor := by
  have hlim' : ∀ (x : Cat.{v, max u v}) (c : Sg.Cat), HasFiniteLimits (x ⟶ M.obj c) :=
    fun x c => have := hlim c; hasFiniteLimits_of_equivalence (catHomEquivalence x (M.obj c))
  have h₁ := preservesFiniteLimits_of_repPreservesFiniteLimits _
    (M.repPreservesFiniteLimits_codCell sg hlim' halg.1)
  have h₂ := preservesFiniteLimits_of_repPreservesFiniteLimits _
    ((M.Peq sg T).repPreservesFiniteLimits_lift _
      (M.repPreservesFiniteLimits_eqnCoarity sg hlim' T halg.2))
  have : PreservesLimitsOfShape WalkingCospan (modelDatum M sg T).g'.toFunctor :=
    h₂.preservesFiniteLimits WalkingCospan
  exact ⟨h₁.preservesFiniteLimits WalkingCospan,
    preservesJointMonoOfShape_of_preservesLimitsOfShape _⟩

/-- If each `M_c` has reflexive coequalizers and each `M(B)` preserves them componentwise, the
arity data of `modelDatum` preserve reflexive coequalizers: `F = (M(t₁))_f` preserves them and
`F' = (M(t₁'))_r` sends regular epimorphisms to epimorphisms. -/
theorem modelDatum_arity (hlim : ∀ c : Sg.Cat, HasFiniteLimits (M.obj c : Type (max u v)))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M WalkingReflexivePair B) :
    PreservesColimitsOfShape WalkingReflexivePair (modelDatum M sg T).f.toFunctor ∧
      ∀ ⦃a b : ((modelDatum M sg T).c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
        Epi ((modelDatum M sg T).f'.toFunctor.map e) := by
  let e := walkingReflexivePairCatEquiv'.{u, v}
  have : IsSifted (walkingReflexivePairCat'.{u, v} : Type (max u v)) :=
    IsSifted.isSifted_of_equiv e.symm
  have hB' : ∀ B : Sg.Fun, PreservesColimitsComponentwise M walkingReflexivePairCat'.{u, v} B :=
    fun B i x => by
      obtain ⟨h⟩ := hB B i x
      exact ⟨preservesColimitsOfShape_of_equiv e _⟩
  have : HasPullbacks ((modelDatum M sg T).c : Type (max u v)) :=
    have hlim' : ∀ (x : Cat.{v, max u v}) (c : Sg.Cat), HasFiniteLimits (x ⟶ M.obj c) :=
      fun x c => have := hlim c; hasFiniteLimits_of_equivalence (catHomEquivalence x (M.obj c))
    have := M.hasFiniteLimits_hom_P0 sg hlim' One
    have : HasFiniteLimits ((M.P0 sg).pt : Type (max u v)) :=
      hasFiniteLimits_of_equivalence ((catHomEquivalence One (M.P0 sg).pt).trans
        (oneEquiv (M.P0 sg).pt)).symm
    inferInstanceAs (HasPullbacks ((M.P0 sg).pt : Type (max u v)))
  have : PreservesColimitsOfShape WalkingReflexivePair (modelDatum M sg T).f'.toFunctor := by
    have : PreservesColimitsOfShape walkingReflexivePairCat'.{u, v}
        (modelDatum M sg T).f'.toFunctor := ⟨fun {K} => by
      have : ∀ r, PreservesColimit K (M.tm sg (T.dom r)).toFunctor :=
        fun r => (preservesColimitsOfShape_tm M sg _ hB' (T.dom r)).preservesColimit
      exact Product.lift_preservesColimit (M.Peq sg T) _ K⟩
    exact preservesColimitsOfShape_of_equiv e.symm _
  refine ⟨?_, fun _ _ f hf => epi_map_of_regularEpi _ f hf⟩
  have : PreservesColimitsOfShape walkingReflexivePairCat'.{u, v}
      (modelDatum M sg T).f.toFunctor :=
    preservesColimitsOfShape_domCell M sg walkingReflexivePairCat'.{u, v} hB'
  exact preservesColimitsOfShape_of_equiv e.symm _

end ModelDatum

/-- **Corollary 6.9** ([forsman2026syntactic]): let `σ₁ ⊆ σ₂` be 1-signatures with the same sorts,
here `σ₁ = sg.restrictFn jFn`, and `T₁ ⊆ T₂` algebraic theories, here
`T₁ = T.restrictSig jFn jEq lhs₁ rhs₁`, whose equation paths translate to those of `T₂ = T`.
If each `M_c` has finite limits and reflexive coequalizers, each `M(B)` preserves reflexive
coequalizers componentwise and `M^{T₁}` is exact, then `M^{T₂}` is exact. -/
theorem cor_6_9 {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn)
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    {E : Type s₃} (jEq : E → T.Eqn)
    (lhs₁ rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r)))
    (hlhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (lhs₁ r) = T.lhs (jEq r))
    (hrhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (rhs₁ r) = T.rhs (jEq r))
    (halg : T.IsAlgebraic)
    (hlim : ∀ c : Sg.Cat, HasFiniteLimits (M.obj c : Type (max u v)))
    (hrc : ∀ c : Sg.Cat, HasReflexiveCoequalizers (M.obj c : Type (max u v)))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M WalkingReflexivePair B)
    [BarrExact (M.thyObj (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) :
      Type (max u v))] :
    BarrExact (M.thyObj sg T : Type (max u v)) := by
  let sg₁ := sg.restrictFn jFn
  let T₁ := T.restrictSig jFn jEq lhs₁ rhs₁
  let B₁ := modelDatum M sg T
  let B₂ := modelDatum M sg₁ T₁
  let E₁ : Equifier B₁.α B₁.β :=
    Equifier.conj (M.thyEquif sg T) (M.sigCell_eq sg T T.dom) (M.sigCell_eq sg T T.cod).symm
  let E₂ : Equifier B₂.α B₂.β :=
    Equifier.conj (M.thyEquif sg₁ T₁) (M.sigCell_eq sg₁ T₁ T₁.dom)
      (M.sigCell_eq sg₁ T₁ T₁.cod).symm
  -- `F` is the identity of `M₀`, as `σ₁` and `σ₂` have the same sorts
  let F : B₁.c ⟶ B₂.c := 𝟙 B₁.c
  have hsq : M.thySubSigForget sg jFn T jEq lhs₁ rhs₁ hlhs hrhs ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F :=
    (M.thySubSigForget_thyForget sg jFn T jEq lhs₁ rhs₁ hlhs hrhs).trans
      (Category.comp_id _).symm
  have : PreservesLimitsOfShape WalkingCospan F.toFunctor :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (𝟭 _))
  have : PreservesColimitsOfShape WalkingReflexivePair F.toFunctor :=
    inferInstanceAs (PreservesColimitsOfShape WalkingReflexivePair (𝟭 _))
  have : F.toFunctor.ReflectsIsomorphisms := inferInstanceAs (𝟭 _).ReflectsIsomorphisms
  -- `M₀` has finite limits and reflexive coequalizers
  have hlim' : ∀ (x : Cat.{v, max u v}) (c : Sg.Cat), HasFiniteLimits (x ⟶ M.obj c) :=
    fun x c => have := hlim c; hasFiniteLimits_of_equivalence (catHomEquivalence x (M.obj c))
  have := M.hasFiniteLimits_hom_P0 sg hlim' One
  have : HasFiniteLimits ((M.P0 sg).pt : Type (max u v)) :=
    hasFiniteLimits_of_equivalence ((catHomEquivalence One (M.P0 sg).pt).trans
      (oneEquiv (M.P0 sg).pt)).symm
  have : HasPullbacks (B₁.c : Type (max u v)) :=
    inferInstanceAs (HasPullbacks ((M.P0 sg).pt : Type (max u v)))
  have := fun c => hasReflexiveCoequalizers_iff.2 (hrc c)
  have : HasColimitsOfShape WalkingReflexivePair ((M.P0 sg).pt : Type (max u v)) :=
    Adjunction.hasColimitsOfShape_of_equivalence (Product.toPi (M.P0 sg))
  have : HasReflexiveCoequalizers (B₁.c : Type (max u v)) :=
    hasReflexiveCoequalizers_iff.1 this
  -- the arity and coarity data of both theories
  have halg₁ : T₁.IsAlgebraic := halg.restrictSig jFn jEq lhs₁ rhs₁
  obtain ⟨_, hF'₁⟩ := modelDatum_arity M sg T hlim hB
  obtain ⟨_, hF'₂⟩ := modelDatum_arity M sg₁ T₁ hlim hB
  obtain ⟨_, hG'₁⟩ := modelDatum_coarity M sg T hlim halg
  obtain ⟨_, hG'₂⟩ := modelDatum_coarity M sg₁ T₁ hlim halg₁
  -- `M^{T₂}` has a terminal object
  have : HasFiniteLimits (One.{v, max u v} ⟶ M.thyObj sg T) :=
    M.hasFiniteLimits_hom_thyObj sg hlim' T halg One
  have : HasFiniteLimits (M.thyObj sg T : Type (max u v)) :=
    hasFiniteLimits_of_equivalence ((catHomEquivalence One (M.thyObj sg T)).trans
      (oneEquiv (M.thyObj sg T))).symm
  obtain ⟨-, -, -, -, -, h⟩ := cor_6_8.{u, v} B₁ B₂ E₁ E₂ F
    (M.thySubSigForget sg jFn T jEq lhs₁ rhs₁ hlhs hrhs) hsq hF'₁ hF'₂ hG'₁ hG'₂
  exact h (inferInstanceAs (BarrExact (M.thyObj sg₁ T₁ : Type (max u v))))
    (inferInstanceAs (HasTerminal (M.thyObj sg T : Type (max u v))))

/-- Working form of `cor_6_9`, with the OFS-based notions (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`, `UlmerBialgebras.IsEquivRel`, `UlmerBialgebras.extremalEpi`).
**Corollary 6.9** ([forsman2026syntactic]): let `σ₁ ⊆ σ₂` be 1-signatures with the same sorts,
here `σ₁ = sg.restrictFn jFn`, and `T₁ ⊆ T₂` algebraic theories, here
`T₁ = T.restrictSig jFn jEq lhs₁ rhs₁`, whose equation paths translate to those of `T₂ = T`. If each
`M_c` has finite limits and reflexive coequalizers, each `M(B)` preserves reflexive coequalizers
componentwise and `M^{T₁}` is exact, then `M^{T₂}` is exact. -/
theorem isExactCat_thyObj_of_restrict {Sg : TwoSig.{u₁, u₂, u₃}}
    (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn)
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    {E : Type s₃} (jEq : E → T.Eqn)
    (lhs₁ rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r)))
    (hlhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (lhs₁ r) = T.lhs (jEq r))
    (hrhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (rhs₁ r) = T.rhs (jEq r))
    (halg : T.IsAlgebraic)
    (hlim : ∀ c : Sg.Cat, HasFiniteLimits (M.obj c : Type (max u v)))
    (hrc : ∀ c : Sg.Cat, HasReflexiveCoequalizers (M.obj c : Type (max u v)))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M WalkingReflexivePair B)
    (hex₁ : IsExactCat
      (M.thyObj (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) : Type (max u v))) :
    IsExactCat (M.thyObj sg T : Type (max u v)) :=
  have := isExactCat_iff_barrExact.1 hex₁
  isExactCat_iff_barrExact.2 (cor_6_9 M sg jFn T jEq lhs₁ rhs₁ hlhs hrhs halg hlim hrc hB)

end UlmerBialgebras.Paper
