module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Foundations.CategoryTheory.Limits.PreservesReflexiveCoeq

/-!
# Reflecting regularity and exactness along a jointly conservative family

This file formalises Lemma 4.1 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

the local-to-global reflection argument used in Section 4 of the paper to extend the main
theorem from fields to commutative von Neumann regular rings.

Given a family of functors `F i : C ⥤ D i` which is jointly conservative and preserves
pullbacks and coequalizers, and such that every `D i` is a regular category, we show that the
family jointly reflects regular epimorphisms and that `C` inherits regularity and
Barr-exactness (see the main results below).

Along the way we prove two facts of independent interest: an effective equivalence relation is the
kernel pair of its own coequalizer (`CategoryTheory.isKernelPair_of_isColimitCofork`), and internal
equivalence relations are preserved by finite-limit-preserving functors
(`CategoryTheory.IsInternalEquivalenceRelation.map`).

Compared with the statement in the paper we ask that the functors preserve the relevant
coequalizers; this is what makes the comparison of the canonical factorisations in `C` and in
`D i` legitimate (the paper's `Hopf`-theoretic applications provide functors preserving
reflexive coequalizers, which covers the coequalizers of kernel pairs and of equivalence
relations occurring here).

## Main results

* `CategoryTheory.isRegularEpi_of_forall_map`: the family jointly reflects regular epimorphisms
  (Lemma 4.1 of [forsman2026semiabeliannessaffinegroupschemes]);
* `CategoryTheory.regular_of_jointlyConservative`: if in addition `C` has finite limits and
  coequalizers of kernel pairs, then `C` is regular (Lemma 4.1, regular case);
* `CategoryTheory.isBarrExact_of_jointlyConservative`: the exact half of the lemma — if moreover the
  functors preserve all finite limits, every `D i` is Barr-exact and `C` has coequalizers of
  internal equivalence relations, then `C` is Barr-exact (Lemma 4.1, exact case);
* `CategoryTheory.isKernelPair_of_isColimitCofork`: a kernel pair `(a, b)` of a morphism is the
  kernel pair of any coequalizer of `a` and `b`;
* `CategoryTheory.IsInternalEquivalenceRelation.map`: internal equivalence relations are preserved
  by finite-limit-preserving functors.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Lemma 4.1
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 6.5 (3), Lemma 6.10 and Corollary 6.11
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u v₂ u₂ w

open CategoryTheory Limits

namespace CategoryTheory
open CategoryTheory

variable {C : Type u} [Category.{v} C] {I : Type w} {D : I → Type u₂}
  [∀ i, Category.{v₂} (D i)]

/-- A family of functors out of `C` is *jointly conservative* if a morphism of `C` which is sent
to an isomorphism by every member of the family is itself an isomorphism. -/
abbrev JointlyConservative (F : ∀ i, C ⥤ D i) : Prop :=
  JointlyReflectIsomorphisms F

/-- A jointly conservative family reflects an isomorphism from explicit component proofs. -/
theorem JointlyConservative.isIso_of_forall {F : ∀ i, C ⥤ D i}
    (h : JointlyConservative F) {X Y : C} (f : X ⟶ Y)
    (hf : ∀ i, IsIso ((F i).map f)) : IsIso f := by
  have : ∀ i, IsIso ((F i).map f) := hf
  exact h.isIso f

/-- Mathlib's structure has the same meaning as the explicit reflection condition. -/
theorem jointlyConservative_iff (F : ∀ i, C ⥤ D i) :
    JointlyConservative F ↔
      ∀ ⦃X Y : C⦄ (f : X ⟶ Y), (∀ i, IsIso ((F i).map f)) → IsIso f := by
  constructor
  · intro h X Y f hf
    exact h.isIso_of_forall f hf
  · intro h
    exact ⟨fun f => h f inferInstance⟩

/-- An internal equivalence relation is a reflexive pair. -/
lemma _root_.CategoryTheory.IsInternalEquivalenceRelation.isReflexivePair {R X : C} {r₁ r₂ : R ⟶ X}
    (h : IsInternalEquivalenceRelation r₁ r₂) : IsReflexivePair r₁ r₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := h.refl
  exact .mk' d hd₁ hd₂

variable (F : ∀ i, C ⥤ D i)

/-- **Lemma 4.1** (reflection of regular epimorphisms). A jointly conservative family of
functors preserving pullbacks and coequalizers, with regular codomains, jointly reflects
regular epimorphisms. -/
theorem isRegularEpi_of_forall_map (hcons : JointlyConservative F)
    [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    (hrefl : ∀ i, PreservesReflexiveCoeq (F i))
    {R X Y : C} {f : X ⟶ Y} {a b : R ⟶ X} (k : IsKernelPair f a b)
    [HasCoequalizer a b] (h : ∀ i, IsRegularEpi ((F i).map f)) :
    IsRegularEpi f := by
  have : IsReflexivePair a b := k.isReflexivePair
  set e : X ⟶ coequalizer a b := coequalizer.π a b with he
  set m : coequalizer a b ⟶ Y := coequalizer.desc f k.w with hm
  have hem : e ≫ m = f := coequalizer.π_desc _ _
  have hiso : IsIso m := by
    refine hcons.isIso_of_forall m fun i => ?_
    -- the image of the kernel pair is a kernel pair
    have hk : IsKernelPair ((F i).map f) ((F i).map a) ((F i).map b) := k.map (F i)
    -- the image of `e` is still a coequalizer
    have := (hrefl i).preserves a b ‹IsReflexivePair a b›
    have hP : IsColimit (Cofork.ofπ ((F i).map e)
        (by rw [← (F i).map_comp, ← (F i).map_comp, he, coequalizer.condition]) :
          Cofork ((F i).map a) ((F i).map b)) :=
      isColimitCoforkMapOfIsColimit (F i) (coequalizer.condition a b)
        (coequalizerIsCoequalizer a b)
    -- and so is the image of `f`, being a regular epimorphism with the same kernel pair
    have := h i
    have hQ : IsColimit (Cofork.ofπ ((F i).map f) hk.w) := hk.toCoequalizer'
    have hcomp : (F i).map e ≫ (F i).map m = (F i).map f := by
      rw [← (F i).map_comp, hem]
    have key : (IsColimit.coconePointUniqueUpToIso hP hQ).hom = (F i).map m := by
      refine Cofork.IsColimit.hom_ext hP ?_
      have h1 := IsColimit.comp_coconePointUniqueUpToIso_hom hP hQ WalkingParallelPair.one
      simpa [Cofork.π, hcomp] using h1
    rw [← key]
    infer_instance
  refine ⟨R, a, b, k.w, ?_⟩
  exact IsColimit.ofIsoColimit (coequalizerIsCoequalizer a b)
    (Cofork.ext (asIso m) (by simpa using hem))

section RegularEpiKernelPair

variable {D₀ : Type u₂} [Category.{v₂} D₀]

/-- **A regular epimorphism is the coequalizer of its own kernel pair.** -/
noncomputable def isColimitCoforkOfIsKernelPair {R X Y : C} {f : X ⟶ Y} [IsRegularEpi f]
    {a b : R ⟶ X} (k : IsKernelPair f a b) : IsColimit (Cofork.ofπ f k.w) := by
  have key : ∀ {Z : C} (h : X ⟶ Z), a ≫ h = b ≫ h →
      IsRegularEpi.left f ≫ h = IsRegularEpi.right f ≫ h := by
    intro Z h hh
    set t := k.lift (IsRegularEpi.left f) (IsRegularEpi.right f) (IsRegularEpi.w f) with ht
    have ht₁ : t ≫ a = IsRegularEpi.left f := k.lift_fst _ _ _
    have ht₂ : t ≫ b = IsRegularEpi.right f := k.lift_snd _ _ _
    rw [← ht₁, ← ht₂, Category.assoc, Category.assoc, hh]
  exact Cofork.IsColimit.mk _
    (fun s => IsRegularEpi.desc f s.π (key s.π s.condition))
    (fun s => IsRegularEpi.fac f s.π _)
    (fun s m hm => IsRegularEpi.uniq f s.π _ m hm)

/-- **A functor preserving pullbacks and reflexive coequalizers preserves regular
epimorphisms**: a regular epimorphism is the coequalizer of its kernel pair, which is a
reflexive pair. -/
theorem isRegularEpi_map (G : C ⥤ D₀) [HasPullbacks C]
    (hrefl : ∀ ⦃X Y : C⦄ (u v : X ⟶ Y), IsReflexivePair u v →
      PreservesColimit (parallelPair u v) G)
    {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] : IsRegularEpi (G.map f) := by
  have k : IsKernelPair f (pullback.fst f f) (pullback.snd f f) := IsKernelPair.of_hasPullback f
  have : IsReflexivePair (pullback.fst f f) (pullback.snd f f) := k.isReflexivePair
  have := hrefl (pullback.fst f f) (pullback.snd f f) ‹_›
  exact isRegularEpi_of_regularEpi
    { W := G.obj (pullback f f)
      left := G.map (pullback.fst f f)
      right := G.map (pullback.snd f f)
      w := by rw [← G.map_comp, ← G.map_comp, k.w]
      isColimit := isColimitCoforkMapOfIsColimit G k.w (isColimitCoforkOfIsKernelPair k) }

end RegularEpiKernelPair

/-- **Lemma 4.1** (regular case). If `C` has finite limits and coequalizers of kernel pairs,
and admits a jointly conservative family of pullback- and coequalizer-preserving functors into
regular categories, then `C` is regular. -/
theorem regular_of_jointlyConservative [HasFiniteLimits C] (hcons : JointlyConservative F)
    [∀ i, PreservesLimitsOfShape WalkingCospan (F i)]
    (hrefl : ∀ i, PreservesReflexiveCoeq (F i))
    [∀ i, Regular (D i)]
    (hcoeq : ∀ {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X}, IsKernelPair f g₁ g₂ →
      HasCoequalizer g₁ g₂) :
    Regular C where
  hasCoequalizer_of_isKernelPair := hcoeq
  regularEpiIsStableUnderBaseChange := by
    constructor
    intro X Y Y' S f g f' g' hpb hg
    have hg' : IsRegularEpi g := hg
    have hker : IsKernelPair g' (pullback.fst g' g') (pullback.snd g' g') :=
      IsKernelPair.of_hasPullback g'
    have : HasCoequalizer (pullback.fst g' g') (pullback.snd g' g') := hcoeq hker
    refine isRegularEpi_of_forall_map F hcons hrefl hker fun i => ?_
    have himg : IsPullback ((F i).map f') ((F i).map g') ((F i).map g) ((F i).map f) :=
      hpb.map (F i)
    have : IsRegularEpi ((F i).map g) := isRegularEpi_map (F i) (hrefl i).preserves g
    exact Regular.regularEpiIsStableUnderBaseChange.of_isPullback himg this

/-- If `(a, b)` is the kernel pair of some morphism `f` and `q` is a coequalizer of `a` and `b`,
then `(a, b)` is also the kernel pair of `q`: an effective equivalence relation is the kernel
pair of its own coequalizer. -/
theorem isKernelPair_of_isColimitCofork {R X Y Q : C} {f : X ⟶ Y} {a b : R ⟶ X}
    (k : IsKernelPair f a b) {q : X ⟶ Q} {w : a ≫ q = b ≫ q}
    (hq : IsColimit (Cofork.ofπ q w)) : IsKernelPair q a b := by
  obtain ⟨m, hm⟩ : ∃ m : Q ⟶ Y, q ≫ m = f :=
    ⟨hq.desc (Cofork.ofπ f k.w), by simpa using hq.fac (Cofork.ofπ f k.w) WalkingParallelPair.one⟩
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux' (PullbackCone.mk a b w) fun s => ?_)
  have hs : s.fst ≫ f = s.snd ≫ f := by
    rw [← hm, ← Category.assoc, ← Category.assoc, s.condition]
  refine ⟨k.lift s.fst s.snd hs, by simp, by simp, ?_⟩
  intro m' h₁ h₂
  apply PullbackCone.IsLimit.hom_ext k.isLimit
  · exact h₁.trans (k.lift_fst _ _ _).symm
  · exact h₂.trans (k.lift_snd _ _ _).symm

section Exact

variable {D₀ : Type u₂} [Category.{v₂} D₀]

/-- A functor preserving pullbacks preserves monomorphisms. -/
theorem mono_map_of_preservesPullback (G : C ⥤ D₀) [PreservesLimitsOfShape WalkingCospan G]
    {X Y : C} (f : X ⟶ Y) [Mono f] : Mono (G.map f) :=
  IsKernelPair.mono_of_isIso_fst (by simpa using (IsKernelPair.id_of_mono f).map G)

/-- A jointly monic pair stays jointly monic under a finite-limit-preserving functor. -/
theorem jointly_mono_map (G : C ⥤ D₀) [HasFiniteLimits C] [PreservesFiniteLimits G]
    {R X : C} {r₁ r₂ : R ⟶ X}
    (hjm : ∀ ⦃T : C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b)
    ⦃T : D₀⦄ (u v : T ⟶ G.obj R) (hu : u ≫ G.map r₁ = v ≫ G.map r₁)
    (hv : u ≫ G.map r₂ = v ≫ G.map r₂) : u = v := by
  have hmono : Mono (prod.lift r₁ r₂) := by
    constructor
    intro T a b hab
    exact hjm a b (by simpa using hab =≫ prod.fst) (by simpa using hab =≫ prod.snd)
  have hGmono : Mono (G.map (prod.lift r₁ r₂)) := mono_map_of_preservesPullback G _
  have hprod : IsLimit (BinaryFan.mk (G.map (prod.fst : X ⨯ X ⟶ X))
      (G.map (prod.snd : X ⨯ X ⟶ X))) :=
    isLimitMapConeBinaryFanEquiv G _ _ (isLimitOfPreserves G (prodIsProd X X))
  rw [← cancel_mono (G.map (prod.lift r₁ r₂))]
  refine BinaryFan.IsLimit.hom_ext hprod ?_ ?_
  · simp only [Category.assoc, ← G.map_comp, BinaryFan.mk_fst]
    simpa using hu
  · simp only [Category.assoc, ← G.map_comp, BinaryFan.mk_snd]
    simpa using hv

/-- Internal equivalence relations are preserved by finite-limit-preserving functors. -/
theorem IsInternalEquivalenceRelation.map (G : C ⥤ D₀) [HasFiniteLimits C]
    [PreservesFiniteLimits G] {R X : C} {r₁ r₂ : R ⟶ X}
    (h : IsInternalEquivalenceRelation r₁ r₂) :
    IsInternalEquivalenceRelation (G.map r₁) (G.map r₂) where
  jointly_mono := jointly_mono_map G h.jointly_mono
  refl := by
    obtain ⟨d, hd₁, hd₂⟩ := h.refl
    exact ⟨G.map d, by rw [← G.map_comp, hd₁, G.map_id], by rw [← G.map_comp, hd₂, G.map_id]⟩
  symm := by
    obtain ⟨s, hs₁, hs₂⟩ := h.symm
    exact ⟨G.map s, by rw [← G.map_comp, hs₁], by rw [← G.map_comp, hs₂]⟩
  trans := by
    intro T u v huv
    obtain ⟨c, hc₁, hc₂⟩ := h.trans (pullback.fst r₂ r₁) (pullback.snd r₂ r₁) pullback.condition
    have hd : IsPullback (G.map (pullback.fst r₂ r₁)) (G.map (pullback.snd r₂ r₁))
        (G.map r₂) (G.map r₁) := (IsPullback.of_hasPullback r₂ r₁).map G
    obtain ⟨l, hl₁, hl₂⟩ : ∃ l : T ⟶ G.obj (pullback r₂ r₁),
        l ≫ G.map (pullback.fst r₂ r₁) = u ∧ l ≫ G.map (pullback.snd r₂ r₁) = v :=
      ⟨_, (PullbackCone.IsLimit.lift' hd.isLimit u v huv).2⟩
    refine ⟨l ≫ G.map c, ?_, ?_⟩
    · rw [Category.assoc, ← G.map_comp, hc₁, G.map_comp, ← Category.assoc, hl₁]
    · rw [Category.assoc, ← G.map_comp, hc₂, G.map_comp, ← Category.assoc, hl₂]

/-- **Lemma 4.1** (exact case). If `C` has finite limits, coequalizers of kernel pairs and
coequalizers of internal equivalence relations, and admits a jointly conservative family of
finite-limit- and coequalizer-preserving functors into Barr-exact categories, then `C` is
Barr-exact. -/
theorem isBarrExact_of_jointlyConservative [HasFiniteLimits C] (hcons : JointlyConservative F)
    [∀ i, PreservesFiniteLimits (F i)]
    (hrefl : ∀ i, PreservesReflexiveCoeq (F i))
    [∀ i, IsBarrExact (D i)]
    (hcoeq : ∀ {X Y Z : C} {f : X ⟶ Y} {g₁ g₂ : Z ⟶ X}, IsKernelPair f g₁ g₂ →
      HasCoequalizer g₁ g₂)
    (hcoeqrel : ∀ {R X : C} {r₁ r₂ : R ⟶ X}, IsInternalEquivalenceRelation r₁ r₂ →
      HasCoequalizer r₁ r₂) :
    IsBarrExact C := by
  have hreg : Regular C := regular_of_jointlyConservative F hcons hrefl hcoeq
  refine { hreg with isKernelPair_of_isInternalEquivalenceRelation := ?_ }
  intro R X r₁ r₂ h
  have := hcoeqrel h
  have : IsReflexivePair r₁ r₂ := h.isReflexivePair
  refine ⟨coequalizer r₁ r₂, coequalizer.π r₁ r₂, ?_⟩
  -- Form the coequalizer `q` of `(r₁, r₂)` and compare `R` with the kernel pair of `q`.
  set q : X ⟶ coequalizer r₁ r₂ := coequalizer.π r₁ r₂ with hq
  have hS : IsKernelPair q (pullback.fst q q) (pullback.snd q q) := IsKernelPair.of_hasPullback q
  set t : R ⟶ pullback q q := hS.lift r₁ r₂ (coequalizer.condition r₁ r₂) with hto
  have ht₁ : t ≫ pullback.fst q q = r₁ := hS.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd q q = r₂ := hS.lift_snd _ _ _
  -- Check that the comparison morphism `t` is an isomorphism by checking each `F i`.
  have hiso : IsIso t := by
    refine hcons.isIso_of_forall t fun i => ?_
    have hSi : IsKernelPair ((F i).map q) ((F i).map (pullback.fst q q))
        ((F i).map (pullback.snd q q)) := hS.map (F i)
    have hcof : IsColimit (Cofork.ofπ ((F i).map q)
        (show (F i).map r₁ ≫ (F i).map q = (F i).map r₂ ≫ (F i).map q by
          rw [← (F i).map_comp, ← (F i).map_comp, coequalizer.condition]) :
          Cofork ((F i).map r₁) ((F i).map r₂)) :=
      letI := (hrefl i).preserves r₁ r₂ ‹IsReflexivePair r₁ r₂›
      isColimitCoforkMapOfIsColimit (F i) (coequalizer.condition r₁ r₂)
        (coequalizerIsCoequalizer r₁ r₂)
    obtain ⟨Y', g, hg⟩ :=
      CategoryTheory.IsBarrExact.isKernelPair_of_isInternalEquivalenceRelation (h.map (F i))
    have hKP : IsKernelPair ((F i).map q) ((F i).map r₁) ((F i).map r₂) :=
      isKernelPair_of_isColimitCofork hg hcof
    -- Both `(F i).map r` and `(F i).map (pullback q q)` are kernel pairs of `(F i).map q`.
    have hkey : (IsLimit.conePointUniqueUpToIso hKP.isLimit hSi.isLimit).hom = (F i).map t := by
      refine PullbackCone.IsLimit.hom_ext hSi.isLimit ?_ ?_
      · have h := IsLimit.conePointUniqueUpToIso_hom_comp hKP.isLimit hSi.isLimit WalkingCospan.left
        have hm : (F i).map t ≫ (F i).map (pullback.fst q q) = (F i).map r₁ := by
          rw [← (F i).map_comp, ht₁]
        exact h.trans hm.symm
      · have h := IsLimit.conePointUniqueUpToIso_hom_comp hKP.isLimit hSi.isLimit
          WalkingCospan.right
        have hm : (F i).map t ≫ (F i).map (pullback.snd q q) = (F i).map r₂ := by
          rw [← (F i).map_comp, ht₂]
        exact h.trans hm.symm
    rw [← hkey]
    exact Iso.isIso_hom _
  exact IsPullback.of_iso_pullback ⟨coequalizer.condition r₁ r₂⟩ (asIso t) ht₁ ht₂

end Exact

end CategoryTheory
