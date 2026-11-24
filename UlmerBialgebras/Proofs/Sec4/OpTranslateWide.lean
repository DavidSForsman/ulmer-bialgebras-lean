module

public import Foundations.CategoryTheory.Limits.OpTranslate
public import UlmerBialgebras.Kan.RegMonoWidePullback
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutModel
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Opposite translations for regular wide diagrams

The generic translations live in `OpTranslate.lean`. This file adds the paper's
regular-epi predicates and the regular-mono wide-pullback interfaces, after their defining
modules are available, to keep the product-limit layer independent of `Challenge.Defs2`.

## Main results

* `UlmerBialgebras.OpTranslate.preservesWidePullbacks_iff_op_in`: `F` preserves wide pullbacks of
  regular monomorphisms iff `F.op` preserves wide pushouts of regular epimorphisms.
* `UlmerBialgebras.OpTranslate.preservesWidePullbacks_and_regularMonos_pi_of_op`: both clauses of
  the dual of Corollary 4.18, for a functor on a finite product.
* `UlmerBialgebras.OpTranslate.regEpis_reflexive_of_kernelPairs`: with kernel pairs, regular
  epimorphisms have reflexive coequalizer presentations.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.18
  and Example 4.20 (2)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.OpTranslate

open CategoryTheory Limits Opposite

variable {C : Type u} [Category.{v} C]

/-- Coreflexive equalizer presentations are the paper's reflexive coequalizer presentations
in the opposite category. -/
lemma regularMonos_coreflexive_iff_op :
    RegMonoWide.RegularMonosAreCoreflexiveEqualizers C ↔
      Paper.RegEpisAreReflexiveCoequalizers Cᵒᵖ := by
  constructor
  · intro h a c m hm
    obtain ⟨q, f, g, hfg, w, ⟨hl⟩⟩ := h m.unop
      ((isRegularMono_unop_iff_isRegularEpi m).2 ⟨hm⟩)
    have w' : f.op ≫ m = g.op ≫ m := by simpa using congrArg Quiver.Hom.op w
    refine ⟨Opposite.op q, f.op, g.op, (isCoreflexivePair_iff_op f g).1 hfg, w', ⟨?_⟩⟩
    exact Fork.isLimitOfιEquivIsColimitOp m.unop m.unop w w' rfl hl
  · intro h a c m hm
    obtain ⟨q, f, g, hfg, w, ⟨hl⟩⟩ := h m.op ((isRegularMono_iff_op m).1 hm).regularEpi
    have w' : m ≫ f.unop = m ≫ g.unop := by simpa using congrArg Quiver.Hom.unop w
    refine ⟨q.unop, f.unop, g.unop, (isCoreflexivePair_iff_op f.unop g.unop).2 hfg,
      w', ⟨?_⟩⟩
    exact Cofork.isColimitOfπEquivIsLimitUnop m.op m.op w w' rfl hl

/-- A wide cospan becomes a wide span in the opposite category. -/
@[implicit_reducible]
def wideCospanOp {K : Type w} (D : WidePullbackShape K ⥤ C) :
    WidePushoutShape K ⥤ Cᵒᵖ :=
  (widePullbackShapeOpEquiv K).inverse ⋙ D.op

/-- A wide span in the opposite category becomes a wide cospan. -/
@[implicit_reducible]
def wideSpanUnop {K : Type w} (D : WidePushoutShape K ⥤ Cᵒᵖ) :
    WidePullbackShape K ⥤ C := widePullbackShapeOp K ⋙ D.leftOp

/-- Unop of a wide span matches Mathlib's shape equivalence after taking opposites. -/
lemma wideSpanUnop_op {K : Type w} (D : WidePushoutShape K ⥤ Cᵒᵖ) :
    (wideSpanUnop D).op = (widePullbackShapeOpEquiv K).functor ⋙ D := rfl

/-- Regular-mono wide-pullback preservation is regular-epi wide-pushout preservation in
opposites. -/
lemma preservesWidePullbacks_iff_op_in {K : Type w} {E : Type*} [Category E] (F : C ⥤ E) :
    RegMonoWide.PreservesWidePullbacksIn K (RegMonoWide.regMono C) F ↔
      RegEpiWide.PreservesWidePushoutsIn K (RegEpiWide.regEpi Cᵒᵖ) F.op := by
  constructor
  · intro h D hD
    have : PreservesLimit (wideSpanUnop D) F := by
      apply h
      intro k
      change IsRegularMono ((D.map (WidePushoutShape.Hom.init k)).unop)
      exact (isRegularMono_unop_iff_isRegularEpi _).2 (hD k)
    have : PreservesColimit (wideSpanUnop D).op F.op :=
      (preservesLimit_iff_op (wideSpanUnop D) F).1 inferInstance
    have : PreservesColimit ((widePullbackShapeOpEquiv K).functor ⋙ D) F.op := by
      rw [← wideSpanUnop_op D]
      infer_instance
    exact Functor.Final.preservesColimit_of_comp (widePullbackShapeOpEquiv K).functor
  · intro h D hD
    have : PreservesColimit ((widePullbackShapeOpEquiv K).inverse ⋙ D.op) F.op := by
      apply h (wideCospanOp D)
      intro k
      change IsRegularEpi (D.map (WidePullbackShape.Hom.term k)).op
      exact (isRegularMono_iff_op _).1 (hD k)
    have : PreservesColimit D.op F.op :=
      Functor.Final.preservesColimit_of_comp (widePullbackShapeOpEquiv K).inverse
    exact (preservesLimit_iff_op D F).2 inferInstance

/-- The paper's witness predicate and the regular-epi morphism property agree. -/
lemma preservesWidePushouts_iff_in {K : Type w} {A E : Type*} [Category A] [Category E]
    (F : A ⥤ E) :
    Paper.PreservesWidePushoutsOfRegEpis K F ↔
      RegEpiWide.PreservesWidePushoutsIn K (RegEpiWide.regEpi A) F := by
  constructor
  · intro h D hD
    exact h D (fun k => (hD k).regularEpi)
  · intro h D hD
    exact h D (fun k => ⟨hD k⟩)

/-- Precomposition by an equivalence transports wide-pushout preservation of regular epis. -/
lemma preservesWidePushouts_precompose {K : Type w} {A B E : Type*}
    [Category A] [Category B] [Category E] (H : A ⥤ B) [H.IsEquivalence] (F : B ⥤ E)
    (hF : RegEpiWide.PreservesWidePushoutsIn K (RegEpiWide.regEpi B) F) :
    RegEpiWide.PreservesWidePushoutsIn K (RegEpiWide.regEpi A) (H ⋙ F) := by
  intro D hD
  have : PreservesColimit (D ⋙ H) F := by
    apply hF
    intro k
    have : IsRegularEpi (D.map (WidePushoutShape.Hom.init k)) := hD k
    exact isRegularEpi_map H (D.map (WidePushoutShape.Hom.init k))
  infer_instance

/-- Componentwise regular monomorphisms assemble by the primal regular-epi result. -/
lemma isRegularMono_of_components {ι : Type*} (A : ι → Type u) [∀ i, Category.{v} (A i)]
    {x y : ∀ i, A i} (m : x ⟶ y) (hm : ∀ i, IsRegularMono (m i)) : IsRegularMono m := by
  have : IsRegularEpi ((piOpTo A).map m.op) :=
    RegEpiWide.isRegularEpi_of_piRegEpi _
      (fun i => (isRegularMono_iff_op (m i)).1 (hm i))
  have hout := isRegularEpi_map (piOpFrom A) ((piOpTo A).map m.op)
  change IsRegularEpi m.op at hout
  exact (isRegularMono_iff_op m).2 hout

/-- The componentwise preservation hypotheses commute with the product/opposite equivalence. -/
lemma componentwise_op_preservesWide {K : Type w} {ι : Type*} [DecidableEq ι]
    (A : ι → Type u) [∀ i, Category.{v} (A i)] {E : Type*} [Category E]
    (F : (∀ i, A i) ⥤ E)
    (hF : ∀ i (x : ∀ j, A j), RegMonoWide.PreservesWidePullbacksIn K
      (RegMonoWide.regMono (A i)) (updateFunctor x i ⋙ F)) :
    ∀ i (x : ∀ j, (A j)ᵒᵖ), RegEpiWide.PreservesWidePushoutsIn K
      (RegEpiWide.regEpi (A i)ᵒᵖ) (updateFunctor x i ⋙ (piOpFrom A ⋙ F.op)) := by
  intro i x
  have h := (preservesWidePullbacks_iff_op_in
    (updateFunctor (fun j => (x j).unop) i ⋙ F)).1 (hF i (fun j => (x j).unop))
  have he : updateFunctor x i ⋙ piOpFrom A =
      (updateFunctor (fun j => (x j).unop) i).op := by
    simpa only [Opposite.op_unop] using
      update_op_comp_piOpFrom A (fun j => (x j).unop) i
  rw [← Functor.assoc, he]
  exact h

/-- Both clauses of the dual Corollary 4.18 follow from the primal corollary in opposites. -/
lemma preservesWidePullbacks_and_regularMonos_pi_of_op {K : Type w} [Nontrivial K]
    {ι : Type*} [DecidableEq ι] [Finite ι] (A : ι → Type u) [∀ i, Category.{v} (A i)]
    {E : Type*} [Category E] (F : (∀ i, A i) ⥤ E)
    (hA : ∀ i, RegMonoWide.RegularMonosAreCoreflexiveEqualizers (A i))
    (hF : ∀ i (x : ∀ j, A j), RegMonoWide.PreservesWidePullbacksIn K
      (RegMonoWide.regMono (A i)) (updateFunctor x i ⋙ F)) :
    RegMonoWide.PreservesWidePullbacksIn K (RegMonoWide.regMono (∀ i, A i)) F ∧
      ∀ ⦃x y : ∀ i, A i⦄ (m : x ⟶ y), IsRegularMono m → IsRegularMono (F.map m) := by
  have h := RegEpiWide.preservesWidePushouts_and_regularEpis_pi (piOpFrom A ⋙ F.op)
    (fun i => (regularMonos_coreflexive_iff_op (C := A i)).1 (hA i))
    (fun i x => (preservesWidePushouts_iff_in _).2
      (componentwise_op_preservesWide A F hF i x))
  have hback := preservesWidePushouts_precompose (piOpTo A) (piOpFrom A ⋙ F.op)
    ((preservesWidePushouts_iff_in _).1 h.1)
  refine ⟨(preservesWidePullbacks_iff_op_in F).2 ?_, ?_⟩
  · simpa only [← Functor.assoc, piOpTo_comp_piOpFrom, Functor.id_comp] using hback
  · intro x y m hm
    have : IsRegularEpi m.op := (isRegularMono_iff_op m).1 hm
    have hm' := isRegularEpi_map (piOpTo A) m.op
    have hout : IsRegularEpi ((F.map m).op) := by
      change IsRegularEpi ((piOpFrom A ⋙ F.op).map ((piOpTo A).map m.op))
      exact ⟨h.2 ((piOpTo A).map m.op) hm'.regularEpi⟩
    exact (isRegularEpi_op_iff_isRegularMono (F.map m)).1 hout

/-- Single-diagram product-valued preservation is dual to the primal colimit helper. -/
lemma pi'_preservesLimit_of_op {ι : Type*} (A : ι → Type u) [∀ i, Category.{v} (A i)]
    {J B : Type*} [Category J] [Category B] (D : J ⥤ B) (F : ∀ i, B ⥤ A i)
    [∀ i, PreservesLimit D (F i)] : PreservesLimit D (Functor.pi' F) := by
  have : ∀ i, PreservesColimit D.op (F i).op :=
    fun i => (preservesLimit_iff_op D (F i)).1 inferInstance
  have : PreservesColimit D.op (Functor.pi' (fun i => (F i).op)) :=
    RegEpiWide.pi'_preservesColimit D.op (fun i => (F i).op)
  have : PreservesColimit D.op ((Functor.pi' F).op ⋙ piOpTo A) := by
    rw [pi'_op_comp_piOpTo]
    infer_instance
  have : PreservesColimit D.op (Functor.pi' F).op :=
    preservesColimit_of_reflects_of_preserves _ (piOpTo A)
  exact (preservesLimit_iff_op D (Functor.pi' F)).2 inferInstance

/-- With kernel pairs, regular epimorphisms have reflexive coequalizer presentations. -/
lemma regEpis_reflexive_of_kernelPairs
    (h : ∀ ⦃a b : C⦄ (f : a ⟶ b), HasPullback f f) :
    Paper.RegEpisAreReflexiveCoequalizers C := by
  intro a b f ⟨r⟩
  have := h f
  have k : IsKernelPair f (pullback.fst f f) (pullback.snd f f) := IsPullback.of_hasPullback f f
  exact ⟨pullback f f, pullback.fst f f, pullback.snd f f,
    IsReflexivePair.mk' (pullback.lift (𝟙 a) (𝟙 a) rfl) (by simp) (by simp), k.w,
    ⟨k.toCoequalizer r⟩⟩

end UlmerBialgebras.OpTranslate
