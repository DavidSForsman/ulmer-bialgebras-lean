module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushout
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2

/-!
# Componentwise preservation of wide pushouts in a finite product

The finite-set induction packages both clauses of Corollary 4.18. The regular-mono version
in `RegMonoWidePullbackPi.lean` applies these results in opposite categories.

## Main results

* `UlmerBialgebras.RegEpiWide.preservesWidePushouts_regularEpi_pi`: Corollary 4.18 (wide-pushout
  clause) for a functor on a finite product.
* `UlmerBialgebras.RegEpiWide.preservesWidePushouts_and_regularEpis_pi`: both conclusions of
  Corollary 4.18, with the paper's predicates.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.18
-/

@[expose] public section

universe w w' v u v₃ u₃

namespace UlmerBialgebras.RegEpiWide

open CategoryTheory Limits

variable {K : Type w} [Nontrivial K]
variable {ι : Type w'} [DecidableEq ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {E : Type u₃} [Category.{v₃} E]

/-- The class of morphisms of `∏_j C_j` that are componentwise regular epimorphisms. -/
def piRegEpi : MorphismProperty (∀ j, C j) := fun _ _ f => ∀ j, IsRegularEpi (f j)

omit [DecidableEq ι] in
/-- A componentwise regular epimorphism in `∏_j C_j` is an epimorphism. -/
lemma epi_of_piRegEpi {x y : ∀ j, C j} (f : x ⟶ y) (hf : piRegEpi f) : Epi f := by
  constructor
  intro Z g h e
  funext j
  have := hf j
  exact (cancel_epi (f j)).1 (congr_fun e j)

omit [DecidableEq ι] in
/-- Each component `f j` of a regular epimorphism `f` in `∏_j C_j` is a regular epimorphism, since
evaluation preserves the coequalizer presenting `f`. -/
lemma isRegularEpi_eval {x y : ∀ j, C j} (f : x ⟶ y) [IsRegularEpi f] (j : ι) :
    IsRegularEpi (f j) := by
  classical
  obtain ⟨h⟩ := IsRegularEpi.regularEpi (f := f)
  exact ⟨⟨{ W := h.W j
            left := h.left j
            right := h.right j
            w := congr_fun h.w j
            isColimit := (isColimitMapCoconeCoforkEquiv (Pi.eval C j) h.w)
              (piEvalIsColimit h.isColimit j) }⟩⟩

omit [DecidableEq ι] in
/-- Componentwise regular epis assemble to a regular epi. -/
lemma isRegularEpi_of_piRegEpi {x y : ∀ j, C j} (m : x ⟶ y) (hm : piRegEpi m) :
    IsRegularEpi m := by
  classical
  let hs : ∀ j, RegularEpi (m j) := fun j => (hm j).regularEpi.some
  refine ⟨⟨{ W := fun j => (hs j).W
             left := fun j => (hs j).left
             right := fun j => (hs j).right
             w := funext fun j => (hs j).w
             isColimit := Cofork.IsColimit.mk _ (fun s j =>
              ((hs j).desc' (s.π j) (congr_fun s.condition j)).1)
              (fun s => ?_) (fun s l hl => ?_) }⟩⟩
  · funext j
    exact ((hs j).desc' (s.π j) (congr_fun s.condition j)).2
  · funext j
    have := RegularEpi.epi (m j) (hs j)
    apply (cancel_epi (m j)).1
    exact (congr_fun hl j).trans
      ((hs j).desc' (s.π j) (congr_fun s.condition j)).2.symm

omit [DecidableEq ι] in
/-- If regular epis in each `C_i` are codiagonal coequalizers of regular-epi pairs, the same holds
for componentwise regular epis in `∏_j C_j`, with componentwise regular-epi pairs. -/
lemma piRegEpi_core (h : ∀ i, RegularEpisAreCodiagonalCoequalizers (C i))
    ⦃b c : ∀ j, C j⦄ (m : c ⟶ b) (hm : piRegEpi m) :
    ∃ (q : ∀ j, C j) (f g : q ⟶ c), piRegEpi f ∧ piRegEpi g ∧
      IsCodiagonalCoequalizer m f g := by
  choose q f g hf hg hfg using fun j => h j (m j) (hm j)
  refine ⟨q, f, g, hf, hg, ⟨funext fun j => (hfg j).condition,
    fun T t t' e => funext fun j => (hfg j).codiag _ _ (congr_fun e j), fun T t e => ?_⟩⟩
  choose u hu using fun j => (hfg j).factor (t j) (congr_fun e j)
  exact ⟨u, funext hu⟩

variable (F : (∀ j, C j) ⥤ E)

omit [Nontrivial K] in
/-- If `F` preserves `K`-wide pushouts of regular epis in each variable separately, then `F`
restricted to the single variable `i` (others fixed at `x`) preserves wide pushouts of componentwise
regular epis. -/
lemma restrictP_single_preservesWide
    (hF : ∀ (i : ι) (x : ∀ j, C j),
      PreservesWidePushoutsIn K (regEpi (C i)) (updateFunctor x i ⋙ F))
    (i : ι) (x : ∀ j, C j) :
    PreservesWidePushoutsIn K piRegEpi (restrictP x (· = i) ⋙ F) := by
  have e : restrictP x (· = i) = Pi.eval C i ⋙ updateFunctor x i := by
    rw [restrictP, updateFunctor, comp_pi']
    refine pi'_congr (fun j => ?_)
    by_cases hj : j = i
    · subst hj
      rw [ite_eq_left rfl, dite_eq_left rfl]
      rfl
    · rw [ite_eq_right hj, dite_eq_right hj]
      rfl
  intro Dg hDg
  rw [e, Functor.assoc]
  have : PreservesColimit (Dg ⋙ Pi.eval C i) (updateFunctor x i ⋙ F) :=
    hF i x _ (fun k => hDg k i)
  infer_instance

/-- If `F` preserves `K`-wide pushouts of regular epis in each variable separately, then for every
finite set `s` of variables, `F` restricted to the variables in `s` (others fixed at `x`) preserves
wide pushouts of componentwise regular epis (induction on `s`). -/
theorem restrictP_finset_preservesWide
    (hC : ∀ i, RegularEpisAreCodiagonalCoequalizers (C i))
    (hF : ∀ (i : ι) (x : ∀ j, C j),
      PreservesWidePushoutsIn K (regEpi (C i)) (updateFunctor x i ⋙ F)) :
    ∀ (s : Finset ι) (x : ∀ j, C j),
      PreservesWidePushoutsIn K piRegEpi (restrictP x (fun j => j ∈ s) ⋙ F) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro x Dg _
      rw [restrictP_congr x (q := fun _ => False) (fun j => by simp), restrictP_false]
      have : PreservesColimitsOfShape (WidePushoutShape K)
          ((Functor.const (∀ j, C j)).obj x ⋙ F) :=
        preservesColimitsOfShape_of_natIso (Functor.constComp _ x F).symm
      infer_instance
  | insert i₀ s hi₀ ih =>
      intro x Dg hDg
      have hmix : PreservesColimit (Dg ⋙ Functor.diag (∀ j, C j))
          (mix x i₀ (fun j => j ∈ s) ⋙ F) := by
        refine preservesColimit_prod_of_componentwise (mix x i₀ (fun j => j ∈ s) ⋙ F)
          piRegEpi piRegEpi (fun _ _ f hf => epi_of_piRegEpi f hf)
          (fun _ _ f hf => epi_of_piRegEpi f hf) (fun y => ?_) (fun z => ?_)
          (piRegEpi_core hC) _ (fun k => ⟨hDg k, hDg k⟩)
        · rw [← Functor.assoc, sectL_comp_mix x y i₀ (fun j => j ∈ s)]
          exact restrictP_single_preservesWide F hF i₀ _
        · rw [← Functor.assoc, sectR_comp_mix x z i₀ (fun j => j ∈ s) hi₀]
          exact ih _
      rw [restrictP_congr x (q := fun j => j = i₀ ∨ j ∈ s) (fun j => by simp),
        ← diag_comp_mix x i₀ (fun j => j ∈ s), Functor.assoc]
      infer_instance

/-- Corollary 4.18 of [forsman2026syntactic] (wide-pushout clause): if regular epis in each `C_i`
are codiagonal coequalizers of regular-epi pairs (e.g. reflexive coequalizers) and `F : ∏_i C_i ⥤ E`
preserves `K`-wide pushouts of regular epis componentwise, then `F` preserves `K`-wide pushouts of
regular epis. The reduction to two variables is an induction over `ι`. -/
theorem preservesWidePushouts_regularEpi_pi [Finite ι]
    (hC : ∀ i, RegularEpisAreCodiagonalCoequalizers (C i))
    (hF : ∀ (i : ι) (x : ∀ j, C j),
      PreservesWidePushoutsIn K (regEpi (C i)) (updateFunctor x i ⋙ F)) :
    PreservesWidePushoutsIn K (regEpi (∀ j, C j)) F := by
  have := Fintype.ofFinite ι
  intro Dg hDg
  have hDg' : IsWideSpanIn piRegEpi Dg := fun k j => by
    have : IsRegularEpi (Dg.map (WidePushoutShape.Hom.init k)) := hDg k
    exact isRegularEpi_eval _ j
  have key := restrictP_finset_preservesWide F hC hF Finset.univ (Dg.obj none)
  rw [restrictP_congr _ (q := fun _ => True) (fun j => by simp), restrictP_true,
    Functor.id_comp] at key
  exact key Dg hDg'

omit [DecidableEq ι] in
/-- Assemble the same presentations in the product, for the regular-epi preservation clause. -/
lemma regularEpisAreCodiagonalCoequalizers_pi
    (hC : ∀ i, RegularEpisAreCodiagonalCoequalizers (C i)) :
    RegularEpisAreCodiagonalCoequalizers (∀ j, C j) := by
  classical
  intro b c m hm
  have := hm
  obtain ⟨q, f, g, hf, hg, hfg⟩ := piRegEpi_core hC m (fun j => isRegularEpi_eval m j)
  exact ⟨q, f, g, isRegularEpi_of_piRegEpi f hf, isRegularEpi_of_piRegEpi g hg, hfg⟩

/-- Convert the paper's reflexive-coequalizer hypothesis into codiagonal presentations. -/
lemma codiagonal_of_reflexive (X : Type u) [Category.{v} X]
    (h : Paper.RegEpisAreReflexiveCoequalizers X) :
    RegularEpisAreCodiagonalCoequalizers X := by
  intro a c m hm
  obtain ⟨q, f, g, hfg, w, ⟨hl⟩⟩ := h m hm.regularEpi
  have : IsReflexivePair f g := hfg
  obtain ⟨r, hrf, hrg⟩ := IsReflexivePair.common_section f g
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨r, hrf⟩
  have : IsSplitEpi g := IsSplitEpi.mk' ⟨r, hrg⟩
  exact ⟨q, f, g, inferInstance, inferInstance, isCodiagonalCoequalizer_of_reflexive hl⟩

/-- Both conclusions of Corollary 4.18, with the paper's predicates. -/
theorem preservesWidePushouts_and_regularEpis_pi [Finite ι]
    (hC : ∀ i, Paper.RegEpisAreReflexiveCoequalizers (C i))
    (hF : ∀ (i : ι) (x : ∀ j, C j),
      Paper.PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙ F)) :
    Paper.PreservesWidePushoutsOfRegEpis K F ∧
      ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi (F.map f)) := by
  have hC' : ∀ i, RegularEpisAreCodiagonalCoequalizers (C i) :=
    fun i => codiagonal_of_reflexive (C i) (hC i)
  have hF' : ∀ (i : ι) (x : ∀ j, C j),
      PreservesWidePushoutsIn K (regEpi (C i)) (updateFunctor x i ⋙ F) := by
    intro i x Dg hDg
    exact hF i x Dg (fun k => (hDg k).regularEpi)
  have hwide := preservesWidePushouts_regularEpi_pi F hC' hF'
  constructor
  · intro Dg hDg
    exact hwide Dg (fun k => ⟨hDg k⟩)
  · intro x y f hf
    exact (regularEpi_map_of_preservesWide
      (regularEpisAreCodiagonalCoequalizers_pi hC') hwide f ⟨hf⟩).regularEpi

end UlmerBialgebras.RegEpiWide
