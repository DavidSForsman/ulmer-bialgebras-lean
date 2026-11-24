module

public import Foundations.CategoryTheory.Limits.MultiReflexivePair
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Wide pushouts of regular epimorphisms as colimits of families of reflexive pairs

For a family of regular epimorphisms `f j : a ⟶ b j` with kernel pairs, the wide pushout of the
`f j` is the colimit of the family of kernel pairs (`kernelPairDiagram`), a diagram of the sifted
shape `MultiReflexivePair` ([forsman2026syntactic], §4, the sifted shapes, example 3). Hence a
functor preserving the coequalizers of the kernel pairs and the colimit of the kernel-pair diagram
preserves the wide pushout (`preservesColimit_widePushout_of_kernelPairs`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], §4
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace UlmerBialgebras

namespace MultiReflexivePair

variable {L : Type u} {D : Type*} [Category D] (G : MultiReflexivePair L ⥤ D)

/-- The cocone on `G` given by a morphism out of the apex which coequalizes every pair. -/
def coconeOfApex {X : D} (g : G.obj apex ⟶ X)
    (hg : ∀ j, G.map (d j false) ≫ g = G.map (d j true) ≫ g) : Cocone G where
  pt := X
  ι :=
    { app := fun x => match x with
        | apex => g
        | src j => G.map (d j false) ≫ g
      naturality := by
        rintro (_ | j) (_ | i) ⟨φ⟩
        · cases φ
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [show (⟨()⟩ : (apex : MultiReflexivePair L) ⟶ apex) = 𝟙 (apex : MultiReflexivePair L)
            from rfl, G.map_id,
            Category.id_comp]
        · cases φ
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc, ← G.map_comp]
          exact (G.congr_map (s_d i false) =≫ g).trans (by simp)
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          cases φ
          · rfl
          · exact (hg j).symm
        · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
          rw [← Category.assoc, ← G.map_comp]
          obtain ⟨_ | b, hφ⟩ := φ
          · obtain rfl := hφ rfl
            rw [show (⟨⟨none, hφ⟩⟩ : (src i : MultiReflexivePair L) ⟶ src i) =
              𝟙 (src i : MultiReflexivePair L) from rfl,
              Category.id_comp]
          · cases b
            · rfl
            · exact (hg j).symm }

/-- The leg at the apex of `coconeOfApex G g hg` is `g`. -/
@[simp] lemma coconeOfApex_ι_apex {X : D} (g : G.obj apex ⟶ X)
    (hg : ∀ j, G.map (d j false) ≫ g = G.map (d j true) ≫ g) :
    (coconeOfApex G g hg).ι.app apex = g := rfl

/-- The components of a cocone are determined by its apex component. -/
lemma cocone_ι_src (c : Cocone G) (j : L) :
    c.ι.app (src j) = G.map (d j false) ≫ c.ι.app apex := by
  exact (c.w (d j false)).symm

/-- A cocone coequalizes every pair at its apex component. -/
lemma cocone_condition (c : Cocone G) (j : L) :
    G.map (d j false) ≫ c.ι.app apex = G.map (d j true) ≫ c.ι.app apex := by
  rw [c.w, c.w]

/-- Morphisms out of the apex of a colimit cocone are determined by the apex component. -/
lemma IsColimit.hom_ext' {c : Cocone G} (hc : IsColimit c) {X : D} {m m' : c.pt ⟶ X}
    (h : c.ι.app apex ≫ m = c.ι.app apex ≫ m') : m = m' := by
  refine hc.hom_ext fun x => ?_
  rcases x with _ | j
  · exact h
  · rw [cocone_ι_src, Category.assoc, Category.assoc, h]

end MultiReflexivePair

section WidePushout

open MultiReflexivePair

variable {C : Type*} [Category C] {D : Type*} [Category D] {L : Type u}
  (dg : WidePushoutShape L ⥤ C) [∀ j, HasPullback (dg.map (WidePushoutShape.Hom.init j))
    (dg.map (WidePushoutShape.Hom.init j))]

/-- The legs of a wide pushout diagram. -/
abbrev leg (j : L) : dg.obj none ⟶ dg.obj (some j) := dg.map (WidePushoutShape.Hom.init j)

/-- **The kernel-pair diagram** of a wide pushout diagram: the family of the kernel pairs of the
legs, a diagram of the sifted shape `MultiReflexivePair L`. -/
def kernelPairDiagram : MultiReflexivePair L ⥤ C :=
  mkFunctor (dg.obj none) (fun j => pullback (leg dg j) (leg dg j))
    (fun j => pullback.fst _ _) (fun j => pullback.snd _ _)
    (fun j => pullback.lift (𝟙 _) (𝟙 _) rfl) (fun _ => by simp) (fun _ => by simp)

/-- The kernel-pair diagram sends the `false` leg `d j false` to the first projection of the kernel
pair of `leg dg j`. -/
@[simp] lemma kernelPairDiagram_map_d_false (j : L) :
    (kernelPairDiagram dg).map (d j false) = pullback.fst (leg dg j) (leg dg j) := rfl

/-- The kernel-pair diagram sends the `true` leg `d j true` to the second projection of the kernel
pair of `leg dg j`. -/
@[simp] lemma kernelPairDiagram_map_d_true (j : L) :
    (kernelPairDiagram dg).map (d j true) = pullback.snd (leg dg j) (leg dg j) := rfl

variable {dg}

/-- The cocone on the kernel-pair diagram of a cocone on `dg`. -/
def kernelPairCocone (c : Cocone dg) : Cocone (kernelPairDiagram dg) :=
  coconeOfApex _ (c.ι.app none) fun j => by
    simp only [kernelPairDiagram_map_d_false, kernelPairDiagram_map_d_true]
    rw [← c.w (WidePushoutShape.Hom.init j)]
    exact pullback.condition_assoc (f := leg dg j) (g := leg dg j) _

/-- A regular epimorphism with a kernel pair is the coequalizer of its kernel pair. -/
def kernelPairCoforkIsColimit (hdg : ∀ j, Nonempty (RegularEpi (leg dg j))) (j : L) :
    IsColimit (Cofork.ofπ (leg dg j) (pullback.condition (f := leg dg j) (g := leg dg j))) :=
  IsKernelPair.toCoequalizer (IsPullback.of_hasPullback (leg dg j) (leg dg j)) (hdg j).some

/-- The cocone on a wide pushout diagram given by a morphism out of the apex `a` and morphisms
out of the `b j` through which it factors. -/
def widePushoutCocone {C' : Type*} [Category C'] (F : WidePushoutShape L ⥤ C') {X : C'}
    (a : F.obj none ⟶ X) (e : ∀ j, F.obj (some j) ⟶ X)
    (he : ∀ j, F.map (WidePushoutShape.Hom.init j) ≫ e j = a) : Cocone F where
  pt := X
  ι :=
    { app := fun x => match x with
        | none => a
        | some j => e j
      naturality := by
        rintro (_ | j) (_ | i) (_ | _)
        · simp
        · simpa using he _
        · simp }

variable (hdg : ∀ j, Nonempty (RegularEpi (leg dg j)))
include hdg

/-- The cocone on `dg` of a cocone on the kernel-pair diagram: the legs are induced by the
coequalizer property of the regular epimorphisms. -/
def coconeOfKernelPairCocone (s : Cocone (kernelPairDiagram dg)) : Cocone dg :=
  widePushoutCocone dg (s.ι.app apex)
    (fun j => (kernelPairCoforkIsColimit hdg j).desc
      (Cofork.ofπ (s.ι.app apex) (cocone_condition _ s j)))
    (fun j => (kernelPairCoforkIsColimit hdg j).fac _ WalkingParallelPair.one)

/-- **The kernel-pair cocone of a colimit cocone is a colimit cocone.** -/
def isColimitKernelPairCocone {c : Cocone dg} (hc : IsColimit c) :
    IsColimit (kernelPairCocone c) where
  desc s := hc.desc (coconeOfKernelPairCocone hdg s)
  fac s x := by
    rcases x with _ | j
    · exact hc.fac _ none
    · rw [cocone_ι_src, cocone_ι_src]
      exact (Category.assoc _ _ _).trans (_ ≫= hc.fac _ none)
  uniq s m hm := by
    refine hc.hom_ext fun x =>
      (?_ : c.ι.app x ≫ m = (coconeOfKernelPairCocone hdg s).ι.app x).trans (hc.fac _ x).symm
    rcases x with _ | j
    · exact hm apex
    · refine Cofork.IsColimit.hom_ext (kernelPairCoforkIsColimit hdg j) ?_
      exact (Category.assoc _ _ _).symm.trans
        ((c.w (WidePushoutShape.Hom.init j) =≫ m).trans
          ((hm apex).trans ((kernelPairCoforkIsColimit hdg j).fac
            (Cofork.ofπ (s.ι.app apex) (cocone_condition _ s j)) WalkingParallelPair.one).symm))

/-- **A functor preserving the coequalizers of the kernel pairs and the colimit of the kernel-pair
diagram preserves the wide pushout of a family of regular epimorphisms.** -/
theorem preservesColimit_widePushout_of_kernelPairs (F : C ⥤ D)
    [∀ j, PreservesColimit (parallelPair (pullback.fst (leg dg j) (leg dg j))
      (pullback.snd (leg dg j) (leg dg j))) F]
    [PreservesColimit (kernelPairDiagram dg) F] : PreservesColimit dg F := by
  refine ⟨fun {c} hc => ⟨?_⟩⟩
  have hk : IsColimit (F.mapCocone (kernelPairCocone c)) :=
    isColimitOfPreserves F (isColimitKernelPairCocone hdg hc)
  have hFk : ∀ j, IsColimit (Cofork.ofπ (F.map (leg dg j))
      (by simp only [← F.map_comp, pullback.condition]) :
        Cofork (F.map (pullback.fst (leg dg j) (leg dg j)))
          (F.map (pullback.snd (leg dg j) (leg dg j)))) := fun j =>
    isColimitCoforkMapOfIsColimit F _ (kernelPairCoforkIsColimit hdg j)
  have hepi : ∀ j, Epi (F.map (leg dg j)) := fun j => epi_of_isColimit_cofork (hFk j)
  have cond : ∀ (t : Cocone (dg ⋙ F)) (j : L),
      (kernelPairDiagram dg ⋙ F).map (d j false) ≫ t.ι.app none =
        (kernelPairDiagram dg ⋙ F).map (d j true) ≫ t.ι.app none := fun t j => by
    rw [← t.w (WidePushoutShape.Hom.init j)]
    have h := F.congr_map (pullback.condition (f := leg dg j) (g := leg dg j)) =≫ t.ι.app (some j)
    simp only [Functor.map_comp, Category.assoc] at h
    exact h
  exact
    { desc := fun t => hk.desc (coconeOfApex _ (t.ι.app none) (cond t))
      fac := fun t x => by
        rcases x with _ | j
        · exact hk.fac _ apex
        · refine (hepi j).left_cancellation _ _ ?_
          have h1 : F.map (leg dg j) ≫ F.map (c.ι.app (some j)) = F.map (c.ι.app none) := by
            rw [← F.map_comp, c.w]
          exact (Category.assoc _ _ _).symm.trans ((h1 =≫ _).trans
            ((hk.fac _ apex).trans (t.w (WidePushoutShape.Hom.init j)).symm))
      uniq := fun t m hm => IsColimit.hom_ext' _ hk
        ((hm none).trans (hk.fac (coconeOfApex _ (t.ι.app none) (cond t)) apex).symm) }

end WidePushout

end UlmerBialgebras
