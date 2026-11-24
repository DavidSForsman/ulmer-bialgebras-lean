module

public import UlmerBialgebras.Models.CoHom
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers

/-!
# Creation of equalizers and coequalizers in `K^co`

Creation of an equalizer in a hom-category of `K` is creation of the corresponding
coequalizer in `K^co`. We use the opposite-category limit API and the hom equivalence.

## Main results

* `UlmerBialgebras.Co.createsColimitCancelEquivalence`: if `F ⋙ e.functor` creates a colimit, for an
  equivalence `e`, then so does `F`.
* `UlmerBialgebras.Co.createsCoequalizerOp`, `UlmerBialgebras.Co.createsEqualizerOfOp`: creation of
  an equalizer by `F` and creation of the opposite coequalizer by `F.op` imply each other.
* `UlmerBialgebras.Co.postcompCreatesCoequalizer`, `UlmerBialgebras.Co.postcompCreatesEqualizer`:
  creation of an equalizer by post-composition in `K` gives creation of the corresponding
  coequalizer by post-composition in `K^co`, and conversely.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.2 and Corollary 5.3
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Co

open CategoryTheory Limits

section Categories

variable {C D E J : Type*} [Category C] [Category D] [Category E] [Category J]

/-- Cancel an equivalence after a functor that creates a specified colimit. -/
@[instance_reducible]
noncomputable def createsColimitCancelEquivalence (F : C ⥤ D) (e : D ≌ E) (L : J ⥤ C)
    [CreatesColimit L (F ⋙ e.functor)] : CreatesColimit L F := by
  haveI : CreatesColimit L ((F ⋙ e.functor) ⋙ e.inverse) := inferInstance
  exact createsColimitOfNatIso
    (Functor.associator F e.functor e.inverse ≪≫
      Functor.isoWhiskerLeft F e.unitIso.symm ≪≫ F.rightUnitor)

/-- Creation of an equalizer gives creation of its opposite coequalizer. -/
@[instance_reducible]
noncomputable def createsCoequalizerOp (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
    [CreatesLimit (parallelPair f g) F] :
    CreatesColimit (parallelPair f.op g.op) F.op := by
  haveI : CreatesLimit ((CategoryTheory.opOpEquivalence WalkingParallelPair).functor ⋙
      parallelPair f g) F := inferInstance
  haveI : CreatesLimit (parallelPair f g).op.leftOp F :=
    inferInstanceAs (CreatesLimit
      ((CategoryTheory.opOpEquivalence WalkingParallelPair).functor ⋙ parallelPair f g) F)
  haveI : CreatesColimit (parallelPair f g).op F.op := createsColimitOp _ _
  haveI : CreatesColimit (walkingParallelPairOpEquiv.functor ⋙ (parallelPair f g).op) F.op :=
    inferInstance
  exact createsColimitOfIsoDiagram F.op (parallelPairOpIso f g).symm

/-- Creation of an opposite coequalizer gives creation of the original equalizer. -/
@[instance_reducible]
noncomputable def createsEqualizerOfOp (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
    [CreatesColimit (parallelPair f.op g.op) F.op] :
    CreatesLimit (parallelPair f g) F := by
  haveI : CreatesColimit (walkingParallelPairOpEquiv.inverse ⋙ parallelPair f.op g.op) F.op :=
    inferInstance
  haveI : CreatesColimit (parallelPair f g).op F.op :=
    createsColimitOfIsoDiagram F.op (opParallelPairIso f g).symm
  exact createsLimitOfOp _ _

end Categories

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- Creation of an equalizer in `K` is creation of a coequalizer in `K^co`. -/
@[instance_reducible]
noncomputable def postcompCreatesCoequalizer (x : Obj) {a b : Obj} (v : a ⟶ b)
    {f g : x ⟶ a} (α β : g ⟶ f)
    [CreatesLimit (parallelPair α β) (postcomp x v)] :
    CreatesColimit (parallelPair (cell α) (cell β))
      (postcomp (Obj := Co Obj) (Co.op x) (hom v)) := by
  let L := parallelPair (cell α) (cell β)
  haveI : CreatesColimit (parallelPair α.op β.op) (postcomp x v).op :=
    createsCoequalizerOp _ α β
  have e : L ⋙ homToOp x a ≅ parallelPair α.op β.op := diagramIsoParallelPair _
  haveI : CreatesColimit (L ⋙ homToOp x a) (postcomp x v).op :=
    createsColimitOfIsoDiagram _ e.symm
  haveI : CreatesColimit L (homToOp x a ⋙ (postcomp x v).op) := inferInstance
  haveI : CreatesColimit L ((postcomp (Obj := Co Obj) (Co.op x) (hom v)) ⋙ homToOp x b) := by
    rw [postcomp_homToOp]
    infer_instance
  letI : CreatesColimit L
      (postcomp (Obj := Co Obj) (Co.op x) (hom v) ⋙ (homEquiv x b).functor) := by
    change CreatesColimit L (postcomp (Obj := Co Obj) (Co.op x) (hom v) ⋙ homToOp x b)
    infer_instance
  exact createsColimitCancelEquivalence (postcomp (Obj := Co Obj) (Co.op x) (hom v))
    (homEquiv x b) L

/-- Creation of a coequalizer in `K^co` is creation of an equalizer in `K`. -/
@[instance_reducible]
noncomputable def postcompCreatesEqualizer (x : Obj) {a b : Obj} (v : a ⟶ b)
    {f g : x ⟶ a} (α β : g ⟶ f)
    [CreatesColimit (parallelPair (cell α) (cell β))
      (postcomp (Obj := Co Obj) (Co.op x) (hom v))] :
    CreatesLimit (parallelPair α β) (postcomp x v) := by
  let L := parallelPair α.op β.op
  have e : L ⋙ homFromOp x a ≅ parallelPair (cell α) (cell β) := diagramIsoParallelPair _
  haveI : CreatesColimit (L ⋙ homFromOp x a)
      (postcomp (Obj := Co Obj) (Co.op x) (hom v)) := createsColimitOfIsoDiagram _ e.symm
  haveI : CreatesColimit L
      ((homFromOp x a ⋙ postcomp (Obj := Co Obj) (Co.op x) (hom v)) ⋙ homToOp x b) :=
    inferInstance
  haveI : CreatesColimit L (postcomp x v).op :=
    inferInstanceAs (CreatesColimit L
      ((homFromOp x a ⋙ postcomp (Obj := Co Obj) (Co.op x) (hom v)) ⋙ homToOp x b))
  exact createsEqualizerOfOp _ α β

end UlmerBialgebras.Co
