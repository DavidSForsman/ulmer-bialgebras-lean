module

public import InternalGroups.GrpKernelDetection
public import Foundations.CategoryTheory.Grp.GrpObjEqualizer

/-!
# Equalizers of internal groups, towards the points condition

Let `C` be a cartesian monoidal category with finite limits and let `r₁, r₂ : R ⇉ X` be a
*reflexive* relation of internal groups with coequalizer `q : X ⟶ Q`.  The *points* half of the
connected reduction of `InternalGroups/GrpKernelDetection.lean` reads:

> if the coequalizer is computed in `C` and the global points functor `C(1,-)` preserves it,
> then a global point of `X` killed by `q` is a point of the normal subobject of the relation.

That statement itself is not formalized in this file.  What is recorded here is the ingredient
that **equalizers of internal groups are computed in `C`**
(`InternalGroups.ConnExact.isLimitForkGrp`), which is what lets a generalized element killed by `r₁`
be factored through the kernel of `r₁` (`InternalGroups.ConnExact.exists_relKernel_factor`).

## Main results

* `InternalGroups.ConnExact.eqGrp`, `InternalGroups.ConnExact.eqGrpι`,
  `InternalGroups.ConnExact.isLimitForkGrp`: the equalizer of two morphisms of internal groups,
  computed in `C`;
* `InternalGroups.ConnExact.exists_relKernel_factor`.

## References

* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite

namespace InternalGroups
open CategoryTheory.GrpEqualizer CategoryTheory.MonEqualizer

namespace ConnExact

/-! ### The relation induced on generalized elements -/

section Rel

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

variable {R X : Grp C} {r₁ r₂ : R ⟶ X} {d : X ⟶ R}

variable (hd₁ : d ≫ r₁ = 𝟙 X) (hd₂ : d ≫ r₂ = 𝟙 X)

include hd₁ hd₂

end Rel

/-! ### Coequalizers of equivalence relations of sets -/

section Types

end Types

/-! ### Equalizers of internal groups are computed in the base -/

section GrpEq

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {G H : Grp C} {u v : G ⟶ H} {E : C} {e : E ⟶ G.X}
  {w : e ≫ u.hom.hom = e ≫ v.hom.hom} (he : IsLimit (Fork.ofι e w))

include he

/-- The equalizer of a pair of morphisms of internal groups, as an internal group. -/
noncomputable abbrev eqGrp : Grp C :=
  letI := CategoryTheory.GrpEqualizer.grpObj he
  .mk E

/-- The inclusion of the equalizer, as a morphism of internal groups. -/
noncomputable def eqGrpι : eqGrp he ⟶ G :=
  letI := CategoryTheory.GrpEqualizer.grpObj he
  letI := CategoryTheory.MonEqualizer.isMonHom_e he
  Grp.homMk e

/-- The inclusion of the equalizer equalizes `u` and `v` in `Grp C`. -/
lemma eqGrp_condition : eqGrpι he ≫ u = eqGrpι he ≫ v :=
  Grp.hom_ext _ _ w

/-- **Equalizers of internal groups are created in the base category.** -/
noncomputable def isLimitForkGrp : IsLimit (Fork.ofι (eqGrpι he) (eqGrp_condition he)) :=
  Fork.IsLimit.mk _
    (fun s =>
      letI := CategoryTheory.GrpEqualizer.grpObj he
      letI := CategoryTheory.MonEqualizer.isMonHom_liftMon he s.ι.hom.hom
        (congr(($(s.condition)).hom.hom))
      Grp.homMk (CategoryTheory.MonEqualizer.liftMon he s.ι.hom.hom
        (congr(($(s.condition)).hom.hom))))
    (fun s => Grp.hom_ext _ _ (CategoryTheory.MonEqualizer.liftMon_comp he s.ι.hom.hom
      (congr(($(s.condition)).hom.hom))))
    (fun s m hm => Grp.hom_ext _ _ (by
      have := CategoryTheory.MonEqualizer.mono_e he
      have h1 : m.hom.hom ≫ e = s.ι.hom.hom := congr(($hm).hom.hom)
      rw [← cancel_mono e, h1]
      exact (CategoryTheory.MonEqualizer.liftMon_comp he s.ι.hom.hom
        (congr(($(s.condition)).hom.hom))).symm))

end GrpEq

/-! ### Factoring a generalized element through the kernel -/

section RelKernel

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  [HasEqualizers C]

open Internal

/-- **A generalized element killed by `r₁` factors through the kernel of `r₁`.**  This uses that
the equalizer defining the kernel is computed in `C`. -/
theorem exists_relKernel_factor {R X : Grp C} (r₁ : R ⟶ X) {W : C} (n : W ⟶ R.X)
    (hn : n ≫ r₁.hom.hom = (1 : W ⟶ X.X)) :
    ∃ n' : W ⟶ (relKernel r₁).X, n' ≫ (relKernelι r₁).hom.hom = n := by
  classical
  -- the equalizer computed in `C`
  have hE := equalizerIsEqualizer r₁.hom.hom (0 : R ⟶ X).hom.hom
  have hlim := isLimitForkGrp hE
  -- compare it with the kernel, which is the equalizer computed in `Grp C`
  have hK := equalizerIsEqualizer r₁ (0 : R ⟶ X)
  let φ := IsLimit.conePointUniqueUpToIso hlim hK
  have hφ : φ.hom ≫ relKernelι r₁ = eqGrpι hE :=
    IsLimit.conePointUniqueUpToIso_hom_comp hlim hK WalkingParallelPair.zero
  -- the trivial morphism agrees with `1`
  have htriv : (0 : R ⟶ X).hom.hom = (1 : R.X ⟶ X.X) := zero_hom_hom
  have hn' : n ≫ r₁.hom.hom = n ≫ (0 : R ⟶ X).hom.hom := by
    rw [htriv, hn, Pi0.comp_one_hom]
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : W ⟶ equalizer r₁.hom.hom (0 : R ⟶ X).hom.hom,
      n₀ ≫ equalizer.ι _ _ = n := ⟨equalizer.lift n hn', equalizer.lift_ι _ _⟩
  refine ⟨n₀ ≫ φ.hom.hom.hom, ?_⟩
  have h2 : φ.hom.hom.hom ≫ (relKernelι r₁).hom.hom
      = equalizer.ι r₁.hom.hom (0 : R ⟶ X).hom.hom := by
    have := congr(($hφ).hom.hom)
    exact this
  exact (Category.assoc _ _ _).trans ((n₀ ≫= h2).trans hn₀)

end RelKernel

/-! ### The points condition -/

section Points

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
  [HasEqualizers C]

open Internal

end Points

end ConnExact

end InternalGroups
