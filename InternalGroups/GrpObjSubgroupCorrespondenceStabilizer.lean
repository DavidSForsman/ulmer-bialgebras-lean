module

public import InternalGroups.GrpObjSubgroupCorrespondenceExact
public import InternalGroups.GrpRegularStabilizer

/-!
# Newman's correspondence: monomorphisms are stabilizers, and the exactness of `Grp C`

Standing hypotheses, as in `InternalGroups/GrpRegularStabilizer.lean`: `C` is cartesian monoidal
with finite limits and reflexive coequalizers, which the binary product preserves in each
variable.

Newman's correspondence holds for every internal group of `C` iff every monomorphism of `Grp C`
is a stabilizer and every epimorphic coset quotient is a regular coset quotient
(`InternalGroups.subgroupCorrespondence_iff_monos_are_stabilizers`). The first condition is the
effectivity of the coset relations (`InternalGroups.cosetInjective_iff_monos_are_stabilizers`),
and the second gives the coset composite condition (S′)
(`InternalGroups.regularEpiCosetCompHom_of_everyEpiQuotientRegular`). Under (S′) the regular
epimorphisms of `Grp C` are stably stabilizer-extremal, hence stably extremal once every
monomorphism is a stabilizer, so `Grp C` is regular, and Barr exact
(`InternalGroups.isBarrExact_grp_of_monos_are_stabilizers`).

These results are due to D. Forsman. They were announced by the author and will appear in a
forthcoming preprint.

## Main results

* `InternalGroups.grpIsStabilizer_of_mono_of_cosetInjective`,
  `InternalGroups.cosetInjective_iff_monos_are_stabilizers`;
* `InternalGroups.subgroupCorrespondence_iff_monos_are_stabilizers`: the translation of Newman's
  correspondence;
* `InternalGroups.isBarrExact_grp_of_regularEpiCosetCompHom_of_monos`: under (S′), `Grp C` is Barr
  exact when every monomorphism is a stabilizer;
* `InternalGroups.isBarrExact_grp_of_subgroupCorrespondence`: **Newman's correspondence for every
  internal group implies that `Grp C` is Barr exact**.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj

namespace InternalGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

/-! ## Newman's correspondence: monomorphisms are stabilizers -/

/-- **Under the effectivity of the coset relations, every monomorphism of `Grp C` is a
stabilizer.**  The subgroup object `m` of `B` is recovered from its coset quotient
(`CosetInjective`), and the stabilizer of the base point of the coset quotient is a stabilizer. -/
theorem grpIsStabilizer_of_mono_of_cosetInjective (hinj : CosetInjective C) {A B : Grp C}
    (m : A ⟶ B) [Mono m] : GrpIsStabilizer m := by
  have : Mono m.hom.hom := mono_hom_of_mono m
  let s : SubGrp B.X := ⟨A.X, m.hom.hom⟩
  have hs : GrpIsStabilizer s.inclGrp :=
    (isGrpStabilizer_stab s.quot).of_iso (SubGrp.isoOfLe (le_stab_quot s) (hinj B.X s))
      (SubGrp.isoOfLe_hom_inclGrp _ _)
  exact hs.of_iso (Iso.refl _) (Category.id_comp _)

/-- **The coset relations are effective iff every monomorphism of `Grp C` is a stabilizer.** -/
theorem cosetInjective_iff_monos_are_stabilizers :
    CosetInjective C ↔ ∀ {A B : Grp C} (m : A ⟶ B), Mono m → GrpIsStabilizer m := by
  refine ⟨fun hinj _ _ m _ => grpIsStabilizer_of_mono_of_cosetInjective hinj m, ?_⟩
  intro hmono G _ _ s
  have : Mono s.inclGrp := (Grp.forget C).mono_of_mono_map s.mono_i
  exact stab_quot_le_of_grpIsStabilizer s (hmono s.inclGrp this)

/-- **Newman's correspondence, translated**: it holds for every internal group
of `C` iff every monomorphism of `Grp C` is a stabilizer and every epimorphic coset quotient is a
regular coset quotient. -/
theorem subgroupCorrespondence_iff_monos_are_stabilizers :
    SubgroupCorrespondence C ↔
      (∀ {A B : Grp C} (m : A ⟶ B), Mono m → GrpIsStabilizer m) ∧ EveryEpiQuotientRegular C :=
  subgroupCorrespondence_iff.trans (and_congr_left' cosetInjective_iff_monos_are_stabilizers)

variable [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- **`Grp C` is Barr exact under (S′) when every monomorphism of `Grp C` is a stabilizer.**  The
coset relations are then effective (`InternalGroups.cosetInjective_iff_monos_are_stabilizers`). -/
theorem isBarrExact_grp_of_regularEpiCosetCompHom_of_monos (hcomp : RegularEpiCosetCompHom C)
    (hmono : ∀ {A B : Grp C} (m : A ⟶ B), Mono m → GrpIsStabilizer m) : IsBarrExact (Grp C) :=
  isBarrExact_grp_of_monos_are_stabilizers (cosetInjective_iff_monos_are_stabilizers.2 hmono)
    hcomp hmono

/-- **Newman's correspondence implies exactness.**  If Newman's correspondence is bijective
for every internal group of `C`, then `Grp C` is Barr exact: every monomorphism is a stabilizer,
and every epimorphic coset quotient is regular, which gives (S′); so the regular epimorphisms of
`Grp C` are stably stabilizer-extremal, hence stably extremal, and `Grp C` is regular and exact
(`InternalGroups.isBarrExact_grp_of_regularEpiCosetCompHom_of_monos`). -/
theorem isBarrExact_grp_of_subgroupCorrespondence (h : SubgroupCorrespondence C) :
    IsBarrExact (Grp C) :=
  isBarrExact_grp_of_regularEpiCosetCompHom_of_monos
    (regularEpiCosetCompHom_of_everyEpiQuotientRegular (subgroupCorrespondence_iff.1 h).2)
    (subgroupCorrespondence_iff_monos_are_stabilizers.1 h).1

end InternalGroups
