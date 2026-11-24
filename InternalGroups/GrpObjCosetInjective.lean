module

public import InternalGroups.GrpObjSubgroupCorrespondence
public import Foundations.CategoryTheory.Monoidal.ModObjColimits
public import Foundations.CategoryTheory.Monoidal.MonadReflexive

/-!
# Injectivity of Newman's correspondence as a property of the base category

`InternalGroups/GrpObjSubgroupCorrespondence.lean` constructs, for a group object `G` of a category
`C` with finite limits and reflexive coequalizers of modules, the Galois connection

  `Sub(G) ⇆ Quot(G)`

between subgroup objects of `G` and quotient `G`-modules of `G`; its **injectivity** at a
subgroup object `N` (the stabiliser of the coset quotient `G / N` is `N` again) holds as soon as
the coset relation `G ⊗ N ⇉ G` of `N` is effective (`InternalGroups.stab_quot_le`).

This file packages that injectivity as a single property `InternalGroups.CosetInjective C` of the
base category, and collects small facts used in its application
(`InternalGroups/GrpExactFromCoset.lean`: `Grp C` is Barr exact).

## Main definitions and results

* `InternalGroups.CosetInjective`: injectivity of Newman's correspondence for every group object
  of `C`;
* `InternalGroups.kills_quot_i`: the inclusion of a subgroup object kills its coset quotient;
* `InternalGroups.hasReflexiveCoequalizers_mod`: module categories have reflexive
  coequalizers.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

section Kills

variable {G : C} [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- **The inclusion of a subgroup object kills its own coset quotient.**  In `Set`: for `n ∈ N`
the coset `nN` is the base point of `G / N`. -/
lemma kills_quot_i (s : SubGrp G) : Kills s.quot s.i := by
  obtain ⟨f, hf⟩ := le_stab_quot s
  exact (kills_iff_factors _ _).2 ⟨f, hf⟩

/-- Injectivity of Newman's correspondence at `s`, spelled out: a generalized element killed by
the coset quotient of `s` factors through `s`. -/
lemma factors_of_kills_quot (s : SubGrp G) (hinj : stab s.quot ≤ s) {T : C} {g : T ⟶ G}
    (hg : Kills s.quot g) : ∃ k : T ⟶ s.N, k ≫ s.i = g := by
  obtain ⟨h₀, hh₀⟩ := (kills_iff_factors s.quot g).1 hg
  obtain ⟨f, hf⟩ := hinj
  simp only [SubGrp.toSubMon_i, stab_i] at hf
  refine ⟨h₀ ≫ f, ?_⟩
  have hf' : f ≫ s.i = s.quot.subIncl := hf
  exact (Category.assoc _ _ _).trans ((congrArg (h₀ ≫ ·) hf').trans hh₀)

end Kills

section Property

variable (C)

/-- **Injectivity of Newman's correspondence** for `C`: for every group object `G` of `C` and
every subgroup object `N` of `G`, the stabiliser of the base point of the coset quotient
`G ⟶ G / N` is `N` again.

By `InternalGroups.stab_quot_le` this holds as soon as the coset relation of every subgroup
object of every group object of `C` is effective. -/
def CosetInjective : Prop :=
  ∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)] (s : SubGrp G),
    stab s.quot ≤ s

variable {C}

omit [HasPullbacks C] in
/-- The category of modules over a monoid object of `C` has reflexive coequalizers as soon as `C`
has them and the product preserves them. -/
instance hasReflexiveCoequalizers_mod [HasReflexiveCoequalizers C]
    [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)] (M : C) [MonObj M] :
    HasReflexiveCoequalizers (CategoryTheory.Mod C M) :=
  CategoryTheory.Mod_.hasReflexiveCoequalizers (A := M)
    fun _ => inferInstance

end Property


end InternalGroups
