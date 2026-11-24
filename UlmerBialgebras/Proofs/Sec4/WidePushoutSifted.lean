module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import Foundations.CategoryTheory.Limits.WidePushoutRegEpi

/-!
# Wide pushouts of regular epimorphisms from sifted colimits

In a category with kernel pairs, a functor that preserves reflexive coequalizers and colimits of
the sifted shape `MultiReflexivePair L` preserves `L`-indexed wide pushouts of regular
epimorphisms ([forsman2026syntactic], §4, the sifted shapes, example 3): the wide pushout is the
colimit of the kernel pairs of its legs.

## Main results

* `UlmerBialgebras.preservesWidePushoutsOfRegEpis_of_kernelPairs`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], §4
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace UlmerBialgebras

/-- **Wide pushouts of regular epimorphisms are sifted colimits**: in a category with kernel pairs,
a functor preserving reflexive coequalizers and colimits of shape `MultiReflexivePair L` preserves
`L`-indexed wide pushouts of regular epimorphisms. -/
theorem preservesWidePushoutsOfRegEpis_of_kernelPairs {A E : Type*} [Category A] [Category E]
    (F : A ⥤ E) (L : Type u) (hk : ∀ {X Y : A} (f : X ⟶ Y), HasPullback f f)
    [PreservesColimitsOfShape WalkingReflexivePair F]
    [PreservesColimitsOfShape (MultiReflexivePair L) F] :
    Paper.PreservesWidePushoutsOfRegEpis L F := by
  intro dg hdg
  have : ∀ j, HasPullback (leg dg j) (leg dg j) := fun j => hk _
  have : ∀ j, PreservesColimit (parallelPair (pullback.fst (leg dg j) (leg dg j))
      (pullback.snd (leg dg j) (leg dg j))) F := fun j => by
    have : IsReflexivePair (pullback.fst (leg dg j) (leg dg j))
        (pullback.snd (leg dg j) (leg dg j)) :=
      IsKernelPair.isReflexivePair (IsPullback.of_hasPullback (leg dg j) (leg dg j))
    exact preservesColimit_of_iso_diagram F (inclusionWalkingReflexivePairOfIsReflexivePairIso _ _)
  exact preservesColimit_widePushout_of_kernelPairs hdg F

end UlmerBialgebras
