module

public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.RegularCategory.Basic

/-!
# Kernel-pair coequalizers from a regular epimorphism

A regular epimorphism is an effective epimorphism, and a kernel pair of an effective
epimorphism has a coequalizer (Mathlib's `isColimitCoforkOfEffectiveEpi`).  Hence:

* `isColimitCoforkKernelPairOfIsRegularEpi` — a regular epimorphism is the coequalizer of
  its own kernel pair;
* `isKernelPair_comp_of_mono` — if `f = e ≫ m` with `m` monic, then the kernel pair of `e` is a
  kernel pair of `f`.

The second fact is the step in the characterization of regular categories: a category in which
every morphism factors as a regular epimorphism followed by a monomorphism has coequalizers of
kernel pairs, because the regular-epi part is such a coequalizer.

## References

* [M. Barr, *Exact Categories*][Ba]
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- **A regular epimorphism is the coequalizer of its kernel pair.** -/
noncomputable def isColimitCoforkKernelPairOfIsRegularEpi {X Y : 𝒞} (e : X ⟶ Y)
    [IsRegularEpi e] [HasPullback e e] :
    IsColimit (Cofork.ofπ e (pullback.condition (f := e) (g := e))) :=
  isColimitCoforkOfEffectiveEpi e (pullback.cone e e) (pullback.isLimit e e)

/-- **If `f = e ≫ m` with `m` monic, then `f` and `e` have the same kernel pair**: the kernel
pair of `e` is a kernel pair of `f`.  This is `IsKernelPair.comp_of_mono` of Mathlib, applied to
the kernel pair of a regular epimorphism. -/
theorem isKernelPair_comp_of_mono {X I Y : 𝒞} (e : X ⟶ I) (m : I ⟶ Y) [Mono m]
    [HasPullback e e] :
    IsKernelPair (e ≫ m) (pullback.fst e e) (pullback.snd e e) :=
  (IsKernelPair.of_hasPullback e).comp_of_mono (f₂ := m)

end UlmerBialgebras
