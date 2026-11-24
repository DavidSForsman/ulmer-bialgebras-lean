module

public import Companion.Hopf.Cocommutative.CocommHopfExact
public import Companion.Hopf.Mathlib.CocommEquivalenceExtra
public import UlmerBialgebras.Proofs.Sec6.SubgroupCorrespondenceBiIdeal

/-!
# The cocommutative Hopf algebras over a field form a Barr-exact category

For a field `k`, the category `UlmerBialgebras.GrpHopf.CocommHopf (ModuleCat k)` of cocommutative
Hopf monoids of `ModuleCat k`, that is, of cocommutative Hopf `k`-algebras, is Barr-exact, with no
hypothesis beyond `k` being a field. So is the category of cocommutative Hopf algebras on Mathlib's
side, the full subcategory of `HopfAlgCat k` on the cocommutative ones.

The first statement (`InternalGroups.isBarrExact_cocommHopf_of_field`) is Newman's bi-ideal
correspondence over a field (`InternalGroups.biIdealMap_bijective_of_field`,
`UlmerBialgebras/Proofs/Sec6/SubgroupCorrespondenceBiIdeal.lean`).
Mathlib's cocommutative Hopf algebras are equivalent to the cocommutative Hopf monoids by
restricting `CategoryTheory.HopfAlgCat.hopfEquivalence`
(`CategoryTheory.HopfAlgCat.isCommComonObj_toHopf_iff`,
`CategoryTheory.HopfAlgCat.ofHopf_isCocomm_iff`).

## Main results

* `InternalGroups.isBarrExact_cocommHopf_of_field`: the cocommutative Hopf monoids of
  `ModuleCat k` form a Barr-exact category;
* `UlmerBialgebras.CocommComon.isBarrExact_cocommHopfAlg`: the cocommutative Hopf algebras of
  `HopfAlgCat k` form a Barr-exact category.

## References

* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171], who first proved the Barr exactness of `Hopf_k^coc`
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe u

open CategoryTheory UlmerBialgebras.GrpHopf

namespace InternalGroups

variable {k : Type u} [Field k] in
/-- **Cocommutative Hopf algebras over a field form a Barr-exact category**, by Newman's
bi-ideal correspondence (`InternalGroups.isBarrExact_cocommHopf_of_biIdeal`), which holds over a
field (`InternalGroups.biIdealMap_bijective_of_field`). -/
theorem isBarrExact_cocommHopf_of_field :
    IsBarrExact (UlmerBialgebras.GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  isBarrExact_cocommHopf_of_biIdeal fun h _ => biIdealMap_bijective_of_field h

end InternalGroups

namespace UlmerBialgebras.CocommComon

variable (k : Type u) [Field k]

/-! ## Mathlib's cocommutative Hopf algebras -/

/-- The cocommutative Hopf algebras among Mathlib's `HopfAlgCat k`. -/
def cocommHopfAlg : ObjectProperty (HopfAlgCat.{u} k) := fun H => Coalgebra.IsCocomm k H

/-- The functor from Mathlib's cocommutative `k`-Hopf algebras to the cocommutative Hopf monoids of
`ModuleCat k`: the restriction of `HopfAlgCat.hopfEquivalence`. -/
noncomputable def cocommHopfAlgToCocommHopf :
    (cocommHopfAlg k).FullSubcategory ⥤ CocommHopf (ModuleCat.{u} k) :=
  (cocommHopf _).lift ((cocommHopfAlg k).ι ⋙ (HopfAlgCat.hopfEquivalence k).functor)
    (fun H => (HopfAlgCat.isCommComonObj_toHopf_iff H.obj).2 H.property)

/-- `cocommHopfAlgToCocommHopf` is fully faithful: followed by the inclusion of `CocommHopf`, it is
the inclusion of the cocommutative Hopf algebras followed by the equivalence `hopfEquivalence`. -/
noncomputable def fullyFaithfulCocommHopfAlgToCocommHopf :
    (cocommHopfAlgToCocommHopf k).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := (cocommHopf (ModuleCat.{u} k)).ι)
    ((cocommHopfAlg k).fullyFaithfulι.comp (HopfAlgCat.hopfEquivalence k).fullyFaithfulFunctor)

instance : (cocommHopfAlgToCocommHopf k).Full := (fullyFaithfulCocommHopfAlgToCocommHopf k).full

instance : (cocommHopfAlgToCocommHopf k).Faithful :=
  (fullyFaithfulCocommHopfAlgToCocommHopf k).faithful

/-- Every cocommutative Hopf monoid of `ModuleCat k` comes from a cocommutative Hopf algebra. -/
instance : (cocommHopfAlgToCocommHopf k).EssSurj where
  mem_essImage M := by
    let e := HopfAlgCat.hopfEquivalence k
    have hM : Coalgebra.IsCocomm k (e.inverse.obj M.obj) :=
      (HopfAlgCat.ofHopf_isCocomm_iff M.obj).2 M.property
    exact ⟨⟨e.inverse.obj M.obj, hM⟩,
      ⟨(cocommHopf _).fullyFaithfulι.preimageIso (e.counitIso.app M.obj)⟩⟩

instance : (cocommHopfAlgToCocommHopf k).IsEquivalence where

/-- **Mathlib's cocommutative Hopf algebras over a field `k`** (the full subcategory of
`HopfAlgCat k` on the cocommutative ones) **form a Barr-exact category.** -/
theorem isBarrExact_cocommHopfAlg : IsBarrExact (cocommHopfAlg k).FullSubcategory :=
  have : IsBarrExact (CocommHopf (ModuleCat.{u} k)) :=
    InternalGroups.isBarrExact_cocommHopf_of_field (k := k)
  isBarrExact_of_equivalence (cocommHopfAlgToCocommHopf k).asEquivalence

end UlmerBialgebras.CocommComon
