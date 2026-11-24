module

public import UlmerBialgebras.Proofs.Sec6.SubgroupCorrespondenceCategorical
public import Hopf.Cocommutative.BiIdealDictionary
public import UlmerBialgebras.Proofs.Sec6.SubgroupCorrespondenceBiIdeal
public import InternalGroups.GrpObjSubgroupCorrespondenceExactCocomm
public import UlmerBialgebras.Proofs.Sec6.ComonDescent
public import UlmerBialgebras.Proofs.Sec6.HopfExactness

/-!
# Cocommutative Hopf algebras over a field form a Barr-exact category

Let `k` be a field and `C = Comon_k^coc = CommComon (ModuleCat k)`, so that `Grp C` is the category
of cocommutative Hopf `k`-algebras. This file proves that `Grp C` is Barr-exact
(`UlmerBialgebras.CocommComon.isBarrExact_grp_of_field`). The route, general first:

* in `Grp C` for a general `C`, regular epimorphisms are stably stabilizer-extremal under (S′), so
  `Grp C` is regular, and Barr exact, when every monomorphism is a stabilizer
  (`InternalGroups.isBarrExact_grp_of_monos_are_stabilizers`);
* Newman's correspondence says exactly that monomorphisms are stabilizers and that epimorphic
  coset quotients are regular, which gives (S′)
  (`InternalGroups.subgroupCorrespondence_iff_monos_are_stabilizers`,
  `InternalGroups.isBarrExact_grp_of_subgroupCorrespondence`);
* for `C = Comon_A^coc` with `A` abelian and the tensor exact, Newman's correspondence is the
  bijectivity of the bi-ideal map (`InternalGroups.isBarrExact_grp_commComon_of_biIdeal`), and for
  `A = ModuleCat k` with `k` a field the bi-ideal map is bijective
  (`InternalGroups.biIdealMap_bijective_of_field`,
  `UlmerBialgebras/Proofs/Sec6/SubgroupCorrespondenceBiIdeal.lean`).

The proof by this route is due to D. Forsman. It was announced by the author and will appear in
a forthcoming preprint.

The inputs of an earlier route (`InternalGroups.isBarrExact_grp_of_stablyEpiMono`) are in
the development repository's `Solution/HopfCocStablyEpiMono.lean`, outside the paper's proofs.

## Main results

* `UlmerBialgebras.CocommComon.isBarrExact_grp_of_field`: `Grp (CommComon (ModuleCat k))` is
  Barr-exact.
* `UlmerBialgebras.Paper.Loc.isBarrExact_grp_commComon_modU_of_isField`: the same for `ModU k`, the
  category of `k`-modules used in Corollary 6.11.

## Attribution

The Barr exactness of `Hopf_k^coc` was first proved by Gran, Sterck and Vercruysse
[GRAN20194171]. The bi-ideal correspondence used here is Newman's [Newman1975], in the categorical
form of `InternalGroups/GrpObjSubgroupCorrespondenceBiIdeal.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (the field case used there)
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory
open scoped MonObj ComonObj

namespace UlmerBialgebras.CocommComon

variable {k : Type u} [Field k]

/-- **The cocommutative Hopf algebras over a field form a Barr-exact category.** This was first
proved by Gran, Sterck and Vercruysse [GRAN20194171]. Here it follows from Newman's bi-ideal
correspondence [Newman1975], which holds over a field
(`InternalGroups.biIdealMap_bijective_of_field`), by the bi-ideal form of the exactness of group
objects of cocommutative comonoids (`InternalGroups.isBarrExact_grp_commComon_of_biIdeal`). -/
theorem isBarrExact_grp_of_field :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModuleCat.{u} k))) :=
  InternalGroups.isBarrExact_grp_commComon_of_biIdeal fun h _ =>
    InternalGroups.biIdealMap_bijective_of_field h

end UlmerBialgebras.CocommComon

namespace UlmerBialgebras.Paper.Loc

open CategoryTheory Limits MonoidalCategory

/-- **`Hopf^coc_k` is Barr-exact for every field `k`**, for the category `Mod_k` with lifted
hom-sets used in Corollary 6.11. It is transported from `isBarrExact_grp_of_field` along the
braided monoidal equivalence `Mod_k ≌ ModuleCat k`. -/
theorem isBarrExact_grp_commComon_modU_of_isField (k : Type u) [CommRing k] (hk : IsField k) :
    CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModU k))) := by
  let := hk.toField
  have : CategoryTheory.IsBarrExact (Grp (CategoryTheory.CommComon (ModuleCat.{u} k))) :=
    UlmerBialgebras.CocommComon.isBarrExact_grp_of_field
  exact GrpDescent.isBarrExact_grp_of_equivalence (ComonDescent.commComonEquiv (modEquiv k)).symm

end UlmerBialgebras.Paper.Loc
