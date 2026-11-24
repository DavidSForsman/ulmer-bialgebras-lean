module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Companion.Foundations.CategoryTheory.Limits.RegularMonoEquivalence
public import Companion.Hopf.Cocommutative.GrpCommComonHopf
public import Companion.InternalGroups.EmbedsInGrpObj

/-!
# Checked Hopf and coalgebra results beyond the numbered paper

These statements expose the existing library results on regular monomorphisms, Barr exactness,
coalgebra embeddings, and cartesian closedness to the statement comparator. The embeddings hold
for commutative base rings; the exactness, regular-monomorphism, and closedness results assume a
field. The target Hopf algebra of each embedding is commutative as an algebra, and is also
cocommutative as a coalgebra when the source is.

The statements retain the hypotheses and universes of the corresponding library results.

## Main results

* `UlmerBialgebras.Paper.coalgebra_embeds_hopf`, `cocomm_coalgebra_embeds_hopf`;
* `UlmerBialgebras.Paper.cocomm_comonoid_embeds_group`;
* `UlmerBialgebras.Paper.grp_cocomm_comonoid_monos_regular`, `cocomm_hopf_monos_regular`;
* `UlmerBialgebras.Paper.cocomm_hopf_barr_exact`;
* `UlmerBialgebras.Paper.cocomm_comonoid_cartesian_closed`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler]: the embeddings of coalgebras into Hopf algebras
  (`coalgebra_embeds_hopf`, `cocomm_coalgebra_embeds_hopf`, `cocomm_comonoid_embeds_group`).
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]: the
  correspondence that the proofs of `grp_cocomm_comonoid_monos_regular` and
  `cocomm_hopf_monos_regular` use (the regularity of the monomorphisms is not stated there).
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171]: cocommutative Hopf algebras over a field form a semi-abelian, hence
  Barr-exact, category (`cocomm_hopf_barr_exact`).
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]: the
  commutative and cocommutative case, which Gran, Sterck and Vercruysse extend.
* [T. F. Fox, *Coalgebras and cartesian categories*][foxCoalgebrasCartesianCategories1976]: the
  cartesian structure of cocommutative coalgebras (`cocomm_comonoid_cartesian_closed`).
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper

open CategoryTheory

/-- **Every coalgebra over a commutative ring embeds into a commutative Hopf algebra**
(additional checked result). -/
theorem coalgebra_embeds_hopf (k : Type u) [CommRing k] (C : Type u)
    [AddCommGroup C] [Module k C] [Coalgebra k C] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H) (f : C →ₗc[k] H),
      Function.Injective f :=
  sorry

/-- **Every cocommutative coalgebra embeds into a commutative cocommutative Hopf algebra**
(additional checked result). -/
theorem cocomm_coalgebra_embeds_hopf (k : Type u) [CommRing k] (C : Type u)
    [AddCommGroup C] [Module k C] [Coalgebra k C] [Coalgebra.IsCocomm k C] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H) (_ : Coalgebra.IsCocomm k H)
      (f : C →ₗc[k] H), Function.Injective f :=
  sorry

/-- **Every cocommutative comonoid of modules over a commutative ring embeds into a group
object** (additional checked result). -/
theorem cocomm_comonoid_embeds_group (k : Type u) [CommRing k] :
    InternalGroups.EmbedsInGrpObj (CommComon (ModuleCat.{u} k)) :=
  sorry

/-- **Every mono of group objects in cocommutative coalgebras over a field is regular**
(additional checked result). -/
theorem grp_cocomm_comonoid_monos_regular (k : Type u) [Field k] :
    IsRegularMonoCategory (Grp (CommComon (ModuleCat.{u} k))) :=
  sorry

/-- **Every mono of cocommutative Hopf algebras over a field is regular** (additional checked
result). -/
theorem cocomm_hopf_monos_regular (k : Type u) [Field k] :
    IsRegularMonoCategory (GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  sorry

/-- **Cocommutative Hopf algebras over a field form a Barr-exact category** (additional
checked result). -/
theorem cocomm_hopf_barr_exact (k : Type u) [Field k] :
    IsBarrExact (GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  sorry

/-- **Cocommutative coalgebras over a field form a cartesian closed category** (additional
checked result). -/
theorem cocomm_comonoid_cartesian_closed (k : Type u) [Field k] :
    Nonempty (MonoidalClosed (CommComon (ModuleCat.{u} k))) :=
  sorry

end UlmerBialgebras.Paper
