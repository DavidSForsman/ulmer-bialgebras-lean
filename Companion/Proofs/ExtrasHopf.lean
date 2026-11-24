module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Foundations.CategoryTheory.Exact.SemiAbelian
public import Companion.Foundations.CategoryTheory.Limits.RegularMonoEquivalence
public import Companion.Hopf.Cocommutative.GrpCommComonHopf
public import Companion.InternalGroups.EmbedsInGrpObj

public import Companion.Proofs.HopfMonoRegular
public import Companion.Proofs.CocommHopfExactField

/-!
# Hopf and coalgebra results beyond the numbered paper

These statements are the library results on regular monomorphisms, Barr exactness, coalgebra
embeddings and cartesian closedness, stated for the paper's categories. The embeddings hold
for commutative base rings; the exactness, regular-monomorphism, and closedness results assume a
field. The target Hopf algebra of each embedding is commutative as an algebra, and is also
cocommutative as a coalgebra when the source is. Each statement keeps the hypotheses and universes
of the library result it restates.

## Main results

* `UlmerBialgebras.Paper.coalgebra_embeds_hopf`, `cocomm_coalgebra_embeds_hopf`;
* `UlmerBialgebras.Paper.cocomm_comonoid_embeds_group`;
* `UlmerBialgebras.Paper.grp_cocomm_comonoid_monos_regular`, `cocomm_hopf_monos_regular`;
* `UlmerBialgebras.Paper.cocomm_hopf_barr_exact`;
* `UlmerBialgebras.Paper.cocomm_comonoid_cartesian_closed`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. Gran, F. Sterck, J. Vercruysse, *A semi-abelian extension of a theorem by
  Takeuchi*][GRAN20194171], for `cocomm_hopf_barr_exact`
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper

open CategoryTheory

/-- **Every coalgebra over a commutative ring embeds into a commutative Hopf algebra**
(addition beyond [forsman2026syntactic]). -/
theorem coalgebra_embeds_hopf (k : Type u) [CommRing k] (C : Type u)
    [AddCommGroup C] [Module k C] [Coalgebra k C] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H) (f : C →ₗc[k] H),
      Function.Injective f :=
  Coalgebra.exists_injective_coalgHom_hopfAlgebra k C

/-- **Every cocommutative coalgebra embeds into a commutative cocommutative Hopf algebra**
(addition beyond [forsman2026syntactic]). -/
theorem cocomm_coalgebra_embeds_hopf (k : Type u) [CommRing k] (C : Type u)
    [AddCommGroup C] [Module k C] [Coalgebra k C] [Coalgebra.IsCocomm k C] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra k H) (_ : Coalgebra.IsCocomm k H)
      (f : C →ₗc[k] H), Function.Injective f :=
  Coalgebra.exists_injective_coalgHom_cocomm_hopfAlgebra k C

/-- **Every cocommutative comonoid of modules over a commutative ring embeds into a group
object** (addition beyond [forsman2026syntactic]). -/
theorem cocomm_comonoid_embeds_group (k : Type u) [CommRing k] :
    InternalGroups.EmbedsInGrpObj (CommComon (ModuleCat.{u} k)) :=
  InternalGroups.embedsInGrpObj_commComon_moduleCat (k := k)

/-- **Every mono of group objects in cocommutative coalgebras over a field is regular**
(addition beyond [forsman2026syntactic]). -/
theorem grp_cocomm_comonoid_monos_regular (k : Type u) [Field k] :
    IsRegularMonoCategory (Grp (CommComon (ModuleCat.{u} k))) :=
  InternalGroups.isRegularMonoCategory_grp_commComon_of_field k

/-- **Every mono of cocommutative Hopf algebras over a field is regular** (addition beyond
[forsman2026syntactic]). -/
theorem cocomm_hopf_monos_regular (k : Type u) [Field k] :
    IsRegularMonoCategory (GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  InternalGroups.isRegularMonoCategory_cocommHopf_of_field k

/-- **Cocommutative Hopf algebras over a field form a Barr-exact category** (addition beyond
[forsman2026syntactic]). -/
theorem cocomm_hopf_barr_exact (k : Type u) [Field k] :
    IsBarrExact (GrpHopf.CocommHopf (ModuleCat.{u} k)) :=
  InternalGroups.isBarrExact_cocommHopf_of_field (k := k)

/-- **Cocommutative coalgebras over a field form a cartesian closed category** (addition beyond
[forsman2026syntactic]). -/
theorem cocomm_comonoid_cartesian_closed (k : Type u) [Field k] :
    Nonempty (MonoidalClosed (CommComon (ModuleCat.{u} k))) :=
  ⟨UlmerBialgebras.CommComon.monoidalClosed_moduleCat (k := k)⟩

end UlmerBialgebras.Paper
