module

public import Companion.Hopf.Embed.UnitsHopf
public import Companion.Hopf.Cocommutative.GrpCommComonHopf
public import Companion.Hopf.Mathlib.HopfEquivalence
public import Companion.Hopf.Mathlib.CocommEquivalenceExtra
public import Companion.InternalGroups.EmbedsInGrpObj
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Every cocommutative comonoid of `ModuleCat k` embeds into a group object

The categorical form of `Coalgebra.exists_injective_coalgHom_hopfAlgebra`: in
`CommComon (ModuleCat k)`, with its cartesian monoidal structure, every object has a monomorphism
into a group object (`InternalGroups.EmbedsInGrpObj`).

For `X : CommComon (ModuleCat k)` with coalgebra `C`, the group object is the cocommutative Hopf
algebra `Coalgebra.UnitsHopf k C`, seen as a group object through `UlmerBialgebras.GrpHopf.ofHopf`.
The monomorphism is the injective coalgebra map `Coalgebra.UnitsHopf.coalgHom k C`, seen as a
morphism of comonoids through `CoalgCat.toComon`. The comonoid structures agree definitionally.

## Main results

* `InternalGroups.embedsInGrpObj_commComon_moduleCat`.

## References

* M. E. Sweedler, *Hopf Algebras* (1969)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace InternalGroups

variable (k : Type u) [CommRing k]

/-- **Every object of `CommComon (ModuleCat k)` embeds into a group object**: every cocommutative
`k`-coalgebra has an injective comonoid morphism into a cocommutative Hopf algebra. -/
theorem embedsInGrpObj_commComon_moduleCat : EmbedsInGrpObj (CommComon (ModuleCat.{u} k)) := by
  intro X
  let C := CoalgCat.ofComonObj X.X
  have : IsCommComonObj (ModuleCat.of k C) := X.comm
  have : Coalgebra.IsCocomm k C := CoalgCat.instIsCocomm C
  let H : HopfAlgCat k := HopfAlgCat.of k (Coalgebra.UnitsHopf k C)
  have : Coalgebra.IsCocomm k H :=
    inferInstanceAs (Coalgebra.IsCocomm k (Coalgebra.UnitsHopf k C))
  let C' : CoalgCat k :=
    (forget₂ (BialgCat k) (CoalgCat k)).obj ((forget₂ (HopfAlgCat k) (BialgCat k)).obj H)
  let A := (HopfAlgCat.toHopf k).obj H
  have : IsCommComonObj A.X := HopfAlgCat.instCommComonObj H
  let G := UlmerBialgebras.GrpHopf.ofHopf A.X
  let φ : C ⟶ C' := ⟨Coalgebra.UnitsHopf.coalgHom k C⟩
  let m : X.toComon ⟶ G.X.toComon := (CoalgCat.toComon k).map φ
  let f : X ⟶ G.X := InducedCategory.homMk m
  have hf : Mono f.hom.hom := by
    rw [ModuleCat.mono_iff_injective]
    exact Coalgebra.UnitsHopf.coalgHom_injective k C
  refine ⟨G, f, ⟨fun g h e => CommComon.hom_ext _ _ ?_⟩⟩
  exact (cancel_mono f.hom.hom).1 (congrArg (fun φ => φ.hom.hom) e)

end InternalGroups
