module

public import Hopf.Mathlib.CocommEquivalence
public import Companion.Hopf.Mathlib.BimonEquivalence
public import Companion.Hopf.Mathlib.HopfEquivalence

/-!
# Identification of cocommutative bialgebras and Hopf algebras across category equivalences

Given a commutative ring `R`, this file extends `Hopf/Mathlib/CocommEquivalence.lean` from
coalgebras to bialgebras and Hopf algebras, establishing the compatibility of cocommutativity
(`Coalgebra.IsCocomm`) with commutative comonoid objects (`IsCommComonObj` and `CommComon`) in
`ModuleCat R` across the equivalences:
* `BialgCat R ≌ Bimon (ModuleCat R)`
* `HopfAlgCat R ≌ Hopf (ModuleCat R)`

## Main results

### Bialgebras (`BialgCat`)
* `CategoryTheory.BialgCat.isCommComonObj_iff_isCocomm`: an `R`-bialgebra has a commutative
  comonoid object structure on its underlying module if and only if it is cocommutative.
* `CategoryTheory.BialgCat.instCommComonObj`: instance providing
  `IsCommComonObj (ModuleCat.of R B)` for cocommutative `B : BialgCat R`.
* `CategoryTheory.BialgCat.instIsCocomm`: theorem deducing `Coalgebra.IsCocomm R B` from
  `IsCommComonObj (ModuleCat.of R B)`.
* `CategoryTheory.BialgCat.isCommComonObj_toBimon_iff`: the comonoid object
  `((toBimon R).obj B).X.X` is commutative if and only if `B` is cocommutative.
* `CategoryTheory.BialgCat.ofBimon_isCocomm_iff`: the bialgebra `(ofBimon R).obj M` is
  cocommutative if and only if `M.X.X` is commutative.
* `CategoryTheory.BialgCat.toCommComonObj`: bundles a cocommutative `B : BialgCat R` into a
  `CommComon (ModuleCat R)`.

### Hopf algebras (`HopfAlgCat`)
* `CategoryTheory.HopfAlgCat.isCommComonObj_iff_isCocomm`: an `R`-Hopf algebra has a commutative
  comonoid object structure on its underlying module if and only if it is cocommutative.
* `CategoryTheory.HopfAlgCat.instCommComonObj`: instance providing
  `IsCommComonObj (ModuleCat.of R H)` for cocommutative `H : HopfAlgCat R`.
* `CategoryTheory.HopfAlgCat.instIsCocomm`: theorem deducing `Coalgebra.IsCocomm R H` from
  `IsCommComonObj (ModuleCat.of R H)`.
* `CategoryTheory.HopfAlgCat.isCommComonObj_toHopf_iff`: the comonoid object
  `((toHopf R).obj H).X` is commutative if and only if `H` is cocommutative.
* `CategoryTheory.HopfAlgCat.ofHopf_isCocomm_iff`: the Hopf algebra `(ofHopf R).obj M` is
  cocommutative if and only if `M.X` is commutative.
* `CategoryTheory.HopfAlgCat.toCommComonObj`: bundles a cocommutative `H : HopfAlgCat R` into a
  `CommComon (ModuleCat R)`.

## References

* M. E. Sweedler, *Hopf Algebras* (1969)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory ComonObj
open scoped TensorProduct

variable {R : Type u} [CommRing R]

namespace CategoryTheory

namespace BialgCat

/-- An `R`-bialgebra has a commutative comonoid object structure on its underlying module if and
only if it is cocommutative as an `R`-coalgebra. -/
theorem isCommComonObj_iff_isCocomm (B : BialgCat R) :
    IsCommComonObj (ModuleCat.of R B) ↔ Coalgebra.IsCocomm R B :=
  CoalgCat.isCommComonObj_iff_isCocomm (CoalgCat.of R B)

/-- A cocommutative `R`-bialgebra has a commutative comonoid object structure on its underlying
module. -/
instance instCommComonObj (B : BialgCat R) [Coalgebra.IsCocomm R B] :
    IsCommComonObj (ModuleCat.of R B) :=
  (isCommComonObj_iff_isCocomm B).mpr ‹_›

/-- A bialgebra whose underlying module is a commutative comonoid object is cocommutative. -/
theorem instIsCocomm (B : BialgCat R) [IsCommComonObj (ModuleCat.of R B)] :
    Coalgebra.IsCocomm R B :=
  (isCommComonObj_iff_isCocomm B).mp ‹_›

/-- The bimonoid object corresponding to an `R`-bialgebra under `toBimon` has a commutative comonoid
object structure if and only if the bialgebra is cocommutative. -/
theorem isCommComonObj_toBimon_iff (B : BialgCat R) :
    IsCommComonObj ((toBimon R).obj B).X.X ↔ Coalgebra.IsCocomm R B :=
  isCommComonObj_iff_isCocomm B

/-- A bimonoid object in `ModuleCat R` corresponds to a cocommutative `R`-bialgebra under
`ofBimon` if and only if its underlying comonoid object is commutative. -/
theorem ofBimon_isCocomm_iff (M : Bimon (ModuleCat R)) :
    Coalgebra.IsCocomm R ((Bimon.ofBimon R).obj M) ↔ IsCommComonObj M.X.X := by
  let _ : Coalgebra R M.X.X := (CoalgCat.ofComonObj M.X.X).instCoalgebra
  constructor
  · intro h
    constructor
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : M.X.X)
    exact @Coalgebra.comm_comul R ((Bimon.ofBimon R).obj M) _ _ _ _ h x
  · intro h
    constructor
    have hcomm := IsCommComonObj.comul_comm (X := M.X.X)
    apply LinearMap.ext
    intro (x : M.X.X)
    exact (LinearMap.ext_iff.mp (ModuleCat.hom_ext_iff.mp hcomm)) x

/-- Construct a commutative comonoid object in `ModuleCat R` from a cocommutative `R`-bialgebra. -/
@[simps X]
noncomputable def toCommComonObj (B : BialgCat R) [Coalgebra.IsCocomm R B] :
    CommComon (ModuleCat R) where
  X := ModuleCat.of R B
  comon := inferInstance
  comm := instCommComonObj B

/-- The comonoid underlying `toCommComonObj B` is the comonoid on `ModuleCat.of R B`. -/
@[simp]
theorem toCommComonObj_toComon (B : BialgCat R) [Coalgebra.IsCocomm R B] :
    (toCommComonObj B).toComon = ⟨ModuleCat.of R B⟩ :=
  rfl

end BialgCat

namespace HopfAlgCat

/-- An `R`-Hopf algebra has a commutative comonoid object structure on its underlying module if and
only if it is cocommutative as an `R`-coalgebra. -/
theorem isCommComonObj_iff_isCocomm (H : HopfAlgCat R) :
    IsCommComonObj (ModuleCat.of R H) ↔ Coalgebra.IsCocomm R H :=
  CoalgCat.isCommComonObj_iff_isCocomm (CoalgCat.of R H)

/-- A cocommutative `R`-Hopf algebra has a commutative comonoid object structure on its underlying
module. -/
instance instCommComonObj (H : HopfAlgCat R) [Coalgebra.IsCocomm R H] :
    IsCommComonObj (ModuleCat.of R H) :=
  (isCommComonObj_iff_isCocomm H).mpr ‹_›

/-- A Hopf algebra whose underlying module is a commutative comonoid object is cocommutative. -/
theorem instIsCocomm (H : HopfAlgCat R) [IsCommComonObj (ModuleCat.of R H)] :
    Coalgebra.IsCocomm R H :=
  (isCommComonObj_iff_isCocomm H).mp ‹_›

/-- The Hopf monoid object corresponding to an `R`-Hopf algebra under `toHopf` has a commutative
comonoid object structure if and only if the Hopf algebra is cocommutative. -/
theorem isCommComonObj_toHopf_iff (H : HopfAlgCat R) :
    IsCommComonObj ((toHopf R).obj H).X ↔ Coalgebra.IsCocomm R H :=
  isCommComonObj_iff_isCocomm H

/-- A Hopf monoid object in `ModuleCat R` corresponds to a cocommutative `R`-Hopf algebra under
`ofHopf` if and only if its underlying comonoid object is commutative. -/
theorem ofHopf_isCocomm_iff (M : Hopf (ModuleCat R)) :
    Coalgebra.IsCocomm R ((Hopf.ofHopf R).obj M) ↔ IsCommComonObj M.X := by
  let _ : Coalgebra R M.X := (CoalgCat.ofComonObj M.X).instCoalgebra
  constructor
  · intro h
    constructor
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : M.X)
    exact @Coalgebra.comm_comul R ((Hopf.ofHopf R).obj M) _ _ _ _ h x
  · intro h
    constructor
    have hcomm := IsCommComonObj.comul_comm (X := M.X)
    apply LinearMap.ext
    intro (x : M.X)
    exact (LinearMap.ext_iff.mp (ModuleCat.hom_ext_iff.mp hcomm)) x

/-- Construct a commutative comonoid object in `ModuleCat R` from a cocommutative `R`-Hopf
algebra. -/
@[simps X]
noncomputable def toCommComonObj (H : HopfAlgCat R) [Coalgebra.IsCocomm R H] :
    CommComon (ModuleCat R) where
  X := ModuleCat.of R H
  comon := inferInstance
  comm := instCommComonObj H

/-- The comonoid underlying `toCommComonObj H` is the comonoid on `ModuleCat.of R H`. -/
@[simp]
theorem toCommComonObj_toComon (H : HopfAlgCat R) [Coalgebra.IsCocomm R H] :
    (toCommComonObj H).toComon = ⟨ModuleCat.of R H⟩ :=
  rfl

end HopfAlgCat

end CategoryTheory
