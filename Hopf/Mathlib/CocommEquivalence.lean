module

public import Mathlib.Algebra.Category.CoalgCat.ComonEquivalence
public import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Identification of cocommutative coalgebras across category equivalences

Given a commutative ring `R`, this file establishes the compatibility of coalgebra
cocommutativity (`Coalgebra.IsCocomm`) with commutative comonoid objects (`IsCommComonObj`
and `CommComon`) in `ModuleCat R` across the equivalence `CoalgCat R ≌ Comon (ModuleCat R)`.
The extensions to `BialgCat R` and `HopfAlgCat R` live in
`Companion/Hopf/Mathlib/CocommEquivalenceExtra.lean`.

## Main results

### Coalgebras (`CoalgCat`)
* `CategoryTheory.CoalgCat.isCommComonObj_iff_isCocomm`: an `R`-coalgebra has a commutative
  comonoid object structure on its underlying module if and only if it is cocommutative.
* `CategoryTheory.CoalgCat.instCommComonObj`: instance providing
  `IsCommComonObj (ModuleCat.of R C)` for cocommutative `C : CoalgCat R`.
* `CategoryTheory.CoalgCat.instIsCocomm`: theorem deducing `Coalgebra.IsCocomm R C` from
  `IsCommComonObj (ModuleCat.of R C)`.
* `CategoryTheory.CoalgCat.isCommComonObj_toComon_iff`: the comonoid object `(toComon R).obj C`
  is commutative if and only if `C` is cocommutative.
* `CategoryTheory.CoalgCat.ofComon_isCocomm_iff`: the coalgebra `(ofComon R).obj M` is
  cocommutative if and only if `M.X` is commutative.
* `CategoryTheory.CoalgCat.toCommComonObj`: bundles a cocommutative `C : CoalgCat R` into a
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

namespace CoalgCat

/-- An `R`-coalgebra has a commutative comonoid object structure in `ModuleCat R` if and only if
it is cocommutative as an `R`-coalgebra. -/
theorem isCommComonObj_iff_isCocomm (C : CoalgCat R) :
    IsCommComonObj (ModuleCat.of R C) ↔ Coalgebra.IsCocomm R C := by
  constructor
  · intro h
    constructor
    have hcomm := IsCommComonObj.comul_comm (X := ModuleCat.of R C)
    apply LinearMap.ext
    intro x
    exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.1 hcomm) x
  · intro h
    constructor
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Coalgebra.comm_comul R x

instance instCommComonObj (C : CoalgCat R) [Coalgebra.IsCocomm R C] :
    IsCommComonObj (ModuleCat.of R C) :=
  (isCommComonObj_iff_isCocomm C).mpr ‹_›

/-- A coalgebra whose underlying module is a commutative comonoid object is cocommutative. -/
theorem instIsCocomm (C : CoalgCat R) [IsCommComonObj (ModuleCat.of R C)] :
    Coalgebra.IsCocomm R C :=
  (isCommComonObj_iff_isCocomm C).mp ‹_›

/-- The comonoid object corresponding to an `R`-coalgebra under `toComon` has a commutative
comonoid object structure if and only if the coalgebra is cocommutative. -/
theorem isCommComonObj_toComon_iff (C : CoalgCat R) :
    IsCommComonObj ((CoalgCat.toComon R).obj C).X ↔ Coalgebra.IsCocomm R C :=
  isCommComonObj_iff_isCocomm C

/-- A comonoid object in `ModuleCat R` corresponds to a cocommutative `R`-coalgebra under
`ofComon` if and only if it is commutative. -/
theorem ofComon_isCocomm_iff (M : Comon (ModuleCat R)) :
    Coalgebra.IsCocomm R ((CoalgCat.ofComon R).obj M) ↔ IsCommComonObj M.X := by
  constructor
  · intro h
    constructor
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro (x : M.X)
    exact @Coalgebra.comm_comul R ((CoalgCat.ofComon R).obj M) _ _ _ _ h x
  · intro h
    constructor
    have hcomm := IsCommComonObj.comul_comm (X := M.X)
    apply LinearMap.ext
    intro (x : M.X)
    exact LinearMap.ext_iff.1 (ModuleCat.hom_ext_iff.1 hcomm) x

/-- Construct a commutative comonoid object in `ModuleCat R` from a cocommutative `R`-coalgebra. -/
@[simps X]
noncomputable def toCommComonObj (C : CoalgCat R) [Coalgebra.IsCocomm R C] :
    CommComon (ModuleCat R) where
  X := ModuleCat.of R C
  comon := inferInstance
  comm := instCommComonObj C

/-- The comonoid underlying `toCommComonObj C` is the image of `C` under `CoalgCat.toComon`. -/
@[simp]
theorem toCommComonObj_toComon (C : CoalgCat R) [Coalgebra.IsCocomm R C] :
    (toCommComonObj C).toComon = (CoalgCat.toComon R).obj C :=
  rfl

end CoalgCat

end CategoryTheory
