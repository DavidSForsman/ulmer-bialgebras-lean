module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Hopf.Basic.ComoduleTensor
public import Hopf.Basic.HopfModule
public import Hopf.Basic.RelativeHopfModule

/-!
# Coalgebra representations as comodules

Bundling a coalgebra representation as a comodule.

## Main results

* `Coalgebra.Repr.toComodule`: a representation `r` of `Δ c` in a coalgebra `C`, read as a
  representation (`Coalgebra.Comodule.Repr`) of the coaction of `C` on itself at `c`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Proposition 2.5
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.1.1
-/

@[expose] public section

open Coalgebra Coalgebra.Comodule TensorProduct

/-- A Sweedler representation of the comultiplication, read as a representation of the coaction
of the coalgebra on itself. -/
def Coalgebra.Repr.toComodule {R C : Type*} [CommSemiring R] [AddCommMonoid C]
    [Module R C] [Coalgebra R C] {c : C} {ι : Type*} (r : Coalgebra.Repr R c ι) :
    Coalgebra.Comodule.Repr R C c where
  index := r.index
  left := r.left
  right := r.right
  eq := r.eq
