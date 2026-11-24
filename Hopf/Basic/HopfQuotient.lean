module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.AntipodeAlgHom
public import Hopf.Basic.NormalHopfIdeal

/-!
# The quotient of a Hopf algebra by a Hopf ideal

Let `H` be a commutative Hopf algebra over a commutative von Neumann regular ring `k` (for instance
a field) and let `I` be a **Hopf ideal** of `H` (`HopfAlgebra.IsHopfIdeal`), that is an ideal
with

`ε I = 0`,  `Δ I ⊆ I ⊗ H + H ⊗ I`,  `S I ⊆ I`.

This file endows the quotient algebra `H ⧸ I` with the structure of a Hopf algebra, so that the
quotient map `H → H ⧸ I` is a morphism of Hopf algebras.  Mathlib has no quotient construction
for coalgebras, bialgebras or Hopf algebras, so everything is built by hand: the comultiplication,
counit and antipode of `H ⧸ I` are the maps induced by those of `H` (the three conditions above
are exactly what is needed for them to descend), and each axiom is checked on the image of an
element of `H`, using the surjectivity of the quotient map.

The structures are provided as instances guarded by `Fact (IsHopfIdeal k I)`; to use them, put
`haveI : Fact (HopfAlgebra.IsHopfIdeal k I) := ⟨hI⟩` in scope.

## Main definitions and results

* `HopfAlgebra.quotCoalgebra`, `HopfAlgebra.quotBialgebra`, `HopfAlgebra.quotHopfAlgebra`:
  the coalgebra, bialgebra and Hopf algebra structures on `H ⧸ I`;
* `HopfAlgebra.quotBialgHom`: the quotient map as a morphism of Hopf algebras `H →ₐc[k] H ⧸ I`;
* `HopfAlgebra.quotCounit_mk`, `HopfAlgebra.quotComul_mk`, `HopfAlgebra.quotAntipode_mk`:
  the defining formulas for the structure maps of the quotient.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Sections 2 and 3
-/

@[expose] public section

section
open HopfAlgebra
namespace HopfAlgebra

open TensorProduct Coalgebra

variable {H : Type*} (k : Type*) [CommRing k] [CommRing H] [HopfAlgebra k H]

section Defs

variable (I : Ideal H) [hI : Fact (IsHopfIdeal k I)]

/-- The comultiplication of `H ⧸ I`, as an algebra homomorphism. -/
noncomputable abbrev quotComulAlg : (H ⧸ I) →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I) :=
  letI : Ideal.IsHopfIdeal k I := hI.out
  Bialgebra.Quotient.comulAlgHom I

/-- The counit of `H ⧸ I`, as an algebra homomorphism. -/
noncomputable abbrev quotCounitAlg : (H ⧸ I) →ₐ[k] k :=
  letI : Ideal.IsHopfIdeal k I := hI.out
  Bialgebra.Quotient.counitAlgHom I

/-- The antipode of `H ⧸ I`, as an algebra homomorphism. -/
noncomputable abbrev quotAntipodeAlg : (H ⧸ I) →ₐ[k] (H ⧸ I) :=
  letI : Ideal.IsHopfIdeal k I := hI.out
  HopfAlgebra.antipodeAlgHom k (H ⧸ I)

/-- The linear map `H ⊗ H → (H ⧸ I) ⊗ (H ⧸ I)` induced by the quotient map. -/
noncomputable abbrev quotMap2 : H ⊗[k] H →ₗ[k] (H ⧸ I) ⊗[k] (H ⧸ I) :=
  TensorProduct.map (Ideal.Quotient.mkₐ k I).toLinearMap (Ideal.Quotient.mkₐ k I).toLinearMap

/-- The comultiplication of `H ⧸ I` on a class `[x]` is `quotMap2 (Δ x)`. -/
@[simp] lemma quotComulAlg_mk (x : H) :
    quotComulAlg k I (Ideal.Quotient.mk I x) = quotMap2 k I (comul (R := k) x) := by
  change (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I))
      (comul (R := k) x) = _
  induction (comul (R := k) x) with
  | tmul a b => simp
  | add p q hp hq => simp only [map_add, hp, hq]
/-- The counit of `H ⧸ I` on a class `[x]` is `ε(x)`. -/
@[simp] lemma quotCounitAlg_mk (x : H) :
    quotCounitAlg k I (Ideal.Quotient.mk I x) = counit (R := k) x := rfl

/-- The antipode of `H ⧸ I` on a class `[x]` is `[S x]`. -/
@[simp] lemma quotAntipodeAlg_mk (x : H) :
    quotAntipodeAlg k I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (antipode k x) := rfl

/-! ### The coalgebra, bialgebra and Hopf algebra structures -/

/-- **The quotient of a Hopf algebra by a Hopf ideal is a coalgebra.** -/
noncomputable instance quotCoalgebra : Coalgebra k (H ⧸ I) := by
  letI : Ideal.IsHopfIdeal k I := hI.out
  infer_instance

/-- The counit of `H/I` on a class `[x]` is `ε(x)`. -/
@[simp] lemma quotCounit_mk (x : H) :
    counit (R := k) (A := H ⧸ I) (Ideal.Quotient.mk I x) = counit (R := k) x := rfl

/-- The comultiplication of `H/I` on a class `[x]` is `(π ⊗ π) (Δ x)`. -/
@[simp] lemma quotComul_mk (x : H) :
    comul (R := k) (A := H ⧸ I) (Ideal.Quotient.mk I x) = quotMap2 k I (comul (R := k) x) :=
  quotComulAlg_mk k I x

/-- **The quotient of a Hopf algebra by a Hopf ideal is a bialgebra.** -/
noncomputable instance quotBialgebra : Bialgebra k (H ⧸ I) := by
  letI : Ideal.IsHopfIdeal k I := hI.out
  infer_instance

/-- **The quotient of a Hopf algebra by a Hopf ideal is a Hopf algebra.** -/
noncomputable instance quotHopfAlgebra : HopfAlgebra k (H ⧸ I) := by
  letI : Ideal.IsHopfIdeal k I := hI.out
  infer_instance

/-- The antipode of `H/I` on a class `[x]` is `[S x]`. -/
@[simp] lemma quotAntipode_mk (x : H) :
    antipode k (A := H ⧸ I) (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (antipode k x) := rfl

/-- The quotient map as a morphism of Hopf algebras. -/
noncomputable abbrev quotBialgHom : H →ₐc[k] H ⧸ I :=
  letI : Ideal.IsHopfIdeal k I := hI.out
  Bialgebra.Quotient.mkBialgHom I

/-- `quotBialgHom k I` sends `x` to its class in `H ⧸ I`. -/
@[simp] lemma quotBialgHom_apply (x : H) :
    quotBialgHom k I x = Ideal.Quotient.mk I x := rfl

/-- The quotient map `H → H/I` is surjective. -/
lemma quotBialgHom_surjective : Function.Surjective (quotBialgHom k I) :=
  Ideal.Quotient.mk_surjective

end Defs

end HopfAlgebra
end
