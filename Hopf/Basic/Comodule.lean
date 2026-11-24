module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Right comodules over a coalgebra

Mathlib has coalgebras, but no comodules.  Takeuchi's paper
(*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972))
is written throughout in the language of comodules and (relative) Hopf modules, so we develop
here the small amount of the theory that is needed.

## Main definitions

* `Coalgebra.RightComodule R C M`: a right comodule structure on an `R`-module `M` over an
  `R`-coalgebra `C`, i.e. a coassociative counital coaction `ρ : M →ₗ[R] M ⊗[R] C`;
* `Coalgebra.Comodule.Repr`: a finite representation `∑ mᵢ ⊗ cᵢ = ρ m` of the coaction of an
  element, the comodule analogue of `Coalgebra.Repr`;
* `Coalgebra.Comodule.IsSubcomodule`: a submodule `N ≤ M` with `ρ N ⊆ N ⊗ C` (expressed as
  membership in the range of `N ⊗ C → M ⊗ C`).

## Main results

* `Coalgebra.Comodule.sum_counit_smul`: the counit law `∑ ε(cᵢ) • mᵢ = m`;
* `Coalgebra.Comodule.sum_tmul_tmul_eq`: coassociativity in Sweedler form.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter II
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open TensorProduct

namespace Coalgebra

universe u v w

/-- A **right comodule** over an `R`-coalgebra `C` is an `R`-module `M` together with a
coassociative and counital coaction `ρ : M →ₗ[R] M ⊗[R] C`. -/
class RightComodule (R : Type u) (C : Type v) (M : Type w) [CommSemiring R]
    [AddCommMonoid C] [Module R C] [CoalgebraStruct R C] [AddCommMonoid M] [Module R M] where
  /-- The coaction of the comodule. -/
  coact : M →ₗ[R] M ⊗[R] C
  /-- Coassociativity of the coaction. -/
  coassoc : (TensorProduct.assoc R M C C).toLinearMap ∘ₗ (LinearMap.rTensor C coact) ∘ₗ coact
      = (LinearMap.lTensor M (comul (R := R) (A := C))) ∘ₗ coact
  /-- Counitality of the coaction. -/
  counit_coact : (TensorProduct.rid R M).toLinearMap ∘ₗ
      (LinearMap.lTensor M (counit (R := R) (A := C))) ∘ₗ coact = LinearMap.id

namespace Comodule

export RightComodule (coact)

variable {R : Type u} {C : Type v} {M : Type w} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [CoalgebraStruct R C] [AddCommMonoid M] [Module R M]

section Repr

variable (R C)

/-- A representation of the coaction of an element `m` of a right `C`-comodule `M` is a finite
sum of pure tensors `∑ mᵢ ⊗ cᵢ` equal to `ρ m`. -/
structure Repr [RightComodule R C M] (m : M) where
  /-- the indexing type -/
  {ι : Type*}
  /-- the finite indexing set -/
  (index : Finset ι)
  /-- the `M`-coordinates -/
  (left : ι → M)
  /-- the `C`-coordinates -/
  (right : ι → C)
  /-- the defining equation -/
  (eq : ∑ i ∈ index, left i ⊗ₜ[R] right i = coact (R := R) (C := C) m)

/-- An arbitrarily chosen representation of the coaction of an element. -/
noncomputable def Repr.arbitrary [RightComodule R C M] (m : M) : Repr R C m where
  left := Prod.fst
  right := Prod.snd
  index := TensorProduct.exists_finset (R := R) (coact (R := R) (C := C) m) |>.choose
  eq := TensorProduct.exists_finset (R := R) (coact (R := R) (C := C) m) |>.choose_spec.symm

end Repr

variable [RightComodule R C M]

/-- The counit law in Sweedler form: `∑ ε(cᵢ) • mᵢ = m`. -/
lemma sum_counit_smul {m : M} (r : Repr R C m) :
    ∑ i ∈ r.index, (counit (R := R) (r.right i)) • r.left i = m := by
  have h := congr($(Coalgebra.RightComodule.counit_coact (R := R) (C := C) (M := M)) m)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at h
  rw [← r.eq] at h
  simpa [map_sum, TensorProduct.smul_tmul'] using h

/-- Coassociativity in Sweedler form. -/
lemma sum_tmul_tmul_eq {m : M} (r : Repr R C m)
    (a : (i : r.ι) → Repr R C (r.left i)) {κ : r.ι → Type*}
    (b : (i : r.ι) → Coalgebra.Repr R (r.right i) (κ i)) :
    ∑ i ∈ r.index, ∑ j ∈ (a i).index,
      (a i).left j ⊗ₜ[R] ((a i).right j ⊗ₜ[R] r.right i)
      = ∑ i ∈ r.index, ∑ j ∈ (b i).index,
      r.left i ⊗ₜ[R] ((b i).left j ⊗ₜ[R] (b i).right j) := by
  simpa [(b _).eq, ← (a _).eq, ← TensorProduct.tmul_sum, TensorProduct.sum_tmul, ← r.eq]
    using congr($(Coalgebra.RightComodule.coassoc (R := R) (C := C) (M := M)) m)

section Subcomodule

/-- A submodule `N` of a right `C`-comodule `M` is a **subcomodule** if the coaction maps `N`
into `N ⊗ C`. -/
def IsSubcomodule (N : Submodule R M) : Prop :=
  ∀ x ∈ N, coact (R := R) (C := C) x ∈ LinearMap.range (LinearMap.rTensor C N.subtype)

end Subcomodule

/-- A coalgebra is a right comodule over itself, via the comultiplication. -/
instance (priority := 100) _root_.Coalgebra.RightComodule.instSelf
    (R : Type u) (C : Type v) [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C] :
    RightComodule R C C where
  coact := comul
  coassoc := Coalgebra.coassoc
  counit_coact := by
    ext c
    simp

/-- The coaction of a coalgebra `C` regarded as a right comodule over itself is `Δ`. -/
@[simp] lemma coact_self (R : Type u) (C : Type v) [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] : coact (R := R) (C := C) (M := C) = comul := rfl

end Comodule

end Coalgebra
