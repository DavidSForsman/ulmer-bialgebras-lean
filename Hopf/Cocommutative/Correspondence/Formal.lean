module

public import Hopf.Cocommutative.GenerationGeneral
public import Hopf.Cocommutative.PrimitiveMem
public import Hopf.Cocommutative.DescentAlgClosure

/-!
# Newman's correspondence, layer 1: the formal part

Let `H` be a cocommutative Hopf algebra over a field `k`. Newman's correspondence pairs a sub-Hopf
algebra `K ⊆ H` with the left bi-ideal `τ K = H K⁺`, and a left bi-ideal `I` with the sub-Hopf
algebra `μ I = {h | Δ h - h ⊗ 1 ∈ H ⊗ I}` of coinvariants. This file contains the part of the
proof that uses no structure theory of Hopf algebras: everything follows from a **right
`K`-linear unital retraction** `E : H ↠ K`, which makes `K` a direct summand of `H` as a right
`K`-module, so `K ⊆ H` is pure. A retraction does not make `H` faithfully flat over `K`, and
nothing here needs that.

The descent statements hold more generally over absolutely flat base rings
(`HopfAlgebra.Cocommutative.descent_of_retraction`).

Layer 2 (`Cocommutative/Correspondence/Structure.lean`) provides the retraction for pointed `H`,
and layer 3 (`Cocommutative/Correspondence/Main.lean`) assembles the correspondence over an
arbitrary field.

## Main results

* `HopfAlgebra.Cocommutative.Correspondence.RightRetraction`: a right `K`-linear unital retraction
  `H ↠ K`.
* `HopfAlgebra.Cocommutative.Correspondence.descent_of_rightRetraction`: an element of `H` which is
  balanced in `H ⊗_K H` lies in `K` (descent along the pure inclusion `K ⊆ H`);
* `HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq_of_rightRetraction`: the first closure
  identity `μ (τ K) = K`;
* `HopfAlgebra.Cocommutative.Correspondence.mem_tau_coinv_of_primitive`: Masuoka's criterion, the
  formal half of the second closure identity `τ (μ I) = I`: given a retraction onto `μ I`, an
  element of `I` that is primitive modulo `τ (μ I)` lies in `τ (μ I)`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative.Correspondence

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- A **right `K`-linear unital retraction** `H ↠ K` onto a subalgebra `K`: a `k`-linear map
`E : H → H` with values in `K`, which is the identity on `K` and satisfies `E (x a) = E x · a`
for `a ∈ K`. -/
structure RightRetraction (K : Subalgebra k H) where
  /-- The underlying linear map. -/
  toLinearMap : H →ₗ[k] H
  mem : ∀ x : H, toLinearMap x ∈ K
  map_of_mem : ∀ a ∈ K, toLinearMap a = a
  map_mul : ∀ (x : H), ∀ a ∈ K, toLinearMap (x * a) = toLinearMap x * a

variable {K : Subalgebra k H}

omit [Coalgebra.IsCocomm k H] in
/-- **Descent along `K ⊆ H`**, from a right `K`-linear retraction: an element `h` with
`h ⊗ 1 = 1 ⊗ h` in `H ⊗_K H` lies in `K`. -/
theorem descent_of_rightRetraction (E : RightRetraction K) : Descent k K :=
  fun _ hh => descent_of_retraction K E.toLinearMap E.mem E.map_of_mem E.map_mul hh

/-- **The first closure identity** `μ (τ K) = K`, from a right `K`-linear retraction. -/
theorem coinv_tau_eq_of_rightRetraction (hK : IsSubHopfAlgebra k K) (E : RightRetraction K) :
    coinv (tau (Subalgebra.toSubmodule K)) = Subalgebra.toSubmodule K :=
  coinv_tau_eq_of_retraction hK E.toLinearMap E.mem E.map_of_mem E.map_mul

/-- **Masuoka's criterion.** Let `I` be a left bi-ideal and suppose the sub-Hopf algebra `μ I`
admits a right `μ I`-linear retraction. Then every `y ∈ I` that is primitive modulo
`N = τ (μ I)` lies in `N`. -/
theorem mem_tau_coinv_of_primitive {I : Submodule k H} (hI : IsLeftBiIdeal I)
    (E : RightRetraction (coinvSubalgebra hI.mul_mem)) {y : H} (hy : y ∈ I)
    (hprim : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y ∈
      leftTensor (tau (coinv I)) ⊔ rightTensor (tau (coinv I))) :
    y ∈ tau (coinv I) :=
  HopfAlgebra.Cocommutative.mem_tau_coinv_of_primitive hI E.toLinearMap E.mem E.map_of_mem
    E.map_mul hy hprim

end HopfAlgebra.Cocommutative.Correspondence
