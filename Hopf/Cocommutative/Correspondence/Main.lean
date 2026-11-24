module

public import Hopf.Cocommutative.Correspondence.Structure
public import Hopf.Cocommutative.CoinvBaseChange

/-!
# Newman's correspondence, layer 3: assembly over an arbitrary field

Let `H` be a cocommutative Hopf algebra over a field `k`. The maps

* `τ : K ↦ H K⁺` from sub-Hopf algebras to left bi-ideals, and
* `μ : I ↦ {h | Δ h − h ⊗ 1 ∈ H ⊗ I}` from left bi-ideals to sub-Hopf algebras

form a Galois connection (`HopfAlgebra.Cocommutative.galoisConnection_tauMap_muMap`). Newman's
theorem says they are mutually inverse. Both closure identities are proved for pointed `H` in
layer 2. They reach an arbitrary field by base change to an algebraic closure `k̄`: `k̄ ⊗ H` is
pointed, and

* descent along `K ⊆ H` descends from descent along `k̄ ⊗ K ⊆ k̄ ⊗ H`
  (`HopfAlgebra.Cocommutative.descent_of_algebraicClosure`), giving `μ (τ K) = K`;
* `τ (μ I) = I` descends from the identity for `k̄ ⊗ I`
  (`HopfAlgebra.Cocommutative.tau_coinv_eq_of_baseChange'`).

## Main results

* `HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq`: `μ (τ K) = K`;
* `HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq`: `τ (μ I) = I`;
* `HopfAlgebra.Cocommutative.Correspondence.tauEquiv`,
  `HopfAlgebra.Cocommutative.Correspondence.tauOrderIso`: **Newman's correspondence** as an
  equivalence and an order isomorphism;
* `HopfAlgebra.Cocommutative.Correspondence.exists_unique_subHopf`: every left bi-ideal is `H K⁺`
  for exactly one sub-Hopf algebra `K`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975], Theorems 3.1–3.4
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra

namespace HopfAlgebra.Cocommutative.Correspondence

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- **The first closure identity** `μ (τ K) = K` for every sub-Hopf algebra `K` of a cocommutative
Hopf algebra over a field. -/
theorem coinv_tau_eq {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) :
    coinv (tau (Subalgebra.toSubmodule K)) = Subalgebra.toSubmodule K :=
  coinv_tau_eq_of_descent hK <| descent_of_algebraicClosure
    (fun _ _ _ _ _ _ _ _ hK' =>
      descent_of_rightRetraction (rightRetraction_of_isPointed isPointed_of_isAlgClosed hK').some)
          hK

/-- **The second closure identity** `τ (μ I) = I` for every left bi-ideal `I` of a cocommutative
Hopf algebra over a field. -/
theorem tau_coinv_eq {I : Submodule k H} (hI : IsLeftBiIdeal I) : tau (coinv I) = I :=
  tau_coinv_eq_of_baseChange' (L := AlgebraicClosure k) hI fun _ hJ =>
    tau_coinv_eq_of_isPointed isPointed_of_isAlgClosed hJ

/-- `μ (τ K) = K` for every sub-Hopf algebra `K`, as an equality in `SubHopfAlg k H`. -/
lemma muMap_tauMap (K : SubHopfAlg k H) : muMap (tauMap K) = K :=
  SubHopfAlg.ext (Subalgebra.toSubmodule_injective (coinv_tau_eq K.isSubHopf))

/-- `τ (μ I) = I` for every left bi-ideal `I`, as an equality in `LeftBiIdeal k H`. -/
lemma tauMap_muMap (I : LeftBiIdeal k H) : tauMap (muMap I) = I :=
  LeftBiIdeal.ext (tau_coinv_eq I.isLeftBiIdeal)

/-- **Newman's correspondence**: `τ : K ↦ H K⁺` and `μ` are mutually inverse bijections between
the sub-Hopf algebras and the left bi-ideals of a cocommutative Hopf algebra over a field
(Newman [Newman1975]). -/
noncomputable def tauEquiv : SubHopfAlg k H ≃ LeftBiIdeal k H where
  toFun := tauMap
  invFun := muMap
  left_inv := muMap_tauMap
  right_inv := tauMap_muMap

/-- The carrier of `tauEquiv K` is `τ K`. -/
@[simp] lemma tauEquiv_apply (K : SubHopfAlg k H) :
    (tauEquiv K).carrier = tau K.carrier.toSubmodule := rfl

/-- The carrier of `tauEquiv.symm I` is `μ I`. -/
@[simp] lemma tauEquiv_symm_apply (I : LeftBiIdeal k H) :
    (tauEquiv.symm I).carrier.toSubmodule = coinv I.carrier := rfl

/-- **Newman's correspondence, elementwise**: every left bi-ideal `I` is `H K⁺` for exactly one
sub-Hopf algebra `K`, namely `K = μ I` (Newman [Newman1975]). -/
theorem exists_unique_subHopf (I : LeftBiIdeal k H) : ∃! K : SubHopfAlg k H, tauMap K = I :=
  ⟨muMap I, tauMap_muMap I, fun K hK => by rw [← hK, muMap_tauMap]⟩

end HopfAlgebra.Cocommutative.Correspondence
