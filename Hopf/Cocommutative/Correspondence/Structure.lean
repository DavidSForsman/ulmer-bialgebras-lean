module

public import Hopf.Cocommutative.Correspondence.Formal
public import Hopf.Cocommutative.Retraction
public import Hopf.Cocommutative.PointedDecompositionReduction
public import Hopf.Cocommutative.PrimitiveReduction

/-!
# Newman's correspondence, layer 2: structure of pointed cocommutative Hopf algebras

The one non-formal input of Newman's correspondence: for a **pointed** cocommutative Hopf algebra
`H` over a field,

* every sub-Hopf algebra `K` admits a right `K`-linear unital retraction `H ↠ K`
  (`HopfAlgebra.Cocommutative.Correspondence.rightRetraction_of_isPointed`). This is where
  Sweedler's freeness theorem enters: `H` is free over the irreducible part of `K`, and a complement
  can be chosen stable under right multiplication by `K`;
* the second closure identity reduces to primitive elements of the irreducible component of `1` (the
  coradical filtration) and then, by Kostant's decomposition of `H` into the components of its
  group-like elements, to all of `H`
  (`HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq_of_isPointed`).

Over an algebraically closed field every cocommutative coalgebra is pointed, which is how layer 3
reaches arbitrary fields.

## Main results

* `HopfAlgebra.Cocommutative.Correspondence.rightRetraction_of_isPointed`: for pointed cocommutative
  `H`, every sub-Hopf algebra `K` admits a right `K`-linear unital retraction `H ↠ K`.
* `HopfAlgebra.Cocommutative.Correspondence.irreducibleCore_of_isPointed`: for pointed cocommutative
  `H` and a left bi-ideal `I`, every element of `I` in the irreducible component of `1` lies in
  `τ (μ I)`.
* `HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq_of_isPointed`: for pointed `H`,
  `τ (μ I) = I` for every left bi-ideal `I`.
* `HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq_of_isPointed`: for pointed `H`,
  `μ (τ K) = K` for every sub-Hopf algebra `K`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapters 8–11
* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [D. E. Radford, *Pointed Hopf algebras are free over Hopf
  subalgebras*][radfordPointedHopfAlgebras1977]
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative.Correspondence

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- **Freeness.** Over a pointed cocommutative Hopf algebra, every sub-Hopf algebra `K` admits a
right `K`-linear unital retraction `H ↠ K`. -/
theorem rightRetraction_of_isPointed (hpt : Coalgebra.Coradical.IsPointed k H) {K : Subalgebra k H}
    (hK : IsSubHopfAlgebra k K) : Nonempty (RightRetraction K) := by
  obtain ⟨E, hmem, hid, hmul⟩ := HopfAlgebra.Cocommutative.exists_rightRetraction_subHopf hpt hK
  exact ⟨⟨E, hmem, hid, hmul⟩⟩

/-- **The irreducible core.** In a pointed cocommutative Hopf algebra, every element of a left
bi-ideal `I` lying in the irreducible component of `1` lies in `τ (μ I)`: Masuoka's criterion
(layer 1) applied to the retraction onto `μ I`, together with the reduction to primitives along
the coradical filtration. -/
theorem irreducibleCore_of_isPointed (hpt : Coalgebra.Coradical.IsPointed k H) {I : Submodule k H}
    (hI : IsLeftBiIdeal I) : IrreducibleCore k H I := by
  obtain ⟨E⟩ := rightRetraction_of_isPointed hpt (isSubHopf_coinvSubalgebra I hI.mul_mem)
  intro y hy hy1
  exact inf_glComponent_le_of_primitive_mem hI
    (fun _ hz _ hzp => mem_tau_coinv_of_primitive hI E hz hzp) ⟨hy, hy1⟩

/-- **The second closure identity for pointed `H`**: `τ (μ I) = I`, by Kostant's decomposition
from the irreducible core. -/
theorem tau_coinv_eq_of_isPointed (hpt : Coalgebra.Coradical.IsPointed k H) {I : Submodule k H}
    (hI : IsLeftBiIdeal I) : tau (coinv I) = I :=
  tau_coinv_eq_of_irreducibleCore hpt hI (irreducibleCore_of_isPointed hpt hI)

/-- **The first closure identity for pointed `H`**: `μ (τ K) = K`, from the retraction. -/
theorem coinv_tau_eq_of_isPointed (hpt : Coalgebra.Coradical.IsPointed k H) {K : Subalgebra k H}
    (hK : IsSubHopfAlgebra k K) :
    coinv (tau (Subalgebra.toSubmodule K)) = Subalgebra.toSubmodule K :=
  coinv_tau_eq_of_rightRetraction hK (rightRetraction_of_isPointed hpt hK).some

end HopfAlgebra.Cocommutative.Correspondence
