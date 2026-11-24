module

public import Hopf.Cocommutative.Amitsur
public import Hopf.Cocommutative.CoinvAntipode

/-!
# Masuoka's criterion: elements of `I` primitive modulo `τ (μ I)` lie in `τ (μ I)`

This is the input that the reduction of Newman's second closure identity to primitives
(`HopfAlgebra.Cocommutative.inf_glComponent_le_of_primitive_mem`) needs.  Given a right `μ I`-linear
retraction `E : H ↠ μ I` — which Sweedler's freeness theorem provides for a pointed cocommutative
`H` — Masuoka's coring argument (`HopfAlgebra.Cocommutative.exists_comul_sub_mem`) produces, for
`y ∈ I` primitive modulo `N = τ (μ I)`, an element `x` with `Δ x - 1 ⊗ x + y ⊗ 1 ∈ N ⊗ H`.  Two
contractions of this relation finish the proof: the first leg shows `x ∈ μ I`, and applying `id ⊗ ε`
shows `y ≡ ε(x) 1 - x` modulo `N`, which lies in `N` because `x ∈ μ I`.

## Main result

* `HopfAlgebra.Cocommutative.mem_tau_coinv_of_primitive` — `y ∈ I` primitive modulo `τ (μ I)` lies
  in `τ (μ I)`.

## References

* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section


open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

universe u

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### The contraction `id ⊗ ε` -/

variable (k H) in
/-- The contraction `id ⊗ ε : H ⊗ H → H`. -/
noncomputable def epsR : H ⊗[k] H →ₗ[k] H :=
  (TensorProduct.rid k H).toLinearMap ∘ₗ LinearMap.lTensor H (counit (R := k) (A := H))

/-- `epsR (a ⊗ b) = ε(b) • a`. -/
@[simp] lemma epsR_tmul (a b : H) :
    epsR k H (a ⊗ₜ[k] b) = (counit (R := k) b) • a := by
  simp [epsR]

/-- `(id ⊗ ε) (Δ x) = x`. -/
lemma epsR_comul (x : H) : epsR k H (comul (R := k) x) = x := by
  simp only [epsR, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show LinearMap.lTensor H (counit (R := k) (A := H)) (comul (R := k) x) = x ⊗ₜ[k] (1 : k) from
    congr($(lTensor_counit_comp_comul (R := k) (A := H)) x)]
  simp

/-- `id ⊗ ε` maps `N ⊗ H` into `N`. -/
lemma epsR_mem_of_mem_leftTensor {N : Submodule k H} {t : H ⊗[k] H}
    (ht : t ∈ HopfAlgebra.Cocommutative.leftTensor N) : epsR k H t ∈ N := by
  refine leftTensor_le (P := Submodule.comap (epsR k H) N) (fun x hx a => ?_) ht
  simpa using N.smul_mem _ hx

/-- The twist exchanges `N ⊗ H` and `H ⊗ N`. -/
lemma comm_mem_rightTensor {N : Submodule k H} {t : H ⊗[k] H}
    (ht : t ∈ HopfAlgebra.Cocommutative.leftTensor N) :
    (TensorProduct.comm k H H) t ∈ HopfAlgebra.Cocommutative.rightTensor N := by
  refine leftTensor_le (P := Submodule.comap (TensorProduct.comm k H H).toLinearMap
    (HopfAlgebra.Cocommutative.rightTensor N)) (fun x hx a => ?_) ht
  simpa using HopfAlgebra.Cocommutative.tmul_mem_rightTensor a hx

/-! ### The criterion -/

variable [Coalgebra.IsCocomm k H]

/-- For a cocommutative `H`, the left-handed coinvariance condition implies the right-handed
one, which is Newman's `μ`. -/
lemma mem_coinv_of_comul_sub_one_tmul {I : Submodule k H} {x : H}
    (hx : comul (R := k) x - (1 : H) ⊗ₜ[k] x ∈ HopfAlgebra.Cocommutative.leftTensor I) :
    x ∈ HopfAlgebra.Cocommutative.coinv I := by
  have hcomm := comm_mem_rightTensor hx
  rw [map_sub, TensorProduct.comm_tmul] at hcomm
  have hco : (TensorProduct.comm k H H) (comul (R := k) x) = comul (R := k) x := by
    have h := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := H)) x)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe] using h
  rw [hco] at hcomm
  exact hcomm

/-- **Masuoka's criterion.**  Let `I` be a left bi-ideal of a cocommutative Hopf algebra `H` over
a field, and suppose the sub-Hopf algebra `μ I` of coinvariants admits a right `μ I`-linear
retraction `E : H ↠ μ I`.  Then every `y ∈ I` whose class modulo `N = τ (μ I)` is primitive lies
in `N`. -/
theorem mem_tau_coinv_of_primitive {I : Submodule k H} (hI : IsLeftBiIdeal I)
    (E : H →ₗ[k] H) (hEmem : ∀ x : H, E x ∈ HopfAlgebra.Cocommutative.coinv I)
    (hEid : ∀ a ∈ HopfAlgebra.Cocommutative.coinv I, E a = a)
    (hEmul : ∀ (x : H), ∀ a ∈ HopfAlgebra.Cocommutative.coinv I, E (x * a) = E x * a)
    {y : H} (hy : y ∈ I)
    (hprim : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y ∈
      leftTensor (tau (coinv I)) ⊔
        rightTensor (tau (coinv I))) :
    y ∈ HopfAlgebra.Cocommutative.tau (HopfAlgebra.Cocommutative.coinv I) := by
  classical
  set K : Subalgebra k H := HopfAlgebra.Cocommutative.coinvSubalgebra hI.mul_mem with hKdef
  have hKsub : K.toSubmodule = HopfAlgebra.Cocommutative.coinv I := rfl
  have hK : IsSubHopfAlgebra k K := isSubHopf_coinvSubalgebra I hI.mul_mem
  set N : Submodule k H := HopfAlgebra.Cocommutative.tau (HopfAlgebra.Cocommutative.coinv I) with hN
  have hNI : N ≤ I := HopfAlgebra.Cocommutative.tau_coinv_le hI.mul_mem
  obtain ⟨x, hx⟩ := exists_comul_sub_mem hK E hEmem hEid hEmul (y := y) (by rw [hKsub]; exact hprim)
  rw [hKsub] at hx
  -- the first leg: `x` is a coinvariant
  have hxI : comul (R := k) x - (1 : H) ⊗ₜ[k] x ∈ HopfAlgebra.Cocommutative.leftTensor I := by
    have h1 : comul (R := k) x - (1 : H) ⊗ₜ[k] x
        = (comul (R := k) x - (1 : H) ⊗ₜ[k] x + y ⊗ₜ[k] (1 : H)) - y ⊗ₜ[k] (1 : H) := by abel
    rw [h1]
    refine Submodule.sub_mem _ ?_ (HopfAlgebra.Cocommutative.tmul_mem_leftTensor hy 1)
    exact Submodule.map₂_le_map₂ hNI le_rfl hx
  have hxK : x ∈ HopfAlgebra.Cocommutative.coinv I := mem_coinv_of_comul_sub_one_tmul hxI
  -- the second contraction
  have hcontract : x - (counit (R := k) x) • (1 : H) + y ∈ N := by
    have h := epsR_mem_of_mem_leftTensor hx
    rw [map_add, map_sub, epsR_comul, epsR_tmul, epsR_tmul] at h
    simpa using h
  have hxaug : x - (counit (R := k) x) • (1 : H) ∈ N := by
    refine HopfAlgebra.Cocommutative.augPart_le_tau ?_
    refine ⟨Submodule.sub_mem _ hxK (Submodule.smul_mem _ _ (one_mem_coinv I)), ?_⟩
    simp
  have : y = (x - (counit (R := k) x) • (1 : H) + y) - (x - (counit (R := k) x) • (1 : H)) := by
    abel
  rw [this]
  exact Submodule.sub_mem _ hcontract hxaug

end HopfAlgebra.Cocommutative
