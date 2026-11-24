module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Hopf.Cocommutative.GenerationGeneral

/-!
# Descent for Newman's correspondence descends along a field extension

The remaining input of Newman's closure identity `μ (τ K) = K` for a sub-Hopf algebra `K` of a
cocommutative Hopf algebra `H` over a field `k` is *descent along `K ⊆ H`*:

```
h ⊗ 1 - 1 ⊗ h ∈ balRel K  →  h ∈ K .
```

This file proves that this input **descends along an arbitrary field extension** `k ⊆ L`: if it
holds for the base-changed pair `L ⊗ K ⊆ L ⊗ H` over `L`, it holds for `K ⊆ H` over `k`.  This
is the "simple scalar extension" step of Newman's paper: it reduces the whole question to an
algebraically closed base field, over which every cocommutative coalgebra is pointed.

Unlike the base-change reductions for Takeuchi's correspondence of commutative Hopf algebras
(`Hopf/Commutative/AugSpanBaseChange.lean`), nothing here requires `H` or `K` to be
commutative: the statement is about the `k`-submodule `balRel K` of `H ⊗ H`, not about a tensor
product over the possibly noncommutative ring `K`, so no flatness API over noncommutative rings
is needed.

## Main results

* `HopfAlgebra.Cocommutative.one_tmul_injective` — `m ↦ 1 ⊗ m` is injective on a `k`-module, for any
  field extension `L / k`;
* `HopfAlgebra.Cocommutative.mem_of_one_tmul_mem_baseChange` — `1 ⊗ h ∈ L ⊗ K` forces `h ∈ K`;
* `HopfAlgebra.Cocommutative.bcRel` — the comparison map `H ⊗_k H → (L ⊗ H) ⊗_L (L ⊗ H)`, and
  `HopfAlgebra.Cocommutative.bcRel_balRel_mem` — it carries `balRel K` into `balRel (L ⊗ K)`;
* `HopfAlgebra.Cocommutative.descent_of_baseChange` — **descent descends along `k ⊆ L`**.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

universe u

namespace HopfAlgebra.Cocommutative

section BaseChange

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- For a field extension `L / k` and a `k`-module `M`, the map `m ↦ 1 ⊗ m` is injective. -/
theorem one_tmul_injective (M : Type u) [AddCommGroup M] [Module k M] :
    Function.Injective (fun m : M => (1 : L) ⊗ₜ[k] m) := by
  have halg : Function.Injective (Algebra.linearMap k L) := fun a b hab =>
    (algebraMap k L).injective (by simpa using hab)
  have hinj : Function.Injective (LinearMap.rTensor M (Algebra.linearMap k L)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ halg
  intro m₁ m₂ h
  have h' : LinearMap.rTensor M (Algebra.linearMap k L) ((1 : k) ⊗ₜ[k] m₁)
      = LinearMap.rTensor M (Algebra.linearMap k L) ((1 : k) ⊗ₜ[k] m₂) := by
    simpa using h
  have := hinj h'
  simpa using congrArg (TensorProduct.lid k M) this

variable {k L}
variable {H : Type u} [Ring H] [HopfAlgebra k H]

/-- An element of `H` whose image `1 ⊗ h` lies in the base change of a submodule `K` already
lies in `K`. -/
theorem mem_of_one_tmul_mem_baseChange (K : Submodule k H) {h : H}
    (hh : (1 : L) ⊗ₜ[k] h ∈ K.baseChange L) : h ∈ K := by
  set q : L ⊗[k] H →ₗ[L] L ⊗[k] (H ⧸ K) := LinearMap.baseChange L K.mkQ with hq
  have hker : K.baseChange L ≤ LinearMap.ker q := by
    rw [Submodule.baseChange_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    simp [hq, LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 ha]
  have h0 : q ((1 : L) ⊗ₜ[k] h) = 0 := hker hh
  rw [hq, LinearMap.baseChange_tmul] at h0
  have h1 : ((1 : L) ⊗ₜ[k] (K.mkQ h)) = ((1 : L) ⊗ₜ[k] (0 : H ⧸ K)) := by simpa using h0
  exact (Submodule.Quotient.mk_eq_zero _).1 (one_tmul_injective k L (H ⧸ K) h1)

/-- The `k`-linear comparison map `H ⊗_k H → (L ⊗ H) ⊗_L (L ⊗ H)`, `x ⊗ y ↦ (1 ⊗ x) ⊗ (1 ⊗ y)`. -/
noncomputable def bcRel : H ⊗[k] H →ₗ[k] (L ⊗[k] H) ⊗[L] (L ⊗[k] H) :=
  TensorProduct.lift <| LinearMap.mk₂ k (fun x y : H => ((1 : L) ⊗ₜ[k] x) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] y))
    (fun x₁ x₂ y => by simp [TensorProduct.tmul_add, TensorProduct.add_tmul])
    (fun c x y => by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rfl)
    (fun x y₁ y₂ => by simp [TensorProduct.tmul_add])
    (fun c x y => by
      rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul])

/-- `bcRel (x ⊗ y) = (1 ⊗ x) ⊗ (1 ⊗ y)`. -/
@[simp]
theorem bcRel_tmul (x y : H) :
    bcRel (k := k) (L := L) (x ⊗ₜ[k] y) = ((1 : L) ⊗ₜ[k] x) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] y) := rfl

/-- The comparison map carries the `K`-balanced relations into the `L ⊗ K`-balanced relations. -/
theorem bcRel_balRel_mem (K : Submodule k H) {t : H ⊗[k] H} (ht : t ∈ balRel K) :
    bcRel (L := L) t ∈ balRel (K.baseChange L) := by
  have hle : balRel K ≤ Submodule.comap (bcRel (L := L))
      (Submodule.restrictScalars k (balRel (K.baseChange L))) := by
    refine balRel_le fun x y a ha => ?_
    have hmem : ((1 : L) ⊗ₜ[k] a) ∈ K.baseChange L :=
      Submodule.tmul_mem_baseChange_of_mem _ ha
    have := sub_mem_balRel (k := L) (H := L ⊗[k] H) (K := K.baseChange L)
      ((1 : L) ⊗ₜ[k] x) ((1 : L) ⊗ₜ[k] y) hmem
    simpa [Submodule.mem_comap, bcRel_tmul, map_sub, Algebra.TensorProduct.tmul_mul_tmul] using this
  exact hle ht

/-- **Descent descends along a field extension.**  If an element of `L ⊗ H` that becomes balanced
in `(L ⊗ H) ⊗_{L ⊗ K} (L ⊗ H)` already lies in `L ⊗ K`, then the same holds for `K ⊆ H` over
`k`. -/
theorem descent_of_baseChange (K : Subalgebra k H)
    (hL : ∀ z : L ⊗[k] H,
      z ⊗ₜ[L] (1 : L ⊗[k] H) - (1 : L ⊗[k] H) ⊗ₜ[L] z ∈ balRel (K.toSubmodule.baseChange L) →
        z ∈ K.toSubmodule.baseChange L)
    {h : H} (hh : h ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] h ∈ balRel K.toSubmodule) : h ∈ K := by
  have hone : (1 : L ⊗[k] H) = (1 : L) ⊗ₜ[k] (1 : H) := rfl
  have himg := bcRel_balRel_mem (L := L) K.toSubmodule hh
  rw [map_sub, bcRel_tmul, bcRel_tmul, ← hone] at himg
  exact mem_of_one_tmul_mem_baseChange (L := L) K.toSubmodule (hL _ himg)

variable [IsCocomm k H]

end BaseChange

end HopfAlgebra.Cocommutative
