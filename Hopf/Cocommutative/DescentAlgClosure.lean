module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Hopf.Cocommutative.DescentBaseChange
public import Hopf.Coradical.Pointed

/-!
# Reduction of Newman's descent input to a pointed Hopf algebra over an algebraically closed field

`Hopf/Cocommutative/DescentBaseChange.lean` shows that the descent input of Newman's closure
identity descends along a field extension `k ⊆ L`.  To turn that into a genuine reduction one
still has to know that the base change of the data is data of the same kind, namely that

* `L ⊗ K` is a **sub-Hopf algebra** of `L ⊗ H` (`HopfAlgebra.Cocommutative.isSubHopf_baseChange`),
  and
* `L ⊗ H` is again **cocommutative** (an instance in Mathlib).

This file supplies those two facts and assembles the reduction: to prove descent — hence Newman's
closure identity `μ (τ K) = K` — for every sub-Hopf algebra of every cocommutative Hopf algebra over
`k`, it suffices to prove it over an algebraic closure of `k`, where by
`Coalgebra.Coradical.isPointed_of_isAlgClosed` every cocommutative Hopf algebra is pointed. This is
the "simple scalar extension" step of Newman's paper.

## Main results

* `HopfAlgebra.Cocommutative.toSubmodule_baseChange` — the underlying submodule of `K.baseChange L`
  is `K.toSubmodule.baseChange L`;
* `HopfAlgebra.Cocommutative.comul_one_tmul`, `HopfAlgebra.Cocommutative.antipode_one_tmul` — the
  base-changed structure maps on elements `1 ⊗ a`;
* `HopfAlgebra.Cocommutative.isSubHopf_baseChange` — the base change of a sub-Hopf algebra is a
  sub-Hopf algebra;
* `HopfAlgebra.Cocommutative.Descent` — the descent input, as a predicate on a sub-Hopf algebra;
* `HopfAlgebra.Cocommutative.descent_of_descent_baseChange` — descent descends along `k ⊆ L`, stated
  with `HopfAlgebra.Cocommutative.Descent` on both sides;
* `HopfAlgebra.Cocommutative.descent_of_algebraicClosure` — the reduction to an algebraically closed
  base field (used for `HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq`).

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

universe u

namespace HopfAlgebra.Cocommutative

section BaseChange

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {H : Type u} [Ring H] [HopfAlgebra k H]

/-- The underlying `L`-submodule of the base change of a subalgebra is the base change of its
underlying `k`-submodule. -/
theorem toSubmodule_baseChange (K : Subalgebra k H) :
    Subalgebra.toSubmodule (K.baseChange L) = K.toSubmodule.baseChange L := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.inductionOn with
    | tmul b c => exact Submodule.tmul_mem_baseChange_of_mem _ c.2
    | add x y hx hy => simpa [map_add] using Submodule.add_mem _ hx hy
  · rw [Submodule.baseChange_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Subalgebra.tmul_mem_baseChange ha 1

/-- The comparison map `bcRel` is exactly the base-changed comultiplication on elements
`1 ⊗ a`. -/
theorem comul_one_tmul (a : H) :
    comul (R := L) ((1 : L) ⊗ₜ[k] a) = bcRel (L := L) (comul (R := k) a) := by
  have key : ∀ t : H ⊗[k] H,
      AlgebraTensorModule.tensorTensorTensorComm k L k L L L H H
        (((1 : L) ⊗ₜ[L] (1 : L)) ⊗ₜ[k] t) = bcRel (L := L) t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => simp [AlgebraTensorModule.tensorTensorTensorComm]
    | add x y hx hy => simp [TensorProduct.tmul_add, map_add, hx, hy]
  rw [TensorProduct.comul_tmul]
  exact key _

/-- The base-changed antipode on elements `1 ⊗ a`. -/
theorem antipode_one_tmul (a : H) :
    antipode L ((1 : L) ⊗ₜ[k] a) = (1 : L) ⊗ₜ[k] antipode k a := rfl

/-- **The base change of a sub-Hopf algebra is a sub-Hopf algebra.** -/
theorem isSubHopf_baseChange {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) :
    IsSubHopfAlgebra L (K.baseChange L) := by
  have hgen : Subalgebra.toSubmodule (K.baseChange L)
      = Submodule.span L ((fun a : H => (1 : L) ⊗ₜ[k] a) '' (K.toSubmodule : Set H)) := by
    rw [toSubmodule_baseChange, Submodule.baseChange_eq_span]
    congr 1
  constructor
  · intro x hx
    rw [← Subalgebra.mem_toSubmodule, hgen] at hx
    refine Submodule.span_induction ?_ (by simp) (fun y z _ _ hy hz => by
      simpa [map_add] using Submodule.add_mem _ hy hz)
      (fun c y _ hy => by simpa [map_smul] using Submodule.smul_mem _ c hy) hx
    rintro _ ⟨a, ha, rfl⟩
    rw [comul_one_tmul]
    -- `bcRel` carries `K ⊗ K` into `(L ⊗ K) ⊗_L (L ⊗ K)`
    have hcomul := hK.toIsSubBialg.comul_mem a ha
    rw [TensorProduct.range_mapIncl] at hcomul
    have hle : Submodule.map₂ (TensorProduct.mk k H H) K.toSubmodule K.toSubmodule ≤
        Submodule.comap (bcRel (L := L)) (Submodule.restrictScalars k
          (LinearMap.range (TensorProduct.mapIncl
            (Subalgebra.toSubmodule (K.baseChange L))
            (Subalgebra.toSubmodule (K.baseChange L))))) := by
      refine Submodule.map₂_le.2 fun x hx y hy => ?_
      have hx' : (1 : L) ⊗ₜ[k] x ∈ Subalgebra.toSubmodule (K.baseChange L) :=
        Subalgebra.tmul_mem_baseChange hx 1
      have hy' : (1 : L) ⊗ₜ[k] y ∈ Subalgebra.toSubmodule (K.baseChange L) :=
        Subalgebra.tmul_mem_baseChange hy 1
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, bcRel_tmul,
        Submodule.restrictScalars_mem, TensorProduct.range_mapIncl]
      exact Submodule.apply_mem_map₂ _ hx' hy'
    exact hle hcomul
  · intro x hx
    rw [← Subalgebra.mem_toSubmodule, hgen] at hx
    rw [← Subalgebra.mem_toSubmodule, hgen]
    refine Submodule.span_induction ?_ (by simp) (fun y z _ _ hy hz => by
      simpa [map_add] using Submodule.add_mem _ hy hz)
      (fun c y _ hy => by simpa [map_smul] using Submodule.smul_mem _ c hy) hx
    rintro _ ⟨a, ha, rfl⟩
    rw [antipode_one_tmul]
    exact Submodule.subset_span ⟨antipode k a, hK.antipode_mem a ha, rfl⟩

/-- The **descent input** for a subalgebra `K` of `H`: an element of `H` which becomes balanced
in `H ⊗_K H` already lies in `K`. -/
def Descent (k : Type u) [Field k] {H : Type u} [Ring H] [HopfAlgebra k H]
    (K : Subalgebra k H) : Prop :=
  ∀ h : H, h ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] h ∈ balRel K.toSubmodule → h ∈ K

/-- **Descent descends along a field extension.** -/
theorem descent_of_descent_baseChange (K : Subalgebra k H)
    (hL : Descent L (K.baseChange L)) : Descent k K := by
  intro h hh
  refine descent_of_baseChange (L := L) K (fun z hz => ?_) hh
  have hz' : z ⊗ₜ[L] (1 : L ⊗[k] H) - (1 : L ⊗[k] H) ⊗ₜ[L] z
      ∈ balRel (Subalgebra.toSubmodule (K.baseChange L)) := by
    rw [toSubmodule_baseChange]; exact hz
  have := hL z hz'
  rwa [← Subalgebra.mem_toSubmodule, toSubmodule_baseChange] at this

end BaseChange

section AlgClosure

variable {k : Type u} [Field k]
variable {H : Type u} [Ring H] [HopfAlgebra k H] [IsCocomm k H]

/-- **Reduction of the descent input to an algebraically closed base field.**  If descent holds
for every sub-Hopf algebra of every cocommutative Hopf algebra over an algebraically closed field,
then it holds over an arbitrary field.

Over an algebraically closed field every cocommutative coalgebra is pointed
(`Coalgebra.Coradical.isPointed_of_isAlgClosed`), so the hypothesis only concerns pointed
cocommutative Hopf algebras. -/
theorem descent_of_algebraicClosure
    (hAC : ∀ (k' H' : Type u) [Field k'] [IsAlgClosed k'] [Ring H'] [HopfAlgebra k' H']
      [IsCocomm k' H'] (K' : Subalgebra k' H'), IsSubHopfAlgebra k' K' → Descent k' K')
    {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) : Descent k K := by
  refine descent_of_descent_baseChange (L := AlgebraicClosure k) K ?_
  exact hAC (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] H) _ (isSubHopf_baseChange hK)

end AlgClosure

end HopfAlgebra.Cocommutative
