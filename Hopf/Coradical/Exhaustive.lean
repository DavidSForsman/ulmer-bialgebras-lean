module

public import Mathlib.RingTheory.Artinian.Ring
public import Hopf.Coradical.IdealCorrespondence

/-!
# Exhaustiveness of the coradical filtration (cocommutative case)

Let `k` be a field and `C` a finite-dimensional **cocommutative** `k`-coalgebra.  Then the dual
convolution algebra `C*` is a finite-dimensional *commutative* `k`-algebra, hence an Artinian
ring, and the annihilator correspondence of `Hopf/Coradical/IdealCorrespondence.lean`
identifies

* subcoalgebras of `C` with ideals of `C*`;
* simple subcoalgebras with maximal ideals;
* the wedge product with the product of ideals.

This file sets up the ideal-theoretic side of that correspondence.

## Main results

* `Coalgebra.Coradical.annIdeal`: the annihilator of a subcoalgebra, as an ideal of `C*`.
* `Coalgebra.Coradical.isTwoSided_restrictScalars`: for cocommutative `C`, every ideal of `C*` is
  two-sided.
* `Coalgebra.Coradical.isSimpleSubcoalgebra_coann_maximal`: for finite-dimensional cocommutative
  `C`, the subspace annihilated by a maximal ideal of `C*` is a simple subcoalgebra.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapters 8–9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Chapter 5
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

section Generic

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

end Generic

/-- The dual algebra of a finite-dimensional coalgebra is finite-dimensional. -/
noncomputable instance instFiniteDimensionalDualAlg [FiniteDimensional k C] :
    FiniteDimensional k (Coalgebra.Coradical.DualAlg k C) :=
  Module.Finite.equiv (WithConv.linearEquiv k (C →ₗ[k] k)).symm

section Cocomm

variable [IsCocomm k C]

/-- The annihilator of a subcoalgebra, as an ideal of the dual algebra. -/
noncomputable def annIdeal (W : Submodule k C) (hW : IsSubcoalgebra W) :
    Ideal (Coalgebra.Coradical.DualAlg k C) where
  carrier := (ann W : Set (Coalgebra.Coradical.DualAlg k C))
  add_mem' ha hb := (ann W).add_mem ha hb
  zero_mem' := (ann W).zero_mem
  smul_mem' a f hf := (isTwoSided_ann hW a f hf).1

omit [IsCocomm k C] in
/-- The ideal `annIdeal W` has underlying subspace `ann W`. -/
@[simp] theorem restrictScalars_annIdeal (W : Submodule k C) (hW : IsSubcoalgebra W) :
    Submodule.restrictScalars k (annIdeal W hW) = ann W := rfl

/-- For cocommutative `C`, every ideal of the (then commutative) dual algebra is two-sided. -/
theorem isTwoSided_restrictScalars (I : Ideal (Coalgebra.Coradical.DualAlg k C)) :
    IsTwoSided (Submodule.restrictScalars k I) :=
  fun a _ hf => ⟨I.mul_mem_left a hf, I.mul_mem_right a hf⟩

variable [FiniteDimensional k C]

/-- The dual algebra of a finite-dimensional coalgebra is an Artinian ring. -/
instance instIsArtinianRingDualAlg : IsArtinianRing (Coalgebra.Coradical.DualAlg k C) :=
  IsArtinianRing.of_finite k _

/-- The subspace of `C` annihilated by a maximal ideal of the dual algebra is a simple
subcoalgebra. -/
theorem isSimpleSubcoalgebra_coann_maximal (M : Ideal (Coalgebra.Coradical.DualAlg k C))
    (hM : M.IsMaximal) : IsSimpleSubcoalgebra (coann (Submodule.restrictScalars k M)) := by
  set N : Submodule k C := coann (Submodule.restrictScalars k M) with hN
  have hannN : ann N = Submodule.restrictScalars k M := ann_coann _
  have hsub : IsSubcoalgebra N :=
    isSubcoalgebra_of_isTwoSided_ann (hannN ▸ isTwoSided_restrictScalars M)
  have hne : N ≠ ⊥ := by
    intro h
    have : (Submodule.restrictScalars k M) = ⊤ := by rw [← hannN, h, ann_bot]
    exact hM.ne_top ((Submodule.restrictScalars_eq_top_iff _ _ _).1 this)
  refine ⟨hsub, hne, ?_⟩
  intro V hVN hV
  by_cases hV0 : V = ⊥
  · exact Or.inl hV0
  refine Or.inr ?_
  have hle : M ≤ annIdeal V hV := by
    intro f hf
    exact (hannN ▸ ann_antitone hVN) hf
  have hVtop : annIdeal V hV ≠ ⊤ := by
    intro h
    apply hV0
    have : ann V = ⊤ := by
      rw [← restrictScalars_annIdeal V hV, h, Submodule.restrictScalars_top]
    rw [← coann_ann V, this, coann_top]
  have : M = annIdeal V hV := hM.eq_of_le hVtop hle
  have : ann V = ann N := by
    rw [hannN, ← restrictScalars_annIdeal V hV, ← this]
  exact ann_injective this

end Cocomm

end Coalgebra.Coradical
