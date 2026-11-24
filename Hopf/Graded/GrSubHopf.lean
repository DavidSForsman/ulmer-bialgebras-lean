module

public import Hopf.Graded.GrSubGrading
public import Hopf.Basic.NormalHopfIdeal

/-!
# The associated graded subalgebra is a sub-Hopf algebra

If `A ⊆ H` is a sub-Hopf algebra which is preserved by the projections of a
`HopfAlgebra.Graded.HopfSplit`, then `gr A ⊆ S.Gr` is a sub-Hopf algebra of the associated graded
Hopf algebra.

## Main results

* `HopfAlgebra.Graded.HopfSplit.isSubHopfAlgebra_grSub`: if `A` (preserved by the projections and
  containing `1`) is stable under the comultiplication and the antipode, then `gr A` is a sub-Hopf
  algebra of `S.Gr`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] {S : HopfSplit k H}
  {A : Subalgebra k H} (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) (h1A : (1 : H) ∈ A)

/-- The degree-`n` component map, corestricted to `gr A`. -/
noncomputable def cmpToGrSub (n : ℕ) :
    ↥(Subalgebra.toSubmodule A) →ₗ[k] ↥(Subalgebra.toSubmodule (S.grSub A hprA h1A)) :=
  LinearMap.codRestrict _ ((S.cmp n) ∘ₗ (Subalgebra.toSubmodule A).subtype) (fun a => by
    rw [Subalgebra.mem_toSubmodule, grSub, Submodule.mem_toSubalgebra, mem_grSubmodule,
      LinearMap.comp_apply, S.emb_cmp]
    exact hprA n _ a.2)

/-- Composing `cmpToGrSub hprA h1A n` with the inclusion of `gr A` gives `cmp n` restricted
to `A`. -/
theorem subtype_comp_cmpToGrSub (n : ℕ) :
    (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype ∘ₗ cmpToGrSub hprA h1A n
      = (S.cmp n) ∘ₗ (Subalgebra.toSubmodule A).subtype := rfl

/-- For `w ∈ A ⊗ A`, applying `cmp i ⊗ cmp j` to the image of `w` in `H ⊗ H` lands in the
image of `gr A ⊗ gr A` in `S.Gr ⊗ S.Gr`. -/
theorem map_cmp_mem_range (i j : ℕ)
    (w : ↥(Subalgebra.toSubmodule A) ⊗[k] ↥(Subalgebra.toSubmodule A)) :
    TensorProduct.map (S.cmp i) (S.cmp j)
        (TensorProduct.map (Subalgebra.toSubmodule A).subtype
          (Subalgebra.toSubmodule A).subtype w)
      ∈ LinearMap.range (TensorProduct.map
          (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype
          (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype) := by
  refine ⟨TensorProduct.map (cmpToGrSub hprA h1A i) (cmpToGrSub hprA h1A j) w, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, subtype_comp_cmpToGrSub,
    subtype_comp_cmpToGrSub, ← LinearMap.comp_apply, ← TensorProduct.map_comp]

/-- `phi n` maps the image of `A ⊗ A` in `H ⊗ H` into the image of `gr A ⊗ gr A` in
`S.Gr ⊗ S.Gr`. -/
theorem phi_mem_range {n : ℕ} {z : H ⊗[k] H}
    (hz : z ∈ LinearMap.range (TensorProduct.map (Subalgebra.toSubmodule A).subtype
      (Subalgebra.toSubmodule A).subtype)) :
    S.phi n z ∈ LinearMap.range (TensorProduct.map
      (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype
      (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype) := by
  obtain ⟨w, rfl⟩ := hz
  rw [phi, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ => map_cmp_mem_range hprA h1A i (n - i) w

/-- **`gr A` is a sub-Hopf algebra of `S.Gr`.** -/
theorem isSubHopfAlgebra_grSub
    (hcomulA : ∀ a ∈ A, comul (R := k) a ∈ LinearMap.range (TensorProduct.map
      (Subalgebra.toSubmodule A).subtype (Subalgebra.toSubmodule A).subtype))
    (hantiA : ∀ a ∈ A, antipode k a ∈ A) :
    HopfAlgebra.IsSubHopfAlgebra k (S.grSub A hprA h1A) where
  comul_mem := by
    have key : ∀ (n : ℕ), ∀ x ∈ S.grAPiece A n, S.gcomul x ∈ LinearMap.range (TensorProduct.map
        (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype
        (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype) := by
      intro n x hx
      rw [eq_cmp_emb hx.1, S.gcomul_cmp (S.c_le_f n hx.1), S.dAux_apply]
      exact phi_mem_range hprA h1A (hcomulA _ hx.2)
    intro x hx
    have hx' : x ∈ ⨆ n, S.grAPiece A n := by
      rw [← grSubmodule_eq_iSup hprA]
      exact hx
    refine Submodule.iSup_induction
      (motive := fun x => S.gcomul x ∈ LinearMap.range (TensorProduct.map
        (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype
        (Subalgebra.toSubmodule (S.grSub A hprA h1A)).subtype)) _ hx' key ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  antipode_mem := by
    have key : ∀ (n : ℕ), ∀ x ∈ S.grAPiece A n, S.gantipode x ∈ S.grSubmodule A := by
      intro n x hx
      rw [eq_cmp_emb hx.1, S.gantipode_cmp (S.c_le_f n hx.1)]
      rw [mem_grSubmodule, S.emb_cmp]
      exact hprA n _ (hantiA _ hx.2)
    intro x hx
    have hx' : x ∈ ⨆ n, S.grAPiece A n := by
      rw [← grSubmodule_eq_iSup hprA]
      exact hx
    refine Submodule.iSup_induction
      (motive := fun x => S.gantipode x ∈ S.grSubmodule A) _ hx' key ?_ ?_
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro y z hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz

end HopfSplit

end HopfAlgebra.Graded
