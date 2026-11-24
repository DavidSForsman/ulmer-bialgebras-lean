module

public import Hopf.Graded.SplitExists
public import Hopf.Graded.AssocGradedHopf
public import Hopf.Graded.FreeBasis
public import Hopf.Cocommutative.CoinvAntipode

/-!
# The associated graded Hopf algebra of the coradical filtration

Let `H` be a **cocommutative** Hopf algebra over a field `k` and let

```
Fₙ = (k · 1)^{∧ (n+1)} = Coalgebra.Coradical.oneFiltration k H n
```

be the coradical filtration of the irreducible component `H₁` of the unit. It is an algebra
filtration (`Coalgebra.Coradical.mul_wedgePow_le`), a coalgebra filtration
(`Coalgebra.Coradical.comul_wedgePow_le`), stable under the antipode (the antipode of a
cocommutative Hopf algebra is a coalgebra map,
`HopfAlgebra.Cocommutative.comul_comp_antipode_of_isCocomm`), and almost commutative
(`Coalgebra.Coradical.comm_oneFiltration_le`).

Consequently the filtration underlies a `HopfAlgebra.Graded.HopfSplit`, for any choice of splitting,
and the splitting can be chosen adapted to a prescribed subalgebra `A ∋ 1` of `H`
(`HopfAlgebra.Graded.Split.exists_adapted_of_counit`). The associated graded object is then a
*connected commutative Hopf algebra*, by `Hopf/Graded/AssocGradedHopf.lean`.

## Main result

* `HopfAlgebra.Graded.exists_hopfSplit_oneFiltration` — the coradical filtration of `H₁` underlies a
  `HopfAlgebra.Graded.HopfSplit` whose projections preserve `A`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1 and Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical

namespace HopfAlgebra.Graded

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- The antipode of a cocommutative Hopf algebra preserves the coradical filtration of the
irreducible component of the unit. -/
theorem antipode_oneFiltration_le (n : ℕ) :
    Submodule.map (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) (oneFiltration k H n)
      ≤ oneFiltration k H n := by
  have hcomul : TensorProduct.map (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)
      (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) ∘ₗ (comul : H →ₗ[k] H ⊗[k] H)
      = comul ∘ₗ (HopfAlgebra.antipode (R := k) : H →ₗ[k] H) :=
    (HopfAlgebra.Cocommutative.comul_comp_antipode_of_isCocomm (k := k) (H := H)).symm
  have hmap := map_wedgePow_le (f := (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)) hcomul
    (Submodule.span k {((1 : GroupLike k H) : H)}) n
  have hspan : Submodule.map (HopfAlgebra.antipode (R := k) : H →ₗ[k] H)
      (Submodule.span k {((1 : GroupLike k H) : H)})
      = Submodule.span k {((1 : GroupLike k H) : H)} := by
    rw [Submodule.map_span]
    simp [GroupLike.val_one]
  rw [hspan] at hmap
  exact hmap

/-- **The coradical filtration of the irreducible component of the unit underlies a split
filtered Hopf algebra structure**, with the splitting adapted to a prescribed subalgebra `A`. -/
theorem exists_hopfSplit_oneFiltration (A : Submodule k H) (h1A : (1 : H) ∈ A) :
    ∃ S : HopfSplit k H, S.F = oneFiltration k H ∧ ∀ n, ∀ a ∈ A, S.pr n a ∈ A := by
  -- `X = k · 1` is a multiplicatively closed subcoalgebra; its wedge powers are the filtration.
  have hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra
      (Submodule.span k {((1 : GroupLike k H) : H)}) :=
    isSubcoalgebra_span_groupLike (1 : GroupLike k H).2
  have hXmul : Submodule.span k {((1 : GroupLike k H) : H)}
      * Submodule.span k {((1 : GroupLike k H) : H)}
      ≤ Submodule.span k {((1 : GroupLike k H) : H)} := by
    rw [Submodule.span_mul_span]
    refine Submodule.span_le.2 ?_
    rintro x ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    simp [GroupLike.val_one]
  have hF0 : oneFiltration k H 0 = Submodule.span k {(1 : H)} := by
    simp [oneFiltration, GroupLike.val_one]
  have h1F : ∀ n, (1 : H) ∈ oneFiltration k H n := by
    intro n
    refine oneFiltration_monotone (Nat.zero_le n) ?_
    rw [hF0]
    exact Submodule.subset_span rfl
  -- A splitting adapted to `A` and to the counit; the axioms of a split filtered Hopf algebra
  -- are the wedge-power results for `X`.
  obtain ⟨T, hTF, hTA, hTe, _⟩ := Split.exists_adapted_of_counit (F := oneFiltration k H) (A := A)
    oneFiltration_monotone (counit : H →ₗ[k] k) 1 (by simp) hF0 h1F h1A
  refine ⟨{ toSplit := T
            F_zero := by rw [hTF]; exact hF0
            mul_mem := by
              intro m n
              rw [hTF]
              exact mul_wedgePow_le hX hXmul m n
            comul_mem := by
              intro n x hx
              rw [hTF] at hx ⊢
              exact comul_wedgePow_le hX n ⟨x, hx, rfl⟩
            antipode_mem := by
              intro n x hx
              rw [hTF] at hx ⊢
              exact antipode_oneFiltration_le n ⟨x, hx, rfl⟩
            counit_pr := by
              intro n hn x
              exact hTe n hn x
            commutator_mem := by
              intro m n x hx y hy
              rw [hTF] at hx hy ⊢
              exact comm_oneFiltration_le m n x hx y hy }, hTF, hTA⟩

end HopfAlgebra.Graded
