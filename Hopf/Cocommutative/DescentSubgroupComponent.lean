module

public import Hopf.Coradical.IrrComponentSubalgebra
public import Hopf.Cocommutative.CoinvAntipode
public import Hopf.Cocommutative.GenerationGeneral

/-!
# Kostant components: the antipode and the decomposition as a linear isomorphism

Let `H` be a **pointed** cocommutative Hopf algebra over a field `k`, so that Kostant's
decomposition reads

```
H = ⨁_{g ∈ G(H)} H_g ,       H_g = glComponent g .
```

This file records two facts about this decomposition used by the descent arguments of
`Hopf/Cocommutative/DescentTranslates.lean` and `Hopf/Cocommutative/DescentFreeBasis.lean`
(projections onto sums of components indexed by a subgroup of `G(H)`).

## Main results

* `Coalgebra.Coradical.map_antipode_glComponent` — the antipode maps `H_d` into `H_{d⁻¹}`;
* `HopfAlgebra.Cocommutative.glEquiv` — Kostant's decomposition of a pointed `H` as a linear
  isomorphism `⨁_{g ∈ G(H)} H_g ≃ H`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.6
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra Coalgebra.Coradical

universe u

namespace Coalgebra.Coradical

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

variable [Coalgebra.IsCocomm k H]

/-- The antipode maps the component of a group-like element `d` into the component of `d⁻¹`. -/
theorem map_antipode_glComponent (d : GroupLike k H) :
    Submodule.map (antipode k : H →ₗ[k] H) (glComponent d) ≤ glComponent d⁻¹ := by
  have hcomul : _root_.TensorProduct.map (antipode k : H →ₗ[k] H) (antipode k : H →ₗ[k] H)
      ∘ₗ (comul : H →ₗ[k] H ⊗[k] H) = comul ∘ₗ (antipode k : H →ₗ[k] H) :=
    (HopfAlgebra.Cocommutative.comul_comp_antipode_of_isCocomm (k := k) (H := H)).symm
  refine le_trans (map_irrComponent_le hcomul _) (le_of_eq ?_)
  congr 1
  rw [Submodule.map_span]
  simp [GroupLike.val_inv]

end Coalgebra.Coradical

namespace HopfAlgebra.Cocommutative

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

section Proj

variable [DecidableEq (GroupLike k H)]

/-- Kostant's decomposition of a pointed Hopf algebra, as a linear isomorphism. -/
noncomputable def glEquiv (hpt : IsPointed k H) :
    DirectSum (GroupLike k H) (fun g => ↥(glComponent g)) ≃ₗ[k] H :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _) (isInternal_glComponent hpt)

end Proj

end HopfAlgebra.Cocommutative
