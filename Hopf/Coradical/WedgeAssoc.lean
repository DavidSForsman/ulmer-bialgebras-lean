module

public import Hopf.Coradical.Irreducible

/-!
# Associativity of the wedge product

The wedge product `X ∧ Y = Δ⁻¹ (X ⊗ C + C ⊗ Y)` of two subspaces of a coalgebra is associative:
both `(X ∧ Y) ∧ Z` and `X ∧ (Y ∧ Z)` are the kernel of

```
C --Δ₂--> C ⊗ C ⊗ C --π_X ⊗ π_Y ⊗ π_Z--> (C/X) ⊗ (C/Y) ⊗ (C/Z),
```

by coassociativity. The key observation is that in a tensor product one may replace a factor
`π_W : C → C/W` by any linear map with kernel `W` (`Coalgebra.Coradical.ker_map_left_eq`,
`Coalgebra.Coradical.ker_map_right_eq`), because over a field the tensor product of an injection
with the identity is injective.

The consequence used later is the additivity of the wedge powers,
`X^{∧(m+n+1)} = X^{∧m} ∧ X^{∧n}` (`Coalgebra.Coradical.wedgePow_add`).

## Main results

* `Coalgebra.Coradical.ker_map_left_eq`, `Coalgebra.Coradical.ker_map_right_eq`: over a field,
  `ker (f ⊗ g) = ker (π ⊗ g)` (resp. `ker (g ⊗ f) = ker (g ⊗ π)`), where `π` is the projection
  onto the quotient by `ker f`.
* `Coalgebra.Coradical.wedge_assoc`: `wedge (wedge X Y) Z = wedge X (wedge Y Z)`.
* `Coalgebra.Coradical.wedgePow_add`:
  `wedgePow X (m + n + 1) = wedge (wedgePow X m) (wedgePow X n)`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

open TensorProduct
open TensorProduct (assoc)
open Coalgebra

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

/-- In a tensor product, a linear map may be replaced by the projection onto the quotient by its
kernel without changing the kernel of the induced map (left-hand factor). -/
theorem ker_map_left_eq {V U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup U]
    [Module k U] (f : C →ₗ[k] V) (g : C →ₗ[k] U) :
    LinearMap.ker (map f g)
      = LinearMap.ker (map (LinearMap.ker f).mkQ g) := by
  set W := LinearMap.ker f with hW
  set ι : (C ⧸ W) →ₗ[k] V := W.liftQ f le_rfl with hι
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfac : f = ι ∘ₗ W.mkQ := by ext x; simp [hι]
  have hsplit : map f g
      = map ι LinearMap.id ∘ₗ map W.mkQ g := by
    rw [hfac, ← TensorProduct.map_comp]; simp
  have hinj2 : Function.Injective (map ι (LinearMap.id : U →ₗ[k] U)) := by
    have he : map ι (LinearMap.id : U →ₗ[k] U) = LinearMap.rTensor U ι := by
      ext; simp [LinearMap.rTensor]
    rw [he]; exact Module.Flat.rTensor_preserves_injective_linearMap ι hinj
  rw [hsplit, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj2, Submodule.comap_bot]

/-- In a tensor product, a linear map may be replaced by the projection onto the quotient by its
kernel without changing the kernel of the induced map (right-hand factor). -/
theorem ker_map_right_eq {V U : Type u} [AddCommGroup V] [Module k V] [AddCommGroup U]
    [Module k U] (g : C →ₗ[k] U) (f : C →ₗ[k] V) :
    LinearMap.ker (map g f)
      = LinearMap.ker (map g (LinearMap.ker f).mkQ) := by
  set W := LinearMap.ker f with hW
  set ι : (C ⧸ W) →ₗ[k] V := W.liftQ f le_rfl with hι
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  have hfac : f = ι ∘ₗ W.mkQ := by ext x; simp [hι]
  have hsplit : map g f
      = map LinearMap.id ι ∘ₗ map g W.mkQ := by
    rw [hfac, ← TensorProduct.map_comp]; simp
  have hinj2 : Function.Injective (map (LinearMap.id : U →ₗ[k] U) ι) := by
    have he : map (LinearMap.id : U →ₗ[k] U) ι = LinearMap.lTensor U ι := by
      ext; simp [LinearMap.lTensor]
    rw [he]; exact Module.Flat.lTensor_preserves_injective_linearMap ι hinj
  rw [hsplit, LinearMap.ker_comp, LinearMap.ker_eq_bot.2 hinj2, Submodule.comap_bot]

variable [Coalgebra k C]

/-- **The wedge product is associative.** -/
theorem wedge_assoc (X Y Z : Submodule k C) :
    wedge (wedge X Y) Z = wedge X (wedge Y Z) := by
  -- Both sides are kernels of maps `C → C/X ⊗ C/Y ⊗ C/Z`: `G` through `(Δ ⊗ 1) Δ` and `G'`
  -- through `(1 ⊗ Δ) Δ`.
  set M := map (map X.mkQ Y.mkQ) Z.mkQ with hM
  set M' := map X.mkQ (map Y.mkQ Z.mkQ) with hM'
  set G := M ∘ₗ (LinearMap.rTensor C (comul : C →ₗ[k] C ⊗[k] C) ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
    with hG
  set G' := M' ∘ₗ (LinearMap.lTensor C (comul : C →ₗ[k] C ⊗[k] C) ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
    with hG'
  have hL : wedge (wedge X Y) Z = LinearMap.ker G := by
    have h1 : M ∘ₗ LinearMap.rTensor C (comul : C →ₗ[k] C ⊗[k] C)
        = map
            (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
            Z.mkQ := by
      rw [hM]; ext a b; simp
    have h2 : LinearMap.ker (M ∘ₗ LinearMap.rTensor C (comul : C →ₗ[k] C ⊗[k] C))
        = LinearMap.ker (map (wedge X Y).mkQ Z.mkQ) := by
      rw [h1, ker_map_left_eq]; rfl
    rw [hG, ← LinearMap.comp_assoc, LinearMap.ker_comp, h2, wedge, LinearMap.ker_comp]
  have hR : wedge X (wedge Y Z) = LinearMap.ker G' := by
    have h1 : M' ∘ₗ LinearMap.lTensor C (comul : C →ₗ[k] C ⊗[k] C)
        = map X.mkQ
            (map Y.mkQ Z.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) := by
      rw [hM']; ext a b; simp
    have h2 : LinearMap.ker (M' ∘ₗ LinearMap.lTensor C (comul : C →ₗ[k] C ⊗[k] C))
        = LinearMap.ker (map X.mkQ (wedge Y Z).mkQ) := by
      rw [h1, ker_map_right_eq]; rfl
    rw [hG', ← LinearMap.comp_assoc, LinearMap.ker_comp, h2, wedge, LinearMap.ker_comp]
  -- By coassociativity, `G'` is `G` followed by the associator, an isomorphism.
  have hnat : M' ∘ₗ (assoc k C C C).toLinearMap
      = (assoc k (C ⧸ X) (C ⧸ Y) (C ⧸ Z)).toLinearMap ∘ₗ M := by
    rw [hM, hM']; ext a b c; simp
  have hGG : G' = (assoc k (C ⧸ X) (C ⧸ Y) (C ⧸ Z)).toLinearMap ∘ₗ G := by
    rw [hG', hG, ← Coalgebra.coassoc (R := k) (A := C), ← LinearMap.comp_assoc, hnat,
      LinearMap.comp_assoc]
  have hkerG :
      LinearMap.ker ((assoc k (C ⧸ X) (C ⧸ Y) (C ⧸ Z)).toLinearMap ∘ₗ G)
      = LinearMap.ker G := by
    exact LinearEquiv.ker_comp _ _
  rw [hL, hR, hGG, hkerG]

/-- The wedge powers of a subspace add up: `X^{∧(m+n+1)} = X^{∧m} ∧ X^{∧n}`.  (With the
convention `wedgePow X 0 = X` of this development.) -/
theorem wedgePow_add (X : Submodule k C) (m n : ℕ) :
    wedgePow X (m + n + 1) = wedge (wedgePow X m) (wedgePow X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : m + (n + 1) + 1 = (m + n + 1) + 1 := by ring
      rw [h, wedgePow_succ, ih, wedge_assoc]
      rfl

end Coalgebra.Coradical
