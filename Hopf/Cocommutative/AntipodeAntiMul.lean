module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Hopf.Cocommutative.HopfBiIdeal

/-!
# The antipode is an anti-morphism of algebras

For an arbitrary Hopf algebra `H` over a commutative ring `k` the antipode satisfies

```
S (x * y) = S y * S x .
```

Mathlib lists this as future work in `Mathlib/RingTheory/HopfAlgebra/Basic.lean`, and the
project so far had it only for a *commutative* `H` (where it is the statement that `S` is an
algebra map, `HopfAlgebra.antipode_mul_distrib`).  Newman's correspondence lives on
cocommutative — typically noncommutative — Hopf algebras, where the anti-multiplicativity is the
identity relating the left bi-ideal `H K⁺` attached to a sub-Hopf algebra `K` with the right
bi-ideal `K⁺ H`.

The proof is the classical convolution argument, carried out in the convolution monoid of the
`k`-linear maps `H ⊗[k] H → H`: both `S ∘ m` and `m ∘ τ ∘ (S ⊗ S)` are inverse to the
multiplication `m` — the first on the right, the second on the left — hence they agree.

## Main results

* `HopfAlgebra.Cocommutative.antipode_mul`: `S (x * y) = S y * S x`;
* `HopfAlgebra.Cocommutative.antipode_comp_mul`: the same identity as an equality of linear maps
  `H ⊗ H → H`;
* `HopfAlgebra.Cocommutative.antipode_antipode`: for a **cocommutative** `H` the antipode is
  involutive, `S ∘ S = id`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.5
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv

namespace HopfAlgebra.Cocommutative

section AntiMul

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

/-- A Sweedler representation of a product, obtained from representations of the two factors. -/
noncomputable def Repr.mul {x y : H} {ι κ : Type*} (r : Coalgebra.Repr k x ι)
    (s : Coalgebra.Repr k y κ) : Coalgebra.Repr k (x * y) (ι × κ) where
  index := r.index ×ˢ s.index
  left p := r.left p.1 * s.left p.2
  right p := r.right p.1 * s.right p.2
  eq := by
    classical
    rw [Bialgebra.comul_mul, ← r.eq, ← s.eq, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (Algebra.TensorProduct.tmul_mul_tmul _ _ _ _).symm

/-- A Sweedler representation of `x ⊗ₜ y` in the tensor product coalgebra `H ⊗ H`. -/
noncomputable def Repr.tmul {x y : H} {ι κ : Type*} (r : Coalgebra.Repr k x ι)
    (s : Coalgebra.Repr k y κ) : Coalgebra.Repr k (x ⊗ₜ[k] y) (ι × κ) where
  index := r.index ×ˢ s.index
  left p := r.left p.1 ⊗ₜ[k] s.left p.2
  right p := r.right p.1 ⊗ₜ[k] s.right p.2
  eq := by
    classical
    have hx := r.eq
    have hy := s.eq
    conv_rhs => rw [TensorProduct.comul_tmul, ← hx, ← hy, TensorProduct.sum_tmul, map_sum]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by simp

variable (k H) in
/-- The multiplication `m : H ⊗ H → H` as an element of the convolution monoid. -/
noncomputable def convMulMap : WithConv ((H ⊗[k] H) →ₗ[k] H) := toConv (LinearMap.mul' k H)

variable (k H) in
/-- The map `x ⊗ y ↦ S (x y)` as an element of the convolution monoid. -/
noncomputable def convAntipodeMul : WithConv ((H ⊗[k] H) →ₗ[k] H) :=
  toConv ((antipode k : H →ₗ[k] H) ∘ₗ LinearMap.mul' k H)

variable (k H) in
/-- The map `x ⊗ y ↦ S y * S x` as an element of the convolution monoid. -/
noncomputable def convMulAntipodeSwap : WithConv ((H ⊗[k] H) →ₗ[k] H) :=
  toConv (LinearMap.mul' k H ∘ₗ (TensorProduct.comm k H H).toLinearMap ∘ₗ
    TensorProduct.map (antipode k) (antipode k))

/-- `convMulMap k H` sends `x ⊗ y` to `x * y`. -/
@[simp] lemma convMulMap_apply (x y : H) :
    (convMulMap k H).ofConv (x ⊗ₜ[k] y) = x * y := by simp [convMulMap]

/-- `convAntipodeMul k H` sends `x ⊗ y` to `S (x * y)`. -/
@[simp] lemma convAntipodeMul_apply (x y : H) :
    (convAntipodeMul k H).ofConv (x ⊗ₜ[k] y) = antipode k (x * y) := by simp [convAntipodeMul]

/-- `convMulAntipodeSwap k H` sends `x ⊗ y` to `S y * S x`. -/
@[simp] lemma convMulAntipodeSwap_apply (x y : H) :
    (convMulAntipodeSwap k H).ofConv (x ⊗ₜ[k] y) = antipode k y * antipode k x := by
  simp [convMulAntipodeSwap]

/-- `m ⋆ (S ∘ m) = 1` in the convolution monoid of `H ⊗ H → H`. -/
lemma convMulMap_convMul_convAntipodeMul :
    convMulMap k H * convAntipodeMul k H = 1 := by
  classical
  apply toConv_injective
  ext x y
  have h := (Repr.tmul (ℛ k x) (ℛ k y)).convMul_apply (convMulMap k H) (convAntipodeMul k H)
  simp only [Repr.tmul, convMulMap_apply, convAntipodeMul_apply] at h
  have h2 : ∑ p ∈ (ℛ k x).index ×ˢ (ℛ k y).index,
      ((ℛ k x).left p.1 * (ℛ k y).left p.2) *
        antipode k ((ℛ k x).right p.1 * (ℛ k y).right p.2)
      = (counit (R := k) (x * y)) • (1 : H) :=
    HopfAlgebra.sum_mul_antipode_eq_smul (Repr.mul (ℛ k x) (ℛ k y))
  simpa [Bialgebra.counit_mul, Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    using h.trans h2

/-- `(m ∘ τ ∘ (S ⊗ S)) ⋆ m = 1` in the convolution monoid of `H ⊗ H → H`. -/
lemma convMulAntipodeSwap_convMul_convMulMap :
    convMulAntipodeSwap k H * convMulMap k H = 1 := by
  classical
  apply toConv_injective
  ext x y
  have h := (Repr.tmul (ℛ k x) (ℛ k y)).convMul_apply (convMulAntipodeSwap k H) (convMulMap k H)
  simp only [Repr.tmul, convMulMap_apply, convMulAntipodeSwap_apply] at h
  have hstep : ∑ p ∈ (ℛ k x).index ×ˢ (ℛ k y).index,
      (antipode k ((ℛ k y).left p.2) * antipode k ((ℛ k x).left p.1)) *
        ((ℛ k x).right p.1 * (ℛ k y).right p.2)
      = ((counit (R := k) x) * (counit (R := k) y)) • (1 : H) := by
    rw [Finset.sum_product_right]
    have hinner : ∀ j ∈ (ℛ k y).index,
        ∑ i ∈ (ℛ k x).index,
          (antipode k ((ℛ k y).left j) * antipode k ((ℛ k x).left i)) *
            ((ℛ k x).right i * (ℛ k y).right j)
          = (counit (R := k) x) •
              (antipode k ((ℛ k y).left j) * (ℛ k y).right j) := by
      intro j _
      have : ∀ i ∈ (ℛ k x).index,
          (antipode k ((ℛ k y).left j) * antipode k ((ℛ k x).left i)) *
              ((ℛ k x).right i * (ℛ k y).right j)
            = antipode k ((ℛ k y).left j) *
                ((antipode k ((ℛ k x).left i) * (ℛ k x).right i) * (ℛ k y).right j) := by
        intro i _; simp [mul_assoc]
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Finset.sum_mul,
        HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k x)]
      simp
    rw [Finset.sum_congr rfl hinner, ← Finset.smul_sum,
      HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k y), smul_smul]
  simpa [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm] using h.trans hstep

/-- **The antipode is an anti-morphism of algebras**, as an identity of linear maps
`H ⊗ H → H`. -/
theorem antipode_comp_mul :
    (antipode k : H →ₗ[k] H) ∘ₗ LinearMap.mul' k H
      = LinearMap.mul' k H ∘ₗ (TensorProduct.comm k H H).toLinearMap ∘ₗ
        TensorProduct.map (antipode k) (antipode k) := by
  have h : convAntipodeMul k H = convMulAntipodeSwap k H :=
    (left_inv_eq_right_inv (a := convMulMap k H) convMulAntipodeSwap_convMul_convMulMap
      convMulMap_convMul_convAntipodeMul).symm
  exact congr(WithConv.ofConv $h)

/-- **The antipode is an anti-morphism of algebras**: `S (x * y) = S y * S x`, for an arbitrary
Hopf algebra over a commutative ring. -/
theorem antipode_mul (x y : H) :
    antipode k (x * y) = antipode k y * antipode k x := by
  have := congr($(antipode_comp_mul (k := k) (H := H)) (x ⊗ₜ[k] y))
  simpa using this

end AntiMul

/-! ### The antipode of a cocommutative Hopf algebra is involutive -/

section Involutive

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

/-- The Sweedler representation with the two legs exchanged; available because `H` is
cocommutative. -/
noncomputable def Repr.swap {x : H} {ι : Type*} (r : Coalgebra.Repr k x ι) :
    Coalgebra.Repr k x ι where
  index := r.index
  left := r.right
  right := r.left
  eq := by
    have hcomm := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := H)) x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hcomm
    rw [← hcomm, ← r.eq, map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl

/-- `∑ x₍₂₎ S(x₍₁₎) = ε(x) 1` for a cocommutative Hopf algebra. -/
lemma sum_right_mul_antipode_left {x : H} {ι : Type*} (r : Coalgebra.Repr k x ι) :
    ∑ i ∈ r.index, r.right i * antipode k (r.left i) = (counit (R := k) x) • (1 : H) :=
  HopfAlgebra.sum_mul_antipode_eq_smul (Repr.swap r)

/-- **The antipode of a cocommutative Hopf algebra is involutive**: `S (S x) = x`. -/
theorem antipode_antipode (x : H) : antipode k (antipode k x) = x := by
  have hAId : toConv (antipode k : H →ₗ[k] H) * toConv (LinearMap.id (R := k) (M := H)) = 1 := by
    apply toConv_injective
    ext y
    rw [(ℛ k y).convMul_apply]
    simpa [Algebra.algebraMap_eq_smul_one] using HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k y)
  have hA2A : toConv ((antipode k : H →ₗ[k] H) ∘ₗ (antipode k : H →ₗ[k] H)) *
      toConv (antipode k : H →ₗ[k] H) = 1 := by
    apply toConv_injective
    ext y
    rw [(ℛ k y).convMul_apply]
    have hstep : ∀ i ∈ (ℛ k y).index,
        (antipode k (antipode k ((ℛ k y).left i))) * antipode k ((ℛ k y).right i)
          = antipode k ((ℛ k y).right i * antipode k ((ℛ k y).left i)) := by
      intro i _
      rw [antipode_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [Finset.sum_congr rfl hstep, ← map_sum, sum_right_mul_antipode_left (ℛ k y)]
    simp [Algebra.algebraMap_eq_smul_one]
  have h : toConv ((antipode k : H →ₗ[k] H) ∘ₗ (antipode k : H →ₗ[k] H))
      = toConv (LinearMap.id (R := k) (M := H)) :=
    left_inv_eq_right_inv hA2A hAId
  have := congr($(congrArg WithConv.ofConv h) x)
  simpa using this

end Involutive

/-! ### The antipode exchanges the left and the right bi-ideal of a sub-Hopf algebra -/

section TauRight

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

end TauRight

end HopfAlgebra.Cocommutative
