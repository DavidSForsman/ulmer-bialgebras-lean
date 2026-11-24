module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Hopf.Basic.CoalgebraReprMul
public import Hopf.Basic.AntipodeBialgHom

/-!
# The mixed Galois map of a morphism of commutative Hopf algebras

Let `j : K →ₐc[k] H` be a morphism of commutative Hopf algebras over a field `k`.  The *mixed
Galois map* is the `k`-linear map
```
β : K ⊗[k] H → K ⊗[k] H,   x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(x₍₂₎) y
```
(in Sweedler notation).  It is bijective, with inverse `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y`.

This is the computation underlying Takeuchi's Lemma 3.9 ([Takeuchi1972]), which identifies
`K ⊗_A H` with `(K / A⁺K) ⊗_k H` for a Hopf subalgebra `A ⊆ K`.

## Main results

* `HopfAlgebra.Commutative.mixedGalois`: the mixed Galois map `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(x₍₂₎) y` on
  `K ⊗[k] H`.
* `HopfAlgebra.Commutative.mixedGaloisInv_comp_mixedGalois`:
  `HopfAlgebra.Commutative.mixedGaloisInv` is a left inverse of `mixedGalois`.
* `HopfAlgebra.Commutative.mixedGalois_comp_mixedGaloisInv`: `mixedGaloisInv` is a right inverse of
  `mixedGalois`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Lemma 3.9
* [S. U. Chase, M. E. Sweedler, *Hopf Algebras and Galois Theory*][chaseHopfAlgebrasGalois1969]
-/

@[expose] public section

section
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k K H : Type*} [Field k] [CommRing K] [CommRing H] [HopfAlgebra k K] [HopfAlgebra k H]

variable (k K H) in
/-- The mixed Galois map `β : K ⊗[k] H → K ⊗[k] H`, `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(x₍₂₎) y`. -/
noncomputable def mixedGalois (j : K →ₐc[k] H) : K ⊗[k] H →ₗ[k] K ⊗[k] H :=
  (LinearMap.lTensor K ((LinearMap.mul' k H) ∘ₗ
      TensorProduct.map (j : K →ₗ[k] H) LinearMap.id)) ∘ₗ
    (TensorProduct.assoc k K K H).toLinearMap ∘ₗ
    (LinearMap.rTensor H (Coalgebra.comul (R := k) (A := K)))

variable (k K H) in
/-- The candidate inverse `γ : K ⊗[k] H → K ⊗[k] H`, `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y`. -/
noncomputable def mixedGaloisInv (j : K →ₐc[k] H) : K ⊗[k] H →ₗ[k] K ⊗[k] H :=
  (LinearMap.lTensor K ((LinearMap.mul' k H) ∘ₗ
      TensorProduct.map ((j : K →ₗ[k] H) ∘ₗ HopfAlgebra.antipode k) LinearMap.id)) ∘ₗ
    (TensorProduct.assoc k K K H).toLinearMap ∘ₗ
    (LinearMap.rTensor H (Coalgebra.comul (R := k) (A := K)))

variable (j : K →ₐc[k] H)

/-- `mixedGalois (x ⊗ y) = ∑ᵢ x₁ⁱ ⊗ j(x₂ⁱ) y` for any representation `Δ x = ∑ᵢ x₁ⁱ ⊗ x₂ⁱ`. -/
@[simp] lemma mixedGalois_tmul (x : K) (y : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    mixedGalois k K H j (x ⊗ₜ[k] y) = ∑ i ∈ r.index, r.left i ⊗ₜ[k] (j (r.right i) * y) := by
  simp [mixedGalois, ← r.eq, TensorProduct.sum_tmul, map_sum]

/-- `mixedGaloisInv (x ⊗ y) = ∑ᵢ x₁ⁱ ⊗ j(S x₂ⁱ) y` for any representation `Δ x = ∑ᵢ x₁ⁱ ⊗ x₂ⁱ`. -/
@[simp] lemma mixedGaloisInv_tmul (x : K) (y : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    mixedGaloisInv k K H j (x ⊗ₜ[k] y)
      = ∑ i ∈ r.index, r.left i ⊗ₜ[k] (j (antipode k (r.right i)) * y) := by
  simp [mixedGaloisInv, ← r.eq, TensorProduct.sum_tmul, map_sum]

/-- `mixedGaloisInv` is a left inverse of `mixedGalois` on pure tensors:
`γ (β (x ⊗ y)) = x ⊗ y`. -/
lemma mixedGaloisInv_mixedGalois_tmul (x : K) (y : H) :
    mixedGaloisInv k K H j (mixedGalois k K H j (x ⊗ₜ[k] y)) = x ⊗ₜ[k] y := by
  classical
  set r := ℛ k x with hr
  set a₁ : (i : K × K) → Coalgebra.Repr k (r.left i) (K × K) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : K × K) → Coalgebra.Repr k (r.right i) (K × K) := fun i => ℛ k (r.right i) with ha2
  -- coassociativity, `∑ x₁₁ ⊗ x₁₂ ⊗ x₂ = ∑ x₁ ⊗ x₂₁ ⊗ x₂₂`, mapped by
  -- `u ⊗ v ⊗ w ↦ u ⊗ S(v) w y`
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  set g : K ⊗[k] K →ₗ[k] H :=
    (LinearMap.mulRight k y) ∘ₗ (LinearMap.mul' k H) ∘ₗ
      TensorProduct.map ((j : K →ₗ[k] H) ∘ₗ HopfAlgebra.antipode k) (j : K →ₗ[k] H) with hg
  set φ : K ⊗[k] (K ⊗[k] K) →ₗ[k] K ⊗[k] H := LinearMap.lTensor K g with hφ
  have hφapp : ∀ u v w : K, φ (u ⊗ₜ[k] (v ⊗ₜ[k] w))
      = u ⊗ₜ[k] (j (antipode k v) * j w * y) := by
    intro u v w; simp [hφ, hg]
  apply_fun φ at key
  simp only [map_sum, hφapp] at key
  -- expand `γ (β (x ⊗ y)) = ∑ x₁₁ ⊗ S(x₁₂) x₂ y` and apply `key`
  rw [mixedGalois_tmul j x y r, map_sum]
  have h1 : ∀ i ∈ r.index, mixedGaloisInv k K H j (r.left i ⊗ₜ[k] (j (r.right i) * y))
      = ∑ l ∈ (a₁ i).index,
          (a₁ i).left l ⊗ₜ[k] (j (antipode k ((a₁ i).right l)) * (j (r.right i) * y)) :=
    fun i _ => mixedGaloisInv_tmul j _ _ (a₁ i)
  rw [Finset.sum_congr rfl h1]
  have h1' : ∀ i ∈ r.index, ∑ l ∈ (a₁ i).index,
      (a₁ i).left l ⊗ₜ[k] (j (antipode k ((a₁ i).right l)) * (j (r.right i) * y))
      = ∑ l ∈ (a₁ i).index,
          (a₁ i).left l ⊗ₜ[k] (j (antipode k ((a₁ i).right l)) * j (r.right i) * y) :=
    fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
  rw [Finset.sum_congr rfl h1', key]
  have h2 : ∀ i ∈ r.index, ∑ l ∈ (a₂ i).index,
      r.left i ⊗ₜ[k] (j (antipode k ((a₂ i).left l)) * j ((a₂ i).right l) * y)
      = ((Coalgebra.counit (R := k) (r.right i)) • r.left i) ⊗ₜ[k] y := by
    -- the antipode axiom `∑ S(x₂₁) x₂₂ = ε(x₂)`, then the counit axiom
    intro i _
    have hsum : ∑ l ∈ (a₂ i).index, j (antipode k ((a₂ i).left l)) * j ((a₂ i).right l) * y
        = j (∑ l ∈ (a₂ i).index, antipode k ((a₂ i).left l) * ((a₂ i).right l)) * y := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul]
    rw [← TensorProduct.tmul_sum, hsum, HopfAlgebra.sum_antipode_mul_eq_smul (a₂ i)]
    rw [map_smul, map_one, smul_mul_assoc, one_mul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  rw [Finset.sum_congr rfl h2, ← TensorProduct.sum_tmul, Coalgebra.sum_smul_counit r]

/-- `mixedGaloisInv` is a right inverse of `mixedGalois` on pure tensors:
`β (γ (x ⊗ y)) = x ⊗ y`. -/
lemma mixedGalois_mixedGaloisInv_tmul (x : K) (y : H) :
    mixedGalois k K H j (mixedGaloisInv k K H j (x ⊗ₜ[k] y)) = x ⊗ₜ[k] y := by
  classical
  set r := ℛ k x with hr
  set a₁ : (i : K × K) → Coalgebra.Repr k (r.left i) (K × K) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : K × K) → Coalgebra.Repr k (r.right i) (K × K) := fun i => ℛ k (r.right i) with ha2
  -- coassociativity, `∑ x₁₁ ⊗ x₁₂ ⊗ x₂ = ∑ x₁ ⊗ x₂₁ ⊗ x₂₂`, mapped by
  -- `u ⊗ v ⊗ w ↦ u ⊗ v S(w) y`
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  set g : K ⊗[k] K →ₗ[k] H :=
    (LinearMap.mulRight k y) ∘ₗ (LinearMap.mul' k H) ∘ₗ
      TensorProduct.map (j : K →ₗ[k] H) ((j : K →ₗ[k] H) ∘ₗ HopfAlgebra.antipode k) with hg
  set φ : K ⊗[k] (K ⊗[k] K) →ₗ[k] K ⊗[k] H := LinearMap.lTensor K g with hφ
  have hφapp : ∀ u v w : K, φ (u ⊗ₜ[k] (v ⊗ₜ[k] w))
      = u ⊗ₜ[k] (j v * j (antipode k w) * y) := by
    intro u v w; simp [hφ, hg]
  apply_fun φ at key
  simp only [map_sum, hφapp] at key
  -- expand `β (γ (x ⊗ y)) = ∑ x₁₁ ⊗ x₁₂ S(x₂) y` and apply `key`
  rw [mixedGaloisInv_tmul j x y r, map_sum]
  have h1 : ∀ i ∈ r.index,
      mixedGalois k K H j (r.left i ⊗ₜ[k] (j (antipode k (r.right i)) * y))
      = ∑ l ∈ (a₁ i).index,
          (a₁ i).left l ⊗ₜ[k] (j ((a₁ i).right l) * (j (antipode k (r.right i)) * y)) :=
    fun i _ => mixedGalois_tmul j _ _ (a₁ i)
  rw [Finset.sum_congr rfl h1]
  have h1' : ∀ i ∈ r.index, ∑ l ∈ (a₁ i).index,
      (a₁ i).left l ⊗ₜ[k] (j ((a₁ i).right l) * (j (antipode k (r.right i)) * y))
      = ∑ l ∈ (a₁ i).index,
          (a₁ i).left l ⊗ₜ[k] (j ((a₁ i).right l) * j (antipode k (r.right i)) * y) :=
    fun i _ => Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
  rw [Finset.sum_congr rfl h1', key]
  have h2 : ∀ i ∈ r.index, ∑ l ∈ (a₂ i).index,
      r.left i ⊗ₜ[k] (j ((a₂ i).left l) * j (antipode k ((a₂ i).right l)) * y)
      = ((Coalgebra.counit (R := k) (r.right i)) • r.left i) ⊗ₜ[k] y := by
    -- the antipode axiom `∑ x₂₁ S(x₂₂) = ε(x₂)`, then the counit axiom
    intro i _
    have hsum : ∑ l ∈ (a₂ i).index, j ((a₂ i).left l) * j (antipode k ((a₂ i).right l)) * y
        = j (∑ l ∈ (a₂ i).index, ((a₂ i).left l) * antipode k ((a₂ i).right l)) * y := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul]
    rw [← TensorProduct.tmul_sum, hsum, HopfAlgebra.sum_mul_antipode_eq_smul (a₂ i)]
    rw [map_smul, map_one, smul_mul_assoc, one_mul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
  rw [Finset.sum_congr rfl h2, ← TensorProduct.sum_tmul, Coalgebra.sum_smul_counit r]

/-- `mixedGaloisInv` is a left inverse of `mixedGalois`. -/
lemma mixedGaloisInv_comp_mixedGalois :
    (mixedGaloisInv k K H j) ∘ₗ (mixedGalois k K H j) = LinearMap.id := by
  ext x y
  simpa using mixedGaloisInv_mixedGalois_tmul j x y

/-- `mixedGaloisInv` is a right inverse of `mixedGalois`. -/
lemma mixedGalois_comp_mixedGaloisInv :
    (mixedGalois k K H j) ∘ₗ (mixedGaloisInv k K H j) = LinearMap.id := by
  ext x y
  simpa using mixedGalois_mixedGaloisInv_tmul j x y

end HopfAlgebra.Commutative
end
