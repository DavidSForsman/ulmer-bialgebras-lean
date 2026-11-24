module

public import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# The Galois map of a Hopf algebra

For a Hopf algebra `B` over a commutative ring `k`, the *Galois map* is the `k`-linear
map
```
β : B ⊗[k] B → B ⊗[k] B,   b ⊗ c ↦ ∑ b * c₍₁₎ ⊗ c₍₂₎
```
(in Sweedler notation).  Geometrically, if `B = k[F]` for an affine group scheme `F`, then `β` is
the comorphism of the isomorphism `F × F ≅ F × F`, `(f, g) ↦ (f, f⁻¹g)` — the map expressing that
the action of `F` on itself by translation is simply transitive.

The main result of this file is that `β` is bijective, with inverse
```
γ : B ⊗[k] B → B ⊗[k] B,   b ⊗ c ↦ ∑ b * S(c₍₁₎) ⊗ c₍₂₎,
```
where `S` is the antipode; this is `HopfAlgebra.galoisEquiv`.

This is the algebraic heart of the "nilpotent" half of the proof of Takeuchi's faithful flatness
theorem ([waterhouseIntroductionAffineGroup1979], Section 14.2): the isomorphism
`B ⊗_A B ≅ B ⊗_k (B/A⁺B)` used there is induced by `β`.

## Main results

* `HopfAlgebra.galoisMap`: the Galois map `b ⊗ c ↦ ∑ b * c₍₁₎ ⊗ c₍₂₎` on `B ⊗[k] B`.
* `HopfAlgebra.galoisInvMap`: the map `b ⊗ c ↦ ∑ b * S(c₍₁₎) ⊗ c₍₂₎` on `B ⊗[k] B`.
* `HopfAlgebra.galoisEquiv`: the Galois map as a `k`-linear equivalence, with inverse
  `galoisInvMap`.

## References

* [S. U. Chase, M. E. Sweedler, *Hopf Algebras and Galois Theory*][chaseHopfAlgebrasGalois1969]
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972]
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Chapter 14
-/

@[expose] public section

section
namespace HopfAlgebra

open TensorProduct Coalgebra

variable (k B : Type*) [CommRing k] [Ring B] [HopfAlgebra k B]

/-- The Galois map `β : B ⊗[k] B → B ⊗[k] B`, `b ⊗ c ↦ ∑ b * c₍₁₎ ⊗ c₍₂₎`. -/
noncomputable def galoisMap : B ⊗[k] B →ₗ[k] B ⊗[k] B :=
  (LinearMap.mul' k B).rTensor B ∘ₗ (TensorProduct.assoc k B B B).symm.toLinearMap ∘ₗ
    (Coalgebra.comul (R := k) (A := B)).lTensor B

/-- The candidate inverse `γ : B ⊗[k] B → B ⊗[k] B`, `b ⊗ c ↦ ∑ b * S(c₍₁₎) ⊗ c₍₂₎`. -/
noncomputable def galoisInvMap : B ⊗[k] B →ₗ[k] B ⊗[k] B :=
  (LinearMap.mul' k B).rTensor B ∘ₗ (TensorProduct.assoc k B B B).symm.toLinearMap ∘ₗ
    (((HopfAlgebra.antipode k (A := B)).rTensor B) ∘ₗ Coalgebra.comul (R := k) (A := B)).lTensor B

variable {k B}

/-- On a Sweedler representation of `c`: `β (b ⊗ c) = ∑ b c₍₁₎ ⊗ c₍₂₎`. -/
@[simp] lemma galoisMap_tmul (b c : B) {ι : Type*} (r : Coalgebra.Repr k c ι) :
    galoisMap k B (b ⊗ₜ c) = ∑ i ∈ r.index, (b * r.left i) ⊗ₜ[k] r.right i := by
  simp [galoisMap, ← r.eq, TensorProduct.tmul_sum]

/-- On a Sweedler representation of `c`: `γ (b ⊗ c) = ∑ b S(c₍₁₎) ⊗ c₍₂₎`. -/
@[simp] lemma galoisInvMap_tmul (b c : B) {ι : Type*} (r : Coalgebra.Repr k c ι) :
    galoisInvMap k B (b ⊗ₜ c) = ∑ i ∈ r.index, (b * antipode k (r.left i)) ⊗ₜ[k] r.right i := by
  simp [galoisInvMap, ← r.eq, TensorProduct.tmul_sum, map_sum]

/-- `β (γ (b ⊗ c)) = b ⊗ c`. -/
lemma galoisMap_galoisInvMap_tmul (b c : B) :
    galoisMap k B (galoisInvMap k B (b ⊗ₜ[k] c)) = b ⊗ₜ[k] c := by
  classical
  set r := ℛ k c with hr
  set a₁ : (i : B × B) → Coalgebra.Repr k (r.left i) (B × B) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : B × B) → Coalgebra.Repr k (r.right i) (B × B) := fun i => ℛ k (r.right i) with ha2
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  set f2 : B ⊗[k] B →ₗ[k] B :=
    TensorProduct.lift ((LinearMap.mul k B) ∘ₗ (LinearMap.mulLeft k b) ∘ₗ (antipode k (A := B)))
      with hf2
  set φ : B ⊗[k] (B ⊗[k] B) →ₗ[k] B ⊗[k] B :=
    (f2.rTensor B) ∘ₗ (TensorProduct.assoc k B B B).symm.toLinearMap with hφ
  have hφapp : ∀ x y z : B, φ (x ⊗ₜ[k] (y ⊗ₜ[k] z)) = (b * antipode k x * y) ⊗ₜ[k] z := by
    intro x y z; simp [hφ, hf2]
  apply_fun φ at key
  simp only [map_sum, hφapp] at key
  rw [galoisInvMap_tmul b c r, map_sum]
  have expand_right : ∀ i ∈ r.index, galoisMap k B ((b * antipode k (r.left i)) ⊗ₜ[k] r.right i)
      = ∑ j ∈ (a₂ i).index, (b * antipode k (r.left i) * (a₂ i).left j) ⊗ₜ[k] (a₂ i).right j :=
    fun i _ => galoisMap_tmul _ _ (a₂ i)
  rw [Finset.sum_congr rfl expand_right, ← key]
  have cancel_left : ∀ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      (b * antipode k ((a₁ i).left j) * (a₁ i).right j) ⊗ₜ[k] r.right i
      = b ⊗ₜ[k] ((Coalgebra.counit (R := k) (r.left i)) • r.right i) := by
    intro i _
    simp only [mul_assoc]
    rw [← TensorProduct.sum_tmul, ← Finset.mul_sum,
      HopfAlgebra.sum_antipode_mul_eq_smul (a₁ i)]
    simp [TensorProduct.smul_tmul']
  rw [Finset.sum_congr rfl cancel_left, ← TensorProduct.tmul_sum, Coalgebra.sum_counit_smul r]

/-- `γ (β (b ⊗ c)) = b ⊗ c`. -/
lemma galoisInvMap_galoisMap_tmul (b c : B) :
    galoisInvMap k B (galoisMap k B (b ⊗ₜ[k] c)) = b ⊗ₜ[k] c := by
  classical
  set r := ℛ k c with hr
  set a₁ : (i : B × B) → Coalgebra.Repr k (r.left i) (B × B) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : B × B) → Coalgebra.Repr k (r.right i) (B × B) := fun i => ℛ k (r.right i) with ha2
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  set f2 : B ⊗[k] B →ₗ[k] B :=
    TensorProduct.lift ((((LinearMap.mul k B) ∘ₗ (LinearMap.mulLeft k b)).compl₂
      (antipode k (A := B)))) with hf2
  set φ : B ⊗[k] (B ⊗[k] B) →ₗ[k] B ⊗[k] B :=
    (f2.rTensor B) ∘ₗ (TensorProduct.assoc k B B B).symm.toLinearMap with hφ
  have hφapp : ∀ x y z : B, φ (x ⊗ₜ[k] (y ⊗ₜ[k] z)) = (b * x * antipode k y) ⊗ₜ[k] z := by
    intro x y z; simp [hφ, hf2, mul_assoc]
  apply_fun φ at key
  simp only [map_sum, hφapp] at key
  rw [galoisMap_tmul b c r, map_sum]
  have expand_right : ∀ i ∈ r.index, galoisInvMap k B ((b * r.left i) ⊗ₜ[k] r.right i)
      = ∑ j ∈ (a₂ i).index, (b * r.left i * antipode k ((a₂ i).left j)) ⊗ₜ[k] (a₂ i).right j :=
    fun i _ => galoisInvMap_tmul _ _ (a₂ i)
  rw [Finset.sum_congr rfl expand_right, ← key]
  have cancel_left : ∀ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      (b * (a₁ i).left j * antipode k ((a₁ i).right j)) ⊗ₜ[k] r.right i
      = b ⊗ₜ[k] ((Coalgebra.counit (R := k) (r.left i)) • r.right i) := by
    intro i _
    simp only [mul_assoc]
    rw [← TensorProduct.sum_tmul, ← Finset.mul_sum,
      HopfAlgebra.sum_mul_antipode_eq_smul (a₁ i)]
    simp [TensorProduct.smul_tmul']
  rw [Finset.sum_congr rfl cancel_left, ← TensorProduct.tmul_sum, Coalgebra.sum_counit_smul r]

/-- `β ∘ γ = id`. -/
lemma galoisMap_comp_galoisInvMap :
    (galoisMap k B) ∘ₗ (galoisInvMap k B) = LinearMap.id := by
  ext b c
  simpa using galoisMap_galoisInvMap_tmul (k := k) b c

/-- `γ ∘ β = id`. -/
lemma galoisInvMap_comp_galoisMap :
    (galoisInvMap k B) ∘ₗ (galoisMap k B) = LinearMap.id := by
  ext b c
  simpa using galoisInvMap_galoisMap_tmul (k := k) b c

variable (k B)

/-- **The Galois map of a Hopf algebra is bijective.**  For a Hopf algebra `B` over `k`, the map
`β : B ⊗[k] B ≃ₗ[k] B ⊗[k] B`, `b ⊗ c ↦ ∑ b * c₍₁₎ ⊗ c₍₂₎`, is a linear isomorphism, with inverse
`b ⊗ c ↦ ∑ b * S(c₍₁₎) ⊗ c₍₂₎`. -/
noncomputable def galoisEquiv : B ⊗[k] B ≃ₗ[k] B ⊗[k] B where
  __ := galoisMap k B
  invFun := galoisInvMap k B
  left_inv x := by
    have := galoisInvMap_comp_galoisMap (k := k) (B := B)
    exact congr($this x)
  right_inv x := by
    have := galoisMap_comp_galoisInvMap (k := k) (B := B)
    exact congr($this x)

variable {k B}

end HopfAlgebra
end
