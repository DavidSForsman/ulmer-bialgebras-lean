module

public import AffineGroupSchemes.HopfEpiSurjectiveGen
public import Hopf.Basic.CoalgebraReprMul
public import Hopf.Basic.SubHopfAlgebra

/-!
# The difference morphism of a reflexive relation of affine group schemes

Let `H` and `R` be commutative Hopf algebras over a commutative von Neumann regular ring `k` (for
instance a field) and let `d₁, d₂ : H →ₐc[k] R` be two morphisms of Hopf algebras. Geometrically
`Spec R` is a subscheme of `Spec H × Spec H` and the two maps are the projections; the *difference
morphism* `(a, b) ↦ a⁻¹b` corresponds to the algebra map

```
p : H →ₐ[k] R,   x ↦ ∑ d₁(S x₍₁₎) d₂(x₍₂₎).
```

This file constructs `p` (`AffineGroupSchemes.Coexact.diffLin`,
`AffineGroupSchemes.Coexact.diffAlg`), proves the fundamental identity `∑ d₁(x₍₁₎) p(x₍₂₎) = d₂ x`
(`AffineGroupSchemes.Coexact.sum_d₁_mul_diff`), and shows that if `(d₁, d₂)` is jointly epimorphic
then the algebra map

```
ψ : H ⊗[k] H →ₐ[k] R,   x ⊗ y ↦ d₁ x · d₂ y
```

is surjective (`AffineGroupSchemes.Coexact.jointAlg_surjective`), by means of the fact that
epimorphisms of commutative Hopf algebras over a field are surjective
(`AffineGroupSchemes.HopfGen.Hopf.surjective_of_injective_of_epi`, in
`AffineGroupSchemes/HopfEpiSurjectiveGen.lean`).

## Main results

* `AffineGroupSchemes.Coexact.diffAlg`: the difference morphism `p : H →ₐ[k] R`,
  `x ↦ ∑ d₁(S x₍₁₎) d₂(x₍₂₎)`.
* `AffineGroupSchemes.Coexact.sum_d₁_mul_diff`: the identity `∑ d₁(x₍₁₎) p(x₍₂₎) = d₂ x`.
* `AffineGroupSchemes.Coexact.jointAlg_surjective`: if `(d₁, d₂)` is jointly epimorphic among
  commutative Hopf algebras, the map `H ⊗[k] H → R`, `x ⊗ y ↦ d₁ x · d₂ y`, is surjective.

## References

* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace AffineGroupSchemes

open HopfAlgebra
namespace Coexact

universe u

variable {k H R : Type u} [CommRing k] [CommRing H] [CommRing R] [HopfAlgebra k H]
    [HopfAlgebra k R]

section Diff

variable (d₁ d₂ : H →ₐc[k] R)

/-- The linear map `H ⊗[k] H → R`, `x ⊗ y ↦ d₁ (S x) · d₂ y`. -/
noncomputable def diffPair : H ⊗[k] H →ₗ[k] R :=
  (LinearMap.mul' k R) ∘ₗ
    (TensorProduct.map
      (((d₁ : H →ₐ[k] R).comp (HopfAlgebra.antipodeAlgHom k H)).toLinearMap)
      ((d₂ : H →ₐ[k] R).toLinearMap))

/-- `diffPair d₁ d₂` sends `x ⊗ y` to `d₁ (S x) · d₂ y`. -/
@[simp] lemma diffPair_tmul (x y : H) :
    diffPair d₁ d₂ (x ⊗ₜ[k] y) = d₁ (antipode k x) * d₂ y := rfl

/-- The **difference morphism** `p : H → R`, `x ↦ ∑ d₁(S x₍₁₎) d₂(x₍₂₎)`, as a linear map. -/
noncomputable def diffLin : H →ₗ[k] R := (diffPair d₁ d₂) ∘ₗ (comul (R := k) (A := H))

/-- The formula `p(x) = ∑ d₁(S x₍₁₎) d₂(x₍₂₎)`, for any Sweedler representation of `Δ x`. -/
lemma diffLin_apply (x : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    diffLin d₁ d₂ x = ∑ i ∈ r.index, d₁ (antipode k (r.left i)) * d₂ (r.right i) := by
  rw [diffLin, LinearMap.comp_apply, ← r.eq, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The difference map sends `1` to `1`. -/
@[simp] lemma diffLin_one : diffLin d₁ d₂ 1 = 1 := by
  rw [diffLin, LinearMap.comp_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    diffPair_tmul]
  simp

/-- The difference map is multiplicative: `p(x y) = p(x) p(y)`. -/
lemma diffLin_mul (x y : H) :
    diffLin d₁ d₂ (x * y) = diffLin d₁ d₂ x * diffLin d₁ d₂ y := by
  classical
  rw [diffLin_apply d₁ d₂ x (ℛ k x), diffLin_apply d₁ d₂ y (ℛ k y),
    diffLin_apply d₁ d₂ (x * y) ((ℛ k x).mul (ℛ k y)), Finset.sum_mul_sum]
  refine Eq.trans (Finset.sum_product (s := (ℛ k x).index) (t := (ℛ k y).index)
    (f := fun p => d₁ (antipode k ((ℛ k x).left p.1 * (ℛ k y).left p.2)) *
      d₂ ((ℛ k x).right p.1 * (ℛ k y).right p.2))) ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [HopfAlgebra.antipode_mul_distrib, map_mul, map_mul]
  ring

/-- The **difference morphism** `p : H →ₐ[k] R`, `x ↦ ∑ d₁(S x₍₁₎) d₂(x₍₂₎)`. -/
noncomputable def diffAlg : H →ₐ[k] R :=
  AlgHom.ofLinearMap (diffLin d₁ d₂) (diffLin_one d₁ d₂) (diffLin_mul d₁ d₂)

/-- `diffAlg d₁ d₂` agrees with `diffLin d₁ d₂` pointwise. -/
@[simp] lemma diffAlg_apply (x : H) : diffAlg d₁ d₂ x = diffLin d₁ d₂ x := rfl

/-- The auxiliary map `H ⊗[k] (H ⊗[k] H) → R`, `u ⊗ (v ⊗ w) ↦ d₁ u · d₁ (S v) · d₂ w`. -/
noncomputable def diffTriple : H ⊗[k] (H ⊗[k] H) →ₗ[k] R :=
  (LinearMap.mul' k R) ∘ₗ
    (TensorProduct.map ((d₁ : H →ₐ[k] R).toLinearMap) (diffPair d₁ d₂))
/-- `diffTriple d₁ d₂` sends `u ⊗ (v ⊗ w)` to `d₁ u · (d₁ (S v) · d₂ w)`. -/
@[simp] lemma diffTriple_tmul (u v w : H) :
    diffTriple d₁ d₂ (u ⊗ₜ[k] (v ⊗ₜ[k] w)) = d₁ u * (d₁ (antipode k v) * d₂ w) := rfl

/-- **The fundamental identity** `∑ d₁(x₍₁₎) p(x₍₂₎) = d₂ x`: the difference morphism is the
convolution inverse of `d₁` composed with `d₂`. -/
theorem sum_d₁_mul_diff (x : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    ∑ i ∈ r.index, d₁ (r.left i) * diffLin d₁ d₂ (r.right i) = d₂ x := by
  classical
  set a₁ : (i : ι) → Coalgebra.Repr k (r.left i) (H × H) := fun i => ℛ k (r.left i) with ha₁
  set a₂ : (i : ι) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i) with ha₂
  have key := congrArg (diffTriple d₁ d₂) (Coalgebra.sum_tmul_tmul_eq r a₁ a₂)
  simp only [map_sum, diffTriple_tmul] at key
  -- the right-hand side is the sum we are computing
  have hrhs : ∑ i ∈ r.index, ∑ j ∈ (a₂ i).index,
      d₁ (r.left i) * (d₁ (antipode k ((a₂ i).left j)) * d₂ ((a₂ i).right j))
      = ∑ i ∈ r.index, d₁ (r.left i) * diffLin d₁ d₂ (r.right i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [diffLin_apply d₁ d₂ (r.right i) (a₂ i), Finset.mul_sum]
  -- the left-hand side collapses by the antipode axiom
  have hlhs : ∑ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      d₁ ((a₁ i).left j) * (d₁ (antipode k ((a₁ i).right j)) * d₂ (r.right i))
      = d₂ x := by
    have hstep : ∀ i ∈ r.index, ∑ j ∈ (a₁ i).index,
        d₁ ((a₁ i).left j) * (d₁ (antipode k ((a₁ i).right j)) * d₂ (r.right i))
        = (counit (R := k) (r.left i)) • d₂ (r.right i) := by
      intro i _
      have : ∀ j ∈ (a₁ i).index,
          d₁ ((a₁ i).left j) * (d₁ (antipode k ((a₁ i).right j)) * d₂ (r.right i))
            = d₁ ((a₁ i).left j * antipode k ((a₁ i).right j)) * d₂ (r.right i) := by
        intro j _; rw [map_mul]; ring
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, ← map_sum,
        HopfAlgebra.sum_mul_antipode_eq_smul (a₁ i)]
      simp [Algebra.smul_def, AlgHomClass.commutes]
    rw [Finset.sum_congr rfl hstep]
    rw [show ∑ i ∈ r.index, (counit (R := k) (r.left i)) • d₂ (r.right i)
        = d₂ (∑ i ∈ r.index, (counit (R := k) (r.left i)) • r.right i) by
      rw [map_sum]; exact Finset.sum_congr rfl fun i _ => (map_smul _ _ _).symm]
    rw [Coalgebra.sum_counit_smul r]
  rw [← hrhs, ← hlhs, key]

end Diff

section Joint

variable (d₁ d₂ : H →ₐc[k] R)

/-- The algebra map `ψ : H ⊗[k] H →ₐ[k] R`, `x ⊗ y ↦ d₁ x · d₂ y`. -/
noncomputable def jointAlg : H ⊗[k] H →ₐ[k] R :=
  Algebra.TensorProduct.lift (d₁ : H →ₐ[k] R) (d₂ : H →ₐ[k] R) fun _ _ => Commute.all _ _

/-- `jointAlg d₁ d₂` sends `x ⊗ y` to `d₁ x · d₂ y`. -/
@[simp] lemma jointAlg_tmul (x y : H) : jointAlg d₁ d₂ (x ⊗ₜ[k] y) = d₁ x * d₂ y := rfl

/-- The subalgebra of `R` generated by the images of `d₁` and `d₂`. -/
noncomputable def jointRange : Subalgebra k R := (jointAlg d₁ d₂).range

/-- Every `d₁ x` lies in `jointRange d₁ d₂`. -/
lemma d₁_mem_jointRange (x : H) : d₁ x ∈ jointRange d₁ d₂ :=
  ⟨x ⊗ₜ[k] 1, by simp⟩

/-- Every `d₂ y` lies in `jointRange d₁ d₂`. -/
lemma d₂_mem_jointRange (y : H) : d₂ y ∈ jointRange d₁ d₂ :=
  ⟨1 ⊗ₜ[k] y, by simp⟩

/-- The subalgebra `(K ⊗ K)` of `R ⊗ R` attached to the subalgebra `K = jointRange`. -/
noncomputable def jointRange2 : Subalgebra k (R ⊗[k] R) :=
  (Algebra.TensorProduct.map (jointRange d₁ d₂).val (jointRange d₁ d₂).val).range

/-- If a bialgebra morphism `d : H →ₐc[k] R` takes values in `jointRange d₁ d₂`, then
`Δ (d a)` lies in `jointRange2 d₁ d₂`. -/
lemma mem_jointRange2_of_comul_bialgHom (d : H →ₐc[k] R)
    (hd : ∀ a : H, d a ∈ jointRange d₁ d₂) (a : H) :
    comul (R := k) (d a) ∈ jointRange2 d₁ d₂ := by
  classical
  set r : Coalgebra.Repr k (d a) (H × H) := (ℛ k a).induced d with hr
  refine ⟨∑ i ∈ r.index, (⟨d ((ℛ k a).left i), hd _⟩ : ↥(jointRange d₁ d₂)) ⊗ₜ[k]
    (⟨d ((ℛ k a).right i), hd _⟩ : ↥(jointRange d₁ d₂)), ?_⟩
  rw [map_sum, ← r.eq]
  rfl

/-- The image of `jointRange d₁ d₂ ⊗ jointRange d₁ d₂` in `R ⊗[k] R` is `jointRange2 d₁ d₂`. -/
lemma range_map_subtype_jointRange :
    LinearMap.range (TensorProduct.map (jointRange d₁ d₂).toSubmodule.subtype
      (jointRange d₁ d₂).toSubmodule.subtype) = (jointRange2 d₁ d₂).toSubmodule := by
  ext t
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, by
      induction w using TensorProduct.inductionOn with
      | tmul u v => rfl
      | add p q hp hq => rw [map_add, map_add, hp, hq]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, by
      induction w using TensorProduct.inductionOn with
      | tmul u v => rfl
      | add p q hp hq => rw [map_add, map_add, hp, hq]⟩

/-- `jointRange d₁ d₂` is a sub-Hopf algebra of `R`. -/
lemma isSubHopfAlgebra_jointRange :
    HopfAlgebra.IsSubHopfAlgebra k (jointRange d₁ d₂) where
  comul_mem := by
    -- `Δ (d₁ a * d₂ b) = Δ (d₁ a) * Δ (d₂ b)`, and both factors lie in `jointRange2`.
    have key : ∀ z : H ⊗[k] H, comul (R := k) (jointAlg d₁ d₂ z) ∈ jointRange2 d₁ d₂ := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        rw [jointAlg_tmul, Bialgebra.comul_mul]
        exact Subalgebra.mul_mem _
          (mem_jointRange2_of_comul_bialgHom d₁ d₂ d₁ (d₁_mem_jointRange d₁ d₂) a)
          (mem_jointRange2_of_comul_bialgHom d₁ d₂ d₂ (d₂_mem_jointRange d₁ d₂) b)
      | add p q hp hq => rw [map_add, map_add]; exact Subalgebra.add_mem _ hp hq
    rintro _ ⟨z, rfl⟩
    rw [range_map_subtype_jointRange]
    exact key z
  antipode_mem := by
    -- `S (d₁ a * d₂ b) = d₁ (S a) * d₂ (S b)`, since `R` is commutative.
    have key : ∀ z : H ⊗[k] H, antipode k (jointAlg d₁ d₂ z) ∈ jointRange d₁ d₂ := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
        rw [jointAlg_tmul, HopfAlgebra.antipode_mul_distrib, antipode_bialgHom_apply,
          antipode_bialgHom_apply]
        exact ⟨(antipode k a) ⊗ₜ[k] (antipode k b), rfl⟩
      | add p q hp hq =>
        rw [map_add, map_add]
        exact Subalgebra.add_mem _ hp hq
    rintro _ ⟨z, rfl⟩
    exact key z

/-- **If `(d₁, d₂)` is a jointly epimorphic pair, the map `ψ : H ⊗ H → R` is surjective.**
This is the algebraic form of the statement that an internal relation of affine group schemes
is a subscheme of the product; it uses that epimorphisms of commutative Hopf algebras over a
field are surjective. -/
theorem jointAlg_surjective [IsAbsFlat k]
    (hjoint : ∀ (T : Type u) (_ : CommRing T) (_ : HopfAlgebra k T) (α β : R →ₐc[k] T),
      (∀ x, α (d₁ x) = β (d₁ x)) → (∀ x, α (d₂ x) = β (d₂ x)) → ∀ r, α r = β r) :
    Function.Surjective (jointAlg d₁ d₂) := by
  let := isSubHopfAlgebra_jointRange d₁ d₂
  have hsurj : Function.Surjective
      (HopfAlgebra.subInclusion (k := k) (K := jointRange d₁ d₂)) := by
    refine HopfGen.Hopf.surjective_of_injective_of_epi _ HopfAlgebra.subInclusion_injective ?_
    intro T _ _ α β h r
    exact hjoint T inferInstance inferInstance α β
      (fun x => h ⟨d₁ x, d₁_mem_jointRange d₁ d₂ x⟩)
      (fun x => h ⟨d₂ x, d₂_mem_jointRange d₁ d₂ x⟩) r
  intro r
  obtain ⟨t, ht⟩ := hsurj r
  obtain ⟨z, hz⟩ := t.2
  exact ⟨z, hz.trans ht⟩

end Joint

end Coexact
end AffineGroupSchemes
