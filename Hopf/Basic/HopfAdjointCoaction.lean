module

public import Hopf.Basic.AntipodeInvolutive

/-!
# The adjoint coaction of a commutative Hopf algebra

Let `H` be a commutative Hopf algebra over a commutative ring `k`, with antipode `S`.  Takeuchi's
notion of a *normal* Hopf ideal ([Takeuchi1972], Definition 4.1) is phrased in terms of the map

```
ad : H → H ⊗[k] H,   x ↦ ∑ x₍₁₎ S(x₍₃₎) ⊗ x₍₂₎ ,
```

which represents the conjugation operation `(g, h) ↦ g h g⁻¹` of the affine group scheme
`Spec H`.  Since `H` is commutative, `ad` is a morphism of algebras; this file constructs it as
such (`HopfAlgebra.adAlgHom`) and develops the calculus needed later.

The main tool is the convolution monoid of `k`-linear maps `H → H ⊗[k] H`.  Writing
`L : x ↦ x ⊗ 1`, `R : x ↦ 1 ⊗ x`, `SL : x ↦ S x ⊗ 1`, `SR : x ↦ 1 ⊗ S x` for four of its
elements, one has `Δ = L ⋆ R`, `ad = L ⋆ R ⋆ SL`, `SL ⋆ L = L ⋆ SL = SR ⋆ R = R ⋆ SR = 1`, and all
the Sweedler identities needed in the sequel become one-line consequences of associativity of the
convolution product.  In particular:

* `HopfAlgebra.convL_convMul_adStar`: `L ⋆ ad* = τ ∘ Δ` where `ad* = (S ⊗ id) ∘ ad` and `τ`
  is the flip of the two tensor factors;
* `HopfAlgebra.adBar_convMul_convR`: `(τ ∘ ad) ⋆ R = τ ∘ Δ`.

These identities are exactly what makes Takeuchi's Lemma 4.4 work.

## Main results

* `HopfAlgebra.comul_comp_antipode`: the antipode is an anti-morphism of coalgebras,
  `Δ ∘ S = SR ⋆ SL` in the convolution monoid (Sweedler form: `comul_antipode_apply`).
* `HopfAlgebra.adAlgHom`: the adjoint coaction `x ↦ ∑ x₍₁₎ S(x₍₃₎) ⊗ x₍₂₎`, as an algebra
  map `H →ₐ[k] H ⊗[k] H`.
* `HopfAlgebra.adAlgHom_eq_conv`: `ad = L ⋆ R ⋆ SL` in the convolution monoid.
* `HopfAlgebra.convL_convMul_adStar`: `L ⋆ ad* = τ ∘ Δ`.
* `HopfAlgebra.adBar_convMul_convR`: `(τ ∘ ad) ⋆ R = τ ∘ Δ`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Section 4
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv LinearMap

section
namespace HopfAlgebra

section Conv

variable (k H : Type*) [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- The convolution unit-type element `L : x ↦ x ⊗ 1`. -/
noncomputable def convL : WithConv (H →ₗ[k] H ⊗[k] H) := toConv ((TensorProduct.mk k H H).flip 1)

/-- The element `R : x ↦ 1 ⊗ x` of the convolution monoid. -/
noncomputable def convR : WithConv (H →ₗ[k] H ⊗[k] H) := toConv (TensorProduct.mk k H H 1)

/-- The element `SL : x ↦ S x ⊗ 1` of the convolution monoid. -/
noncomputable def convSL : WithConv (H →ₗ[k] H ⊗[k] H) :=
  toConv (((TensorProduct.mk k H H).flip 1) ∘ₗ (antipode k : H →ₗ[k] H))

/-- The element `SR : x ↦ 1 ⊗ S x` of the convolution monoid. -/
noncomputable def convSR : WithConv (H →ₗ[k] H ⊗[k] H) :=
  toConv ((TensorProduct.mk k H H 1) ∘ₗ (antipode k : H →ₗ[k] H))

variable {k H}
/-- `L x = x ⊗ 1`. -/
@[simp] lemma convL_apply (x : H) : (convL k H).ofConv x = x ⊗ₜ[k] 1 := rfl

/-- `R x = 1 ⊗ x`. -/
@[simp] lemma convR_apply (x : H) : (convR k H).ofConv x = 1 ⊗ₜ[k] x := rfl

/-- `(S ∘ L) x = S x ⊗ 1`. -/
@[simp] lemma convSL_apply (x : H) : (convSL k H).ofConv x = antipode k x ⊗ₜ[k] 1 := rfl

/-- `(S ∘ R) x = 1 ⊗ S x`. -/
@[simp] lemma convSR_apply (x : H) : (convSR k H).ofConv x = 1 ⊗ₜ[k] antipode k x := rfl


/-- Convolution products are computed on a Sweedler representation. -/
lemma conv_apply (f g : WithConv (H →ₗ[k] H ⊗[k] H)) (x : H) {ι : Type*}
    (r : Coalgebra.Repr k x ι) :
    (f * g).ofConv x = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
  r.convMul_apply f g

/-- `L ⋆ R = Δ`. -/
lemma convL_convMul_convR : convL k H * convR k H = toConv (comul (R := k) (A := H)) := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convL_apply, convR_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [(ℛ k x).eq]

/-- `R ⋆ L = τ ∘ Δ`, where `τ` is the flip. -/
lemma convR_convMul_convL :
    convR k H * convL k H =
      toConv ((TensorProduct.comm k H H).toLinearMap ∘ₗ (comul (R := k) (A := H))) := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convL_apply, convR_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
    LinearMap.coe_comp, Function.comp_apply]
  rw [← (ℛ k x).eq]
  simp

/-- `SL ⋆ L = 1`. -/
lemma convSL_convMul_convL : convSL k H * convL k H = 1 := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convSL_apply, convL_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.sum_tmul, HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

/-- `L ⋆ SL = 1`. -/
lemma convL_convMul_convSL : convL k H * convSL k H = 1 := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convSL_apply, convL_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.sum_tmul, HopfAlgebra.sum_mul_antipode_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

/-- `SR ⋆ R = 1`. -/
lemma convSR_convMul_convR : convSR k H * convR k H = 1 := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convSR_apply, convR_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.tmul_sum, HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]

end Conv

section AntiComul

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- `Δ ⋆ (Δ ∘ S) = 1`: the comultiplication and its composite with the antipode are convolution
inverse to each other. -/
lemma comul_convMul_comul_antipode :
    toConv (comul (R := k) (A := H)) *
      toConv ((comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)) = 1 := by
  apply toConv_injective
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    (Bialgebra.comul_mul (R := k) ((ℛ k x).left i) (antipode k ((ℛ k x).right i))).symm),
    ← map_sum, HopfAlgebra.sum_mul_antipode_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

/-- **The antipode is an anti-morphism of coalgebras**: `Δ (S x) = ∑ S(x₍₂₎) ⊗ S(x₍₁₎)`
([Sweedler], 4.0.1). -/
theorem comul_comp_antipode :
    toConv ((comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)) = convSR k H * convSL k H := by
  refine (left_inv_eq_right_inv (a := toConv (comul (R := k) (A := H)))
    (b := convSR k H * convSL k H) ?_ comul_convMul_comul_antipode).symm
  calc convSR k H * convSL k H * toConv (comul (R := k) (A := H))
      = convSR k H * convSL k H * (convL k H * convR k H) := by rw [convL_convMul_convR]
    _ = convSR k H * ((convSL k H * convL k H) * convR k H) := by simp only [mul_assoc]
    _ = 1 := by rw [convSL_convMul_convL, one_mul, convSR_convMul_convR]

/-- The Sweedler form of anti-comultiplicativity of the antipode. -/
theorem comul_antipode_apply (x : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    comul (R := k) (antipode k x) =
      ∑ i ∈ r.index, antipode k (r.right i) ⊗ₜ[k] antipode k (r.left i) := by
  have antiComul := comul_comp_antipode (k := k) (H := H)
  apply_fun (fun t => t.ofConv x) at antiComul
  simp only [LinearMap.comp_apply] at antiComul
  rw [antiComul, conv_apply _ _ x r]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end AntiComul

section Ad

variable (k H : Type*) [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- The algebra map `H ⊗ H → H ⊗ H`, `y ⊗ z ↦ S z ⊗ y`. -/
noncomputable def adSwap : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeLeft.comp (HopfAlgebra.antipodeAlgHom k H))
    fun _ _ => Commute.all _ _

/-- The algebra map `H ⊗ (H ⊗ H) → H ⊗ H`, `x ⊗ (y ⊗ z) ↦ x S z ⊗ y`. -/
noncomputable def adOuter : H ⊗[k] (H ⊗[k] H) →ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (adSwap k H)
    fun _ _ => Commute.all _ _

/-- **The adjoint coaction** `ad : H → H ⊗[k] H`, `x ↦ ∑ x₍₁₎ S(x₍₃₎) ⊗ x₍₂₎`, as a morphism of
algebras (`H` being commutative).  It represents the conjugation map
`Spec H × Spec H → Spec H`, `(g, h) ↦ g h g⁻¹` (Takeuchi [Takeuchi1972], Section 4). -/
noncomputable def adAlgHom : H →ₐ[k] H ⊗[k] H :=
  (adOuter k H).comp ((Algebra.TensorProduct.map (AlgHom.id k H) (Bialgebra.comulAlgHom k H)).comp
    (Bialgebra.comulAlgHom k H))

/-- The "flipped" adjoint coaction `x ↦ ∑ x₍₂₎ ⊗ x₍₁₎S(x₍₃₎)`, as an algebra map. -/
noncomputable def adBarAlgHom : H →ₐ[k] H ⊗[k] H :=
  ((Algebra.TensorProduct.comm k H H).toAlgHom).comp (adAlgHom k H)

/-- The variant `ad* = (S ⊗ id) ∘ ad : x ↦ ∑ S(x₍₁₎) x₍₃₎ ⊗ x₍₂₎` of the adjoint coaction. -/
noncomputable def adStarAlgHom : H →ₐ[k] H ⊗[k] H :=
  (Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H)).comp
    (adAlgHom k H)

variable {k H}

/-- `adOuter` on pure tensors: `x ⊗ (y ⊗ z) ↦ x S(z) ⊗ y`. -/
@[simp] lemma adOuter_tmul (x y z : H) :
    adOuter k H (x ⊗ₜ[k] (y ⊗ₜ[k] z)) = (x * antipode k z) ⊗ₜ[k] y := by
  simp [adOuter, adSwap, Algebra.TensorProduct.tmul_mul_tmul]

/-- The Sweedler form of the adjoint coaction. -/
lemma adAlgHom_apply (x : H) {ι : Type*} {κ : ι → Type*} (r : Coalgebra.Repr k x ι)
    (r2 : ∀ i, Coalgebra.Repr k (r.right i) (κ i)) :
    adAlgHom k H x = ∑ i ∈ r.index, ∑ j ∈ (r2 i).index,
      (r.left i * antipode k ((r2 i).right j)) ⊗ₜ[k] ((r2 i).left j) := by
  simp only [adAlgHom, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, ← r.eq, map_sum,
    Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Bialgebra.comulAlgHom_apply,
    ← (r2 _).eq, TensorProduct.tmul_sum, adOuter_tmul]

/-- `adBarAlgHom` is `adAlgHom` followed by the swap of the tensor factors. -/
@[simp] lemma adBarAlgHom_apply (x : H) :
    adBarAlgHom k H x = (Algebra.TensorProduct.comm k H H) (adAlgHom k H x) := rfl

/-- `ad* x = (S ⊗ id) (ad x)`. -/
@[simp] lemma adStarAlgHom_apply (x : H) :
    adStarAlgHom k H x =
      Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H)
        (adAlgHom k H x) := rfl

/-- Post-composition with an algebra map distributes over the convolution product. -/
lemma toConv_algHom_comp (F : H ⊗[k] H →ₐ[k] H ⊗[k] H) (f g : WithConv (H →ₗ[k] H ⊗[k] H)) :
    toConv (F.toLinearMap ∘ₗ (f * g).ofConv)
      = toConv (F.toLinearMap ∘ₗ f.ofConv) * toConv (F.toLinearMap ∘ₗ g.ofConv) := by
  rw [LinearMap.algHom_comp_convMul_distrib F f g, toConv_ofConv]

/-- `ad = L ⋆ R ⋆ SL` in the convolution monoid. -/
theorem adAlgHom_eq_conv :
    toConv (adAlgHom k H).toLinearMap = convL k H * convR k H * convSL k H := by
  apply toConv_injective
  ext x
  set r := ℛ k x with hr
  set a₁ : (i : H × H) → Coalgebra.Repr k (r.left i) (H × H) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : H × H) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i) with ha2
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  apply_fun (adOuter k H).toLinearMap at key
  simp only [map_sum, AlgHom.toLinearMap_apply, adOuter_tmul] at key
  change (adAlgHom k H) x = _
  rw [adAlgHom_apply x r a₂, ← key, convL_convMul_convR, conv_apply _ _ x r]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [convSL_apply, ← (a₁ i).eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- Post-composing the adjoint coaction applies the algebra map to each convolution factor. -/
private lemma toConv_comp_adAlgHom (F : H ⊗[k] H →ₐ[k] H ⊗[k] H) :
    toConv (F.toLinearMap ∘ₗ (adAlgHom k H).toLinearMap) =
      toConv (F.toLinearMap ∘ₗ (convL k H).ofConv) *
        toConv (F.toLinearMap ∘ₗ (convR k H).ofConv) *
        toConv (F.toLinearMap ∘ₗ (convSL k H).ofConv) := by
  rw [← ofConv_toConv (adAlgHom k H).toLinearMap, adAlgHom_eq_conv,
    toConv_algHom_comp, toConv_algHom_comp]

/-- `τ ∘ ad = R ⋆ L ⋆ SR` in the convolution monoid. -/
theorem adBarAlgHom_eq_conv :
    toConv (adBarAlgHom k H).toLinearMap = convR k H * convL k H * convSR k H := by
  set F : H ⊗[k] H →ₐ[k] H ⊗[k] H := (Algebra.TensorProduct.comm k H H).toAlgHom with hF
  have swapLeft : toConv (F.toLinearMap ∘ₗ (convL k H).ofConv) = convR k H := by
    apply toConv_injective
    ext x
    simp [hF, convL]
  have swapRight : toConv (F.toLinearMap ∘ₗ (convR k H).ofConv) = convL k H := by
    apply toConv_injective
    ext x
    simp [hF, convR]
  have swapAntipode : toConv (F.toLinearMap ∘ₗ (convSL k H).ofConv) = convSR k H := by
    apply toConv_injective
    ext x
    simp [hF, convSL]
  rw [show toConv (adBarAlgHom k H).toLinearMap
      = toConv (F.toLinearMap ∘ₗ (adAlgHom k H).toLinearMap) from rfl,
    toConv_comp_adAlgHom, swapLeft, swapRight, swapAntipode]

/-- `(τ ∘ ad) ⋆ R = τ ∘ Δ`. -/
theorem adBar_convMul_convR :
    toConv (adBarAlgHom k H).toLinearMap * convR k H =
      toConv ((TensorProduct.comm k H H).toLinearMap ∘ₗ (comul (R := k) (A := H))) := by
  rw [adBarAlgHom_eq_conv, mul_assoc, convSR_convMul_convR, mul_one, convR_convMul_convL]

/-- `ad* = SL ⋆ R ⋆ L` in the convolution monoid. -/
theorem adStarAlgHom_eq_conv :
    toConv (adStarAlgHom k H).toLinearMap = convSL k H * convR k H * convL k H := by
  set F : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
    Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H) (AlgHom.id k H) with hF
  have antipodeLeft : toConv (F.toLinearMap ∘ₗ (convL k H).ofConv) = convSL k H := by
    apply toConv_injective
    ext x
    simp [hF, convL]
  have antipodeRight : toConv (F.toLinearMap ∘ₗ (convR k H).ofConv) = convR k H := by
    apply toConv_injective
    ext x
    simp [hF, convR]
  have antipodeTwice : toConv (F.toLinearMap ∘ₗ (convSL k H).ofConv) = convL k H := by
    apply toConv_injective
    ext x
    simp [hF, convSL, HopfAlgebra.antipode_antipode]
  rw [show toConv (adStarAlgHom k H).toLinearMap
      = toConv (F.toLinearMap ∘ₗ (adAlgHom k H).toLinearMap) from rfl,
    toConv_comp_adAlgHom, antipodeLeft, antipodeRight, antipodeTwice]

/-- `L ⋆ ad* = τ ∘ Δ`. -/
theorem convL_convMul_adStar :
    convL k H * toConv (adStarAlgHom k H).toLinearMap =
      toConv ((TensorProduct.comm k H H).toLinearMap ∘ₗ (comul (R := k) (A := H))) := by
  rw [adStarAlgHom_eq_conv, ← mul_assoc, ← mul_assoc, convL_convMul_convSL, one_mul,
    convR_convMul_convL]

end Ad

end HopfAlgebra
end
