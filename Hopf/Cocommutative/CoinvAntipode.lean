module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Hopf.Cocommutative.CoinvSubcoalgebra

/-!
# Newman's `μ` lands in sub-Hopf algebras: closure under the antipode

Let `H` be a Hopf algebra over a field `k` and `I ⊆ H` a left ideal.  Newman's `λ`-kernel

```
μ I  =  {h ∈ H | Δ h - h ⊗ 1 ∈ H ⊗ I}
```

is a subalgebra for any Hopf algebra (`HopfAlgebra.Cocommutative.coinvSubalgebra`) and a
sub-bialgebra when `H` is cocommutative (`HopfAlgebra.Cocommutative.isSubBialg_coinvSubalgebra`).
This file supplies the missing closure property, that `μ I` is stable under the antipode, so that
`μ` really takes values in sub-Hopf algebras.

The proof is the Hopf-algebraic shadow of the categorical fact that the kernel of an equivariant
quotient is a *subgroup* object, closed in particular under the inverse
(`InternalGroups.QuotObj.kernel_inv` in `InternalGroups/GrpSubQuot.lean`): for a group,
`q a = q 1` forces `q a⁻¹ = a⁻¹ · q a = q (a⁻¹ a) = q 1`.  Written out for generalized elements of
a cocommutative Hopf algebra, that computation is exactly
`HopfAlgebra.Cocommutative.antipode_sub_mem` below, the identity `S h ≡ ε(h) 1 mod I`, obtained by
applying `a ⊗ b ↦ S a · b` to `Δ h - h ⊗ 1 ∈ H ⊗ I`.

## Main results

* `HopfAlgebra.Cocommutative.comul_comp_antipode_eq`: **the antipode of an arbitrary Hopf algebra is
  an anti-morphism of coalgebras**, `Δ ∘ S = τ ∘ (S ⊗ S) ∘ Δ`.  (The project already had this for a
  *commutative* `H`, in `Hopf/Basic/HopfAdjointCoaction.lean`; the proof does not use commutativity,
  and the cocommutative Hopf algebras of Newman's theorem — group algebras, for instance — are not
  commutative.)
* `HopfAlgebra.Cocommutative.comul_comp_antipode_of_isCocomm`: for a cocommutative `H`,
  `Δ ∘ S = (S ⊗ S) ∘ Δ`.
* `HopfAlgebra.Cocommutative.antipode_sub_mem`: for a left ideal `I` and `h ∈ μ I`,
  `ε(h) • 1 - S h ∈ I`.
* `HopfAlgebra.Cocommutative.antipode_mem_coinv`: for a cocommutative `H` and a left ideal `I`,
  `μ I` is stable under the antipode.
* `HopfAlgebra.Cocommutative.isSubHopf_coinvSubalgebra`: hence `μ I` is a **sub-Hopf algebra**; this
  is the well-definedness of Newman's `μ`, and it is packaged as `HopfAlgebra.Cocommutative.muMap`
  together with the Galois connection `HopfAlgebra.Cocommutative.tauMap_le_iff_le_muMap` between
  sub-Hopf algebras and left bi-ideals.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.0.1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.5
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv

namespace HopfAlgebra.Cocommutative

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

/-! ### The antipode is an anti-morphism of coalgebras

The four convolution units below live in the convolution monoid of the `k`-linear maps
`H → H ⊗[k] H`; no commutativity of `H` is needed anywhere. -/

section AntiComul

variable (k H) in
/-- The element `L : x ↦ x ⊗ 1` of the convolution monoid `Hom(H, H ⊗ H)`. -/
noncomputable def convL : WithConv (H →ₗ[k] H ⊗[k] H) := toConv ((TensorProduct.mk k H H).flip 1)

variable (k H) in
/-- The element `R : x ↦ 1 ⊗ x` of the convolution monoid `Hom(H, H ⊗ H)`. -/
noncomputable def convR : WithConv (H →ₗ[k] H ⊗[k] H) := toConv (TensorProduct.mk k H H 1)

variable (k H) in
/-- The element `SL : x ↦ S x ⊗ 1` of the convolution monoid `Hom(H, H ⊗ H)`. -/
noncomputable def convSL : WithConv (H →ₗ[k] H ⊗[k] H) :=
  toConv (((TensorProduct.mk k H H).flip 1) ∘ₗ (antipode k : H →ₗ[k] H))

variable (k H) in
/-- The element `SR : x ↦ 1 ⊗ S x` of the convolution monoid `Hom(H, H ⊗ H)`. -/
noncomputable def convSR : WithConv (H →ₗ[k] H ⊗[k] H) :=
  toConv ((TensorProduct.mk k H H 1) ∘ₗ (antipode k : H →ₗ[k] H))
/-- `convL x = x ⊗ 1`. -/
@[simp] lemma convL_apply (x : H) : (convL k H).ofConv x = x ⊗ₜ[k] 1 := rfl

/-- `convR x = 1 ⊗ x`. -/
@[simp] lemma convR_apply (x : H) : (convR k H).ofConv x = 1 ⊗ₜ[k] x := rfl

/-- `convSL x = S x ⊗ 1`. -/
@[simp] lemma convSL_apply (x : H) : (convSL k H).ofConv x = antipode k x ⊗ₜ[k] 1 := rfl

/-- `convSR x = 1 ⊗ S x`. -/
@[simp] lemma convSR_apply (x : H) : (convSR k H).ofConv x = 1 ⊗ₜ[k] antipode k x := rfl

/-- Convolution products are computed on a Sweedler representation. -/
lemma conv_apply (f g : WithConv (H →ₗ[k] H ⊗[k] H)) (x : H) {ι : Type*} (r : Coalgebra.Repr k x ι)
    :
    (f * g).ofConv x = ∑ i ∈ r.index, f.ofConv (r.left i) * g.ofConv (r.right i) :=
  r.convMul_apply f g

/-- `L ⋆ R = Δ`. -/
lemma convL_convMul_convR : convL k H * convR k H = toConv (comul (R := k) (A := H)) := by
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convL_apply, convR_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [(ℛ k x).eq]

/-- `SL ⋆ L = 1`. -/
lemma convSL_convMul_convL : convSL k H * convL k H = 1 := by
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convSL_apply, convL_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.sum_tmul, HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]

/-- `SR ⋆ R = 1`. -/
lemma convSR_convMul_convR : convSR k H * convR k H = 1 := by
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [convSR_apply, convR_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← TensorProduct.tmul_sum, HopfAlgebra.sum_antipode_mul_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]

/-- `Δ ⋆ (Δ ∘ S) = 1`: the comultiplication and its composite with the antipode are convolution
inverse to each other. -/
lemma comul_convMul_comul_antipode :
    toConv (comul (R := k) (A := H)) *
      toConv ((comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)) = 1 := by
  ext x
  rw [conv_apply _ _ x (ℛ k x)]
  simp only [LinearMap.coe_comp, Function.comp_apply]
  rw [Finset.sum_congr rfl (fun i _ =>
    (Bialgebra.comul_mul (R := k) ((ℛ k x).left i) (antipode k ((ℛ k x).right i))).symm),
    ← map_sum, HopfAlgebra.sum_mul_antipode_eq_smul (ℛ k x)]
  simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]

/-- **The antipode of an arbitrary Hopf algebra is an anti-morphism of coalgebras**, in
convolution form: `Δ ∘ S = SR ⋆ SL`, that is `Δ (S x) = ∑ S(x₍₂₎) ⊗ S(x₍₁₎)`. -/
theorem comul_comp_antipode_conv :
    toConv ((comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)) = convSR k H * convSL k H := by
  refine (left_inv_eq_right_inv (a := toConv (comul (R := k) (A := H)))
    (b := convSR k H * convSL k H) ?_ comul_convMul_comul_antipode).symm
  calc convSR k H * convSL k H * toConv (comul (R := k) (A := H))
      = convSR k H * convSL k H * (convL k H * convR k H) := by rw [convL_convMul_convR]
    _ = convSR k H * ((convSL k H * convL k H) * convR k H) := by simp only [mul_assoc]
    _ = 1 := by rw [convSL_convMul_convL, one_mul, convSR_convMul_convR]

/-- **The antipode is an anti-morphism of coalgebras**: `Δ ∘ S = τ ∘ (S ⊗ S) ∘ Δ`, where `τ` is
the flip of the two tensor factors.  No commutativity or cocommutativity of `H` is used. -/
theorem comul_comp_antipode_eq :
    (comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)
      = (TensorProduct.comm k H H).toLinearMap ∘ₗ
        TensorProduct.map (antipode k) (antipode k) ∘ₗ (comul (R := k) (A := H)) := by
  ext x
  have h := congr(WithConv.ofConv $(comul_comp_antipode_conv (k := k) (H := H)) x)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h ⊢
  rw [h, conv_apply _ _ x (ℛ k x), ← (ℛ k x).eq]
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- For a **cocommutative** Hopf algebra the antipode is an honest morphism of coalgebras:
`Δ ∘ S = (S ⊗ S) ∘ Δ`. -/
theorem comul_comp_antipode_of_isCocomm [Coalgebra.IsCocomm k H] :
    (comul (R := k) (A := H)) ∘ₗ (antipode k : H →ₗ[k] H)
      = TensorProduct.map (antipode k) (antipode k) ∘ₗ (comul (R := k) (A := H)) := by
  ext x
  have hcomm := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := H)) x)
  have hmap : ∀ t : H ⊗[k] H,
      (TensorProduct.comm k H H) (TensorProduct.map (antipode k) (antipode k) t)
        = TensorProduct.map (antipode k) (antipode k) ((TensorProduct.comm k H H) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  have h := congr($(comul_comp_antipode_eq (k := k) (H := H)) x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h hcomm ⊢
  rw [h, hmap, hcomm]

end AntiComul

/-! ### `μ I` is stable under the antipode -/

/-- The linear map `a ⊗ b ↦ S a * b`. -/
noncomputable def mulAntipodeLeft : H ⊗[k] H →ₗ[k] H :=
  LinearMap.mul' k H ∘ₗ LinearMap.rTensor H (antipode k)

/-- `mulAntipodeLeft (a ⊗ b) = S a * b`. -/
@[simp] lemma mulAntipodeLeft_tmul (a b : H) :
    mulAntipodeLeft (k := k) (a ⊗ₜ[k] b) = antipode k a * b := by
  simp [mulAntipodeLeft]

/-- `mulAntipodeLeft (Δ h) = ε(h) • 1`, i.e. `∑ S h₁ * h₂ = ε(h) 1`. -/
lemma mulAntipodeLeft_comul (h : H) :
    mulAntipodeLeft (k := k) (comul (R := k) h) = (counit (R := k) h) • (1 : H) := by
  have := congr($(HopfAlgebra.mul_antipode_rTensor_comul (R := k) (A := H)) h)
  simp [mulAntipodeLeft, Algebra.algebraMap_eq_smul_one] at this ⊢

/-- **`S h ≡ ε(h) 1` modulo `I`, for `h` in the `λ`-kernel of a left ideal `I`.**  This is the
Hopf-algebraic form of the categorical computation `q a⁻¹ = a⁻¹ · q a = q 1` showing that the
kernel of an equivariant quotient is closed under inverses.  Neither cocommutativity nor the
anti-multiplicativity of the antipode is needed. -/
theorem antipode_sub_mem {I : Submodule k H} (hI : ∀ (h : H), ∀ x ∈ I, h * x ∈ I)
    {h : H} (hh : h ∈ coinv I) : (counit (R := k) h) • (1 : H) - antipode k h ∈ I := by
  have hle : rightTensor I ≤ Submodule.comap (mulAntipodeLeft (k := k) (H := H)) I :=
    rightTensor_le fun a x hx => by
      simpa using hI (antipode k a) x hx
  have := hle hh
  simpa [Submodule.mem_comap, mulAntipodeLeft_comul] using this

variable [IsAbsFlat k]

/-- **The `λ`-kernel of a left ideal in a cocommutative Hopf algebra is stable under the
antipode.** -/
theorem antipode_mem_coinv [Coalgebra.IsCocomm k H] {I : Submodule k H}
    (hI : ∀ (h : H), ∀ x ∈ I, h * x ∈ I) {h : H} (hh : h ∈ coinv I) :
    antipode k h ∈ coinv I := by
  classical
  set D : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
    TensorProduct.map (antipode k) (antipode k)
      - TensorProduct.map (antipode k)
          ((LinearMap.toSpanSingleton k H 1) ∘ₗ (counit (R := k) (A := H))) with hD
  -- `D` sends `H ⊗ μ I` into `H ⊗ I`
  have hDmem : ∀ t ∈ rightTensor (coinv I), D t ∈ rightTensor I := by
    intro t ht
    have hle : rightTensor (coinv I) ≤ Submodule.comap D (rightTensor I) := by
      refine rightTensor_le fun a y hy => ?_
      have hy' : (counit (R := k) y) • (1 : H) - antipode k y ∈ I :=
        antipode_sub_mem hI hy
      have : D (a ⊗ₜ[k] y)
          = antipode k a ⊗ₜ[k] (-((counit (R := k) y) • (1 : H) - antipode k y)) := by
        simp [hD, TensorProduct.tmul_sub, LinearMap.toSpanSingleton_apply]
      simp only [Submodule.mem_comap, this]
      exact tmul_mem_rightTensor _ (Submodule.neg_mem _ hy')
    exact hle ht
  -- `D (Δ h) = Δ (S h) - S h ⊗ 1`
  have hsecond : TensorProduct.map (antipode k)
      ((LinearMap.toSpanSingleton k H 1) ∘ₗ (counit (R := k) (A := H))) (comul (R := k) h)
      = antipode k h ⊗ₜ[k] (1 : H) := by
    have hsplit : TensorProduct.map (antipode k)
        ((LinearMap.toSpanSingleton k H 1) ∘ₗ (counit (R := k) (A := H)))
        = LinearMap.rTensor H (antipode k) ∘ₗ
          LinearMap.lTensor H ((LinearMap.toSpanSingleton k H 1) ∘ₗ
            (counit (R := k) (A := H))) := by
      ext a b; simp
    rw [hsplit]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [show LinearMap.lTensor H ((LinearMap.toSpanSingleton k H 1) ∘ₗ
        (counit (R := k) (A := H))) (comul (R := k) h) = h ⊗ₜ[k] (1 : H) from ?_]
    · simp
    · rw [LinearMap.lTensor_comp, LinearMap.comp_apply,
        show LinearMap.lTensor H (counit (R := k) (A := H)) (comul (R := k) h)
          = h ⊗ₜ[k] (1 : k) from congr($(lTensor_counit_comp_comul (R := k) (A := H)) h)]
      simp
  have hfirst : TensorProduct.map (antipode k) (antipode k) (comul (R := k) h)
      = comul (R := k) (antipode k h) :=
    (congr($(comul_comp_antipode_of_isCocomm (k := k) (H := H)) h)).symm
  have hval : D (comul (R := k) h)
      = comul (R := k) (antipode k h) - antipode k h ⊗ₜ[k] (1 : H) := by
    simp only [hD, LinearMap.sub_apply, hfirst, hsecond]
  rw [mem_coinv, ← hval]
  exact hDmem _ (comul_mem_rightTensor_coinv I hh)

/-- **Newman's `μ` lands in sub-Hopf algebras**: for a cocommutative Hopf algebra `H` over a field
and any left ideal `I`, the `λ`-kernel `μ I` is a subalgebra closed under the comultiplication and
the antipode. -/
theorem isSubHopf_coinvSubalgebra [Coalgebra.IsCocomm k H] (I : Submodule k H)
    (hI : ∀ (h : H), ∀ x ∈ I, h * x ∈ I) :
    IsSubHopfAlgebra k (coinvSubalgebra hI) where
  __ := isSubBialg_coinvSubalgebra I hI
  antipode_mem x hx := antipode_mem_coinv hI (show x ∈ coinv I from hx)

/-! ### The correspondence as a map between the two structured types -/

/-- **The quasi-kernel map `μ : I ↦ H^{co H/I}`** from left bi-ideals to sub-Hopf algebras, for a
cocommutative Hopf algebra over a field.  Together with `HopfAlgebra.Cocommutative.tauMap` it
realizes the Galois connection of Newman's correspondence on the two structured types. -/
noncomputable def muMap [Coalgebra.IsCocomm k H] (I : LeftBiIdeal k H) : SubHopfAlg k H :=
  ⟨coinvSubalgebra I.isLeftBiIdeal.mul_mem,
    isSubHopf_coinvSubalgebra I.carrier I.isLeftBiIdeal.mul_mem⟩

/-- The underlying subspace of `muMap I` is `coinv I = {h | Δ h - h ⊗ 1 ∈ H ⊗ I}`. -/
@[simp] lemma muMap_carrier_toSubmodule [Coalgebra.IsCocomm k H] (I : LeftBiIdeal k H) :
    (muMap I).carrier.toSubmodule = coinv I.carrier := rfl

/-- **The Galois connection between sub-Hopf algebras and left bi-ideals** of a cocommutative Hopf
algebra: `τ K ≤ I` if and only if `K ≤ μ I`. -/
theorem tauMap_le_iff_le_muMap [Coalgebra.IsCocomm k H] (K : SubHopfAlg k H)
    (I : LeftBiIdeal k H) :
    (tauMap K).carrier ≤ I.carrier ↔ K.carrier.toSubmodule ≤ (muMap I).carrier.toSubmodule :=
  tau_le_iff_le_coinv K.isSubHopf.toIsSubBialg I.isLeftBiIdeal.mul_mem

/-! ### `μ I` is the kernel of `H ↠ H ⧸ I` in coalgebras -/

end HopfAlgebra.Cocommutative
