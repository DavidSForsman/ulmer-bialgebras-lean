module

public import Hopf.Commutative.HopfMixedGalois
public import Hopf.Basic.HopfQuotientAug
public import Hopf.Basic.HopfTensorQuotEquiv

/-!
# Takeuchi's Lemma 3.9: `K ⊗_A H ≅ H ⊗_k (K / A⁺K)`

Let `A ⊆ K ⊆ H` be commutative Hopf algebras over a field `k` (given by morphisms
`fAK : A →ₐc[k] K` and `j : K →ₐc[k] H` inducing the algebra structures).  Takeuchi's Lemma 3.9
(*A correspondence between Hopf ideals and sub-Hopf algebras*, 1972) states that
```
K ⊗_A H  ≅  (K / A⁺K) ⊗_k H,   x ⊗ y ↦ ∑ [x₍₁₎] ⊗ x₍₂₎ y
```
is an isomorphism of algebras.  Here the two tensor factors on the right are written in the
opposite order, `H ⊗_k (K / A⁺K)`, matching the convention of
`Hopf/Basic/HopfTensorQuotEquiv.lean`; the isomorphism is
```
Φ : K ⊗_A H → H ⊗_k (K / A⁺K),   x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎],
```
with inverse induced by `y ⊗ [x] ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y`.

## Main results

* `HopfAlgebra.Commutative.mixedTensor`: the `A`-linear map `Φ : K ⊗[A] H → H ⊗[k] (K / A⁺K)`,
  `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]`.
* `HopfAlgebra.Commutative.mixedTensorEquiv`: `Φ` as an isomorphism of `A`-modules (Takeuchi's
  Lemma 3.9).

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 3.9
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k A K H : Type*} [Field k] [CommRing A] [CommRing K] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k K] [HopfAlgebra k H]
  [Algebra A K]

variable (k A K H) in
/-- The `k`-linear map `K ⊗[k] H → H ⊗[k] (K/A⁺K)`, `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]`. -/
noncomputable def mixedQuot (j : K →ₐc[k] H) : K ⊗[k] H →ₗ[k] H ⊗[k] QuotAug k A K :=
  (TensorProduct.comm k (QuotAug k A K) H).toLinearMap ∘ₗ
    (LinearMap.rTensor H (mkAug k A K).toLinearMap) ∘ₗ mixedGalois k K H j

variable (j : K →ₐc[k] H)

/-- `mixedQuot (x ⊗ y) = ∑ᵢ j(x₂ⁱ) y ⊗ [x₁ⁱ]` for any representation `Δ x = ∑ᵢ x₁ⁱ ⊗ x₂ⁱ`. -/
lemma mixedQuot_tmul (x : K) (y : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    mixedQuot k A K H j (x ⊗ₜ[k] y)
      = ∑ i ∈ r.index, (j (r.right i) * y) ⊗ₜ[k] mkAug k A K (r.left i) := by
  rw [mixedQuot, LinearMap.comp_apply, LinearMap.comp_apply, mixedGalois_tmul j x y r,
    map_sum, map_sum]
  rfl

variable (k A K H) in
/-- The canonical `k`-linear surjection `K ⊗[k] H → H ⊗[k] (K/A⁺K)`, `x ⊗ y ↦ y ⊗ [x]`. -/
noncomputable def quotLeft : K ⊗[k] H →ₗ[k] H ⊗[k] QuotAug k A K :=
  (TensorProduct.comm k (QuotAug k A K) H).toLinearMap ∘ₗ
    (LinearMap.rTensor H (mkAug k A K).toLinearMap)

/-- `quotLeft : K ⊗[k] H → H ⊗[k] (K/A⁺K)` is surjective. -/
lemma quotLeft_surjective : Function.Surjective (quotLeft k A K H) := by
  refine (TensorProduct.comm k (QuotAug k A K) H).surjective.comp ?_
  exact LinearMap.rTensor_surjective H (g := (mkAug k A K).toLinearMap) mkAug_surjective

/-- `mixedQuot` is `quotLeft` composed with the mixed Galois map (true by definition). -/
lemma mixedQuot_eq_quotLeft (z : K ⊗[k] H) :
    mixedQuot k A K H j z = quotLeft k A K H (mixedGalois k K H j z) := rfl

variable [Algebra A H] [IsScalarTower k A H]

/-- `A`-linearity in the second variable: the `A`-action on `H ⊗[k] (K/A⁺K)` is through `H`. -/
lemma mixedQuot_tmul_smul (a : A) (x : K) (y : H) :
    mixedQuot k A K H j (x ⊗ₜ[k] (a • y)) = a • mixedQuot k A K H j (x ⊗ₜ[k] y) := by
  classical
  rw [mixedQuot_tmul j x (a • y) (ℛ k x), mixedQuot_tmul j x y (ℛ k x), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_smul_comm, TensorProduct.smul_tmul']

variable [IsScalarTower k A K]

variable (k A K H) in
/-- The canonical `k`-linear surjection `K ⊗[k] H → K ⊗[A] H`. -/
noncomputable def mixedTensorProj : K ⊗[k] H →ₗ[k] K ⊗[A] H :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun y => x ⊗ₜ[A] y
          map_add' := fun y y' => TensorProduct.tmul_add x y y'
          map_smul' := fun c y => by
            simp only [RingHom.id_apply]
            rw [← TensorProduct.tmul_smul] }
      map_add' := fun x x' => by
        refine LinearMap.ext fun y => ?_
        simpa using TensorProduct.add_tmul x x' y
      map_smul' := fun c x => by
        refine LinearMap.ext fun y => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
        rw [← TensorProduct.smul_tmul'] }

/-- `mixedTensorProj : K ⊗[k] H → K ⊗[A] H` is surjective. -/
lemma mixedTensorProj_surjective : Function.Surjective (mixedTensorProj k A K H) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact ⟨x ⊗ₜ[k] y, rfl⟩
  | add u v hu hv =>
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    exact ⟨u' + v', by rw [map_add]⟩

variable (k A K H) in
/-- The `k`-linear map `K ⊗[k] H → K ⊗[A] H`, `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y`, obtained from the
inverse mixed Galois map by projecting to the relative tensor product. -/
noncomputable def mixedInvProj : K ⊗[k] H →ₗ[k] K ⊗[A] H :=
  mixedTensorProj k A K H ∘ₗ mixedGaloisInv k K H j

/-- `mixedInvProj (x ⊗ y) = ∑ᵢ x₁ⁱ ⊗_A j(S x₂ⁱ) y` for any representation
`Δ x = ∑ᵢ x₁ⁱ ⊗ x₂ⁱ`. -/
lemma mixedInvProj_tmul (x : K) (y : H) {ι : Type*} (r : Coalgebra.Repr k x ι) :
    mixedInvProj k A K H j (x ⊗ₜ[k] y)
      = ∑ i ∈ r.index, r.left i ⊗ₜ[A] (j (antipode k (r.right i)) * y) := by
  rw [mixedInvProj, LinearMap.comp_apply, mixedGaloisInv_tmul j x y r, map_sum]
  rfl

section Balanced

variable (fAK : A →ₐc[k] K) (halgK : ∀ a, algebraMap A K a = fAK a)
  (halgH : ∀ a, algebraMap A H a = j (fAK a))

include halgK halgH

omit [IsScalarTower k A H] in
/-- **Balancedness.**  The map `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]` moves a scalar from `A` across the
tensor sign, because `A` acts on `K/A⁺K` through its counit. -/
lemma mixedQuot_algebraMap_tmul (a : A) (x : K) (y : H) :
    mixedQuot k A K H j ((algebraMap A K a * x) ⊗ₜ[k] y)
      = mixedQuot k A K H j (x ⊗ₜ[k] (algebraMap A H a * y)) := by
  classical
  set ra : Coalgebra.Repr k (fAK a) (A × A) := (ℛ k a).induced fAK with hra
  set rx : Coalgebra.Repr k x (K × K) := ℛ k x with hrx
  rw [halgK a, mixedQuot_tmul j (fAK a * x) y (ra.mul rx), mixedQuot_tmul j x _ rx]
  refine Eq.trans (Finset.sum_product ra.index rx.index
    (fun p => (j (ra.right p.1 * rx.right p.2) * y) ⊗ₜ[k]
      mkAug k A K (ra.left p.1 * rx.left p.2))) ?_
  have step : ∀ i ∈ ra.index, ∀ l ∈ rx.index,
      (j (ra.right i * rx.right l) * y) ⊗ₜ[k] mkAug k A K (ra.left i * rx.left l)
        = ((Coalgebra.counit (R := k) (ra.left i)) • (j (ra.right i) * (j (rx.right l) * y)))
            ⊗ₜ[k] mkAug k A K (rx.left l) := by
    intro i _ l _
    have h1 : mkAug k A K (ra.left i * rx.left l)
        = (Coalgebra.counit (R := k) (ra.left i)) • mkAug k A K (rx.left l) := by
      have hli : ra.left i = fAK ((ℛ k a).left i) := rfl
      rw [hli, mkAug_f_mul fAK halgK, ← CoalgHomClass.counit_comp_apply (R := k) fAK]
    rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', map_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => step i hi l hl,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← TensorProduct.sum_tmul]
  congr 1
  have hsum : ∑ i ∈ ra.index,
      (Coalgebra.counit (R := k) (ra.left i)) • (j (ra.right i) * (j (rx.right l) * y))
      = j (∑ i ∈ ra.index, (Coalgebra.counit (R := k) (ra.left i)) • ra.right i) *
        (j (rx.right l) * y) := by
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_mul_assoc]
  rw [hsum, Coalgebra.sum_counit_smul ra, halgH a]
  ring

/-- The map `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]` as an `A`-bilinear map. -/
noncomputable def mixedQuotBil : K →ₗ[A] H →ₗ[A] H ⊗[k] QuotAug k A K where
  toFun x :=
    { toFun := fun y => mixedQuot k A K H j (x ⊗ₜ[k] y)
      map_add' := fun y y' => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a y => by
        simpa only [RingHom.id_apply] using mixedQuot_tmul_smul j a x y }
  map_add' := fun x x' => by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [TensorProduct.add_tmul, map_add]
  map_smul' := fun a x => by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [Algebra.smul_def, mixedQuot_algebraMap_tmul j fAK halgK halgH a x y,
      ← Algebra.smul_def, mixedQuot_tmul_smul j a x y]

/-- **Takeuchi's Lemma 3.9, the forward map**: the `A`-linear map
`Φ : K ⊗[A] H → H ⊗[k] (K/A⁺K)`, `x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]`. -/
noncomputable def mixedTensor : K ⊗[A] H →ₗ[A] H ⊗[k] QuotAug k A K :=
  TensorProduct.lift (mixedQuotBil j fAK halgK halgH)

/-- `mixedTensor (x ⊗_A y) = mixedQuot (x ⊗ y)`. -/
@[simp] lemma mixedTensor_tmul (x : K) (y : H) :
    mixedTensor j fAK halgK halgH (x ⊗ₜ[A] y) = mixedQuot k A K H j (x ⊗ₜ[k] y) := rfl

/-- `mixedTensor` composed with `mixedTensorProj` is `mixedQuot`. -/
lemma mixedTensor_mixedTensorProj (z : K ⊗[k] H) :
    mixedTensor j fAK halgK halgH (mixedTensorProj k A K H z) = mixedQuot k A K H j z := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]

/-- **The key vanishing computation.**  If `a` lies in the augmentation ideal of `A`, then
`x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y` kills `(f a * x) ⊗ y`, because `∑ a₍₁₎ S(a₍₂₎) = ε(a) = 0`. -/
lemma mixedInvProj_augmentation_tmul (a : A) (ha : Coalgebra.counit (R := k) a = 0) (x : K)
    (y : H) : mixedInvProj k A K H j ((fAK a * x) ⊗ₜ[k] y) = 0 := by
  classical
  set ra : Coalgebra.Repr k (fAK a) (A × A) := (ℛ k a).induced fAK with hra
  set rx : Coalgebra.Repr k x (K × K) := ℛ k x with hrx
  rw [mixedInvProj_tmul j (fAK a * x) y (ra.mul rx)]
  refine Eq.trans (Finset.sum_product ra.index rx.index
    (fun p => (ra.left p.1 * rx.left p.2) ⊗ₜ[A]
      (j (antipode k (ra.right p.1 * rx.right p.2)) * y))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l _ => ?_
  have step : ∀ i ∈ ra.index,
      (ra.left i * rx.left l) ⊗ₜ[A] (j (antipode k (ra.right i * rx.right l)) * y)
        = rx.left l ⊗ₜ[A]
            (j (ra.left i * antipode k (ra.right i)) *
              (j (antipode k (rx.right l)) * y)) := by
    intro i _
    have hli : ra.left i = algebraMap A K ((ℛ k a).left i) := by rw [halgK]; rfl
    have hsm : ra.left i * rx.left l = (ℛ k a).left i • rx.left l := by
      rw [Algebra.smul_def, hli]
    rw [hsm, TensorProduct.smul_tmul, Algebra.smul_def, halgH]
    congr 1
    rw [show j (fAK ((ℛ k a).left i)) = j (ra.left i) from rfl]
    simp only [HopfAlgebra.antipode_mul_distrib, map_mul]
    ring
  rw [Finset.sum_congr rfl step, ← TensorProduct.tmul_sum, ← Finset.sum_mul, ← map_sum,
    HopfAlgebra.sum_mul_antipode_eq_smul ra]
  have hc : Coalgebra.counit (R := k) (fAK a) = 0 := by
    rw [CoalgHomClass.counit_comp_apply (R := k) fAK, ha]
  rw [hc]
  simp

/-- `x ⊗ y ↦ ∑ x₍₁₎ ⊗ j(S x₍₂₎) y` kills `x ⊗ y` for every `x` in the ideal `A⁺K`. -/
lemma mixedInvProj_tmul_mem {x : K} (hx : x ∈ augIdealB k A K) (y : H) :
    mixedInvProj k A K H j (x ⊗ₜ[k] y) = 0 := by
  classical
  rw [augIdealB, Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, cc, gg, hsum⟩ := hx
  rw [← hsum, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨a, ha, hga⟩ := (gg i).2
  have hcc : cc i • ((gg i : K)) = fAK a * cc i := by
    rw [← hga, halgK a, smul_eq_mul, mul_comm]
  rw [hcc]
  exact mixedInvProj_augmentation_tmul j fAK halgK halgH a ha (cc i) y

/-- `mixedInvProj` factors through `H ⊗[k] (K/A⁺K)`. -/
lemma ker_quotLeft_le :
    LinearMap.ker (quotLeft k A K H) ≤ LinearMap.ker (mixedInvProj k A K H j) := by
  classical
  set J : Submodule k K := (augIdealB k A K).restrictScalars k with hJ
  have hex : Function.Exact (J.subtype) ((mkAug k A K).toLinearMap) := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      simpa [hJ, mkAug, Ideal.Quotient.eq_zero_iff_mem] using hx
    · rintro ⟨y, rfl⟩
      simp only [mkAug, Submodule.subtype_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact y.2
  have hex2 := rTensor_exact (f := J.subtype) (g := (mkAug k A K).toLinearMap) H hex
    mkAug_surjective
  have key : ∀ w : J ⊗[k] H, mixedInvProj k A K H j (LinearMap.rTensor H J.subtype w) = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul x y =>
      simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact mixedInvProj_tmul_mem j fAK halgK halgH x.2 y
    | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  intro z hz
  have hz' : LinearMap.rTensor H (mkAug k A K).toLinearMap z = 0 := by
    have := LinearMap.mem_ker.mp hz
    rw [quotLeft, LinearMap.comp_apply] at this
    exact (TensorProduct.comm k (QuotAug k A K) H).map_eq_zero_iff.mp this
  obtain ⟨w, hw⟩ := (hex2 z).mp hz'
  rw [LinearMap.mem_ker, ← hw]
  exact key w

/-- **Takeuchi's Lemma 3.9, the inverse map**: `Ψ : H ⊗[k] (K/A⁺K) → K ⊗[A] H`. -/
noncomputable def mixedInvTensor : H ⊗[k] QuotAug k A K →ₗ[k] K ⊗[A] H :=
  (Submodule.liftQ (LinearMap.ker (quotLeft k A K H)) (mixedInvProj k A K H j)
      (ker_quotLeft_le j fAK halgK halgH)) ∘ₗ
    ((quotLeft k A K H).quotKerEquivOfSurjective quotLeft_surjective).symm.toLinearMap

/-- `mixedInvTensor` composed with `quotLeft` is `mixedInvProj`. -/
@[simp] lemma mixedInvTensor_quotLeft (z : K ⊗[k] H) :
    mixedInvTensor j fAK halgK halgH (quotLeft k A K H z) = mixedInvProj k A K H j z := by
  have h : ((quotLeft k A K H).quotKerEquivOfSurjective quotLeft_surjective).symm
      (quotLeft k A K H z) = Submodule.Quotient.mk z :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  rw [mixedInvTensor, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]

/-- `mixedInvTensor` is a left inverse of `mixedTensor`. -/
lemma mixedInvTensor_mixedTensor (u : K ⊗[A] H) :
    mixedInvTensor j fAK halgK halgH (mixedTensor j fAK halgK halgH u) = u := by
  obtain ⟨z, rfl⟩ := mixedTensorProj_surjective (k := k) (A := A) (K := K) (H := H) u
  rw [mixedTensor_mixedTensorProj j fAK halgK halgH, mixedQuot_eq_quotLeft,
    mixedInvTensor_quotLeft j fAK halgK halgH, mixedInvProj, LinearMap.comp_apply]
  congr 1
  exact congr($(mixedGaloisInv_comp_mixedGalois j) z)

/-- `mixedInvTensor` is a right inverse of `mixedTensor`. -/
lemma mixedTensor_mixedInvTensor (v : H ⊗[k] QuotAug k A K) :
    mixedTensor j fAK halgK halgH (mixedInvTensor j fAK halgK halgH v) = v := by
  obtain ⟨z, rfl⟩ := quotLeft_surjective (k := k) (A := A) (K := K) (H := H) v
  rw [mixedInvTensor_quotLeft j fAK halgK halgH, mixedInvProj, LinearMap.comp_apply,
    mixedTensor_mixedTensorProj j fAK halgK halgH, mixedQuot_eq_quotLeft]
  congr 1
  exact congr($(mixedGalois_comp_mixedGaloisInv j) z)

/-- **Takeuchi's Lemma 3.9.**  For Hopf algebra maps `A → K → H` over a field `k`, the map
`x ⊗ y ↦ ∑ j(x₍₂₎) y ⊗ [x₍₁₎]` is an isomorphism `K ⊗[A] H ≅ H ⊗[k] (K / A⁺K)` of
`A`-modules. -/
noncomputable def mixedTensorEquiv : (K ⊗[A] H) ≃ₗ[A] H ⊗[k] QuotAug k A K :=
  LinearEquiv.ofBijective (mixedTensor j fAK halgK halgH)
    ⟨Function.LeftInverse.injective (mixedInvTensor_mixedTensor j fAK halgK halgH),
      Function.RightInverse.surjective (mixedTensor_mixedInvTensor j fAK halgK halgH)⟩

/-- The linear isomorphism `mixedTensorEquiv` agrees with the map `mixedTensor`. -/
@[simp] lemma mixedTensorEquiv_apply (u : K ⊗[A] H) :
    mixedTensorEquiv j fAK halgK halgH u = mixedTensor j fAK halgK halgH u := rfl

end Balanced

end HopfAlgebra.Commutative
end
