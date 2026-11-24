module

public import Hopf.Commutative.HopfMixedTensorQuot

/-!
# Naturality of Takeuchi's Lemma 3.9, and injectivity of `K/A⁺K → H/A⁺H`

Let `A → K → H` be morphisms of commutative Hopf algebras over a field `k`, with `A → K` and
`A → H` the induced algebra structures.  Takeuchi's Lemma 3.9
(`Hopf/Commutative/HopfMixedTensorQuot.lean`) gives isomorphisms
```
Φ_K : K ⊗[A] H ≅ H ⊗[k] (K/A⁺K),      Φ_H : H ⊗[A] H ≅ H ⊗[k] (H/A⁺H).
```
This file proves that they fit into a commutative square with the maps
`j ⊗ 1 : K ⊗[A] H → H ⊗[A] H` and `1 ⊗ q : H ⊗[k] (K/A⁺K) → H ⊗[k] (H/A⁺H)`, where
`q : K/A⁺K → H/A⁺H` is induced by `j`.

As a consequence (Takeuchi's proof of Theorem 3.1): if `H` is flat over `A` and `j` is injective,
then `q : K/A⁺K → H/A⁺H` is injective.

## Main results

* `HopfAlgebra.Commutative.quotAugMap`: the `k`-algebra map `q : K/A⁺K → H/A⁺H` induced by `j`.
* `HopfAlgebra.Commutative.mixedTensor_naturality`: `Φ_H ∘ (j ⊗ 1) = (1 ⊗ q) ∘ Φ_K` on `K ⊗[A] H`.
* `HopfAlgebra.Commutative.quotAugMap_injective`: if `H` is flat over `A`, `H` is faithfully flat
  over `k` and `j` is injective, then `q` is injective.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Lemma 3.9, Theorem 3.1
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra

variable {k A K H : Type*} [Field k] [CommRing A] [CommRing K] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k K] [HopfAlgebra k H]
  [Algebra A K] [Algebra A H]

variable (j : K →ₐc[k] H) (fAK : A →ₐc[k] K) (halgK : ∀ a, algebraMap A K a = fAK a)
  (halgH : ∀ a, algebraMap A H a = j (fAK a))

/-- The composite `A → K → H`, as a morphism of Hopf algebras. -/
noncomputable abbrev fAH : A →ₐc[k] H := (BialgHom.comp (j : K →ₐc[k] H) fAK)

include halgK halgH

/-- `j` maps the ideal `A⁺K` into the ideal `A⁺H`. -/
lemma map_augIdealB_le : (augIdealB k A K).map (j : K →ₐ[k] H) ≤ augIdealB k A H := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [augIdealB, Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, cc, gg, hsum⟩ := hx
  rw [Ideal.mem_comap, ← hsum, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha, hga⟩ := (gg i).2
  have hval : (j : K →ₐ[k] H) (cc i • ((gg i : K))) = j (cc i) * algebraMap A H a := by
    change j (cc i • ((gg i : K))) = _
    rw [← hga, halgK a, smul_eq_mul, map_mul, halgH a]
  rw [hval]
  exact Ideal.mul_mem_left _ _ (mem_augIdealB (B := H) a ha)

/-- The map `q : K/A⁺K → H/A⁺H` induced by `j`. -/
noncomputable def quotAugMap : QuotAug k A K →ₐ[k] QuotAug k A H :=
  Ideal.Quotient.liftₐ (augIdealB k A K) ((mkAug k A H).comp (j : K →ₐ[k] H)) <| by
    intro x hx
    have : (j : K →ₐ[k] H) x ∈ augIdealB k A H :=
      map_augIdealB_le j fAK halgK halgH (Ideal.mem_map_of_mem _ hx)
    simpa [mkAug, Ideal.Quotient.eq_zero_iff_mem] using this

/-- `quotAugMap [x] = [j x]`. -/
@[simp] lemma quotAugMap_mkAug (x : K) :
    quotAugMap j fAK halgK halgH (mkAug k A K x) = mkAug k A H (j x) := rfl

/-- `j : K → H` is `A`-linear. -/
noncomputable def jLinear : K →ₗ[A] H where
  toFun := j
  map_add' := map_add _
  map_smul' := fun a x => by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, halgK, halgH]

/-- `jLinear` is `j` as a map of `A`-modules: `jLinear x = j x`. -/
@[simp] lemma jLinear_apply (x : K) : jLinear j fAK halgK halgH x = j x := rfl

omit [Algebra A K] halgK in
/-- `halgH` with the composite `fAH j fAK` on the right: the form that `mixedTensor` for
`K = H` takes as its first compatibility hypothesis. -/
lemma algebraMap_eq_fAH (a : A) : algebraMap A H a = fAH j fAK a := halgH a

omit [Algebra A K] halgK in
/-- `halgH` with `BialgHom.id k H (fAH j fAK a)` on the right: the form that `mixedTensor` for
`K = H` takes as its second compatibility hypothesis. -/
lemma algebraMap_eq_id_fAH (a : A) : algebraMap A H a = BialgHom.id k H (fAH j fAK a) := halgH a

variable [IsScalarTower k A K] [IsScalarTower k A H]

/-- **The naturality square of Takeuchi's Lemma 3.9** ([Takeuchi1972]).  The isomorphisms
`Φ_K : K ⊗[A] H ≅ H ⊗[k] (K/A⁺K)` and `Φ_H : H ⊗[A] H ≅ H ⊗[k] (H/A⁺H)` are compatible with
`j ⊗ 1` and `1 ⊗ q`. -/
lemma mixedTensor_naturality (z : K ⊗[A] H) :
    mixedTensor (BialgHom.id k H) (fAH j fAK)
        (algebraMap_eq_fAH j fAK halgH) (algebraMap_eq_id_fAH j fAK halgH)
        (LinearMap.rTensor H (jLinear j fAK halgK halgH) z)
      = LinearMap.lTensor H (quotAugMap j fAK halgK halgH).toLinearMap
          (mixedTensor j fAK halgK halgH z) := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, jLinear_apply, mixedTensor_tmul, mixedTensor_tmul,
      mixedQuot_tmul _ x y (ℛ k x), mixedQuot_tmul _ (j x) y ((ℛ k x).induced j), map_sum]
    exact Finset.sum_congr rfl fun i _ => rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv, ← map_add, ← map_add]

/-- **Takeuchi's injectivity step** ([Takeuchi1972], proof of Theorem 3.1).  If `H` is flat over `A`
and `j : K → H` is injective, then the induced map `K/A⁺K → H/A⁺H` is injective. -/
theorem quotAugMap_injective [Module.Flat A H] [Module.FaithfullyFlat k H]
    (hj : Function.Injective j) :
    Function.Injective (quotAugMap j fAK halgK halgH) := by
  classical
  have h1 : Function.Injective (LinearMap.rTensor H (jLinear j fAK halgK halgH)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hj
  have h3 : Function.Injective
      (LinearMap.lTensor H (quotAugMap j fAK halgK halgH).toLinearMap) := by
    intro u v huv
    obtain ⟨u', rfl⟩ := (mixedTensorEquiv j fAK halgK halgH).surjective u
    obtain ⟨v', rfl⟩ := (mixedTensorEquiv j fAK halgK halgH).surjective v
    have key : LinearMap.rTensor H (jLinear j fAK halgK halgH) u'
        = LinearMap.rTensor H (jLinear j fAK halgK halgH) v' := by
      apply (mixedTensorEquiv (BialgHom.id k H) (fAH j fAK)
        (algebraMap_eq_fAH j fAK halgH) (algebraMap_eq_id_fAH j fAK halgH)).injective
      rw [mixedTensorEquiv_apply, mixedTensorEquiv_apply,
        mixedTensor_naturality j fAK halgK halgH, mixedTensor_naturality j fAK halgK halgH]
      exact huv
    exact congrArg _ (h1 key)
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective (R := k) (M := H)
    (N := QuotAug k A K) (N' := QuotAug k A H)
    (f := (quotAugMap j fAK halgK halgH).toLinearMap)).mp h3

end HopfAlgebra.Commutative
end
