module

public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.HopfQuotient
public import Hopf.Commutative.HopfMixedSquare

/-!
# `A⁺B` is a Hopf ideal, and `B / A⁺B` is a Hopf algebra

Let `f : A →ₐc[k] B` be a morphism of commutative Hopf algebras over a field `k` making `B` an
`A`-algebra.  This file shows that the ideal `A⁺B` (`HopfAlgebra.augIdealB`) is a Hopf ideal, so
that by `Hopf/Basic/HopfQuotient.lean` the quotient `C = B / A⁺B`
(`HopfAlgebra.QuotAug`) is a Hopf algebra and `B → C` is a morphism of Hopf algebras.

Moreover, for `A → K → H` the induced map `K/A⁺K → H/A⁺H` of
`Hopf/Commutative/HopfMixedSquare.lean` is a morphism of Hopf algebras.

## Main results

* `HopfAlgebra.isHopfIdeal_augIdealB`: for `f : A →ₐc[k] B` inducing the `A`-algebra structure
  of `B`, the ideal `A⁺B` is a Hopf ideal of `B`.
* `HopfAlgebra.quotAugBialgHom`: for `A → K → H`, the induced map `K/A⁺K → H/A⁺H` as a morphism
  of bialgebras.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 14.2
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra

open TensorProduct Coalgebra HopfAlgebra.Commutative

section HopfIdeal

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [HopfAlgebra k A]
    [HopfAlgebra k B]
  [Algebra A B] (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)

include halg

/-- `A⁺B` lies in the kernel of the counit of `B`. -/
theorem augIdealB_le_ker_counit :
    augIdealB k A B ≤ RingHom.ker (Bialgebra.counitAlgHom k B) := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  rw [show (Bialgebra.counitAlgHom k B) (algebraMap A B a) = counit (R := k) (f a) by
    rw [halg]; rfl, CoalgHomClass.counit_comp_apply (R := k) f]
  exact (HopfAlgebra.Commutative.mem_augmentationIdeal k A).1 ha

/-- The antipode of `B` maps `A⁺B` into itself. -/
theorem augIdealB_le_comap_antipode :
    augIdealB k A B ≤ Ideal.comap (HopfAlgebra.antipodeAlgHom k B) (augIdealB k A B) := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  simp only [Ideal.mem_comap]
  have h1 : HopfAlgebra.antipodeAlgHom k B (algebraMap A B a)
      = algebraMap A B (antipode k a) := by
    rw [halg, halg, HopfAlgebra.antipodeAlgHom_apply]
    exact antipode_bialgHom_apply f a
  rw [h1]
  refine mem_augIdealB (B := B) (antipode k a) ?_
  rw [HopfAlgebra.counit_antipode (R := k) a]
  exact (HopfAlgebra.Commutative.mem_augmentationIdeal k A).1 ha

/-- **`A⁺B` is a Hopf ideal.** -/
theorem isHopfIdeal_augIdealB [IsScalarTower k A B] : IsHopfIdeal k (augIdealB k A B) := by
  apply IsHopfIdeal.mk
  -- the counit and the antipode: the two lemmas above
  case hc => exact fun x hx => augIdealB_le_ker_counit f halg hx
  case hs => exact fun x hx => augIdealB_le_comap_antipode f halg hx
  case hd =>
    -- the comultiplication: `ψ = (π ⊗ π) ∘ Δ` kills the generators `a ∈ A⁺` of `A⁺B`
    set ψ : B →ₐ[k] (B ⧸ augIdealB k A B) ⊗[k] (B ⧸ augIdealB k A B) :=
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (augIdealB k A B))
        (Ideal.Quotient.mkₐ k (augIdealB k A B))).comp (Bialgebra.comulAlgHom k B) with hψ
    have hle : augIdealB k A B ≤ RingHom.ker ψ := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      simp only [Ideal.mem_comap, RingHom.mem_ker]
      -- `ψ a = ∑ π(a₁) ⊗ π(a₂)`
      have hcomul : ψ (algebraMap A B a)
          = ∑ i ∈ (ℛ k a).index, (mkAug k A B (f ((ℛ k a).left i))) ⊗ₜ[k]
              (mkAug k A B (f ((ℛ k a).right i))) := by
        rw [hψ, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, halg, show comul (R := k) (f a)
            = ∑ i ∈ (ℛ k a).index, f ((ℛ k a).left i) ⊗ₜ[k] f ((ℛ k a).right i) from
          ((ℛ k a).induced f).eq.symm, map_sum]
        rfl
      -- `π(a₁) = ε(a₁)`, since `A` acts on `B / A⁺B` through the counit
      have hstep : ∀ i ∈ (ℛ k a).index,
          (mkAug k A B (f ((ℛ k a).left i))) ⊗ₜ[k] (mkAug k A B (f ((ℛ k a).right i)))
            = (counit (R := k) ((ℛ k a).left i)) •
                ((1 : B ⧸ augIdealB k A B) ⊗ₜ[k] (mkAug k A B (f ((ℛ k a).right i)))) := by
        intro i _
        rw [show mkAug k A B (f ((ℛ k a).left i))
            = (counit (R := k) ((ℛ k a).left i)) • (1 : B ⧸ augIdealB k A B) by
          rw [← halg, mkAug_algebraMap, Algebra.algebraMap_eq_smul_one],
          TensorProduct.smul_tmul']
      rw [hcomul, Finset.sum_congr rfl hstep]
      -- so `ψ a = 1 ⊗ π(∑ ε(a₁) a₂) = 1 ⊗ π(a) = 1 ⊗ ε(a) = 0`
      have : ∑ i ∈ (ℛ k a).index, (counit (R := k) ((ℛ k a).left i)) •
          ((1 : B ⧸ augIdealB k A B) ⊗ₜ[k] (mkAug k A B (f ((ℛ k a).right i))))
          = (1 : B ⧸ augIdealB k A B) ⊗ₜ[k]
              (mkAug k A B (f (∑ i ∈ (ℛ k a).index,
                (counit (R := k) ((ℛ k a).left i)) • (ℛ k a).right i))) := by
        rw [map_sum, map_sum, TensorProduct.tmul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [map_smul, map_smul, TensorProduct.tmul_smul]
      rw [this, Coalgebra.sum_counit_smul (ℛ k a), ← halg, mkAug_algebraMap,
        (HopfAlgebra.Commutative.mem_augmentationIdeal k A).1 ha]
      simp
    intro x hx
    exact hle hx

/-- The `Fact` instance needed to put the quotient Hopf algebra structure on `B / A⁺B`. -/
lemma fact_isHopfIdeal_augIdealB [IsScalarTower k A B] : Fact (IsHopfIdeal k (augIdealB k A B)) :=
  ⟨isHopfIdeal_augIdealB f halg⟩

end HopfIdeal

section QuotMap

variable {k A K H : Type*} [Field k] [CommRing A] [CommRing K] [CommRing H]
  [HopfAlgebra k A] [HopfAlgebra k K] [HopfAlgebra k H]
  [Algebra A K] [Algebra A H] [IsScalarTower k A K] [IsScalarTower k A H]
  (j : K →ₐc[k] H) (fAK : A →ₐc[k] K) (halgK : ∀ a, algebraMap A K a = fAK a)
  (halgH : ∀ a, algebraMap A H a = j (fAK a))
  [Fact (IsHopfIdeal k (augIdealB k A K))] [Fact (IsHopfIdeal k (augIdealB k A H))]

include halgK halgH

/-- The induced map `K/A⁺K → H/A⁺H` is a morphism of Hopf algebras. -/
noncomputable def quotAugBialgHom : QuotAug k A K →ₐc[k] QuotAug k A H :=
  BialgHom.ofAlgHom (quotAugMap j fAK halgK halgH)
    (by
      refine AlgHom.ext fun u => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := augIdealB k A K) u
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
      rw [show quotAugMap j fAK halgK halgH (Ideal.Quotient.mk _ x)
          = Ideal.Quotient.mk (augIdealB k A H) (j x) from rfl, quotCounit_mk, quotCounit_mk]
      exact CoalgHomClass.counit_comp_apply (R := k) j x)
    (by
      have key : ∀ t : K ⊗[k] K,
          (Algebra.TensorProduct.map (quotAugMap j fAK halgK halgH)
              (quotAugMap j fAK halgK halgH)) (quotMap2 k (augIdealB k A K) t)
            = quotMap2 k (augIdealB k A H)
                (Algebra.TensorProduct.map (j : K →ₐ[k] H) (j : K →ₐ[k] H) t) := by
        intro t
        induction t with
        | tmul x y => rfl
        | add p q hp hq => simp only [map_add, hp, hq]
      refine AlgHom.ext fun u => ?_
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := augIdealB k A K) u
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
      rw [quotComul_mk, key, show quotAugMap j fAK halgK halgH (Ideal.Quotient.mk _ x)
          = Ideal.Quotient.mk (augIdealB k A H) (j x) from rfl, quotComul_mk]
      congr 1
      rw [← CoalgHomClass.map_comp_comul_apply (R := k) j x]
      generalize (comul (R := k) x : K ⊗[k] K) = t
      induction t with
      | tmul a b => rfl
      | add p q hp hq => simp only [map_add, hp, hq])

end QuotMap

end HopfAlgebra
end
