module

public import AffineGroupSchemes.CoexactQuotient
public import Hopf.Basic.HopfTensorQuotEquiv
public import AffineGroupSchemes.HopfPushout
public import Hopf.Commutative.AugIdeal

/-!
# A reflexive relation of affine group schemes is the kernel pair of its quotient

We keep the situation of `AffineGroupSchemes/CoexactSetup.lean`: `d₁, d₂ : H →ₐc[k] R` are the
two projections of a relation of affine group schemes with common retraction `e : R →ₐc[k] H`, and
`p = diffAlg d₁ d₂ : H →ₐ[k] R` is the difference morphism `x ↦ ∑ d₁(S x₍₁₎) d₂(x₍₂₎)`.

Let `I = ker p` and let `K` be a sub-Hopf algebra of `H` with `I = K⁺H` (which is what Takeuchi's
Theorem 4.3 provides, `I` being a normal Hopf ideal).  This file proves:

* `AffineGroupSchemes.Coexact.d₁_eq_d₂_of_mem_coinvLeft`: `d₁` and `d₂` agree on the coinvariants of
  `I`, hence on `K`;
* `AffineGroupSchemes.Coexact.bijective_diffQuotMul`: the map `H ⊗[k] (H/I) → R`,
  `a ⊗ [y] ↦ d₁(a) p(y)`, is bijective (this is Sweedler's isomorphism combined with
  `H/I ≅ R^{co H}`);
* `AffineGroupSchemes.Coexact.bijective_liftBialgHom`: consequently the canonical morphism
  `H ⊗[K] H → R`, `x ⊗ y ↦ d₁(x) d₂(y)`, is bijective — i.e. `Spec R` is the fibre product
  `Spec H ×_{Spec K} Spec H`, so the relation is the kernel pair of `Spec H → Spec K`.

The link between the two last statements is Waterhouse's isomorphism
`H ⊗[K] H ≅ H ⊗[k] (H/K⁺H)` of `Hopf/Basic/HopfTensorQuotEquiv.lean`.

## Main results

* `AffineGroupSchemes.Coexact.d₁_eq_d₂_of_mem_coinvLeft`: `d₁` and `d₂` agree on the coinvariants of
  `I`.
* `AffineGroupSchemes.Coexact.bijective_diffQuotMul`: the map `H ⊗[k] (H/I) → R`,
  `a ⊗ [y] ↦ d₁(a) p(y)`, is bijective.
* `AffineGroupSchemes.Coexact.bijective_liftBialgHom`: if `d₁` and `d₂` agree on `K`, the canonical
  map `H ⊗[K] H → R`, `x ⊗ y ↦ d₁(x) d₂(y)`, is bijective.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  4.3
* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.1.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979]
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace AffineGroupSchemes

open Coalgebra HopfAlgebra
namespace Coexact

universe u

variable {k H R : Type u} [CommRing k] [CommRing H] [CommRing R] [HopfAlgebra k H]
    [HopfAlgebra k R]

section Diff

variable (d₁ d₂ : H →ₐc[k] R)

/-- The linear map `Φ : H ⊗[k] H → R`, `a ⊗ y ↦ d₁(a) · p(y)`. -/
noncomputable def diffMul : H ⊗[k] H →ₗ[k] R :=
  (LinearMap.mul' k R) ∘ₗ
    (TensorProduct.map ((d₁ : H →ₐ[k] R).toLinearMap) (diffLin d₁ d₂))

/-- `Φ(Δ x) = d₂ x`: the fundamental identity of the difference morphism. -/
lemma diffMul_comul (x : H) : diffMul d₁ d₂ (comul (R := k) x) = d₂ x := by
  classical
  rw [← (ℛ k x).eq, map_sum]
  exact sum_d₁_mul_diff d₁ d₂ x (ℛ k x)

variable (I : Ideal H) (hI : ∀ x : H, x ∈ I ↔ diffLin d₁ d₂ x = 0)

/-- The difference morphism factored through `H/I`, `I = ker p`. -/
noncomputable def diffQuotAlg : (H ⧸ I) →ₐ[k] R :=
  Ideal.Quotient.liftₐ I (diffAlg d₁ d₂) fun a ha => (hI a).1 ha

/-- `diffQuotAlg` sends the class `[y]` to `p(y) = diffLin d₁ d₂ y`. -/
@[simp] lemma diffQuotAlg_mk (y : H) :
    diffQuotAlg d₁ d₂ I hI (Ideal.Quotient.mk I y) = diffLin d₁ d₂ y := rfl

/-- The factored difference morphism `diffQuotAlg : H/I →ₐ[k] R` is injective. -/
lemma diffQuotAlg_injective : Function.Injective (diffQuotAlg d₁ d₂ I hI) := by
  intro u v huv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  rw [diffQuotAlg_mk, diffQuotAlg_mk] at huv
  refine Ideal.Quotient.eq.2 ((hI _).2 ?_)
  rw [map_sub, huv, sub_self]

/-- The linear map `Φ̄ : H ⊗[k] (H/I) → R`, `a ⊗ [y] ↦ d₁(a) · p(y)`. -/
noncomputable def diffQuotMul : H ⊗[k] (H ⧸ I) →ₗ[k] R :=
  (LinearMap.mul' k R) ∘ₗ
    (TensorProduct.map ((d₁ : H →ₐ[k] R).toLinearMap) (diffQuotAlg d₁ d₂ I hI).toLinearMap)

/-- `Φ̄ (a ⊗ [y]) = d₁(a) · p(y)`. -/
@[simp] lemma diffQuotMul_tmul (a y : H) :
    diffQuotMul d₁ d₂ I hI (a ⊗ₜ[k] (Ideal.Quotient.mk I y)) = d₁ a * diffLin d₁ d₂ y := rfl

/-- `Φ̄` composed with `id ⊗ (H → H/I)` (`HopfAlgebra.lTensorQuot I`) is `Φ = diffMul d₁ d₂`. -/
lemma diffQuotMul_lTensorQuot (t : H ⊗[k] H) :
    diffQuotMul d₁ d₂ I hI (HopfAlgebra.lTensorQuot I t) = diffMul d₁ d₂ t := by
  induction t with
  | tmul a y => rfl
  | add u v hu hv => simp only [map_add, hu, hv]

include hI in
/-- **`d₁` and `d₂` agree on the coinvariants of `I = ker p`.** -/
lemma d₁_eq_d₂_of_mem_coinvLeft {x : H} (hx : x ∈ (HopfAlgebra.coinvLeft I : Subalgebra k H)) :
    d₁ x = d₂ x := by
  have h := congr(diffQuotMul d₁ d₂ I hI $((HopfAlgebra.mem_coinvLeft I).1 hx))
  rw [diffQuotMul_lTensorQuot, diffMul_comul] at h
  rw [show (1 : H ⧸ I) = Ideal.Quotient.mk I 1 from rfl, diffQuotMul_tmul, diffLin_one,
    mul_one] at h
  exact h.symm

end Diff

section HopfModules

variable {d₁ d₂ : H →ₐc[k] R} {e : R →ₐc[k] H}
  [Algebra H R] [IsScalarTower k H R] [RightComodule k H R] [HopfAlgebra.IsHopfModule k H R]
  (hsmul : ∀ (h : H) (r : R), h • r = d₁ (antipode k h) * r)
  (hcoact : ∀ r : R, Coalgebra.Comodule.coact (R := k) (C := H) r = coactAlg e r)
  (hd₂ : ∀ x, e (d₂ x) = x)
  (hjoint : Function.Surjective (jointAlg d₁ d₂))
  (I : Ideal H) (hI : ∀ x : H, x ∈ I ↔ diffLin d₁ d₂ x = 0)

include hsmul hcoact hd₂ in
/-- `diffQuotAlg` takes values in the coinvariants `R^{co H}`. -/
lemma diffQuotAlg_mem_coinv (u : H ⧸ I) :
    diffQuotAlg d₁ d₂ I hI u ∈ HopfAlgebra.coinv k H R := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [diffQuotAlg_mk]
  exact diff_mem_coinv hsmul hcoact hd₂ y

include hsmul hcoact hd₂ hjoint in
/-- **`H/I` is isomorphic to the coinvariants `R^{co H}`**, via the difference morphism. -/
noncomputable def diffQuotEquiv : (H ⧸ I) ≃ₗ[k] ↥(HopfAlgebra.coinv k H R) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (HopfAlgebra.coinv k H R) (diffQuotAlg d₁ d₂ I hI).toLinearMap
      (diffQuotAlg_mem_coinv hsmul hcoact hd₂ I hI))
    ⟨fun u v huv => diffQuotAlg_injective d₁ d₂ I hI (Subtype.ext_iff.mp huv), by
      rintro ⟨n, hn⟩
      obtain ⟨y, hy⟩ := coinv_le_range_diff hsmul hcoact hd₂ hjoint hn
      exact ⟨Ideal.Quotient.mk I y, Subtype.ext hy⟩⟩

include hsmul hcoact hd₂ hjoint in
/-- **The map `H ⊗[k] (H/I) → R`, `a ⊗ [y] ↦ d₁(a) p(y)`, is bijective**: it is Sweedler's
isomorphism `H ⊗[k] R^{co H} ≅ R` composed with `H/I ≅ R^{co H}`. -/
theorem bijective_diffQuotMul : Function.Bijective (diffQuotMul d₁ d₂ I hI) := by
  have key : ∀ t : H ⊗[k] (H ⧸ I),
      diffQuotMul d₁ d₂ I hI t
        = hopfModuleEquiv k H R
            (TensorProduct.congr (LinearEquiv.refl k H)
              (diffQuotEquiv hsmul hcoact hd₂ hjoint I hI) t) := by
    intro t
    induction t with
    | tmul a u =>
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
      rw [diffQuotMul_tmul, TensorProduct.congr_tmul, hopfModuleEquiv_tmul hsmul]
      rfl
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  have hbij : Function.Bijective
      (fun t : H ⊗[k] (H ⧸ I) => hopfModuleEquiv k H R
        (TensorProduct.congr (LinearEquiv.refl k H)
          (diffQuotEquiv hsmul hcoact hd₂ hjoint I hI) t)) :=
    (hopfModuleEquiv k H R).bijective.comp
      (TensorProduct.congr (LinearEquiv.refl k H)
        (diffQuotEquiv hsmul hcoact hd₂ hjoint I hI)).bijective
  exact (funext key ▸ hbij : _)

end HopfModules

section Pushout

variable [IsAbsFlat k] {d₁ d₂ : H →ₐc[k] R} {e : R →ₐc[k] H}
  [Algebra H R] [IsScalarTower k H R] [RightComodule k H R] [HopfAlgebra.IsHopfModule k H R]
  (hsmul : ∀ (h : H) (r : R), h • r = d₁ (antipode k h) * r)
  (hcoact : ∀ r : R, Coalgebra.Comodule.coact (R := k) (C := H) r = coactAlg e r)
  (hd₂ : ∀ x, e (d₂ x) = x)
  (hjoint : Function.Surjective (jointAlg d₁ d₂))
  (K : Subalgebra k H) [HopfAlgebra.IsSubHopfAlgebra k K]
  (hK : ∀ x : H, x ∈ HopfAlgebra.augIdealB k (↥K) H ↔ diffLin d₁ d₂ x = 0)

omit [Algebra H R] [IsScalarTower k H R] [RightComodule k H R] [HopfAlgebra.IsHopfModule k H R] in
/-- The Galois map computes `d₁(x) d₂(y)`. -/
lemma diffQuotMul_galoisQuot (x y : H) :
    diffQuotMul d₁ d₂ (HopfAlgebra.augIdealB k (↥K) H) hK
        (HopfAlgebra.galoisQuot k (↥K) H (x ⊗ₜ[k] y)) = d₁ x * d₂ y := by
  classical
  rw [HopfAlgebra.galoisQuot_tmul x y (ℛ k y), map_sum]
  have hterm : ∀ i ∈ (ℛ k y).index,
      diffQuotMul d₁ d₂ (HopfAlgebra.augIdealB k (↥K) H) hK
          ((x * (ℛ k y).left i) ⊗ₜ[k] HopfAlgebra.mkAug k (↥K) H ((ℛ k y).right i))
        = d₁ x * (d₁ ((ℛ k y).left i) * diffLin d₁ d₂ ((ℛ k y).right i)) := by
    intro i _
    rw [show HopfAlgebra.mkAug k (↥K) H ((ℛ k y).right i)
        = Ideal.Quotient.mk (HopfAlgebra.augIdealB k (↥K) H) ((ℛ k y).right i) from rfl,
      diffQuotMul_tmul, map_mul, mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_d₁_mul_diff d₁ d₂ y (ℛ k y)]

include hsmul hcoact hd₂ hjoint hK in
/-- **The relation is the fibre product**: the canonical morphism `H ⊗[K] H → R`,
`x ⊗ y ↦ d₁(x) d₂(y)`, is bijective. -/
theorem bijective_liftBialgHom
    (hcomm : ∀ a : ↥K, d₁ (HopfAlgebra.subInclusion (K := K) a)
      = d₂ (HopfAlgebra.subInclusion (K := K) a)) :
    letI := hopfAlgebraTensor (HopfAlgebra.subInclusion (K := K)) (HopfAlgebra.subInclusion (K
        := K))
      (fun _ => rfl) (fun _ => rfl)
    Function.Bijective (liftBialgHom (HopfAlgebra.subInclusion (K := K))
      (HopfAlgebra.subInclusion (K := K)) (fun _ => rfl) (fun _ => rfl) d₁ d₂ hcomm) := by
  let := hopfAlgebraTensor (HopfAlgebra.subInclusion (K := K)) (HopfAlgebra.subInclusion (K := K))
    (fun _ : ↥K => rfl) (fun _ : ↥K => rfl)
  have key : ∀ t : H ⊗[↥K] H,
      liftBialgHom (HopfAlgebra.subInclusion (K := K)) (HopfAlgebra.subInclusion (K := K))
          (fun _ => rfl) (fun _ => rfl) d₁ d₂ hcomm t
        = diffQuotMul d₁ d₂ (HopfAlgebra.augIdealB k (↥K) H) hK
            (HopfAlgebra.galoisTensor (HopfAlgebra.subInclusion (K := K)) (fun _ => rfl) t) := by
    intro t
    induction t with
    | tmul x y =>
      exact (diffQuotMul_galoisQuot (K := K) hK x y).symm
    | add s t hs ht => simp only [map_add, hs, ht]
  have hbij : Function.Bijective (fun t : H ⊗[↥K] H =>
      diffQuotMul d₁ d₂ (HopfAlgebra.augIdealB k (↥K) H) hK
        (HopfAlgebra.galoisTensor (HopfAlgebra.subInclusion (K := K)) (fun _ => rfl) t)) :=
    (bijective_diffQuotMul hsmul hcoact hd₂ hjoint _ hK).comp
      (HopfAlgebra.galoisTensorEquiv (HopfAlgebra.subInclusion (K := K)) (fun _ => rfl)).bijective
  exact (funext key ▸ hbij : _)

end Pushout

end Coexact
end AffineGroupSchemes
