module

public import Hopf.CharZero.AssociatedGraded
public import Hopf.Commutative.PointDensity
public import Hopf.Commutative.PointTranslation
public import Hopf.Basic.AntipodeAlgHom
public import Hopf.Basic.HopfLocallyFinite
public import Hopf.Commutative.FaithfulFlatnessFiniteType

/-!
# Cartier's theorem: commutative Hopf algebras in characteristic zero are reduced

This file completes the proof of **Cartier's theorem**: a commutative Hopf algebra over a field of
characteristic zero is reduced.

The heart of the matter is in `Hopf/CharZero/TangentEstimate.lean` and
`Hopf/CharZero/AssociatedGraded.lean`, where it is shown that for a commutative bialgebra `A`
over a field of characteristic zero the associated graded algebra of the augmentation filtration is
a polynomial algebra; in particular a square-zero element lies in *every* power of the augmentation
ideal `I = ker ε` (`HopfAlgebra.CharZero.mem_pow_of_sq_eq_zero`).

Here this local statement is globalised; the last statement below discharges the hypothesis
`HopfAlgebra.Commutative.CharZeroReduced` used in `Hopf/Commutative/FaithfulFlatnessFiniteType.lean`
and `Hopf/Commutative/FaithfulFlatnessCharZero.lean`.

## Main results

* `HopfAlgebra.CharZero.eq_zero_of_mul_self_eq_zero`: over an algebraically closed field of
  characteristic zero, a finitely generated commutative Hopf algebra has no nonzero square-zero
  element. Given `y ≠ 0` with `y * y = 0`, the annihilator of `y` is a proper ideal, hence contained
  in a maximal ideal, which by the Nullstellensatz is the kernel of a point `u : A →ₐ[k] k`.
  Translating by `u ∘ S` (`HopfAlgebra.Commutative.translAlgEquiv`) moves this point to the unit
  point, so one may assume the annihilator of `y` to be contained in `I`; but then `y` lies in every
  power of `I`, contradicting the Krull intersection theorem.
* `HopfAlgebra.CharZero.isReduced_of_finiteType`: the same hypotheses give `IsReduced A`.
* `HopfAlgebra.CharZero.isReduced_of_finiteType_charZero`: the hypothesis that `k` be algebraically
  closed is removed by base change to the algebraic closure.
* `HopfAlgebra.CharZero.isReduced_charZero` and `HopfAlgebra.CharZero.charZeroReduced_holds`: the
  finiteness hypothesis is removed by local finiteness of commutative Hopf algebras.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 11.4
-/

@[expose] public section

universe u

section
open Coalgebra.Comodule HopfAlgebra.Commutative
namespace HopfAlgebra.CharZero

open TensorProduct _root_.Coalgebra HopfAlgebra.Commutative

/-! ## Reducedness from the absence of square-zero elements -/

/-- A commutative ring without nonzero square-zero elements is reduced. -/
theorem isReduced_of_forall_mul_self {A : Type*} [CommRing A]
    (h : ∀ y : A, y * y = 0 → y = 0) : IsReduced A := by
  have key : ∀ n : ℕ, ∀ x : A, x ^ n = 0 → x = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      match n, ih with
      | 0, _ =>
          rw [pow_zero] at hx
          have := subsingleton_of_zero_eq_one hx.symm
          exact Subsingleton.elim _ _
      | 1, _ => simpa using hx
      | (m + 2), ih =>
          set j := (m + 3) / 2 with hj
          have hjlt : j < m + 2 := by omega
          have hsq : x ^ j * x ^ j = 0 := by
            rw [← pow_add]
            have hrw : x ^ (j + j) = x ^ (m + 2) * x ^ (j + j - (m + 2)) := by
              rw [← pow_add]
              congr 1
              omega
            rw [hrw, hx, zero_mul]
          exact ih j hjlt x (h _ hsq)
  exact ⟨fun x ⟨n, hn⟩ => key n x hn⟩

/-! ## Translating a point to the unit point -/

/-- Evaluating a functional on a translate: `u (w ⇀ x) = (u ⋆ w) (x)`. -/
lemma apply_transl {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (u w : A →ₗ[k] k) (x : A) :
    u (Coalgebra.Comodule.transl w x) = Coalgebra.Comodule.convFun u w x := by
  have h : ∀ t : A ⊗[k] A,
      u ((TensorProduct.rid k A) (LinearMap.lTensor A w t))
        = (LinearMap.mul' k k) (TensorProduct.map u w t) := by
    intro t
    induction t with
    | tmul a b => simp [mul_comm]
    | add a b ha hb => simp [ha, hb]
  simpa [Coalgebra.Comodule.transl, Coalgebra.Comodule.convFun] using h (Coalgebra.comul (R := k) x)

/-- Translating by `u ∘ S` moves the point `u` to the counit: `u (τ x) = ε x`. -/
lemma apply_translAlgEquiv_comp_antipode {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (u : A →ₐ[k] k) (x : A) :
    u (HopfAlgebra.Commutative.translAlgEquiv (u.comp (HopfAlgebra.antipodeAlgHom k A)) x)
      = counit (R := k) x := by
  have hw : (u.comp (HopfAlgebra.antipodeAlgHom k A)).toLinearMap
      = u.toLinearMap ∘ₗ HopfAlgebra.antipode k := rfl
  have key := apply_transl u.toLinearMap
    ((u.comp (HopfAlgebra.antipodeAlgHom k A)).toLinearMap) x
  rw [hw] at key
  rw [HopfAlgebra.Commutative.translAlgEquiv_apply]
  refine key.trans ?_
  rw [HopfAlgebra.Commutative.convFun_comp_antipode_right u]

/-! ## The finitely generated case over an algebraically closed field -/

/-- **The key step in Cartier's theorem.**  A finitely generated commutative Hopf algebra over an
algebraically closed field of characteristic zero has no nonzero square-zero element. -/
theorem eq_zero_of_mul_self_eq_zero (k : Type*) {A : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] (y : A) (hy : y * y = 0) : y = 0 := by
  classical
  by_contra hy0
  have : Nontrivial A := nontrivial_of_ne y 0 hy0
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set I : Ideal A := augmentationIdeal k A with hI
  -- the annihilator of `y` is a proper ideal
  set J : Ideal A := LinearMap.ker (LinearMap.mulLeft A y) with hJ
  have hJmem : ∀ a : A, a ∈ J ↔ y * a = 0 := by
    intro a
    simp [hJ, LinearMap.mem_ker]
  have hJne : J ≠ ⊤ := by
    intro h
    have : y * 1 = 0 := (hJmem 1).1 (h ▸ Submodule.mem_top)
    exact hy0 (by simpa using this)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJne
  have := hm
  obtain ⟨u, hu⟩ := exists_algHom_ker_eq_of_isMaximal (k := k) m
  -- translate so that the point `u` becomes the unit point
  set tau : A ≃ₐ[k] A
      := HopfAlgebra.Commutative.translAlgEquiv (u.comp (HopfAlgebra.antipodeAlgHom k A)) with htau
  have hutau : ∀ x : A, u (tau x) = counit (R := k) x := fun x =>
    apply_translAlgEquiv_comp_antipode u x
  set z : A := tau.symm y with hz
  have htz : tau z = y := by rw [hz]; exact tau.apply_symm_apply y
  have hzsq : z * z = 0 := by
    apply tau.injective
    rw [map_mul, htz, hy, map_zero]
  -- the annihilator of `z` is contained in the augmentation ideal
  have hann : ∀ a : A, z * a = 0 → a ∈ I := by
    intro a ha
    have h1 : y * tau a = 0 := by
      rw [← htz, ← map_mul, ha, map_zero]
    have h2 : tau a ∈ m := hJm ((hJmem _).2 h1)
    have h3 : u (tau a) = 0 := (hu _).2 h2
    rw [hI, mem_augmentationIdeal, ← hutau a]
    exact h3
  -- `z` lies in every power of the augmentation ideal
  obtain ⟨F⟩ : Nonempty (Frame k A) := exists_frame (IsNoetherian.noetherian _)
  have hzpow : ∀ n : ℕ, z ∈ I ^ n := fun n => mem_pow_of_sq_eq_zero F hzsq n
  -- Krull's intersection theorem
  have hmemInf : z ∈ (⨅ i : ℕ, I ^ i • (⊤ : Submodule A A)) := by
    refine (Submodule.mem_iInf _).2 fun i => ?_
    have hsm : I ^ i • (⊤ : Submodule A A) = I ^ i := by
      rw [smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    rw [hsm]
    exact hzpow i
  obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff I z).1 hmemInf
  have hone : (1 : A) - (r : A) ∈ I := by
    refine hann _ ?_
    have hrz : (r : A) * z = z := by simpa [smul_eq_mul] using hr
    rw [mul_comm, sub_mul, one_mul, hrz, sub_self]
  have hI1 : (1 : A) ∈ I := by
    have := Ideal.add_mem I hone r.2
    simpa using this
  exact augmentationIdeal_ne_top k A (Ideal.eq_top_of_isUnit_mem _ hI1 isUnit_one)

/-- **Cartier's theorem, finitely generated case over an algebraically closed field.** -/
theorem isReduced_of_finiteType (k : Type*) {A : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] : IsReduced A :=
  isReduced_of_forall_mul_self (eq_zero_of_mul_self_eq_zero k)

/-! ## Removing the hypothesis that `k` is algebraically closed -/

/-- **Cartier's theorem, finitely generated case.** -/
theorem isReduced_of_finiteType_charZero (k : Type u) {A : Type u} [Field k] [CharZero k]
    [CommRing A] [HopfAlgebra k A] [Algebra.FiniteType k A] : IsReduced A := by
  have : CharZero (AlgebraicClosure k) :=
    charZero_of_injective_algebraMap (algebraMap k (AlgebraicClosure k)).injective
  have : IsReduced (AlgebraicClosure k ⊗[k] A) :=
    isReduced_of_finiteType (AlgebraicClosure k) (A := AlgebraicClosure k ⊗[k] A)
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[k] (AlgebraicClosure k) ⊗[k] A)
    (Algebra.TensorProduct.includeRight_injective <| FaithfulSMul.algebraMap_injective _ _)

/-! ## The general case -/

/-- **Cartier's theorem**: a commutative Hopf algebra over a field of characteristic zero is
reduced.  (Cartier; see [waterhouseIntroductionAffineGroup1979], Section 11.4.) -/
theorem isReduced_charZero (k : Type u) {A : Type u} [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] : IsReduced A := by
  classical
  refine ⟨fun x hx => ?_⟩
  obtain ⟨K, hK, hft,
      hmem⟩ := HopfAlgebra.LocallyFinite.exists_fg_isSubHopfAlgebra (k := k) ({x} : Finset A)
  have := hK
  have := hft
  have hxK : x ∈ K := hmem x (Finset.mem_singleton_self x)
  have : IsReduced (↥K) := isReduced_of_finiteType_charZero k (A := ↥K)
  obtain ⟨n, hn⟩ := hx
  have hpow : (⟨x, hxK⟩ : ↥K) ^ n = 0 := by
    ext
    simpa using hn
  have hz : (⟨x, hxK⟩ : ↥K) = 0 := IsNilpotent.eq_zero ⟨n, hpow⟩
  simpa using Subtype.ext_iff.1 hz

end HopfAlgebra.CharZero

namespace HopfAlgebra.CharZero

/-- **Cartier's theorem** in the form used throughout this development: the proposition
`HopfAlgebra.Commutative.CharZeroReduced` holds. -/
theorem charZeroReduced_holds : CharZeroReduced.{u} :=
  fun k K _ _ _ _ => HopfAlgebra.CharZero.isReduced_charZero k (A := K)

end HopfAlgebra.CharZero
end
