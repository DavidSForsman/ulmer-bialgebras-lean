module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.PicardGroup
public import Hopf.Basic.HopfQuotAugHopf
public import Hopf.Commutative.FrobeniusSubHopf

/-!
# Nilpotence of the augmentation ideal of `K / K^(pʳ)⁺K`

Takeuchi's proof of Theorem 3.1 in characteristic `p` uses that, for a finitely generated
commutative Hopf algebra `K` over a perfect field of characteristic `p` and `A = K^(pʳ)`, the
quotient Hopf algebra `L = K / A⁺K` has *nilpotent* augmentation ideal: every `x ∈ K⁺` satisfies
`x^(pʳ) ∈ A⁺K`, so `L⁺` is a nil ideal of the noetherian ring `L`, hence nilpotent.

* `HopfAlgebra.Commutative.exists_augmentationIdeal_quotAug_pow_eq_bot`: the general statement, for
  any Hopf subalgebra `A ⊆ B` such that every element of `B⁺` has a power in `A⁺B`;
* `HopfAlgebra.Commutative.exists_frobQuot_augmentationIdeal_pow_eq_bot`: the case `A = K^(pʳ)`.

## Main results

* `HopfAlgebra.Commutative.exists_augmentationIdeal_quotAug_pow_eq_bot`: if `B / A⁺B` is noetherian
  and every `x ∈ B` with `ε x = 0` has a power that is `0` or lies in `A⁺B`, then some power of the
  augmentation ideal of `B / A⁺B` is `⊥`.
* `HopfAlgebra.Commutative.pow_mem_augIdealB_frobSubalgebra`: for `A = K^(pʳ)`, every `x ∈ K` with
  `ε x = 0` satisfies `x^(pʳ) ∈ A⁺K`.
* `HopfAlgebra.Commutative.exists_frobQuot_augmentationIdeal_pow_eq_bot`: for a finitely generated
  `K` over a perfect field of characteristic `p`, some power of the augmentation ideal of
  `K / K^(pʳ)⁺K` is `⊥`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Theorem
  3.1
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative HopfAlgebra.Commutative.Frobenius
namespace HopfAlgebra.Commutative

open TensorProduct Coalgebra HopfAlgebra.Commutative

section Nil

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
  [Algebra A B] [Fact (IsHopfIdeal k (augIdealB k A B))]

/-- If every element of `B⁺` has a power lying in `A⁺B`, then the augmentation ideal of
`C = B / A⁺B` consists of nilpotent elements. -/
theorem isNilpotent_of_mem_augmentationIdeal_quotAug
    (hpow : ∀ x : B, counit (R := k) x = 0 → ∃ n, x ^ n = 0 ∨ x ^ n ∈ augIdealB k A B)
    {u : QuotAug k A B} (hu : u ∈ augmentationIdeal k (QuotAug k A B)) : IsNilpotent u := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := augIdealB k A B) u
  have hx : counit (R := k) x = 0 := by
    have h := (HopfAlgebra.Commutative.mem_augmentationIdeal k (QuotAug k A B)).1 hu
    rwa [quotCounit_mk] at h
  obtain ⟨n, hn⟩ := hpow x hx
  refine ⟨n, ?_⟩
  rw [← map_pow]
  rcases hn with hn | hn
  · rw [hn, map_zero]
  · exact Ideal.Quotient.eq_zero_iff_mem.2 hn

/-- Under the same hypothesis, the augmentation ideal of `C = B / A⁺B` is nilpotent. -/
theorem exists_augmentationIdeal_quotAug_pow_eq_bot [IsNoetherianRing (QuotAug k A B)]
    (hpow : ∀ x : B, counit (R := k) x = 0 → ∃ n, x ^ n = 0 ∨ x ^ n ∈ augIdealB k A B) :
    ∃ n, (augmentationIdeal k (QuotAug k A B)) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := IsNoetherianRing.isNilpotent_nilradical (QuotAug k A B)
  refine ⟨n, le_antisymm ?_ bot_le⟩
  have hle : augmentationIdeal k (QuotAug k A B) ≤ nilradical (QuotAug k A B) := fun u hu =>
    isNilpotent_of_mem_augmentationIdeal_quotAug hpow hu
  calc (augmentationIdeal k (QuotAug k A B)) ^ n ≤ (nilradical (QuotAug k A B)) ^ n :=
        Ideal.pow_right_mono hle n
    _ = ⊥ := hn

end Nil

section Frobenius

open HopfAlgebra.Commutative.Frobenius

variable (k K : Type*) [Field k] [CommRing K] [HopfAlgebra k K] (p r : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p] [Nontrivial K]

/-- Every `x ∈ K⁺` satisfies `x^(pʳ) ∈ A⁺K` for `A = K^(pʳ)`: indeed `x^(pʳ)` lies in `A` and is
killed by the counit. -/
theorem pow_mem_augIdealB_frobSubalgebra (x : K)
    (hx : counit (R := k) x = 0) :
    x ^ (p ^ r) ∈ augIdealB k ↥(frobSubalgebra k K p r) K := by
  set A := frobSubalgebra k K p r with hA
  have hmem : x ^ (p ^ r) ∈ A := pow_mem_frobSubalgebra k K p r x
  have hcount : counit (R := k) (A := ↥A) (⟨x ^ (p ^ r), hmem⟩ : ↥A) = 0 := by
    rw [HopfAlgebra.subCounit_apply]
    change counit (R := k) (x ^ (p ^ r)) = 0
    rw [show counit (R := k) (x ^ (p ^ r)) = (counit (R := k) x) ^ (p ^ r) from
      map_pow (Bialgebra.counitAlgHom k K) x (p ^ r), hx,
      zero_pow (pow_ne_zero r (Fact.out : p.Prime).ne_zero)]
  have := mem_augIdealB (k := k) (A := ↥A) (B := K) ⟨x ^ (p ^ r), hmem⟩ hcount
  simpa using this

/-- **The augmentation ideal of `L = K / K^(pʳ)⁺K` is nilpotent** for a finitely generated
commutative Hopf algebra `K` over a perfect field of characteristic `p`. -/
theorem exists_frobQuot_augmentationIdeal_pow_eq_bot [Algebra.FiniteType k K]
    [Fact (IsHopfIdeal k (augIdealB k ↥(frobSubalgebra k K p r) K))] :
    ∃ n, (augmentationIdeal k (QuotAug k ↥(frobSubalgebra k K p r) K)) ^ n = ⊥ := by
  have : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  have : IsNoetherianRing (QuotAug k ↥(frobSubalgebra k K p r) K) :=
    isNoetherianRing_of_surjective K _ (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact exists_augmentationIdeal_quotAug_pow_eq_bot fun x hx =>
    ⟨p ^ r, Or.inr (pow_mem_augIdealB_frobSubalgebra k K p r x hx)⟩

end Frobenius

end HopfAlgebra.Commutative
end
