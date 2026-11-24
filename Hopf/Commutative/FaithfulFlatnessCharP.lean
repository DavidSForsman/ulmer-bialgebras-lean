module

public import Hopf.Commutative.MixedDescent
public import Hopf.Commutative.PointDensity
public import Hopf.Commutative.FrobeniusQuotNilpotent
public import Hopf.Commutative.HopfNilpotentFaithfulFlat
public import Hopf.Basic.HopfQuotAugHopf

/-!
# Takeuchi's Theorem 3.1 in characteristic `p`

Let `k` be an algebraically closed field of characteristic `p > 0`, and let `j : K →ₐc[k] H` be an
injective morphism of finitely generated commutative Hopf `k`-algebras.  Takeuchi's argument
(*A correspondence between Hopf ideals and sub-Hopf algebras*, proof of Theorem 3.1) is:

* the Frobenius sub-Hopf algebra `A = K^(pʳ)` is *reduced* for `r` large
  (`HopfAlgebra.Commutative.Frobenius.exists_isReduced_frobSubalgebra`), so `H` is faithfully flat
  over `A` by Proposition 3.7 (`HopfAlgebra.Commutative.faithfullyFlat_of_isReduced`);
* the induced map of quotients `L = K/A⁺K → M = H/A⁺H` is injective
  (`HopfAlgebra.Commutative.quotAugMap_injective`), and `L` has *nilpotent* augmentation ideal
  (`HopfAlgebra.Commutative.exists_frobQuot_augmentationIdeal_pow_eq_bot`), so `M` is even free, in
  particular faithfully flat, over `L` by Waterhouse's §14.2
  (`HopfAlgebra.Commutative.faithfullyFlat_of_nilpotent_augmentation`);
* Takeuchi's Lemma 3.9 then transports faithful flatness back to `K ⊆ H`
  (`HopfAlgebra.Commutative.faithfullyFlat_of_quotAug_faithfullyFlat`).

The result is `HopfAlgebra.Commutative.faithfullyFlat_of_injective_of_charP`.

## Main results

* `HopfAlgebra.Commutative.faithfullyFlat_of_injective_of_charP`: over an algebraically closed field
  of characteristic `p`, an injective morphism `j : K →ₐc[k] H` of finitely generated commutative
  Hopf algebras makes `H` faithfully flat over `K`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1, Proposition 3.7 and Lemma 3.9
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapter 14
-/

@[expose] public section

section
open HopfAlgebra
namespace HopfAlgebra.Commutative

open TensorProduct _root_.Coalgebra HopfAlgebra.Commutative HopfAlgebra.Commutative.Frobenius

universe u

/-- A Hopf algebra over a field is a nonzero ring. -/
lemma nontrivial_of_hopfAlgebra (k B : Type*) [Field k] [CommRing B] [HopfAlgebra k B] :
    Nontrivial B := by
  refine (subsingleton_or_nontrivial B).resolve_left fun hB => ?_
  have h0 : Coalgebra.counit (R := k) (1 : B) = Coalgebra.counit (R := k) (0 : B) := by
    congr 1; exact Subsingleton.elim _ _
  rw [Bialgebra.counit_one, map_zero] at h0
  exact one_ne_zero h0

/-- **Takeuchi's Theorem 3.1 in characteristic `p`** [Takeuchi1972].  Over an algebraically closed
field of characteristic `p`, a finitely generated commutative Hopf algebra `H` is faithfully flat
over any finitely generated Hopf subalgebra `K`. -/
theorem faithfullyFlat_of_injective_of_charP
    {k K H : Type u} [Field k] [IsAlgClosed k] [CommRing K] [CommRing H]
    [HopfAlgebra k K] [HopfAlgebra k H] [Algebra.FiniteType k K] [Algebra.FiniteType k H]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    [Algebra K H] [IsScalarTower k K H]
    (j : K →ₐc[k] H) (halgKH : ∀ x, algebraMap K H x = j x)
    (hinj : Function.Injective j) :
    Module.FaithfullyFlat K H := by
  have : Nontrivial K := nontrivial_of_hopfAlgebra k K
  have : Nontrivial H := nontrivial_of_hopfAlgebra k H
  have : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  have : ExpChar k p := ExpChar.prime (Fact.out : p.Prime)
  have : PerfectRing k p := inferInstance
  obtain ⟨r, hred⟩ := exists_isReduced_frobSubalgebra k K p
  have := hred
  set A : Subalgebra k K := frobSubalgebra k K p r with hA
  have : Algebra.FiniteType k ↥A := finiteType_frobSubalgebra k K p r
  have : IsNoetherianRing ↥A := Algebra.FiniteType.isNoetherianRing k ↥A
  have : Nontrivial ↥A := nontrivial_of_hopfAlgebra k ↥A
  -- the inclusion `A ⊆ K` and the composite `A → H`
  set fAK : (↥A) →ₐc[k] K := HopfAlgebra.subInclusion with hfAK
  have halgK : ∀ a : ↥A, algebraMap (↥A) K a = fAK a := fun _ => rfl
  have halgH : ∀ a : ↥A, algebraMap (↥A) H a = j (fAK a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply (↥A) K H a, halgKH]
    rfl
  -- Proposition 3.7: `H` is faithfully flat over the reduced Hopf subalgebra `A`
  set φ : (↥A) →ₐc[k] H := BialgHom.comp (j : K →ₐc[k] H) fAK with hφ
  have hφinj : Function.Injective φ := hinj.comp HopfAlgebra.subInclusion_injective
  have hφalg : ∀ x : ↥A, φ x = algebraMap (↥A) H x := fun a => (halgH a).symm
  have : Module.FaithfullyFlat (↥A) H :=
    faithfullyFlat_of_isReduced φ hφalg
      (by intro a b hab; exact hφinj (by rw [hφalg, hφalg, hab]))
  -- the quotients `L = K/A⁺K` and `M = H/A⁺H` are Hopf algebras
  have : Fact (IsHopfIdeal k (augIdealB k (↥A) K)) := fact_isHopfIdeal_augIdealB fAK halgK
  have : Fact (IsHopfIdeal k (augIdealB k (↥A) H)) :=
    fact_isHopfIdeal_augIdealB φ (fun a => (hφalg a).symm)
  have : Module.FaithfullyFlat k H := HopfAlgebra.Commutative.faithfullyFlat_over_base
  set q : QuotAug k (↥A) K →ₐc[k] QuotAug k (↥A) H := quotAugBialgHom j fAK halgK halgH with hq
  have hqinj : Function.Injective q := quotAugMap_injective j fAK halgK halgH hinj
  let : Algebra (QuotAug k (↥A) K) (QuotAug k (↥A) H) := algebraOfBialgHom q
  have hqalg : ∀ u, algebraMap (QuotAug k (↥A) K) (QuotAug k (↥A) H) u = q u := fun _ => rfl
  have : IsScalarTower k (QuotAug k (↥A) K) (QuotAug k (↥A) H) :=
    .of_algebraMap_eq fun c => ((q : QuotAug k (↥A) K →ₐ[k] QuotAug k (↥A) H).commutes c).symm
  -- Waterhouse §14.2: the augmentation ideal of `L` is nilpotent, so `M` is free over `L`
  obtain ⟨n, hn⟩ := exists_frobQuot_augmentationIdeal_pow_eq_bot k K p r
  have : Nontrivial (QuotAug k (↥A) H) := nontrivial_of_hopfAlgebra k _
  have : Module.FaithfullyFlat (QuotAug k (↥A) K) (QuotAug k (↥A) H) :=
    faithfullyFlat_of_nilpotent_augmentation q hqalg hqinj hn
  -- Takeuchi's Lemma 3.9 transports faithful flatness back to `K ⊆ H`
  exact faithfullyFlat_of_quotAug_faithfullyFlat j fAK halgK halgH halgKH hqalg

end HopfAlgebra.Commutative
end
