module

public import Hopf.Commutative.AugSpanPow
public import Hopf.Commutative.AugSpanCases
public import Hopf.Commutative.PointSpan
public import Hopf.Commutative.WeightDecomposition
public import Hopf.Commutative.FrobeniusSubHopf
public import Hopf.Commutative.PointDensity
public import Hopf.CharZero.Reduced

/-!
# Takeuchi's Lemma 4.15: the character functional

Let `H` be a finitely generated commutative Hopf algebra over an algebraically closed field `k` and
let `I` be a normal Hopf ideal of `H`. This file proves the last remaining input of the surjectivity
half of Takeuchi's Theorem 4.3, namely `HopfAlgebra.Commutative.HasCharacterFunctionalPow`: for
every element `g` which is group-like modulo `I`, some power `g^q` is the character of a
one-dimensional *quotient* of a finite-dimensional comodule.

The argument is Takeuchi's.  Replacing `g` by `g^q` for a suitable power of the characteristic
exponent (his Remark 4.14) one may assume that `g` lies in a *reduced* sub-Hopf algebra `K` of
`H` — the Frobenius sub-Hopf algebra `H^(pʳ)` in characteristic `p`, and `H` itself in
characteristic zero, by Cartier's theorem.  The comultiplication of `g` then lands in `H ⊗ V` for
a finite-dimensional subspace `V` of `K`, on which the points of `H` separate (Lemma 3.6); so by
Lemma 3.5 the finite-dimensional comodule `U = H* ⇀ g` of all translates of `g` is spanned by the
translates of `g` by *points* of `H`.  Each such translate is relatively invariant modulo `I`
with a conjugated character — this is where the normality of `I` enters — so `U` decomposes into
weight spaces, and the weight of `g` itself is cut out by a functional.

## Main results

* `HopfAlgebra.Commutative.exists_isReduced_subHopf_pow_mem`: a power of any element lies in a
  reduced sub-Hopf algebra;
* `HopfAlgebra.Commutative.hasCharacterFunctionalPow_of_isAlgClosed`: **Takeuchi's Lemma 4.15**;
* `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_of_isAlgClosed_of_finiteType`: consequently
  **the surjectivity half of Takeuchi's Theorem 4.3** for a finitely generated commutative Hopf
  algebra over an algebraically closed field.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 3.5, 3.6 and 4.15, Remark 4.14, Theorem 4.3
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 11.4 (Cartier's theorem)
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- **A power of any element lies in a reduced sub-Hopf algebra.**  In characteristic zero this
is Cartier's theorem (with `q = 1` and `K = H`); in characteristic `p` one takes the Frobenius
sub-Hopf algebra `K = H^(pʳ)` for `r` large and `q = pʳ`. -/
theorem exists_isReduced_subHopf_pow_mem [IsAlgClosed k] [Algebra.FiniteType k H] (g : H) :
    ∃ (q : ℕ) (K : Subalgebra k H), 0 < q ∧ IsSubHopfAlgebra k K ∧ IsReduced ↥K ∧ g ^ q ∈ K := by
  classical
  have : Nontrivial H := HopfAlgebra.Commutative.nontrivial_of_hopfAlgebra k H
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases (CharP.char_is_prime_or_zero k p) with hprime | hzero
  · -- positive characteristic: the Frobenius sub-Hopf algebra `H^(pʳ)`
    have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨r, hr⟩ := HopfAlgebra.Commutative.Frobenius.exists_isReduced_frobSubalgebra k H p
    exact ⟨p ^ r, HopfAlgebra.Commutative.Frobenius.frobSubalgebra k H p r, pow_pos hprime.pos r,
      HopfAlgebra.Commutative.Frobenius.isSubHopfAlgebra_frobSubalgebra k H p r, hr,
      HopfAlgebra.Commutative.Frobenius.pow_mem_frobSubalgebra k H p r g⟩
  · -- characteristic zero: Cartier's theorem says that `H` itself is reduced
    subst hzero
    have : CharZero k := CharP.charP_to_charZero k
    have : IsReduced H := HopfAlgebra.CharZero.isReduced_charZero k (A := H)
    have : IsReduced ↥(⊤ : Subalgebra k H) :=
      isReduced_of_injective (⊤ : Subalgebra k H).val Subtype.val_injective
    exact ⟨1, ⊤, one_pos, HopfAlgebra.Commutative.isSubHopfAlgebra_top, ‹_›, by simp⟩

/-- The coaction of an element of a sub-Hopf algebra `K` lands in `H ⊗ V` for a
finite-dimensional subspace `V` of `K`. -/
theorem exists_finite_subspace_coact_mem {K : Subalgebra k H} [hK : IsSubHopfAlgebra k K] {x : H}
    (hx : x ∈ K) :
    ∃ V : Submodule k H, V ≤ K.toSubmodule ∧ Module.Finite k ↥V ∧
      coact (R := k) (C := H) x ∈ LinearMap.range (LinearMap.lTensor H V.subtype) := by
  classical
  obtain ⟨t, ht⟩ := hK.comul_mem x hx
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset t
  set V : Submodule k H :=
    Submodule.span k ((fun p : ↥(Subalgebra.toSubmodule K) × ↥(Subalgebra.toSubmodule K) =>
      ((p.2 : H))) '' (↑S : Set (↥(Subalgebra.toSubmodule K) × ↥(Subalgebra.toSubmodule K))))
      with hV
  have hmem : ∀ p ∈ S, ((p.2 : H)) ∈ V := fun p hp => Submodule.subset_span ⟨p, hp, rfl⟩
  refine ⟨V, ?_, ?_, ?_⟩
  · rw [hV, Submodule.span_le]
    rintro _ ⟨p, -, rfl⟩
    exact p.2.2
  · exact Module.Finite.span_of_finite k (S.finite_toSet.image _)
  · refine ⟨∑ p ∈ S.attach, ((p.1.1 : H)) ⊗ₜ[k] (⟨((p.1.2 : H)), hmem p.1 p.2⟩ : ↥V), ?_⟩
    rw [map_sum]
    have hstep : ∀ p ∈ S.attach,
        LinearMap.lTensor H V.subtype (((p.1.1 : H)) ⊗ₜ[k] (⟨((p.1.2 : H)), hmem p.1 p.2⟩ : ↥V))
          = ((p.1.1 : H)) ⊗ₜ[k] ((p.1.2 : H)) := by
      intro p _
      simp
    rw [Finset.sum_congr rfl hstep, Finset.sum_attach S
      (fun p : ↥(Subalgebra.toSubmodule K) × ↥(Subalgebra.toSubmodule K) =>
        ((p.1 : H)) ⊗ₜ[k] ((p.2 : H)))]
    rw [Coalgebra.Comodule.coact_self, ← ht, hS, map_sum]
    rfl

/-- Relative invariance of a vector of a subcomodule is relative invariance in the ambient
comodule. -/
theorem isRelInvMod_subComodule_iff {M : Type u} [AddCommGroup M] [Module k M]
    [RightComodule k H M] {N : Submodule k M} (hN : IsSubcomodule (C := H) N)
    (I : Ideal H) (x : ↥N) (g : H) :
    letI : RightComodule k H ↥N := Coalgebra.Comodule.subComodule hN
    IsRelInvMod k I x g ↔ IsRelInvMod k I (x : M) g := by
  let : RightComodule k H ↥N := Coalgebra.Comodule.subComodule hN
  have key : ∀ z : ↥N ⊗[k] H,
      LinearMap.rTensor (H ⧸ I) N.subtype
          (LinearMap.lTensor ↥N (Ideal.Quotient.mkₐ k I).toLinearMap z)
        = LinearMap.lTensor M (Ideal.Quotient.mkₐ k I).toLinearMap
            (LinearMap.rTensor H N.subtype z) := by
    intro z
    induction z with
    | tmul a b => simp
    | add p q hp hq => simp only [map_add, hp, hq]
  have hco : LinearMap.rTensor H N.subtype (coact (R := k) (C := H) x)
      = coact (R := k) (C := H) (x : M) := Coalgebra.Comodule.rTensor_subtype_subCoact hN x
  constructor
  · intro h
    have h2 := congr(LinearMap.rTensor (H ⧸ I) N.subtype $h)
    rwa [key, hco, LinearMap.rTensor_tmul] at h2
  · intro h
    refine Coalgebra.Comodule.rTensor_subtype_injective (C := H ⧸ I) N ?_
    rw [key, hco, LinearMap.rTensor_tmul]
    exact h

/-- Lifting a finite spanning set of point-translates of `x` from `H` to `translSpan x`. -/
private lemma translSpan_eq_top_of_span_translPoint {x : H} {N : ℕ} {U : Fin N → (H →ₐ[k] k)}
    (hUspan : Submodule.span k (Set.range fun i => translPoint (U i) x) =
      Coalgebra.Comodule.translSpan (k := k) (C := H) x) :
    let T := Coalgebra.Comodule.translSpan (k := k) (C := H) x
    ∃ s : Fin N → ↥T, (∀ i, (s i : H) = translPoint (U i) x) ∧
      Submodule.span k (Set.range s) = ⊤ := by
  intro T
  have hmemT : ∀ i : Fin N, translPoint (U i) x ∈ T := fun i => by
    change translPoint (U i) x ∈ Coalgebra.Comodule.translSpan (k := k) (C := H) x
    rw [← hUspan]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨fun i => ⟨translPoint (U i) x, hmemT i⟩, fun _ => rfl, eq_top_iff.2 ?_⟩
  rintro y -
  have hy : (y : H) ∈ Submodule.span k (Set.range fun i => translPoint (U i) x) := by
    rw [hUspan]; exact y.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨cf, hcf⟩ := hy
  have hysum : y = ∑ i, cf i • (⟨translPoint (U i) x, hmemT i⟩ : ↥T) := by
    refine Subtype.ext ?_
    rw [← hcf]
    push_cast
    rfl
  rw [hysum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Replacing the character of a relatively invariant element by one that is group-like
modulo `I` (taking `1` when the element is `0`). -/
private lemma exists_groupLike_weight_of_isRelInvMod [IsAlgClosed k]
    {I : Ideal H} [Fact (IsHopfIdeal k I)]
    {V : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V] [Module.Projective k V]
    {v : V} {a : H} (hv : IsRelInvMod k I v a) :
    ∃ c : H, IsGroupLikeElem k (Ideal.Quotient.mk I c) ∧ IsRelInvMod k I v c := by
  by_cases h0 : v = 0
  · refine ⟨1, ?_, ?_⟩
    · rw [map_one]; exact IsGroupLikeElem.one
    · rw [IsRelInvMod, h0, map_zero, map_zero, TensorProduct.zero_tmul]
  · obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one k h0
    obtain ⟨c, hc1, hc2, hc3⟩ := exists_groupLikeMod_of_isRelInvMod hv hχ
    exact ⟨c, isGroupLikeElem_mk_of_lTensorQuot I hc1 hc2, hc3⟩

/-- **Takeuchi's Lemma 4.15** [Takeuchi1972].  Over an algebraically closed field, every element
which is group-like modulo a normal Hopf ideal of a finitely generated commutative Hopf algebra has
a power which is the character of a one-dimensional quotient of a finite-dimensional comodule. -/
theorem hasCharacterFunctionalPow_of_isAlgClosed [IsAlgClosed k] [Algebra.FiniteType k H] :
    HasCharacterFunctionalPow k H := by
  classical
  intro I hI g hgc hgcomul
  -- a power `x = g ^ q` lies in a reduced sub-Hopf algebra `K`, and is group-like modulo `I`
  have : Fact (IsHopfIdeal k I) := ⟨hI.toIsHopfIdeal⟩
  have : Nontrivial H := HopfAlgebra.Commutative.nontrivial_of_hopfAlgebra k H
  obtain ⟨q, K, hq, hKsub, hKred, hxK⟩ := exists_isReduced_subHopf_pow_mem (k := k) (H := H) g
  have := hKsub
  set x : H := g ^ q with hx
  have hglx : IsGroupLikeElem k (Ideal.Quotient.mk I x) := by
    rw [hx, map_pow]
    exact (isGroupLikeElem_mk_of_lTensorQuot I hgc hgcomul).pow
  have hrelx : IsRelInvMod k I x x :=
    isRelInvMod_self_pow (isRelInvMod_self_iff.2 hgcomul) q
  have hx0 : x ≠ 0 := by
    intro h0
    have hp : Coalgebra.counit (R := k) (A := H) x = 1 := by
      have hpow : (Bialgebra.counitAlgHom k H) (g ^ q) = ((Bialgebra.counitAlgHom k H) g) ^ q :=
        map_pow _ _ _
      simp only [Bialgebra.counitAlgHom_apply] at hpow
      rw [hx, hpow, hgc, one_pow]
    rw [h0, map_zero] at hp
    exact zero_ne_one hp
  -- `x` lies in a finite-dimensional subspace `V ⊆ K` closed under the coaction, on which the
  -- points separate (`K` is reduced); so the translates of `x` by finitely many points span
  obtain ⟨V, hVK, hVfin, hVcoact⟩ := exists_finite_subspace_coact_mem (K := K) hxK
  have : FiniteDimensional k ↥V := hVfin
  have hsep : ∀ y ∈ V, (∀ u : H →ₐ[k] k, u y = 0) → y = 0 := fun y hy hyu => by
    obtain ⟨m, hm⟩ : IsNilpotent y := isNilpotent_of_forall_algHom_eq_zero hyu
    exact Subtype.ext_iff.1
      (IsNilpotent.eq_zero (⟨m, by ext; simpa using hm⟩ : IsNilpotent (⟨y, hVK hy⟩ : ↥K)))
  obtain ⟨N, U, hUspan⟩ := exists_fin_translPoint_span x V hVcoact hsep
  -- the comodule `T` spanned by the translates of `x` is spanned by relative invariants `s i`,
  -- with group-like weights `c i`
  set T : Submodule k H := Coalgebra.Comodule.translSpan (k := k) (C := H) x
  have hTsub : IsSubcomodule (C := H) T := Coalgebra.Comodule.isSubcomodule_translSpan x
  let : RightComodule k H ↥T := Coalgebra.Comodule.subComodule hTsub
  have : FiniteDimensional k ↥T := Module.Finite.iff_fg.2 (Coalgebra.Comodule.translSpan_fg x)
  obtain ⟨s, hsval, hspanT⟩ := translSpan_eq_top_of_span_translPoint hUspan
  have hcex : ∀ i : Fin N, ∃ c : H, IsGroupLikeElem k (Ideal.Quotient.mk I c) ∧
      IsRelInvMod k I (s i) c := fun i =>
    exists_groupLike_weight_of_isRelInvMod
      ((isRelInvMod_subComodule_iff hTsub I (s i) _).2
        (hsval i ▸ isRelInvMod_translPoint hI (U i) hrelx))
  choose c hcgl hc using hcex
  have hvT : IsRelInvMod k I (⟨x, Coalgebra.Comodule.self_mem_translSpan x⟩ : ↥T) x :=
    (isRelInvMod_subComodule_iff hTsub I _ x).2 hrelx
  have hv0 : (⟨x, Coalgebra.Comodule.self_mem_translSpan x⟩ : ↥T) ≠ 0 :=
    fun h => hx0 (Subtype.ext_iff.1 h)
  -- the character functional of `T` at `x`
  obtain ⟨θ, hθ1, hθ2⟩ :=
    exists_charFunctional_of_weights I s hspanT c hc hcgl hvT hglx hv0
  refine ⟨q - 1, ↥T, inferInstance, inferInstance, inferInstance, inferInstance, θ,
    ⟨x, Coalgebra.Comodule.self_mem_translSpan x⟩, hθ1, ?_⟩
  rw [Nat.sub_add_cancel hq, ← hx]
  exact hθ2

/-- **The surjectivity half of Takeuchi's Theorem 4.3** for a finitely generated commutative Hopf
algebra over an algebraically closed field. -/
theorem normalHopfIdealEqAugSpan_of_isAlgClosed_of_finiteType [IsAlgClosed k]
    [Algebra.FiniteType k H] :
    NormalHopfIdealEqAugSpan k H := by
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  exact normalHopfIdealEqAugSpan_of_hasCharacterFunctionalPow
      hasCharacterFunctionalPow_of_isAlgClosed

end HopfAlgebra.Commutative
end
