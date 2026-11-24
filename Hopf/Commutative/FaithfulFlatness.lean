module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Ring
public import Foundations.RingTheory.FaithfullyFlatBaseChange
public import Hopf.Basic.HopfFaithfulFlatness

/-!
# Takeuchi's faithful flatness theorem

**Takeuchi's theorem.**  Let `k` be a field and let `f : A →ₐc[k] B` be an injective morphism of
*commutative* Hopf `k`-algebras.  Then `B`, regarded as an `A`-algebra through `f`, is faithfully
flat over `A`.

Geometrically: a homomorphism of affine group schemes over a field is faithfully flat as soon as
the corresponding map of Hopf algebras is injective (equivalently, as soon as the homomorphism of
group schemes is an epimorphism).

This file contains

* the precise statement of the theorem, `HopfAlgebra.Commutative.faithfullyFlat_of_injective`,
  together with the reformulation `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_of_algClosed`
  of it as the proposition `HopfAlgebra.InjectiveIsFaithfullyFlat` which is used as a hypothesis in
  `Hopf/Basic/HopfFaithfulFlatness.lean`;
* a *proved* reduction of the theorem to the case of an algebraically closed base field:
  `HopfAlgebra.Commutative.faithfullyFlat_of_injective` is deduced from the proposition
  `HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed` by base change to an algebraic
  closure, using the descent result `Module.FaithfullyFlat.faithfullyFlat_of_baseChange` of
  `Foundations/RingTheory/FaithfullyFlatBaseChange.lean`;
* elementary pieces: the augmentation ideal `HopfAlgebra.Commutative.augmentationIdeal` is proper
  (`HopfAlgebra.Commutative.augmentationIdeal_ne_top`), and the case `A = k` of the theorem
  (`HopfAlgebra.Commutative.faithfullyFlat_over_base`).

In this file, Takeuchi's theorem over an *algebraically closed* field is stated as the proposition
`HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed` and carried as an *explicit hypothesis*
by the results that use it — the same convention as for `HopfAlgebra.InjectiveIsFaithfullyFlat` in
`Hopf/Basic/HopfFaithfulFlatness.lean`. It is proved in
`Hopf/Commutative/FaithfulFlatnessCharZero.lean`
(`HopfAlgebra.Commutative.injectiveIsFaithfullyFlatAlgClosed_of_charZeroReduced`, from Cartier's
theorem), and the theorem is restated without hypotheses in
`Hopf/Commutative/FaithfulFlatnessUnconditional.lean`.

## Main results

* `HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed`: the proposition that an injective
  morphism of commutative Hopf algebras over an algebraically closed field makes the target
  faithfully flat over the source.
* `HopfAlgebra.Commutative.faithfullyFlat_of_injective`: given `InjectiveIsFaithfullyFlatAlgClosed`,
  an injective morphism `f : A →ₐc[k] B` of commutative Hopf algebras over a field makes `B`
  faithfully flat over `A` (Takeuchi's Theorem 3.1).
* `HopfAlgebra.Commutative.injectiveIsFaithfullyFlat_of_algClosed`:
  `InjectiveIsFaithfullyFlatAlgClosed` implies `HopfAlgebra.InjectiveIsFaithfullyFlat`.
* `HopfAlgebra.Commutative.faithfullyFlat_over_base`: a commutative Hopf algebra over a field `k` is
  faithfully flat over `k`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapter 14
* [A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*][EGAIV2], Section 6.9
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes]
-/

@[expose] public section

section
open HopfAlgebra
namespace HopfAlgebra.Commutative

open MonoidAlgebra TensorProduct

universe u

section AugmentationIdeal

variable (k : Type*) (A : Type*) [CommSemiring k] [CommSemiring A] [Bialgebra k A]

/-- The augmentation ideal `A⁺ = ker ε` of a bialgebra `A`. -/
def augmentationIdeal : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)

/-- `a ∈ A⁺ ↔ ε a = 0`. -/
@[simp] lemma mem_augmentationIdeal {a : A} :
    a ∈ augmentationIdeal k A ↔ Coalgebra.counit (R := k) a = 0 := Iff.rfl

/-- The augmentation ideal is a proper ideal. -/
lemma augmentationIdeal_ne_top [Nontrivial k] : augmentationIdeal k A ≠ ⊤ := by
  intro h
  have h1 : (1 : A) ∈ augmentationIdeal k A := h ▸ Submodule.mem_top
  simp only [mem_augmentationIdeal] at h1
  rw [show Coalgebra.counit (R := k) (1 : A) = 1 from Bialgebra.counit_one] at h1
  exact one_ne_zero h1

end AugmentationIdeal

section Basic

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Bialgebra k A] [Bialgebra k B] [Algebra A B]

variable [Nontrivial k]

end Basic

section Local

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Bialgebra k A] [Bialgebra k B] [Algebra A B]

end Local

section Statement

variable {k A B : Type u} [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]

/-- **Takeuchi's theorem over an algebraically closed field** ([Takeuchi1972], Theorem 3.1), stated
as a proposition: an
injective morphism `f : A →ₐc[k] B` of commutative Hopf algebras over an algebraically closed
field `k` makes `B` a faithfully flat `A`-algebra.

This statement is carried as an explicit hypothesis by the results of this file that use it — as
with `HopfAlgebra.InjectiveIsFaithfullyFlat` — rather than being assumed as an axiom. It is proved
in `Hopf/Commutative/FaithfulFlatnessCharZero.lean`
(`HopfAlgebra.Commutative.injectiveIsFaithfullyFlatAlgClosed_of_charZeroReduced`), from Cartier's
theorem, which is itself proved in `Hopf/CharZero/Reduced.lean`.

The general case of Takeuchi's theorem is *reduced* to this one in `faithfullyFlat_of_injective`
below, and the case `A = k` (`faithfullyFlat_over_base`) is unconditional. -/
def InjectiveIsFaithfullyFlatAlgClosed : Prop :=
  ∀ (K A B : Type u) [Field K] [IsAlgClosed K] [CommRing A] [CommRing B] [HopfAlgebra K A]
    [HopfAlgebra K B] (f : A →ₐc[K] B), Function.Injective f →
      letI := algebraOfBialgHom f
      Module.FaithfullyFlat A B

/-- **Takeuchi's theorem** ([Takeuchi1972], Theorem 3.1).  An injective morphism `f : A →ₐc[k] B` of
commutative Hopf algebras over a field `k` makes `B` a faithfully flat `A`-algebra.

This is deduced from the algebraically closed case,
`HopfAlgebra.Commutative.InjectiveIsFaithfullyFlatAlgClosed`, which enters as an explicit
hypothesis, by base change to an algebraic closure `K` of `k`: the base changed morphism
`K ⊗[k] A →ₐc[K] K ⊗[k] B` is again an injective morphism of commutative Hopf algebras (injectivity
because `K` is flat over `k`), and faithful flatness descends along the field extension by
`Module.FaithfullyFlat.faithfullyFlat_of_baseChange`. -/
theorem faithfullyFlat_of_injective (hAC : InjectiveIsFaithfullyFlatAlgClosed.{u}) (f : A →ₐc[k] B)
    (hf : Function.Injective f) :
    letI := algebraOfBialgHom f
    Module.FaithfullyFlat A B := by
  let := algebraOfBialgHom f
  have : IsScalarTower k A B :=
    .of_algebraMap_eq fun r => ((f : A →ₐ[k] B).commutes r).symm
  set K := AlgebraicClosure k
  let f' : K ⊗[k] A →ₐc[K] K ⊗[k] B := Bialgebra.TensorProduct.map (BialgHom.id K K) f
  have hcoe : ∀ x : K ⊗[k] A, f' x = LinearMap.lTensor K ((f : A →ₐ[k] B) : A →ₗ[k] B) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c a => simp [f']
    | add x y hx hy => simp [map_add, hx, hy]
  have hf' : Function.Injective f' := by
    have hinj := Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      ((f : A →ₐ[k] B) : A →ₗ[k] B) hf
    intro x y hxy
    exact hinj (by rw [← hcoe, ← hcoe]; exact hxy)
  let := algebraOfBialgHom f'
  have := hAC K (K ⊗[k] A) (K ⊗[k] B) f' hf'
  refine Module.FaithfullyFlat.faithfullyFlat_of_baseChange (k := k) (K := K) (A := A) (B :=
      B) (fun c a => ?_)
  change f' (c ⊗ₜ[k] a) = c ⊗ₜ[k] (f a)
  exact Bialgebra.TensorProduct.map_tmul (BialgHom.id K K) f c a

/-- Takeuchi's theorem, packaged as the proposition `HopfAlgebra.InjectiveIsFaithfullyFlat` which is
used as a hypothesis throughout `Hopf/Basic/HopfFaithfulFlatness.lean`. -/
theorem injectiveIsFaithfullyFlat_of_algClosed (hAC : InjectiveIsFaithfullyFlatAlgClosed.{u}) :
    HopfAlgebra.InjectiveIsFaithfullyFlat.{u} :=
  fun _ _ _ _ _ _ _ _ f hf => faithfullyFlat_of_injective hAC f hf

/-- The case `A = k` of Takeuchi's theorem: every nonzero Hopf algebra over a field is faithfully
flat over the base field. -/
theorem faithfullyFlat_over_base : Module.FaithfullyFlat k B := by
  have : Nontrivial B := by
    refine (subsingleton_or_nontrivial B).resolve_left fun hB => ?_
    have h0 : Coalgebra.counit (R := k) (1 : B) = Coalgebra.counit (R := k) (0 : B) := by
      congr 1; exact Subsingleton.elim _ _
    rw [Bialgebra.counit_one, map_zero] at h0
    exact one_ne_zero h0
  infer_instance

end Statement

section MonoidAlgebra

variable {k : Type*} [CommRing k] [Nontrivial k] {H G : Type*} [CommGroup H] [CommGroup G]

end MonoidAlgebra

end HopfAlgebra.Commutative
end
