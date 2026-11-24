module

public import Foundations.RingTheory.AmitsurEqualizer
public import Hopf.Basic.HopfFaithfulFlatness
public import AffineGroupSchemes.HopfCorestriction
public import AffineGroupSchemes.HopfSurjInjSystem

/-!
# The image of a morphism of Hopf algebras is the equalizer of its cokernel pair

Let `f : Y →ₐc[k] X` be a morphism of commutative Hopf algebras over a field, and let
`f = i ∘ e` be its factorization as a surjection `e : Y ↠ S` followed by an injection
`i : S ↪ X`.  The cokernel pair of `f` is the pair of canonical morphisms
`inl, inr : X ⇉ X ⊗[Y] X`, and we show that `i` is their equalizer:

* a morphism `t : T →ₐc[k] X` with `t τ ⊗ₜ 1 = 1 ⊗ₜ t τ` for all `τ` takes values in the image of
  `i` — this is faithfully flat descent (`Algebra.TensorProduct.mem_range_of_tmul_eq_of_tower`),
  applied to the faithfully flat morphism `S → X` provided by Takeuchi's theorem;
* the resulting factorization is a morphism of Hopf algebras
  (`AffineGroupSchemes.exists_unique_corestriction`).

Taking `Y = S` and `e = id` shows that every injective morphism of commutative Hopf algebras is
a regular monomorphism, i.e. an equalizer.

As everywhere in this development, Takeuchi's theorem is carried as the explicit hypothesis
`HopfAlgebra.InjectiveIsFaithfullyFlat`.

## Main results

* `AffineGroupSchemes.mem_range_of_tmul_eq_hopf`: assuming `HopfAlgebra.InjectiveIsFaithfullyFlat`,
  an element `x : X` with `x ⊗ₜ 1 = 1 ⊗ₜ x` in `X ⊗[Y] X` lies in the image of `i : S → X`.
* `AffineGroupSchemes.existsUnique_factor_through_image`: assuming
  `HopfAlgebra.InjectiveIsFaithfullyFlat`, a morphism `t : T →ₐc[k] X` equalized by the two
  coprojections `X ⇉ X ⊗[Y] X` factors uniquely through `i`.
* `AffineGroupSchemes.isLimitForkImage`: assuming `HopfAlgebra.InjectiveIsFaithfullyFlat`, `i` is an
  equalizer of the cokernel pair `X ⇉ X ⊗[Y] X` of `f` in `CommHopfAlgCat k`.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Chapters 13–14
-/

@[expose] public section

open TensorProduct Coalgebra Function CategoryTheory Limits

namespace AffineGroupSchemes

open HopfAlgebra

universe u

section Algebraic

variable {k Y S X : Type u} [Field k] [CommRing Y] [CommRing S] [CommRing X]
  [HopfAlgebra k Y] [HopfAlgebra k S] [HopfAlgebra k X]
  [Algebra Y X] [Algebra S X] [Algebra Y S]
  (f : Y →ₐc[k] X) (e : Y →ₐc[k] S) (i : S →ₐc[k] X)
  (hf : ∀ y, algebraMap Y X y = f y) (he : ∀ y, algebraMap Y S y = e y)
  (hi : ∀ s, algebraMap S X s = i s)

include hf he hi in
/-- The tower `Y → S → X` attached to a factorization `f = i ∘ e`. -/
lemma isScalarTower_of_factorization (hcomp : ∀ y, i (e y) = f y) : IsScalarTower Y S X :=
  .of_algebraMap_eq fun y => by rw [hf y, he y, hi (e y), hcomp y]

variable (hcomp : ∀ y, i (e y) = f y) (hinj : Injective i)

include hf he hi hcomp hinj in
/-- **Faithfully flat descent for Hopf algebras.**  An element of `X` which is equalized by the
two coprojections `X ⇉ X ⊗[Y] X` lies in the image of the Hopf image `S` of `f`. -/
theorem mem_range_of_tmul_eq_hopf (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u}) (x : X)
    (hx : x ⊗ₜ[Y] (1 : X) = (1 : X) ⊗ₜ[Y] x) : ∃ s : S, i s = x := by
  have : IsScalarTower Y S X := isScalarTower_of_factorization f e i hf he hi hcomp
  have : Module.FaithfullyFlat S X := by
    have h := hInjFlat k S X i hinj
    have halg : algebraOfBialgHom i = ‹Algebra S X› := by
      exact Algebra.algebra_ext _ _ fun s => (hi s).symm
    rwa [halg] at h
  obtain ⟨s,
      hs⟩ := Algebra.TensorProduct.mem_range_of_tmul_eq_of_tower (Y := Y) (A := S) (B := X) x hx
  exact ⟨s, by rwa [hi s] at hs⟩

include hf he hi hcomp hinj in
/-- **The universal property of the image as an equalizer.**  A morphism of commutative Hopf
algebras `t : T →ₐc[k] X` equalized by the two coprojections `X ⇉ X ⊗[Y] X` factors uniquely
through the Hopf image `S` of `f`. -/
theorem existsUnique_factor_through_image (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    {T : Type u}
    [CommRing T] [HopfAlgebra k T] (t : T →ₐc[k] X)
    (ht : ∀ τ : T, t τ ⊗ₜ[Y] (1 : X) = (1 : X) ⊗ₜ[Y] t τ) :
    ∃! t' : T →ₐc[k] S, ∀ τ : T, i (t' τ) = t τ :=
  exists_unique_corestriction i hinj t fun τ =>
    mem_range_of_tmul_eq_hopf f e i hf he hi hcomp hinj hInjFlat (t τ) (ht τ)

end Algebraic

section Categorical

variable {k Y S X : Type u} [Field k] [CommRing Y] [CommRing S] [CommRing X]
  [HopfAlgebra k Y] [HopfAlgebra k S] [HopfAlgebra k X]
  [Algebra Y X] [Algebra S X] [Algebra Y S] [IsScalarTower k Y X]
  (f : Y →ₐc[k] X) (e : Y →ₐc[k] S) (i : S →ₐc[k] X)
  (hf : ∀ y, algebraMap Y X y = f y) (he : ∀ y, algebraMap Y S y = e y)
  (hi : ∀ s, algebraMap S X s = i s)
  (hcomp : ∀ y, i (e y) = f y) (hinj : Injective i) (hsurj : Surjective e)

omit [Algebra S X] [Algebra Y S] [IsScalarTower k Y X] in
include hf hcomp hsurj in
/-- Elements in the image of `f` are equalized by the two coprojections `X ⇉ X ⊗[Y] X`. -/
lemma tmul_one_eq_one_tmul_image (s : S) :
    (i s) ⊗ₜ[Y] (1 : X) = (1 : X) ⊗ₜ[Y] (i s) := by
  obtain ⟨y, rfl⟩ := hsurj s
  rw [hcomp y, ← hf y, Algebra.algebraMap_eq_smul_one, smul_tmul]

omit [Algebra S X] [Algebra Y S] in
include hf hcomp hsurj in
/-- The fork condition for the image of `f` and the cokernel pair of `f`. -/
lemma fork_condition :
    letI := hopfAlgebraTensor f f hf hf
    CommHopfAlgCat.ofHom i ≫ CommHopfAlgCat.ofHom (inlBialgHom f f hf hf) =
      CommHopfAlgCat.ofHom i ≫ CommHopfAlgCat.ofHom (inrBialgHom f f hf hf) := by
  let := hopfAlgebraTensor f f hf hf
  ext s
  exact tmul_one_eq_one_tmul_image f e i hf hcomp hsurj s

include hf he hi hcomp hinj hsurj in
/-- **The image of a morphism of Hopf algebras is the equalizer of its cokernel pair.** -/
noncomputable def isLimitForkImage (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u}) :
    letI := hopfAlgebraTensor f f hf hf
    IsLimit (Fork.ofι (CommHopfAlgCat.ofHom i) (fork_condition f e i hf hcomp hsurj)) := by
  letI := hopfAlgebraTensor f f hf hf
  let sι : ∀ (s : Fork (CommHopfAlgCat.ofHom (inlBialgHom f f hf hf))
      (CommHopfAlgCat.ofHom (inrBialgHom f f hf hf))), s.pt →ₐc[k] X := fun s => s.ι.hom
  have key : ∀ (s : Fork (CommHopfAlgCat.ofHom (inlBialgHom f f hf hf))
      (CommHopfAlgCat.ofHom (inrBialgHom f f hf hf))) (τ : s.pt),
      (sι s τ) ⊗ₜ[Y] (1 : X) = (1 : X) ⊗ₜ[Y] (sι s τ) := by
    intro s τ
    exact congr(($(s.condition)).hom τ)
  refine Fork.IsLimit.mk _
    (fun s => CommHopfAlgCat.ofHom
      (existsUnique_factor_through_image f e i hf he hi hcomp hinj hInjFlat (sι s) (key s)).choose)
    (fun s => ?_) (fun s m hm => ?_)
  · ext τ
    exact (existsUnique_factor_through_image f e i hf he hi hcomp hinj hInjFlat (sι s)
      (key s)).choose_spec.1 τ
  · obtain ⟨t', ht', huniq⟩ :=
      existsUnique_factor_through_image f e i hf he hi hcomp hinj hInjFlat (sι s) (key s)
    refine CommHopfAlgCat.hom_ext (Eq.trans (huniq m.hom fun τ => ?_) (huniq _ ?_).symm)
    · exact congr(($hm).hom τ)
    · exact (existsUnique_factor_through_image f e i hf he hi hcomp hinj hInjFlat (sι s)
        (key s)).choose_spec.1

end Categorical

end AffineGroupSchemes
