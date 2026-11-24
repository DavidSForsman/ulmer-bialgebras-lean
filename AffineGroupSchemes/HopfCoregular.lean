module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers
public import AffineGroupSchemes.HopfRegularMono
public import AffineGroupSchemes.HopfFiniteColimits
public import AffineGroupSchemes.FaithfullyFlatPushout

/-!
# Coregularity of the category of commutative Hopf algebras

This file proves **Theorem 3.12** of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*:

the category of commutative Hopf algebras over a field is coregular, i.e. the category of
affine group schemes is regular.  As everywhere in this development, Takeuchi's faithful
flatness theorem enters as the explicit hypothesis `HopfAlgebra.InjectiveIsFaithfullyFlat`.

The three ingredients of Mathlib's `CategoryTheory.Regular` are:

* finite limits of affine group schemes, proved in
  `AffineGroupSchemes/HopfFiniteColimits.lean`;
* the existence of coequalizers of kernel pairs, which dually is the existence of equalizers of
  cokernel pairs: the equalizer is the Hopf image of the morphism
  (`AffineGroupSchemes.CommHopfAlgCat.hasEqualizer_of_isPushout`);
* stability of regular epimorphisms under base change, which dually is stability of injective
  (equivalently regular monic) morphisms of Hopf algebras under pushout
  (`AffineGroupSchemes.CommHopfAlgCat.injective_of_isPushout`).

## Main results

* `AffineGroupSchemes.CommHopfAlgCat.injective_of_isPushout`: assuming
  `HopfAlgebra.InjectiveIsFaithfullyFlat`, in a pushout square of commutative Hopf algebras the
  pushout of an injective morphism is injective.
* `AffineGroupSchemes.CommHopfAlgCat.hasEqualizer_of_isPushout`: assuming
  `HopfAlgebra.InjectiveIsFaithfullyFlat`, the cokernel pair of a morphism of commutative Hopf
  algebras over a field has an equalizer.
* `AffineGroupSchemes.CommHopfAlgCat.regular_op`: Theorem 3.12 of
  [forsman2026semiabeliannessaffinegroupschemes] — assuming `HopfAlgebra.InjectiveIsFaithfullyFlat`,
  `(CommHopfAlgCat k)ᵒᵖ` is regular for every field `k`.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
* [M. Takeuchi, *A correspondence between Hopf ideals and
  sub-Hopf algebras*][Takeuchi1972], Theorem 3.1
* [W. C. Waterhouse, *Introduction to Affine Group
  Schemes*][waterhouseIntroductionAffineGroup1979], Chapters 13–14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.11
-/

@[expose] public section

open TensorProduct Coalgebra Function CategoryTheory Limits

namespace AffineGroupSchemes

open HopfAlgebra

universe u

section ForkTransfer

variable {C : Type*} [Category C]

/-- Transfer of an equalizer along an isomorphism of the codomain identifying the two parallel
morphisms. -/
noncomputable def isLimitForkOfIso {X P P' S : C} {r₁ r₂ : X ⟶ P'} {q₁ q₂ : X ⟶ P} (ε : P ≅ P')
    (h₁ : q₁ ≫ ε.hom = r₁) (h₂ : q₂ ≫ ε.hom = r₂) (ι : S ⟶ X) (w : ι ≫ r₁ = ι ≫ r₂)
    (hlim : IsLimit (Fork.ofι ι w)) (w' : ι ≫ q₁ = ι ≫ q₂) :
    IsLimit (Fork.ofι ι w') := by
  have hcond : ∀ {T : C} (t : T ⟶ X), t ≫ q₁ = t ≫ q₂ → t ≫ r₁ = t ≫ r₂ := by
    intro T t ht
    rw [← h₁, ← h₂, ← Category.assoc, ← Category.assoc, ht]
  refine Fork.IsLimit.mk _ (fun s => hlim.lift (Fork.ofι s.ι (hcond s.ι s.condition)))
    (fun s => hlim.fac (Fork.ofι s.ι (hcond s.ι s.condition)) WalkingParallelPair.zero)
    (fun s m hm => ?_)
  have hmι : m ≫ ι = s.ι := by simpa using hm
  have hliftι : hlim.lift (Fork.ofι s.ι (hcond s.ι s.condition)) ≫ ι = s.ι :=
    hlim.fac (Fork.ofι s.ι (hcond s.ι s.condition)) WalkingParallelPair.zero
  exact Fork.IsLimit.hom_ext hlim (by simpa [hliftι] using hmι)

end ForkTransfer

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

section Pushout

/-- **Injective morphisms of commutative Hopf algebras are stable under pushout.**  If the
square `u, v, p, q` is a pushout square and `v` is injective, then so is `p`. -/
theorem injective_of_isPushout (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    {A X B P : CommHopfAlgCat.{u} k} {u : A ⟶ X} {v : A ⟶ B} {p : X ⟶ P} {q : B ⟶ P}
    (h : IsPushout u v p q) (hv : Injective v) : Injective p := by
  let : Algebra A X := algebraOfBialgHom u.hom
  let : Algebra A B := algebraOfBialgHom v.hom
  have : IsScalarTower k A X :=
    .of_algebraMap_eq fun r => ((u.hom : A →ₐ[k] X).commutes r).symm
  have : IsScalarTower k A B :=
    .of_algebraMap_eq fun r => ((v.hom : A →ₐ[k] B).commutes r).symm
  have hu : ∀ a : A, algebraMap A X a = u.hom a := fun _ => rfl
  have hv' : ∀ a : A, algebraMap A B a = v.hom a := fun _ => rfl
  have : Module.FaithfullyFlat A B := hInjFlat k A B v.hom hv
  let := hopfAlgebraTensor u.hom v.hom hu hv'
  have h' : IsPushout u v (CommHopfAlgCat.ofHom (inlBialgHom u.hom v.hom hu hv'))
      (CommHopfAlgCat.ofHom (inrBialgHom u.hom v.hom hu hv')) :=
    isPushout_hopfTensor u.hom v.hom hu hv'
  set ε := h.isoIsPushout _ _ h' with hε
  have hpε : p ≫ ε.hom = CommHopfAlgCat.ofHom (inlBialgHom u.hom v.hom hu hv') :=
    h.inl_isoIsPushout_hom _ _ h'
  have hinl : Injective (fun x : X => x ⊗ₜ[A] (1 : B)) :=
    injective_algebraMap_pushout A B X
  have hpε_apply : ∀ z : X, (ε.hom.hom (p.hom z) : X ⊗[A] B) = z ⊗ₜ[A] (1 : B) := fun z =>
    congr(($hpε).hom z)
  intro x y hxy
  exact hinl ((hpε_apply x).symm.trans (congr(ε.hom.hom $hxy).trans (hpε_apply y)))

end Pushout

section Equalizer

/-- **The equalizer of a cokernel pair.**  If `q₁, q₂ : X ⇉ P` is the cokernel pair of a
morphism `φ : Y ⟶ X` of commutative Hopf algebras over a field, then `q₁` and `q₂` have an
equalizer, namely the Hopf image of `φ`. -/
theorem hasEqualizer_of_isPushout (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u})
    {Y X P : CommHopfAlgCat.{u} k} {φ : Y ⟶ X} {q₁ q₂ : X ⟶ P}
    (h : IsPushout φ φ q₁ q₂) : HasEqualizer q₁ q₂ := by
  obtain ⟨S, _, _, e, i, hesurj, hiinj, hfac⟩ := exists_hopfAlgebra_image_factorization φ.hom
  let : Algebra Y X := algebraOfBialgHom φ.hom
  have : IsScalarTower k Y X :=
    .of_algebraMap_eq fun r => ((φ.hom : Y →ₐ[k] X).commutes r).symm
  let : Algebra Y S := algebraOfBialgHom e
  let : Algebra S X := algebraOfBialgHom i
  have hφ : ∀ y : Y, algebraMap Y X y = φ.hom y := fun _ => rfl
  have he : ∀ y : Y, algebraMap Y S y = e y := fun _ => rfl
  have hi : ∀ s : S, algebraMap S X s = i s := fun _ => rfl
  let := hopfAlgebraTensor φ.hom φ.hom hφ hφ
  have h' : IsPushout φ φ (CommHopfAlgCat.ofHom (inlBialgHom φ.hom φ.hom hφ hφ))
      (CommHopfAlgCat.ofHom (inrBialgHom φ.hom φ.hom hφ hφ)) :=
    isPushout_hopfTensor φ.hom φ.hom hφ hφ
  set ε := h.isoIsPushout _ _ h' with hεdef
  have h₁ : q₁ ≫ ε.hom = CommHopfAlgCat.ofHom (inlBialgHom φ.hom φ.hom hφ hφ) :=
    h.inl_isoIsPushout_hom _ _ h'
  have h₂ : q₂ ≫ ε.hom = CommHopfAlgCat.ofHom (inrBialgHom φ.hom φ.hom hφ hφ) :=
    h.inr_isoIsPushout_hom _ _ h'
  have hlim := isLimitForkImage φ.hom e i hφ he hi hfac hiinj hesurj hInjFlat
  have w' : CommHopfAlgCat.ofHom i ≫ q₁ = CommHopfAlgCat.ofHom i ≫ q₂ := by
    rw [← cancel_mono ε.hom, Category.assoc, Category.assoc, h₁, h₂]
    exact fork_condition φ.hom e i hφ hfac hesurj
  exact HasLimit.mk ⟨_, isLimitForkOfIso ε h₁ h₂ (CommHopfAlgCat.ofHom i)
    (fork_condition φ.hom e i hφ hfac hesurj) hlim w'⟩

end Equalizer

section Coregular

/-- **Theorem 3.12** of [forsman2026semiabeliannessaffinegroupschemes] (coregularity): the category
of commutative Hopf algebras over a field is coregular, i.e. the category of affine group
`k`-schemes is a regular category.

The proof supplies the three ingredients of regularity for the opposite category: finite
limits, coequalizers of kernel pairs (dually, equalizers of cokernel pairs: the Hopf image),
and stability of regular epimorphisms under base change (dually, stability of injective
morphisms under pushout).  Takeuchi's faithful flatness theorem enters as the hypothesis
`hInjFlat`. -/
theorem regular_op (hInjFlat : HopfAlgebra.InjectiveIsFaithfullyFlat.{u}) :
    Regular (CommHopfAlgCat.{u} k)ᵒᵖ where
  hasCoequalizer_of_isKernelPair := by
    intro X Y Z f g₁ g₂ hk
    have hpo : IsPushout f.unop f.unop g₁.unop g₂.unop := hk.unop.flip
    have := hasEqualizer_of_isPushout hInjFlat hpo
    have hcond := equalizer.condition g₁.unop g₂.unop
    have hw : g₁ ≫ (equalizer.ι g₁.unop g₂.unop).op
        = g₂ ≫ (equalizer.ι g₁.unop g₂.unop).op := by
      simpa using congr(($hcond).op)
    exact HasColimit.mk ⟨_, (Cofork.isColimitOfπEquivIsLimitUnop
      (equalizer.ι g₁.unop g₂.unop).op (equalizer.ι g₁.unop g₂.unop).op hw hcond rfl).symm
      (equalizerIsEqualizer g₁.unop g₂.unop)⟩
  regularEpiIsStableUnderBaseChange := by
    constructor
    intro X Y Y' S f g f' g' hpb hg
    have hginj : Injective g.unop :=
      injective_of_regularMono (hg.regularEpi.some.unop)
    have hg'inj : Injective g'.unop := injective_of_isPushout hInjFlat hpb.unop hginj
    exact ⟨⟨(regularMonoOfInjective g'.unop hg'inj hInjFlat).op⟩⟩

end Coregular

end CommHopfAlgCat

end AffineGroupSchemes
