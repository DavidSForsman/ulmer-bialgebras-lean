module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.Localization

/-!
# A local-to-global principle for faithful flatness

Let `R` be a commutative ring and let `A → B` be a morphism of commutative `R`-algebras. The main
result of this file, `Module.FaithfullyFlat.faithfullyFlat_of_isFaithfullyFlatAt_prime`, says that
if for every prime ideal `p` of `R` the localized morphism `Aₚ → Bₚ` (localizations at the
multiplicative set `R \ p`) is faithfully flat, then `A → B` itself is faithfully flat.

This is the local-to-global step used in Section 4 of the paper to extend Takeuchi's theorem
from fields to commutative von Neumann regular rings.

## Main results

* `Module.FaithfullyFlat.IsFaithfullyFlatAt`: `B` is faithfully flat over `A` locally at a
  multiplicative set `T ⊆ A`;
* `Module.FaithfullyFlat.faithfullyFlat_of_isFaithfullyFlatAt_prime`: if a morphism `A → B` of
  commutative `R`-algebras becomes faithfully flat after localizing at `R \ p` for every prime ideal
  `p` of `R`, then it is faithfully flat.

## References

* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 3
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Section 4
-/

@[expose] public section

namespace Module.FaithfullyFlat

open Algebra (algebraMapSubmonoid)

section Defs

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- `B` is faithfully flat over `A` *locally at the multiplicative set `T ⊆ A`* if the
localization of `B` at (the image of) `T` is faithfully flat over the localization of `A` at
`T`. -/
abbrev IsFaithfullyFlatAt (T : Submonoid A) : Prop :=
  Module.FaithfullyFlat (Localization T) (Localization (algebraMapSubmonoid B T))

end Defs

section Transfer

universe u

variable {A B Aₜ Bₜ : Type u} [CommRing A] [CommRing B] [CommRing Aₜ] [CommRing Bₜ]
  [Algebra A B] [Algebra A Aₜ] [Algebra B Bₜ] [Algebra Aₜ Bₜ] [Algebra A Bₜ]
  [IsScalarTower A Aₜ Bₜ] [IsScalarTower A B Bₜ]

/-- If `Aₜ` is a localization of `A` at `T`, `Bₜ` a localization of `B` at the image of `T`, and
`Bₜ` is faithfully flat over `Aₜ`, then `IsFaithfullyFlatAt A B T`: faithful flatness at `T` does
not depend on the chosen localizations. -/
theorem isFaithfullyFlatAt_of_model (T : Submonoid A) [IsLocalization T Aₜ]
    [IsLocalization (algebraMapSubmonoid B T) Bₜ] (h : Module.FaithfullyFlat Aₜ Bₜ) :
    IsFaithfullyFlatAt A B T := by
  have hAT : (algebraMap Aₜ Bₜ).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr h
  -- Compare the given models with the standard localizations.
  let eA : Aₜ ≃ₐ[A] Localization T := IsLocalization.algEquiv T Aₜ (Localization T)
  let eB : Bₜ ≃ₐ[B] Localization (algebraMapSubmonoid B T) :=
    IsLocalization.algEquiv (algebraMapSubmonoid B T) Bₜ _
  have hcomp : ((eB : Bₜ →+* _).comp ((algebraMap Aₜ Bₜ).comp (eA.symm : Localization T →+* Aₜ)))
      = algebraMap (Localization T) (Localization (algebraMapSubmonoid B T)) := by
    refine IsLocalization.ringHom_ext T ?_
    ext a
    have heA : eA.symm (algebraMap A (Localization T) a) = algebraMap A Aₜ a := by
      simp [eA]
    have hAB : algebraMap Aₜ Bₜ (algebraMap A Aₜ a) = algebraMap B Bₜ (algebraMap A B a) := by
      rw [← IsScalarTower.algebraMap_apply A Aₜ Bₜ, IsScalarTower.algebraMap_apply A B Bₜ]
    have heB : eB (algebraMap B Bₜ (algebraMap A B a)) =
        algebraMap B (Localization (algebraMapSubmonoid B T)) (algebraMap A B a) := by
      simp [eB]
    have hloc : algebraMap (Localization T) (Localization (algebraMapSubmonoid B T))
        (algebraMap A (Localization T) a) =
        algebraMap B (Localization (algebraMapSubmonoid B T)) (algebraMap A B a) := by
      rw [← IsScalarTower.algebraMap_apply A (Localization T)
        (Localization (algebraMapSubmonoid B T)),
        IsScalarTower.algebraMap_apply A B (Localization (algebraMapSubmonoid B T))]
    simp only [RingHom.comp_apply]
    rw [show ((eA.symm : Localization T →+* Aₜ)) (algebraMap A (Localization T) a) =
      algebraMap A Aₜ a from heA, hAB]
    exact heB.trans hloc.symm
  -- Faithful flatness transfers along the two isomorphisms.
  have : (algebraMap (Localization T) (Localization (algebraMapSubmonoid B T))).FaithfullyFlat := by
    have hA : ((eA.symm : Localization T →+* Aₜ)).FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective eA.symm.bijective
    have hB : ((eB : Bₜ →+* Localization (algebraMapSubmonoid B T))).FaithfullyFlat :=
      RingHom.FaithfullyFlat.of_bijective eB.bijective
    have h12 := RingHom.FaithfullyFlat.stableUnderComposition
      (eA.symm : Localization T →+* Aₜ) (algebraMap Aₜ Bₜ) hA hAT
    have h123 := RingHom.FaithfullyFlat.stableUnderComposition
      ((algebraMap Aₜ Bₜ).comp (eA.symm : Localization T →+* Aₜ))
      (eB : Bₜ →+* Localization (algebraMapSubmonoid B T)) h12 hB
    rw [← hcomp]
    exact h123
  exact RingHom.faithfullyFlat_algebraMap_iff.mp this

end Transfer

section Local

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- If `A → B` is faithfully flat locally at `T`, then any prime ideal of `A` disjoint from `T`
does not generate the unit ideal of `B`. -/
theorem ideal_smul_top_ne_top_of_isFaithfullyFlatAt {T : Submonoid A}
    (h : IsFaithfullyFlatAt A B T) (I : Ideal A) (hI : I.IsPrime)
    (hd : Disjoint (T : Set A) (I : Set A)) :
    I • (⊤ : Submodule A B) ≠ ⊤ := by
  intro htop
  have hJ : (I.map (algebraMap A (Localization T))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint T _ I hI hd
  refine ((Module.FaithfullyFlat.iff_flat_and_proper_ideal _ _).mp h).2 _ hJ.ne_top ?_
  have htop' : I.map (algebraMap A B) = ⊤ := by
    have h0 := htop
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff] at h0
    exact h0
  rw [Ideal.smul_top_eq_map]
  have : (I.map (algebraMap A (Localization T))).map
      (algebraMap (Localization T) (Localization (algebraMapSubmonoid B T))) = ⊤ := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A (Localization T)
      (Localization (algebraMapSubmonoid B T)),
      IsScalarTower.algebraMap_eq A B (Localization (algebraMapSubmonoid B T)),
      ← Ideal.map_map, htop', Ideal.map_top]
  rw [this]
  rfl

/-- If `A → B` is faithfully flat locally at `T`, then the localization of `B` at any prime
ideal disjoint from the image of `T` is a flat `A`-module. -/
theorem flat_localizationAtPrime_of_isFaithfullyFlatAt {T : Submonoid A}
    (h : IsFaithfullyFlatAt A B T) (P : Ideal B) (hP : P.IsPrime)
    (hd : Disjoint ((algebraMapSubmonoid B T : Submonoid B) : Set B) (P : Set B)) :
    Module.Flat A (Localization.AtPrime P) := by
  have := hP
  -- `B_P` is a localization of `B_T`, hence flat over it.
  have hle : algebraMapSubmonoid B T ≤ P.primeCompl := fun x hx hxP =>
    Set.disjoint_left.mp hd hx hxP
  let : Algebra (Localization (algebraMapSubmonoid B T)) (Localization.AtPrime P) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (algebraMapSubmonoid B T) P.primeCompl hle
  have : IsScalarTower B (Localization (algebraMapSubmonoid B T)) (Localization.AtPrime P) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsLocalization
      (P.primeCompl.map (algebraMap B (Localization (algebraMapSubmonoid B T))))
      (Localization.AtPrime P) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  have : Module.Flat (Localization (algebraMapSubmonoid B T)) (Localization.AtPrime P) :=
    IsLocalization.flat _
      (P.primeCompl.map (algebraMap B (Localization (algebraMapSubmonoid B T))))
  -- Make `B_P` an algebra over `A_T`, compatibly with `A`, and compose the flat maps.
  let : Algebra (Localization T) (Localization.AtPrime P) :=
    ((algebraMap (Localization (algebraMapSubmonoid B T)) (Localization.AtPrime P)).comp
      (algebraMap (Localization T) (Localization (algebraMapSubmonoid B T)))).toAlgebra
  have : IsScalarTower (Localization T) (Localization (algebraMapSubmonoid B T))
      (Localization.AtPrime P) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (Localization T) (Localization.AtPrime P) := by
    refine .of_algebraMap_eq fun a => ?_
    change algebraMap A (Localization.AtPrime P) a
      = algebraMap (Localization (algebraMapSubmonoid B T)) (Localization.AtPrime P)
          (algebraMap (Localization T) (Localization (algebraMapSubmonoid B T))
            (algebraMap A (Localization T) a))
    rw [← IsScalarTower.algebraMap_apply A (Localization T)
        (Localization (algebraMapSubmonoid B T)),
      IsScalarTower.algebraMap_apply A B (Localization (algebraMapSubmonoid B T)),
      ← IsScalarTower.algebraMap_apply B (Localization (algebraMapSubmonoid B T))
        (Localization.AtPrime P),
      ← IsScalarTower.algebraMap_apply A B (Localization.AtPrime P)]
  have : Module.Flat (Localization T) (Localization.AtPrime P) :=
    Module.Flat.trans (Localization T) (Localization (algebraMapSubmonoid B T)) _
  exact (Module.flat_iff_of_isLocalization (Localization T) T (Localization.AtPrime P)).mp
    inferInstance

end Local

section Descent

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- **Local-to-global principle for faithful flatness.** If a morphism `A → B` of commutative
`R`-algebras becomes faithfully flat after localizing at `R \ p` for every prime ideal `p`
of `R`, then it is faithfully flat. -/
theorem faithfullyFlat_of_isFaithfullyFlatAt_prime
    (H : ∀ (p : Ideal R) [p.IsPrime], IsFaithfullyFlatAt A B (algebraMapSubmonoid A p.primeCompl)) :
    Module.FaithfullyFlat A B := by
  rw [Module.faithfullyFlat_iff]
  constructor
  · refine Module.flat_of_isLocalized_maximal (R := A) B B (fun P _ => Localization.AtPrime P)
      (fun P _ => Algebra.linearMap B (Localization.AtPrime P)) ?_
    intro P hP
    have : (P.comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap _
    refine flat_localizationAtPrime_of_isFaithfullyFlatAt (H (P.comap (algebraMap R B)))
      P hP.isPrime ?_
    rw [Set.disjoint_left]
    rintro x ⟨y, ⟨r, hr, rfl⟩, rfl⟩ hxP
    exact hr (by simpa [← IsScalarTower.algebraMap_apply R A B] using hxP)
  · intro m hm
    have : (m.comap (algebraMap R A)).IsPrime := Ideal.IsPrime.comap _
    refine ideal_smul_top_ne_top_of_isFaithfullyFlatAt (H (m.comap (algebraMap R A)))
      m hm.isPrime ?_
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, rfl⟩ hxm
    exact hr hxm

end Descent

end Module.FaithfullyFlat
