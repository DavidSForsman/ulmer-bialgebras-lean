module

public import Foundations.CategoryTheory.Factorization.RegularSectionExtremal
public import Foundations.CategoryTheory.Factorization.StableRegularOFS
public import Foundations.CategoryTheory.Limits.KernelPairComparison

/-!
# A stable orthogonal factorization system from stably extremal regular epimorphisms

Let `𝒞` be a category with pullbacks and coequalizers of kernel pairs.  This file gives
the stable factorization system (regular epimorphisms, monomorphisms) when every regular
epimorphism is stably extremal.

The proof uses the three steps of the author's lemma:

1. if every morphism factors as a regular epimorphism followed by a monomorphism, then regular
   epimorphisms coincide with extremal epimorphisms, and hence are closed under composition
   (extremal epimorphisms compose in a category with pullbacks);
2. the section-extremal criterion of `RegularSectionExtremal.lean` turns a stably extremal
   regular epimorphism `f` into an `S`-epimorphism: in a factorization `f' = k ≫ s` of a base
   change `f'` with `s` a section, `f'` is extremal and `s` is monic, so `s` is invertible;
3. hence every morphism has the kernel-pair factorization with monic second part, which gives the
   factorization system and, with the stability hypothesis, its stability.

## Main results

* `SectionEpi.regularEpiStablySEpi_of_stablyExtremal` — stably extremal regular epimorphisms are
  stably `S`-epic;
* `exists_regularEpi_mono_factorization_of_stablyExtremal` — every morphism factors as a regular
  epimorphism followed by a monomorphism;
* `isRegularEpi_iff_isExtremalEpi_of_stablyExtremal` — regular and extremal epimorphisms coincide;
* `regularEpi_isStableUnderComposition_of_stablyExtremal` — regular epimorphisms are closed under
  composition;
* `regularOFS` — the stable `(regular epimorphism, monomorphism)` factorization system;
* `exists_stableOFS` — the packaged form of the author's lemma (3).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.4
* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits CategoryTheory.LiftedOFS

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-- Every regular epimorphism is stably extremal: each of its base changes is an extremal
epimorphism. -/
def RegularEpiStablyExtremal (𝒞 : Type u) [Category.{v} 𝒞] : Prop :=
  ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), IsRegularEpi f → StablyExtremalEpi f

/-! ## Step 2: stably extremal regular epimorphisms are stably `S`-epic -/

/-- If every regular epimorphism is stably extremal, then every regular epimorphism is stably
`S`-epic: a base change `f' = k ≫ s` with `s` a section (hence monic) has `f'` extremal, so `s`
is invertible. -/
theorem SectionEpi.regularEpiStablySEpi_of_stablyExtremal [HasPullbacks 𝒞]
    (h : RegularEpiStablyExtremal 𝒞) : SectionEpi.RegularEpiStablySEpi 𝒞 := by
  intro X Y f hf P Z fst snd g hpb M k s hs hks
  have hextr : IsExtremalEpi snd := h f hf fst snd g hpb
  have : Mono s := hs.mono
  exact hextr.isIso k s hks

/-! ## Step 3: the factorization and the factorization system -/

section StablyExtremal

variable [HasPullbacks 𝒞] (hkc : HasCoequalizersOfKernelPairs 𝒞)
variable (h : RegularEpiStablyExtremal 𝒞)

include hkc h

/-- Every morphism factors as a regular epimorphism followed by a monomorphism (through the
coequalizer of its kernel pair). -/
theorem exists_regularEpi_mono_factorization_of_stablyExtremal {X Y : 𝒞} (f : X ⟶ Y) :
    ∃ (I : 𝒞) (e : X ⟶ I) (m : I ⟶ Y), IsRegularEpi e ∧ Mono m ∧ e ≫ m = f :=
  SectionEpi.exists_regularEpi_mono_factorization_of_regularEpiStablySEpi hkc
    (SectionEpi.regularEpiStablySEpi_of_stablyExtremal h) f

/-- Regular and extremal epimorphisms coincide. -/
theorem isRegularEpi_iff_isExtremalEpi_of_stablyExtremal {X Y : 𝒞} (f : X ⟶ Y) :
    IsRegularEpi f ↔ IsExtremalEpi f := by
  constructor
  · intro _
    infer_instance
  · intro he
    obtain ⟨I, e, m, hee, hm, hfac⟩ :=
      exists_regularEpi_mono_factorization_of_stablyExtremal hkc h f
    have : IsIso m := IsExtremalEpi.isIso_of_mono he e m hm hfac
    exact ⟨⟨RegularEpi.ofArrowIso
      (Arrow.isoMk (Iso.refl X) (asIso m) (by simpa using hfac.symm))
      (IsRegularEpi.getStruct e)⟩⟩

/-- Regular epimorphisms are closed under composition. -/
theorem regularEpi_isStableUnderComposition_of_stablyExtremal :
    (MorphismProperty.regularEpi 𝒞).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    have hf' : IsExtremalEpi f :=
      (isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h f).1
        ((MorphismProperty.regularEpi_iff f).1 hf)
    have hg' : IsExtremalEpi g :=
      (isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g).1
        ((MorphismProperty.regularEpi_iff g).1 hg)
    exact (MorphismProperty.regularEpi_iff (f ≫ g)).2
      ((isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h (f ≫ g)).2
        (isExtremalEpi_comp hf' hg'))

end StablyExtremal

/-! ## The property/class bridge for extremal epimorphisms -/

section Bridge

variable [HasPullbacks 𝒞] (hkc : HasCoequalizersOfKernelPairs 𝒞)
variable (h : RegularEpiStablyExtremal 𝒞)

include hkc h

/-- The paper's `extremalEpi` property is Mathlib's `ExtremalEpi` class, using the factorization
and the stability hypothesis. -/
theorem extremalEpi_iff_isExtremalEpi_of_stablyExtremal {X Y : 𝒞} (f : X ⟶ Y) :
    extremalEpi 𝒞 f ↔ IsExtremalEpi f := by
  constructor
  · intro hf
    obtain ⟨I, e, m, he, hm, hfac⟩ :=
      exists_regularEpi_mono_factorization_of_stablyExtremal hkc h f
    obtain ⟨d, ⟨-, hd₂⟩, -⟩ := hf m hm e (𝟙 Y) (by rw [hfac, Category.comp_id])
    have hmul : m ≫ d = 𝟙 I := by
      refine (cancel_mono m).1 ?_
      rw [Category.assoc, hd₂, Category.comp_id, Category.id_comp]
    have : IsIso m := ⟨d, hmul, hd₂⟩
    have : IsRegularEpi f :=
      ⟨⟨RegularEpi.ofArrowIso
        (Arrow.isoMk (Iso.refl X) (asIso m) (by simpa using hfac.symm))
        (IsRegularEpi.getStruct e)⟩⟩
    exact inferInstanceAs (ExtremalEpi f)
  · intro he
    have : IsExtremalEpi f := he
    have : StrongEpi f := (extremalEpi_iff_strongEpi_of_hasPullbacks (f := f)).mp he
    intro c d m hm
    have : Mono m := hm
    exact OFS.orthogonal_of_strongEpi_of_mono f m

end Bridge

/-! ## The stable factorization system -/

section RegularOFS

variable [HasPullbacks 𝒞] (hkc : HasCoequalizersOfKernelPairs 𝒞)
variable (h : RegularEpiStablyExtremal 𝒞)

include hkc h

/-- A morphism right orthogonal to every regular epimorphism is a monomorphism. -/
theorem mono_of_rightOrth_regularEpi_of_stablyExtremal {X Y : 𝒞} {g : X ⟶ Y}
    (hg : rightOrth (MorphismProperty.regularEpi 𝒞) g) : Mono g := by
  obtain ⟨I, e, m, he, hm, hfac⟩ :=
    exists_regularEpi_mono_factorization_of_stablyExtremal hkc h g
  have he' : (MorphismProperty.regularEpi 𝒞) e := (MorphismProperty.regularEpi_iff e).mpr he
  obtain ⟨d, ⟨hd₁, hd₂⟩, -⟩ := hg e he' (𝟙 X) m (by rw [Category.id_comp, hfac])
  refine ⟨fun {Z} a b hab => ?_⟩
  have h₁ : a ≫ e = b ≫ e := by
    refine (cancel_mono m).1 ?_
    calc (a ≫ e) ≫ m = a ≫ (e ≫ m) := by rw [Category.assoc]
      _ = a ≫ g := by rw [hfac]
      _ = b ≫ g := hab
      _ = b ≫ (e ≫ m) := by rw [hfac]
      _ = (b ≫ e) ≫ m := by rw [Category.assoc]
  calc a = (a ≫ e) ≫ d := by rw [Category.assoc, hd₁, Category.comp_id]
    _ = (b ≫ e) ≫ d := by rw [h₁]
    _ = b := by rw [Category.assoc, hd₁, Category.comp_id]

/-- The monomorphisms are the right orthogonal class of the regular epimorphisms. -/
theorem monomorphisms_eq_rightOrth_regularEpi_of_stablyExtremal :
    MorphismProperty.monomorphisms 𝒞 = rightOrth (MorphismProperty.regularEpi 𝒞) := by
  ext X Y g
  constructor
  · intro hg a b e he
    have : IsRegularEpi e := (MorphismProperty.regularEpi_iff e).1 he
    exact OFS.orthogonal_of_isRegularEpi_of_mono e g
  · intro hg
    exact mono_of_rightOrth_regularEpi_of_stablyExtremal hkc h hg

/-- The regular epimorphisms are the left orthogonal class of the monomorphisms. -/
theorem regularEpi_eq_leftOrth_monomorphisms_of_stablyExtremal :
    MorphismProperty.regularEpi 𝒞 = leftOrth (MorphismProperty.monomorphisms 𝒞) := by
  ext X Y f
  constructor
  · intro hf
    have : IsRegularEpi f := (MorphismProperty.regularEpi_iff f).1 hf
    exact fun ⦃a b⦄ m hm => OFS.orthogonal_of_isRegularEpi_of_mono f m
  · intro hf
    exact (isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h f).2
      ((extremalEpi_iff_isExtremalEpi_of_stablyExtremal hkc h f).1 hf)

/-- **The stable `(regular epimorphism, monomorphism)` orthogonal factorization system.** -/
noncomputable def regularOFS : OFS 𝒞 where
  E := MorphismProperty.regularEpi 𝒞
  M := MorphismProperty.monomorphisms 𝒞
  fact := fun {x y} (f : x ⟶ y) =>
    exists_regularEpi_mono_factorization_of_stablyExtremal hkc h f
  M_eq := monomorphisms_eq_rightOrth_regularEpi_of_stablyExtremal hkc h
  E_eq := regularEpi_eq_leftOrth_monomorphisms_of_stablyExtremal hkc h

/-- The left class of `regularOFS` is stable under base change. -/
theorem regularOFS_stable : (regularOFS hkc h).E.IsStableUnderBaseChange := by
  refine ⟨?_⟩
  intro X Y Y' S f g f' g' sq hf
  exact (MorphismProperty.regularEpi_iff g').2
    ((isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g').2
      (h g ((MorphismProperty.regularEpi_iff g).1 hf) f' g' f sq))

end RegularOFS

/-! ## The packaged lemma -/

/-- **The author's lemma (3).**  If `𝒞` has pullbacks and coequalizers of kernel pairs and every
regular epimorphism is stably extremal, then there is a stable orthogonal factorization system
whose left class is the regular epimorphisms and whose right class is the monomorphisms. -/
theorem exists_stableOFS [HasPullbacks 𝒞] (hkc : HasCoequalizersOfKernelPairs 𝒞)
    (h : RegularEpiStablyExtremal 𝒞) :
    ∃ S : OFS 𝒞, S.E = MorphismProperty.regularEpi 𝒞 ∧
      S.M = MorphismProperty.monomorphisms 𝒞 ∧
      (MorphismProperty.regularEpi 𝒞).IsStableUnderBaseChange :=
  ⟨regularOFS hkc h, rfl, rfl, regularOFS_stable hkc h⟩

/-! ## The characterization of regular categories -/

section Characterization

variable [HasFiniteLimits 𝒞] (hkc : HasCoequalizersOfKernelPairs 𝒞)

include hkc

/-- **The direction of the characterization of regular categories** that follows from the stable
`(extremal epi, mono)` factorization system: a category with finite limits, coequalizers of
kernel pairs and stably extremal regular epimorphisms is regular in the sense of
Definition 6.4. -/
theorem isRegularCat_of_stablyExtremal (h : RegularEpiStablyExtremal 𝒞) : IsRegularCat 𝒞 := by
  obtain ⟨S, -, hM, hstab⟩ := exists_stableOFS hkc h
  refine ⟨inferInstance, ⟨S, hM⟩, ?_⟩
  refine ⟨fun {X Y Y' S'} {f : X ⟶ S'} {g : Y ⟶ S'} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
    (sq : IsPullback f' g' g f) (hg : extremalEpi 𝒞 g) => ?_⟩
  have hg' : IsExtremalEpi g := (extremalEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g).1 hg
  have hgreg : IsRegularEpi g :=
    (isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g).2 hg'
  have hg_reg : (MorphismProperty.regularEpi 𝒞) g := (MorphismProperty.regularEpi_iff g).2 hgreg
  have hg'_reg : (MorphismProperty.regularEpi 𝒞) g' := hstab.of_isPullback sq hg_reg
  exact (extremalEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g').2
    ((isRegularEpi_iff_isExtremalEpi_of_stablyExtremal hkc h g').1
      ((MorphismProperty.regularEpi_iff g').1 hg'_reg))

end Characterization

end UlmerBialgebras
