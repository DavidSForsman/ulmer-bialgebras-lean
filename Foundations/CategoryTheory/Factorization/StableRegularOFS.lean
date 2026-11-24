module

public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Foundations.CategoryTheory.Factorization.LiftedFactorizationSystem
public import Foundations.CategoryTheory.Factorization.RegularExact
public import Foundations.CategoryTheory.Factorization.OFS

/-!
# A regular category in the sense of Definition 6.4

Mathlib defines a **regular category** as a category with finite limits in which every kernel
pair has a coequalizer and regular epimorphisms are stable under base change
(`CategoryTheory.Regular`).  The paper's Definition 6.4 defines a regular category as a category
with finite limits carrying a stable orthogonal factorization system whose right class is the class
of monomorphisms (`UlmerBialgebras.IsRegularCat`).

This file proves that the two definitions agree in the direction needed for Newman's
theorem: a Mathlib-regular category is regular in the sense of Definition 6.4.  The
factorization system is the (extremal epimorphism, monomorphism) system; extremal epimorphisms
coincide with regular epimorphisms, and the stability of the latter gives the stability of the
former.

## Main results

* `UlmerBialgebras.extremalEpi_iff` — extremal epimorphisms are Mathlib's `ExtremalEpi`;
* `UlmerBialgebras.isRegularEpi_iff_isExtremalEpi` — in a regular category regular and extremal
  epimorphisms coincide;
* `UlmerBialgebras.extremalOFS` — the (extremal epi, mono) orthogonal factorization system;
* `UlmerBialgebras.isRegularCat_of_regular` — `Regular 𝒞 → IsRegularCat 𝒞`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.4
* [M. Barr, *Exact Categories*][Ba]
* [M. Gran, *An Introduction to Regular Categories*][inbook]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits CategoryTheory.LiftedOFS

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## Regular epimorphisms are orthogonal to monomorphisms -/

/-- A strong epimorphism is orthogonal to every monomorphism. -/
lemma OFS.orthogonal_of_strongEpi_of_mono {A B c d : 𝒞} (e : A ⟶ B) (m : c ⟶ d)
    [StrongEpi e] [Mono m] : Orthogonal e m := by
  intro f g hsq
  have : HasLiftingProperty e m := StrongEpi.llp (f := e) m
  have sq : CommSq f e m g := ⟨hsq⟩
  refine ⟨sq.lift, ⟨sq.fac_left, sq.fac_right⟩, ?_⟩
  rintro k ⟨-, k2⟩
  rw [← cancel_mono m, k2, sq.fac_right]

/-- In a category with pullbacks, a regular epimorphism is a strong epimorphism.  This is
Mathlib's instance, found by `infer_instance` from `Mathlib.CategoryTheory.RegularCategory.Basic`;
the former thirty-line direct proof is no longer needed. -/
theorem strongEpi_of_isRegularEpi {X Y : 𝒞} {f : X ⟶ Y} [IsRegularEpi f] : StrongEpi f :=
  inferInstance

/-- A morphism left orthogonal to all monomorphisms is an epimorphism (in a category with
equalizers). -/
lemma OFS.epi_of_leftOrth_monomorphisms [HasEqualizers 𝒞] {X Y : 𝒞} {e : X ⟶ Y}
    (he : leftOrth (MorphismProperty.monomorphisms 𝒞) e) : Epi e := by
  constructor
  intro Z g₁ g₂ hg
  have hw : Mono (equalizer.ι g₁ g₂) := inferInstance
  obtain ⟨h, ⟨-, h2⟩, -⟩ := he (equalizer.ι g₁ g₂) hw (equalizer.lift e hg) (𝟙 Y) (by simp)
  have : IsSplitEpi (equalizer.ι g₁ g₂) := ⟨⟨h, h2⟩⟩
  have : IsIso (equalizer.ι g₁ g₂) := isIso_of_mono_of_isSplitEpi _
  rw [← cancel_epi (equalizer.ι g₁ g₂)]
  exact equalizer.condition g₁ g₂

/-- A regular epimorphism is an extremal epimorphism. -/
instance isExtremalEpi_of_isRegularEpi {X Y : 𝒞} {f : X ⟶ Y} [IsRegularEpi f] :
    ExtremalEpi f :=
  inferInstanceAs (ExtremalEpi f)

/-- A regular epimorphism is orthogonal to every monomorphism. -/
lemma OFS.orthogonal_of_isRegularEpi_of_mono {A B c d : 𝒞} (e : A ⟶ B) (m : c ⟶ d)
    [IsRegularEpi e] [Mono m] : Orthogonal e m := by
  have : StrongEpi e := strongEpi_of_isRegularEpi
  exact OFS.orthogonal_of_strongEpi_of_mono e m

/-! ## Extremal epimorphisms in a regular category -/

section RegularCategory

variable [Regular 𝒞]

/-- The paper's `extremalEpi` is Mathlib's `ExtremalEpi`. -/
theorem extremalEpi_iff {X Y : 𝒞} (f : X ⟶ Y) : extremalEpi 𝒞 f ↔ ExtremalEpi f := by
  constructor
  · intro hf
    refine ExtremalEpi.mk_of_hasEqualizers f (fun {Z} p i fac _ => ?_)
    obtain ⟨d, ⟨-, hd₂⟩, -⟩ := hf i inferInstance p (𝟙 Y) (by rw [fac, Category.comp_id])
    have : IsSplitEpi i := ⟨⟨d, hd₂⟩⟩
    exact isIso_of_mono_of_isSplitEpi i
  · intro _
    have : StrongEpi f :=
      (extremalEpi_iff_strongEpi_of_hasPullbacks (f := f)).mp ‹ExtremalEpi f›
    exact fun {c d} m hm => OFS.orthogonal_of_strongEpi_of_mono f m

/-- In a regular category, regular and extremal epimorphisms coincide. -/
theorem isRegularEpi_iff_isExtremalEpi {X Y : 𝒞} (f : X ⟶ Y) :
    IsRegularEpi f ↔ ExtremalEpi f :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

/-! ## The factorization system -/

/-- A morphism right orthogonal to every extremal epimorphism is a monomorphism: factor it as an
extremal epimorphism followed by a monomorphism and use the diagonal. -/
theorem mono_of_rightOrth_extremalEpi {X Y : 𝒞} {g : X ⟶ Y}
    (hg : rightOrth (extremalEpi 𝒞) g) : Mono g := by
  let F := Regular.strongEpiMonoFactorisation g
  have : Mono F.m := F.m_mono
  have he' : extremalEpi 𝒞 F.e := (extremalEpi_iff F.e).2 inferInstance
  obtain ⟨d, ⟨hd₁, hd₂⟩, -⟩ :=
    hg F.e he' (𝟙 X) F.m (by rw [Category.id_comp, F.fac])
  refine ⟨fun {Z} a b hab => ?_⟩
  have h₁ : a ≫ F.e = b ≫ F.e := by
    refine (cancel_mono F.m).1 ?_
    calc (a ≫ F.e) ≫ F.m = a ≫ (F.e ≫ F.m) := by rw [Category.assoc]
      _ = a ≫ g := by rw [F.fac]
      _ = b ≫ g := hab
      _ = b ≫ (F.e ≫ F.m) := by rw [F.fac]
      _ = (b ≫ F.e) ≫ F.m := by rw [Category.assoc]
  calc a = (a ≫ F.e) ≫ d := by rw [Category.assoc, hd₁, Category.comp_id]
    _ = (b ≫ F.e) ≫ d := by rw [h₁]
    _ = b := by rw [Category.assoc, hd₁, Category.comp_id]

/-- The monomorphisms are the right orthogonal class of the extremal epimorphisms. -/
theorem monomorphisms_eq_rightOrth_extremalEpi :
    MorphismProperty.monomorphisms 𝒞 = rightOrth (extremalEpi 𝒞) := by
  ext X Y g
  constructor
  · intro hg a b e he
    have : ExtremalEpi e := (extremalEpi_iff e).1 he
    have : StrongEpi e := (extremalEpi_iff_strongEpi_of_hasPullbacks (f := e)).mp inferInstance
    have : Mono g := hg
    exact OFS.orthogonal_of_strongEpi_of_mono e g
  · intro hg
    exact mono_of_rightOrth_extremalEpi hg

/-- The (extremal epimorphism, monomorphism) orthogonal factorization system of a regular
category. -/
noncomputable def extremalOFS : OFS 𝒞 where
  E := extremalEpi 𝒞
  M := MorphismProperty.monomorphisms 𝒞
  fact := fun {x y} (f : x ⟶ y) => by
    let F := Regular.strongEpiMonoFactorisation f
    exact ⟨F.I, F.e, F.m, (extremalEpi_iff F.e).2 inferInstance, F.m_mono, F.fac⟩
  M_eq := monomorphisms_eq_rightOrth_extremalEpi
  E_eq := rfl

/-- Extremal epimorphisms are stable under base change in a regular category. -/
theorem extremalEpi_isStableUnderBaseChange :
    (extremalEpi 𝒞).IsStableUnderBaseChange where
  of_isPullback {X Y Y' S f g f' g'} sq hg := by
    have hg' : (MorphismProperty.regularEpi 𝒞) g := (MorphismProperty.regularEpi_iff g).2
      ((isRegularEpi_iff_isExtremalEpi g).2 ((extremalEpi_iff g).1 hg))
    have := Regular.regularEpiIsStableUnderBaseChange.of_isPullback sq hg'
    exact (extremalEpi_iff g').2 ((isRegularEpi_iff_isExtremalEpi g').1
      ((MorphismProperty.regularEpi_iff g').1 this))

end RegularCategory

/-! ## Definition 6.4 from Mathlib's regular categories -/

section IsRegularCat

variable [Regular 𝒞]

/-- **A Mathlib-regular category is regular in the sense of Definition 6.4.** -/
theorem isRegularCat_of_regular : IsRegularCat 𝒞 where
  hasFiniteLimits := inferInstance
  exists_ofs := ⟨extremalOFS, rfl⟩
  stable := extremalEpi_isStableUnderBaseChange

end IsRegularCat

end UlmerBialgebras
