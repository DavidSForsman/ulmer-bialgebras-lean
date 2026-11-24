module

public import Foundations.CategoryTheory.Factorization.RegularStableOFS
public import Foundations.CategoryTheory.Factorization.StableRegularOFS
public import Foundations.CategoryTheory.Limits.KernelPairCoequalizer

/-!
# Characterizations of regular categories

Let `𝒞` be a finitely complete category.  The following four conditions are equivalent:

1. every morphism factors as `f = e ≫ m` with `e` a stably extremal epimorphism and `m` a
   monomorphism;
2. `𝒞` carries a stable orthogonal factorization system whose right class is the
   monomorphisms;
3. `𝒞` has coequalizers of kernel pairs and regular epimorphisms are stable under pullback
   (Mathlib's `CategoryTheory.Regular`);
4. `𝒞` has coequalizers of kernel pairs and regular epimorphisms are stably extremal.

The implications are proved in the order 3 ⇒ 4 ⇒ 1 ⇒ 2 ⇒ 3.

The characterization of regularity through stably `S`-extremal epimorphisms
(`condition4_iff_classEpi`, `regular_iff_classEpi`) is due to D. Forsman. It was announced by the
author and will appear in a forthcoming preprint.

## Main results

* `UlmerBialgebras.FactorizationStablyExtremal`, `StableExtremalOFS`, `Condition4` — the
  conditions;
* `condition4_of_regular` — (3) ⇒ (4);
* `factorization_of_condition4` — (4) ⇒ (1);
* `stableExtremalOFS_of_factorization` — (1) ⇒ (2);
* `condition3_of_stableExtremalOFS` — (2) ⇒ (3);
* `condition4_iff_classEpi`, `regular_iff_classEpi` — condition (4) for the class `S` of
  monomorphisms (`ClassEpi.StablySEpi`; `isSEpi_monomorphisms_iff`: with equalizers, the
  `S`-extremal epimorphisms are the extremal ones). The factorization of (4) ⇒ (1) comes from the
  mono lemma `SectionEpi.mono_of_stablySEpi_of_comp`, and for any class `S` containing the sections,
  `ClassEpi.exists_regularEpi_mono_factorization` gives it from "regular epimorphisms are stably
  `S`-extremal".

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 6.4
* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits CategoryTheory.LiftedOFS

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## The four conditions -/

/-- **(1)** Every morphism factors as a stably extremal epimorphism followed by a
monomorphism. -/
def FactorizationStablyExtremal (𝒞 : Type u) [Category.{v} 𝒞] : Prop :=
  ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), ∃ (I : 𝒞) (e : X ⟶ I) (m : I ⟶ Y),
    StablyExtremalEpi e ∧ Mono m ∧ e ≫ m = f

/-- **(2)** A stable orthogonal factorization system whose right class is the monomorphisms. -/
def StableExtremalOFS (𝒞 : Type u) [Category.{v} 𝒞] : Prop :=
  ∃ S : OFS 𝒞, S.M = MorphismProperty.monomorphisms 𝒞 ∧ S.E.IsStableUnderBaseChange

/-- **(4)** Coequalizers of kernel pairs, and regular epimorphisms are stably extremal. -/
def Condition4 (𝒞 : Type u) [Category.{v} 𝒞] [HasFiniteLimits 𝒞] : Prop :=
  HasCoequalizersOfKernelPairs 𝒞 ∧ RegularEpiStablyExtremal 𝒞

/-! ## (3) ⇒ (4) -/

/-- **(3) ⇒ (4)**: in a regular category, regular epimorphisms are stable under pullback, and
a base change of a regular epimorphism is extremal. -/
theorem condition4_of_regular [Regular 𝒞] : Condition4 𝒞 where
  left := by
    intro X Y f
    exact Regular.hasCoequalizer_of_isKernelPair (IsKernelPair.of_hasPullback f)
  right := by
    intro X Y f hf P Z fst snd g sq
    have hf' : (MorphismProperty.regularEpi 𝒞) f := (MorphismProperty.regularEpi_iff f).2 hf
    have hreg : (MorphismProperty.regularEpi 𝒞) snd :=
      Regular.regularEpiIsStableUnderBaseChange.of_isPullback sq hf'
    have : IsRegularEpi snd := (MorphismProperty.regularEpi_iff snd).1 hreg
    infer_instance

/-! ## (4) ⇒ (1) -/

/-- **(4) ⇒ (1)**: the kernel-pair factorization gives the stably extremal factorization. -/
theorem factorization_of_condition4 [HasFiniteLimits 𝒞] (h : Condition4 𝒞) :
    FactorizationStablyExtremal 𝒞 := by
  obtain ⟨hkc, hse⟩ := h
  intro X Y f
  obtain ⟨I, e, m, he, hm, hfac⟩ :=
    exists_regularEpi_mono_factorization_of_stablyExtremal hkc hse f
  exact ⟨I, e, m, hse e he, hm, hfac⟩

/-! ## (1) ⇒ (2) -/

/-- A monic factor of an extremal epimorphism is an isomorphism. -/
lemma isIso_of_extremalEpi_of_factor {X I Y : 𝒞} {g : X ⟶ Y} (hg : extremalEpi 𝒞 g)
    {e : X ⟶ I} {m : I ⟶ Y} [Mono m] (hfac : e ≫ m = g) : IsIso m := by
  obtain ⟨d, ⟨-, hd₂⟩, -⟩ := hg m ‹Mono m› e (𝟙 Y) (by rw [hfac, Category.comp_id])
  have hmul : m ≫ d = 𝟙 I := by
    refine (cancel_mono m).1 ?_
    rw [Category.assoc, hd₂, Category.comp_id, Category.id_comp]
  exact ⟨d, hmul, hd₂⟩

section ImpliesStableOFS

variable [HasFiniteLimits 𝒞]

/-- An extremal epimorphism (as a class) is in the paper's class `extremalEpi`. -/
lemma extremalEpi_of_isExtremalEpi {X Y : 𝒞} {f : X ⟶ Y} (hf : IsExtremalEpi f) :
    extremalEpi 𝒞 f := by
  intro Z W m hm
  have : StrongEpi f := (extremalEpi_iff_strongEpi_of_hasPullbacks (f := f)).mp hf
  exact OFS.orthogonal_of_strongEpi_of_mono f m

/-- **A morphism right orthogonal to every extremal epimorphism is a monomorphism.** -/
lemma mono_of_rightOrth_extremalEpi_of_factorization {X Y : 𝒞} {g : X ⟶ Y}
    (hfac : FactorizationStablyExtremal 𝒞) (hg : rightOrth (extremalEpi 𝒞) g) : Mono g := by
  obtain ⟨I, e, m, he, hm, hf⟩ := hfac g
  have : Mono m := hm
  have he' : extremalEpi 𝒞 e := extremalEpi_of_isExtremalEpi he.isExtremalEpi
  obtain ⟨d, ⟨hd₁, hd₂⟩, -⟩ := hg e he' (𝟙 X) m (by rw [Category.id_comp, hf])
  refine ⟨fun {Z} a b hab => ?_⟩
  have h₁ : a ≫ e = b ≫ e := by
    refine (cancel_mono m).1 ?_
    calc (a ≫ e) ≫ m = a ≫ (e ≫ m) := by rw [Category.assoc]
      _ = a ≫ g := by rw [hf]
      _ = b ≫ g := hab
      _ = b ≫ (e ≫ m) := by rw [hf]
      _ = (b ≫ e) ≫ m := by rw [Category.assoc]
  calc a = a ≫ 𝟙 X := by rw [Category.comp_id]
    _ = (a ≫ e) ≫ d := by rw [Category.assoc, hd₁]
    _ = (b ≫ e) ≫ d := by rw [h₁]
    _ = b ≫ 𝟙 X := by rw [Category.assoc, hd₁]
    _ = b := by rw [Category.comp_id]

/-- **(1) ⇒ (2)**: the stably extremal factorization is a stable orthogonal factorization
system whose right class is the monomorphisms. -/
theorem stableExtremalOFS_of_factorization (h : FactorizationStablyExtremal 𝒞) :
    StableExtremalOFS 𝒞 := by
  refine ⟨{ E := extremalEpi 𝒞
            M := MorphismProperty.monomorphisms 𝒞
            fact := ?_
            M_eq := ?_
            E_eq := rfl }, rfl, ?_⟩
  · intro X Y f
    obtain ⟨I, e, m, he, hm, hfac⟩ := h f
    exact ⟨I, e, m, extremalEpi_of_isExtremalEpi he.isExtremalEpi, hm, hfac⟩
  · ext X Y g
    constructor
    · intro hg a b e he
      exact he g hg
    · intro hg
      exact mono_of_rightOrth_extremalEpi_of_factorization h hg
  · refine ⟨fun {X Y Y' S} {f : X ⟶ S} {g : Y ⟶ S} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
      (sq : IsPullback f' g' g f) (hg : extremalEpi 𝒞 g) => ?_⟩
    obtain ⟨I, e, m, he, hm, hfac⟩ := h g
    have : Mono m := hm
    have : IsIso m := isIso_of_extremalEpi_of_factor hg hfac
    have sq' : IsPullback f' g' e (f ≫ (asIso m).inv) :=
      IsPullback.of_iso sq (Iso.refl Y') (Iso.refl Y) (Iso.refl X) (asIso m).symm
        (by simp) (by simp)
        (by simp [← hfac])
        (by simp)
    exact extremalEpi_of_isExtremalEpi (he f' g' (f ≫ (asIso m).inv) sq')

end ImpliesStableOFS

/-- If `g` coequalizes the kernel pair of `f`, a kernel pair of `⟨f, g⟩ : X ⟶ Y ⨯ Z` is a kernel
pair of `f`. -/
lemma isKernelPair_of_isKernelPair_prodLift
    {X Y Z P : 𝒞} {f : X ⟶ Y} {g : X ⟶ Z} [HasPullback f f] [HasBinaryProduct Y Z]
    {a b : P ⟶ X} (hg : pullback.fst f f ≫ g = pullback.snd f f ≫ g)
    (hkpu : IsKernelPair (prod.lift f g) a b) : IsKernelPair f a b := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk ?_ (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s x hx₁ hx₂ => ?_))
  · -- the square commutes
    have h := hkpu.w =≫ prod.fst
    simpa [Category.assoc] using h
  · -- lift a cone over (f, f) through the kernel pair of `⟨f, g⟩`
    have hg' : s.fst ≫ g = s.snd ≫ g := by
      let v : s.pt ⟶ pullback f f :=
        (IsKernelPair.of_hasPullback f).lift s.fst s.snd s.condition
      calc s.fst ≫ g = (v ≫ pullback.fst f f) ≫ g := by
            rw [(IsKernelPair.of_hasPullback f).lift_fst]
        _ = v ≫ (pullback.fst f f ≫ g) := by rw [Category.assoc]
        _ = v ≫ (pullback.snd f f ≫ g) := by rw [hg]
        _ = (v ≫ pullback.snd f f) ≫ g := by rw [Category.assoc]
        _ = s.snd ≫ g := by rw [(IsKernelPair.of_hasPullback f).lift_snd]
    have hw' : s.fst ≫ prod.lift f g = s.snd ≫ prod.lift f g := by
      refine prod.hom_ext ?_ ?_
      · simpa [Category.assoc] using s.condition
      · simpa [Category.assoc] using hg'
    exact hkpu.lift s.fst s.snd hw'
  · exact hkpu.lift_fst _ _ _
  · exact hkpu.lift_snd _ _ _
  · refine hkpu.hom_ext ?_ ?_
    · exact hx₁.trans (hkpu.lift_fst _ _ _).symm
    · exact hx₂.trans (hkpu.lift_snd _ _ _).symm

/-! ## (2) ⇒ (3) -/

section Condition3

variable (S : OFS 𝒞) (hM : S.M = MorphismProperty.monomorphisms 𝒞)
variable (hstab : S.E.IsStableUnderBaseChange)

include S hM hstab

/-- In a stable OFS with monic right class, every left-class morphism is stably `S`-epic. -/
lemma stablySEpi_of_stablyExtremal {X Y : 𝒞} {f : X ⟶ Y} (hf : S.E f) :
    SectionEpi.StablySEpi f := by
  have hE : S.E = extremalEpi 𝒞 := S.e_eq_extremalEpi hM
  intro P Z fst snd g hpb M k s hs hks
  have he : extremalEpi 𝒞 snd := hE ▸ hstab.of_isPullback hpb hf
  have : Mono s := hs.mono
  exact isIso_of_extremalEpi_of_factor he hks

variable [HasFiniteLimits 𝒞]

/-- **Every extremal epimorphism is regular** in a category with finite limits and a stable OFS
whose right class is the monomorphisms. -/
theorem isRegularEpi_of_extremalEpi_of_stableOFS {X Y : 𝒞} {f : X ⟶ Y}
    (hf : extremalEpi 𝒞 f) : IsRegularEpi f := by
  have : Epi f := OFS.epi_of_leftOrth_monomorphisms hf
  refine IsRegularEpi.of_epi_of_exists
    (fun {Z} {g} (hg : pullback.fst f f ≫ g = pullback.snd f f ≫ g) => ?_)
  -- Factor `⟨f, g⟩ = e ≫ m`; then `e` and `f` share the same kernel pair.
  let u₀ : X ⟶ Y ⨯ Z := prod.lift f g
  obtain ⟨P, e, m, he, hm, hfac⟩ := S.fact u₀
  have hm' : Mono m := by
    rw [hM] at hm
    exact hm
  have : Mono m := hm'
  have hse : SectionEpi.StablySEpi e := stablySEpi_of_stablyExtremal S hM hstab he
  have hkpu : IsKernelPair u₀ (pullback.fst e e) (pullback.snd e e) := by
    rw [← hfac]
    exact isKernelPair_comp_of_mono e m
  have hw : pullback.fst e e ≫ e = pullback.snd e e ≫ e := by
    refine (cancel_mono m).1 ?_
    have h := hkpu.w
    rw [← hfac] at h
    simpa only [Category.assoc] using h
  have hkpf : IsKernelPair f (pullback.fst e e) (pullback.snd e e) :=
    isKernelPair_of_isKernelPair_prodLift hg hkpu
  have hfacf : e ≫ (m ≫ prod.fst) = f := by
    calc e ≫ (m ≫ prod.fst) = (e ≫ m) ≫ prod.fst := by rw [Category.assoc]
      _ = u₀ ≫ prod.fst := by rw [hfac]
      _ = f := by simp [u₀]
  -- By the mono lemma and extremality of `f`, `m ≫ prod.fst` is invertible, giving the descent map.
  have hmono : Mono (m ≫ prod.fst) :=
    SectionEpi.mono_of_stablySEpi_of_comp hkpf hw hfacf hse
  have : Mono (m ≫ prod.fst) := hmono
  have hiso : IsIso (m ≫ prod.fst) := isIso_of_extremalEpi_of_factor hf hfacf
  have : IsIso (m ≫ prod.fst) := hiso
  have hfA : f ≫ inv (m ≫ prod.fst) = e := by
    rw [← hfacf, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨inv (m ≫ prod.fst) ≫ (m ≫ prod.snd), ?_⟩
  rw [← Category.assoc, hfA]
  rw [← Category.assoc, hfac]
  simp [u₀]

/-- Every kernel pair has a coequalizer in a category with finite limits and a stable OFS whose
right class is the monomorphisms. -/
lemma hasCoequalizer_of_isKernelPair_of_stableOFS {X Y : 𝒞} {f : X ⟶ Y}
    {Z : 𝒞} {g₁ g₂ : Z ⟶ X} (hkp : IsKernelPair f g₁ g₂) : HasCoequalizer g₁ g₂ := by
  obtain ⟨P, e, m, he, hm, hfac⟩ := S.fact f
  have hm' : Mono m := by
    rw [hM] at hm
    exact hm
  have hE : S.E = extremalEpi 𝒞 := S.e_eq_extremalEpi hM
  have hextr : extremalEpi 𝒞 e := hE ▸ he
  have hreg : IsRegularEpi e := isRegularEpi_of_extremalEpi_of_stableOFS S hM hstab hextr
  have : IsRegularEpi e := hreg
  have hwe : g₁ ≫ e = g₂ ≫ e :=
    (cancel_mono m).1 (by
      have h := hkp.w
      rw [← hfac] at h
      simpa only [Category.assoc] using h)
  have hkpm : IsKernelPair (e ≫ m) g₁ g₂ := by
    rw [hfac]
    exact hkp
  have hkpe : IsKernelPair e g₁ g₂ := IsKernelPair.cancel_right hwe hkpm
  obtain ⟨hc⟩ := hkpe.isLimit'
  exact HasColimit.mk ⟨Cofork.ofπ e hwe,
    isColimitCoforkOfEffectiveEpi e (PullbackCone.mk g₁ g₂ hwe) hc⟩

end Condition3

section Condition3Regular

variable [HasFiniteLimits 𝒞]

/-- **(2) ⇒ (3)**: a category with finite limits and a stable OFS whose right class is the
monomorphisms is regular in the sense of Mathlib. -/
theorem condition3_of_stableExtremalOFS (h : StableExtremalOFS 𝒞) :
    Regular 𝒞 where
  hasCoequalizer_of_isKernelPair := by
    obtain ⟨S, hM, hstab⟩ := h
    intro X Y Z f g₁ g₂ hkp
    exact hasCoequalizer_of_isKernelPair_of_stableOFS S hM hstab hkp
  regularEpiIsStableUnderBaseChange := by
    obtain ⟨S, hM, hstab⟩ := h
    have hE : S.E = extremalEpi 𝒞 := S.e_eq_extremalEpi hM
    refine ⟨fun {X Y Y' S'} {f : X ⟶ S'} {g : Y ⟶ S'} {f' : Y' ⟶ Y} {g' : Y' ⟶ X}
      (sq : IsPullback f' g' g f) (hg : (MorphismProperty.regularEpi 𝒞) g) => ?_⟩
    have hreg : IsRegularEpi g := (MorphismProperty.regularEpi_iff g).1 hg
    have : IsRegularEpi g := hreg
    have hgextr : extremalEpi 𝒞 g := extremalEpi_of_isExtremalEpi (inferInstance : IsExtremalEpi g)
    have hg'extr : extremalEpi 𝒞 g' := hE ▸ hstab.of_isPullback sq (hE ▸ hgextr)
    exact (MorphismProperty.regularEpi_iff g').2
      (isRegularEpi_of_extremalEpi_of_stableOFS S hM hstab hg'extr)


end Condition3Regular

/-! ## The four conditions agree -/

section Characterization2

variable [HasFiniteLimits 𝒞]

/-- **The four characterizations of regular categories agree.** -/
theorem characterization_regular :
    (FactorizationStablyExtremal 𝒞 ↔ StableExtremalOFS 𝒞) ∧
      (StableExtremalOFS 𝒞 ↔ Regular 𝒞) ∧
      (Regular 𝒞 ↔ Condition4 𝒞) ∧
      (Condition4 𝒞 ↔ FactorizationStablyExtremal 𝒞) := by
  have h12 : FactorizationStablyExtremal 𝒞 → StableExtremalOFS 𝒞 :=
    stableExtremalOFS_of_factorization
  have h23 : StableExtremalOFS 𝒞 → Regular 𝒞 := fun h => by
    obtain ⟨S, hM, hstab⟩ := h
    exact condition3_of_stableExtremalOFS ⟨S, hM, hstab⟩
  have h34 : Regular 𝒞 → Condition4 𝒞 := fun h => by
    have : Regular 𝒞 := h
    exact condition4_of_regular
  have h41 : Condition4 𝒞 → FactorizationStablyExtremal 𝒞 := factorization_of_condition4
  exact ⟨⟨h12, fun h => h41 (h34 (h23 h))⟩,
    ⟨h23, fun h => h12 (h41 (h34 h))⟩,
    ⟨h34, fun h => h23 (h12 (h41 h))⟩,
    ⟨h41, fun h => h34 (h23 (h12 h))⟩⟩

end Characterization2

/-! ## Condition (4) for the class of monomorphisms -/

/-- With equalizers, the `S`-extremal epimorphisms for the class `S` of monomorphisms are the
extremal epimorphisms (an `S`-extremal morphism is epic: it factors through the equalizer of any
two morphisms it equalizes). -/
theorem isSEpi_monomorphisms_iff [HasEqualizers 𝒞] {X Y : 𝒞} (f : X ⟶ Y) :
    ClassEpi.IsSEpi (MorphismProperty.monomorphisms 𝒞) f ↔ IsExtremalEpi f := by
  constructor
  · intro h
    refine IsExtremalEpi.mk ⟨fun {Z} g g' hgg' => ?_⟩ (fun e m hm fac => h e m hm fac)
    have : IsIso (equalizer.ι g g') :=
      h (equalizer.lift f hgg') (equalizer.ι g g') (MorphismProperty.monomorphisms.infer_property _)
        (equalizer.lift_ι _ _)
    exact (cancel_epi (equalizer.ι g g')).1 (equalizer.condition g g')
  · intro h M k s hs hks
    exact h.isIso_of_mono k s hs hks

/-- With equalizers, the stably `S`-extremal epimorphisms for the class `S` of monomorphisms are
the stably extremal epimorphisms. -/
theorem stablySEpi_monomorphisms_iff [HasEqualizers 𝒞] {X Y : 𝒞} (f : X ⟶ Y) :
    ClassEpi.StablySEpi (MorphismProperty.monomorphisms 𝒞) f ↔ StablyExtremalEpi f :=
  ⟨fun h _ _ fst snd g hpb => (isSEpi_monomorphisms_iff snd).1 (h fst snd g hpb),
    fun h _ _ fst snd g hpb => (isSEpi_monomorphisms_iff snd).2 (h fst snd g hpb)⟩

/-- **Condition (4) in terms of a class**: `𝒞` has coequalizers of kernel pairs and its regular
epimorphisms are stably `S`-extremal for the class `S` of monomorphisms (which contains the
sections, `ClassEpi.ContainsSections`, so that `ClassEpi.exists_regularEpi_mono_factorization`
applies). -/
theorem condition4_iff_classEpi [HasFiniteLimits 𝒞] :
    Condition4 𝒞 ↔ HasCoequalizersOfKernelPairs 𝒞 ∧
      ClassEpi.RegularEpiStablySEpi (MorphismProperty.monomorphisms 𝒞) :=
  and_congr Iff.rfl ⟨fun h _ _ f hf => (stablySEpi_monomorphisms_iff f).2 (h f hf),
    fun h _ _ f hf => (stablySEpi_monomorphisms_iff f).1 (h f hf)⟩

/-- The class of monomorphisms contains the sections. -/
theorem containsSections_monomorphisms :
    ClassEpi.ContainsSections (MorphismProperty.monomorphisms 𝒞) :=
  fun _ _ _ hs => (MorphismProperty.monomorphisms.iff _).2 hs.mono

/-- **`𝒞` is regular iff it has coequalizers of kernel pairs and every regular epimorphism is
stably extremal** (`characterization_regular`), with the regular epi–mono factorization obtained
from the mono lemma (`ClassEpi.exists_regularEpi_mono_factorization`). -/
theorem regular_iff_classEpi [HasFiniteLimits 𝒞] :
    Regular 𝒞 ↔ HasCoequalizersOfKernelPairs 𝒞 ∧
      ClassEpi.RegularEpiStablySEpi (MorphismProperty.monomorphisms 𝒞) :=
  characterization_regular.2.2.1.trans condition4_iff_classEpi

/-! ## The paper's regular categories and Mathlib's agree -/

/-- **A category regular in the sense of Definition 6.4 is Mathlib-regular.** -/
theorem regular_of_isRegularCat (h : IsRegularCat 𝒞) : Regular 𝒞 := by
  have := h.hasFiniteLimits
  obtain ⟨S, hSM⟩ := h.exists_ofs
  have hSE : S.E = extremalEpi 𝒞 := S.e_eq_extremalEpi hSM
  exact condition3_of_stableExtremalOFS ⟨S, hSM, hSE ▸ h.stable⟩

end UlmerBialgebras
