module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Foundations.CategoryTheory.Factorization.LiftedFactorizationSystem

/-!
# Extremal epimorphisms are regular when regular epimorphisms are stably section-extremal

Let `𝒞` be a category with pullbacks in which every kernel pair has a coequalizer.  Let `S` be
the class of **sections** (split monomorphisms).  A morphism `f` is an **`S`-epimorphism**
(`UlmerBialgebras.SectionEpi.IsSEpi`) if in every factorization `f = k ≫ s` with `s` a section,
`s` is an isomorphism, and it is **stably `S`-epic** (`SectionEpi.StablySEpi`) if each of its base
changes is an `S`-epimorphism.  If every regular epimorphism is stably `S`-epic, then every
extremal epimorphism is a regular epimorphism, and every
morphism factors as a regular epimorphism followed by a monomorphism.

These results, stably section-extremal epimorphisms and the mono lemma, are due to D. Forsman.
They were announced by the author and will appear in a forthcoming preprint.

## Main results

* `UlmerBialgebras.SectionEpi.sectionPullbackCondition_of_regularEpiStablySEpi`;
* `UlmerBialgebras.SectionEpi.isPullback_id_coeq` — the base change of `k` along `f` is an
  isomorphism;
* `UlmerBialgebras.SectionEpi.isPullback_diagonal`;
* `UlmerBialgebras.SectionEpi.mono_of_regularEpiStablySEpi` — `k` is a monomorphism;
* `UlmerBialgebras.SectionEpi.isRegularEpi_of_isExtremalEpi` — extremal epimorphisms are regular;
* `UlmerBialgebras.SectionEpi.mono_of_stablySEpi_of_comp_of_isPullback` — the mono lemma: if
  `f = e ≫ m`, `e` and `f` have the same kernel pair and `e` is stably `S`-epic, then `m` is a
  monomorphism, using only a pullback of `f` and `m` and a kernel pair of `m` (the `HasPullbacks`
  form `mono_of_stablySEpi_of_comp` is a corollary);
* `UlmerBialgebras.HasCoequalizersOfKernelPairs` and
  `UlmerBialgebras.SectionEpi.exists_regularEpi_mono_factorization_of_regularEpiStablySEpi`.

For a class `S` of morphisms (a `MorphismProperty`), `UlmerBialgebras.ClassEpi.IsSEpi S` and
`UlmerBialgebras.ClassEpi.StablySEpi S` are the `S`-extremal and stably `S`-extremal
epimorphisms; for the class of sections (`ClassEpi.sections`) they are the notions above. When `S`
contains the sections, the results above hold for `S`:
`UlmerBialgebras.ClassEpi.mono_of_stablySEpi_of_comp` and
`UlmerBialgebras.ClassEpi.exists_regularEpi_mono_factorization`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace UlmerBialgebras

open CategoryTheory.LiftedOFS

namespace SectionEpi

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## `S`-epimorphisms, `S` the class of sections -/

/-- `f` is an **`S`-epimorphism**: in every factorization `f = k ≫ s` of `f` through a section
`s`, the section `s` is an isomorphism. -/
def IsSEpi {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ ⦃M : 𝒞⦄ (k : X ⟶ M) (s : M ⟶ Y), IsSplitMono s → k ≫ s = f → IsIso s

/-- `f` is **stably `S`-epic**: each base change of `f` is an `S`-epimorphism. -/
def StablySEpi {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ ⦃P Z : 𝒞⦄ (fst : P ⟶ X) (snd : P ⟶ Z) (g : Z ⟶ Y), IsPullback fst snd f g → IsSEpi snd

/-- The hypothesis that **every regular epimorphism is stably `S`-epic**. -/
def RegularEpiStablySEpi (𝒞 : Type u) [Category.{v} 𝒞] : Prop :=
  ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), IsRegularEpi f → StablySEpi f

/-- The hypothesis used below: *if a regular epimorphism `f` factors as `f = s ≫ k` with `s` a
section, and the pullback `g` of `f` along `k` factors as `g = t ≫ s`, then `s` is an
isomorphism.* -/
def SectionPullbackCondition (𝒞 : Type u) [Category.{v} 𝒞] : Prop :=
  ∀ ⦃X Y M R : 𝒞⦄ (f : X ⟶ Y) (s : X ⟶ M) (k : M ⟶ Y) (fst : R ⟶ X) (g : R ⟶ M) (t : R ⟶ X),
    IsRegularEpi f → IsSplitMono s → s ≫ k = f → IsPullback fst g f k → g = t ≫ s → IsIso s

/-- If every regular epimorphism is stably `S`-epic, then the section condition holds. -/
theorem sectionPullbackCondition_of_regularEpiStablySEpi (h : RegularEpiStablySEpi 𝒞) :
    SectionPullbackCondition 𝒞 := by
  intro X Y M R f s k fst g t hf hs _ hpb hg
  exact h f hf fst g k hpb t s hs hg.symm

/-! ## The kernel-pair coequalizer of a morphism -/

section KernelPairCoeq

variable {A B Q Rf : 𝒞} {f : A ⟶ B} {f₁ f₂ : Rf ⟶ A} {q : A ⟶ Q} {k : Q ⟶ B}

variable (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ q = f₂ ≫ q) (hk : q ≫ k = f)

include hf hq₁ hk

section

variable {P : 𝒞} {pA : P ⟶ A} {φ : P ⟶ Q} (hPB : IsPullback pA φ f k)

include hPB

/-- The comparison morphism `σ = ⟨𝟙, q⟩ : A ⟶ A ×_B Q`, a section of the base change of `k`
along `f`. -/
theorem isPullback_kernelPair_along_section :
    IsPullback f₂ (f₁ ≫ hPB.lift (𝟙 A) q (by rw [Category.id_comp, hk])) q φ := by
  set σ := hPB.lift (𝟙 A) q (by rw [Category.id_comp, hk]) with hσ
  have hσ₁ : σ ≫ pA = 𝟙 A := hPB.lift_fst _ _ _
  have hσ₂ : σ ≫ φ = q := hPB.lift_snd _ _ _
  have hcomm : f₂ ≫ q = (f₁ ≫ σ) ≫ φ := by
    rw [Category.assoc, hσ₂, hq₁]
  -- Any cone over `(q, φ)` induces a pair of maps equalized by `f`.
  have key : ∀ s : PullbackCone q φ, (s.snd ≫ pA) ≫ f = s.fst ≫ f := by
    intro s
    calc (s.snd ≫ pA) ≫ f = s.snd ≫ pA ≫ f := by rw [Category.assoc]
      _ = s.snd ≫ φ ≫ k := by rw [hPB.w]
      _ = (s.snd ≫ φ) ≫ k := by rw [Category.assoc]
      _ = (s.fst ≫ q) ≫ k := by rw [s.condition]
      _ = s.fst ≫ q ≫ k := by rw [Category.assoc]
      _ = s.fst ≫ f := by rw [hk]
  -- Lift into the kernel pair of `f` and check the two projections and uniqueness.
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
    (fun s => hf.lift (s.snd ≫ pA) s.fst (key s)) (fun s => hf.lift_snd _ _ _)
    (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · set L := hf.lift (s.snd ≫ pA) s.fst (key s) with hLdef
    have hL₁ : L ≫ f₁ = s.snd ≫ pA := hf.lift_fst _ _ _
    have hL₂ : L ≫ f₂ = s.fst := hf.lift_snd _ _ _
    refine hPB.hom_ext ?_ ?_
    · calc (L ≫ f₁ ≫ σ) ≫ pA = L ≫ f₁ ≫ σ ≫ pA := by simp only [Category.assoc]
        _ = L ≫ f₁ := by rw [hσ₁, Category.comp_id]
        _ = s.snd ≫ pA := hL₁
    · calc (L ≫ f₁ ≫ σ) ≫ φ = L ≫ f₁ ≫ σ ≫ φ := by simp only [Category.assoc]
        _ = L ≫ f₁ ≫ q := by rw [hσ₂]
        _ = L ≫ f₂ ≫ q := by rw [hq₁]
        _ = (L ≫ f₂) ≫ q := by rw [Category.assoc]
        _ = s.fst ≫ q := by rw [hL₂]
        _ = s.snd ≫ φ := s.condition
  · refine hf.hom_ext ?_ (by rw [hm₁, hf.lift_snd])
    rw [hf.lift_fst]
    calc m ≫ f₁ = m ≫ f₁ ≫ σ ≫ pA := by rw [hσ₁, Category.comp_id]
      _ = (m ≫ f₁ ≫ σ) ≫ pA := by simp only [Category.assoc]
      _ = s.snd ≫ pA := by rw [hm₂]

/-- **The base change of `k` along `f` is an isomorphism**: the square with `𝟙` and `q` on the
left and top and `f`, `k` on the bottom and right is a pullback. -/
theorem isPullback_id_coeq (hcond : SectionPullbackCondition 𝒞)
    (hq : IsColimit (Cofork.ofπ q hq₁)) : IsPullback (𝟙 A) q f k := by
  set σ := hPB.lift (𝟙 A) q (by rw [Category.id_comp, hk]) with hσ
  have hσ₁ : σ ≫ pA = 𝟙 A := hPB.lift_fst _ _ _
  have hσ₂ : σ ≫ φ = q := hPB.lift_snd _ _ _
  have hsplit : IsSplitMono σ := ⟨⟨pA, hσ₁⟩⟩
  have hqreg : IsRegularEpi q :=
    ⟨⟨{ W := Rf, left := f₁, right := f₂, w := hq₁, isColimit := hq }⟩⟩
  have : IsIso σ :=
    hcond q σ φ f₂ (f₁ ≫ σ) f₁ hqreg hsplit hσ₂
      (isPullback_kernelPair_along_section hf hq₁ hk hPB) rfl
  have hpA : pA = inv σ := by
    rw [← Category.id_comp pA, ← IsIso.inv_hom_id σ, Category.assoc, hσ₁, Category.comp_id]
  refine hPB.of_iso (asIso σ).symm (Iso.refl A) (Iso.refl Q) (Iso.refl B) ?_ ?_ ?_ ?_
  · simpa using hpA
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv]
    rw [← hσ₂, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · simp
  · simp

end

end KernelPairCoeq

/-! ## The diagonal of the kernel pair of `k` -/

section Diagonal

variable {A B Q : 𝒞} {f : A ⟶ B} {q : A ⟶ Q} {k : Q ⟶ B} (hk : q ≫ k = f)
variable {Rk : 𝒞} {k₁ k₂ : Rk ⟶ Q} (hkp : IsKernelPair k k₁ k₂)

include hk hkp

/-- **The base change of `q` along the first projection of the kernel pair of `k` factors
through the diagonal** of that kernel pair. -/
theorem isPullback_diagonal (hP : IsPullback (𝟙 A) q f k) :
    IsPullback (𝟙 A) (q ≫ hkp.lift (𝟙 Q) (𝟙 Q) rfl) q k₁ := by
  set Δ := hkp.lift (𝟙 Q) (𝟙 Q) rfl with hΔ
  have hΔ₁ : Δ ≫ k₁ = 𝟙 Q := hkp.lift_fst _ _ _
  have hΔ₂ : Δ ≫ k₂ = 𝟙 Q := hkp.lift_snd _ _ _
  have hcomm : 𝟙 A ≫ q = (q ≫ Δ) ≫ k₁ := by
    rw [Category.id_comp, Category.assoc, hΔ₁, Category.comp_id]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm (fun s => s.fst)
    (fun s => Category.comp_id _) (fun s => ?_) (fun s m hm₁ _ => by simpa using hm₁))
  -- the second component: `s.snd` is determined by `s.fst`
  have hkey : s.fst ≫ q = s.snd ≫ k₂ := by
    have hcond : s.fst ≫ f = (s.snd ≫ k₂) ≫ k := by
      calc s.fst ≫ f = s.fst ≫ q ≫ k := by rw [hk]
        _ = (s.fst ≫ q) ≫ k := by rw [Category.assoc]
        _ = (s.snd ≫ k₁) ≫ k := by rw [s.condition]
        _ = s.snd ≫ k₁ ≫ k := by rw [Category.assoc]
        _ = s.snd ≫ k₂ ≫ k := by rw [hkp.w]
        _ = (s.snd ≫ k₂) ≫ k := by rw [Category.assoc]
    have h₁ : hP.lift s.fst (s.snd ≫ k₂) hcond ≫ 𝟙 A = s.fst := hP.lift_fst _ _ _
    have h₂ : hP.lift s.fst (s.snd ≫ k₂) hcond ≫ q = s.snd ≫ k₂ := hP.lift_snd _ _ _
    rw [Category.comp_id] at h₁
    rw [← h₂, h₁]
  refine hkp.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hΔ₁, Category.comp_id, s.condition]
  · rw [Category.assoc, Category.assoc, hΔ₂, Category.comp_id, hkey]

end Diagonal

/-- **The morphism induced on the kernel-pair coequalizer is a monomorphism**, granted that
regular epimorphisms are stably `S`-epic. -/
theorem mono_of_regularEpiStablySEpi {A B Q Rf : 𝒞} {f : A ⟶ B} {f₁ f₂ : Rf ⟶ A} {q : A ⟶ Q}
    {k : Q ⟶ B} (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ q = f₂ ≫ q) (hk : q ≫ k = f)
    {Rk : 𝒞} {k₁ k₂ : Rk ⟶ Q} (hkp : IsKernelPair k k₁ k₂) [HasPullbacks 𝒞]
    (h : RegularEpiStablySEpi 𝒞) (hq : IsColimit (Cofork.ofπ q hq₁)) : Mono k := by
  have hqreg : IsRegularEpi q :=
    ⟨⟨{ W := Rf, left := f₁, right := f₂, w := hq₁, isColimit := hq }⟩⟩
  have hP : IsPullback (𝟙 A) q f k :=
    isPullback_id_coeq hf hq₁ hk (IsPullback.of_hasPullback f k)
      (sectionPullbackCondition_of_regularEpiStablySEpi h) hq
  set Δ := hkp.lift (𝟙 Q) (𝟙 Q) rfl with hΔ
  have hΔ₁ : Δ ≫ k₁ = 𝟙 Q := hkp.lift_fst _ _ _
  have hsplit : IsSplitMono Δ := ⟨⟨k₁, hΔ₁⟩⟩
  have : IsIso Δ :=
    h q hqreg (𝟙 A) (q ≫ Δ) k₁ (isPullback_diagonal hk hkp hP) q Δ hsplit rfl
  have : IsIso k₁ := by
    have : k₁ = inv Δ := by
      rw [← Category.id_comp k₁, ← IsIso.inv_hom_id Δ, Category.assoc, hΔ₁, Category.comp_id]
    rw [this]; infer_instance
  exact hkp.mono_of_isIso_fst

/-- **Extremal epimorphisms are regular epimorphisms** in a category with pullbacks in which
kernel pairs have coequalizers and every regular epimorphism is stably `S`-epic. -/
theorem isRegularEpi_of_isExtremalEpi {A B Q Rf : 𝒞} {f : A ⟶ B} {f₁ f₂ : Rf ⟶ A} {q : A ⟶ Q}
    {k : Q ⟶ B} (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ q = f₂ ≫ q) (hk : q ≫ k = f)
    [HasPullbacks 𝒞] (h : RegularEpiStablySEpi 𝒞) (hq : IsColimit (Cofork.ofπ q hq₁))
    (hextr : IsExtremalEpi f) : IsRegularEpi f := by
  have : Mono k := mono_of_regularEpiStablySEpi hf hq₁ hk (IsPullback.of_hasPullback k k) h hq
  have : IsIso k := hextr.isIso_of_mono q k inferInstance hk
  exact ⟨⟨RegularEpi.ofArrowIso (Arrow.isoMk (Iso.refl A) (asIso k) (by simpa using hk.symm))
    { W := Rf, left := f₁, right := f₂, w := hq₁, isColimit := hq }⟩⟩

end SectionEpi

namespace SectionEpi

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## The monic part of a stably `S`-epic factorization -/

section StablySEpiMono

variable {A B Q Rf : 𝒞} {f : A ⟶ B} {e : A ⟶ Q} {m : Q ⟶ B}
variable {f₁ f₂ : Rf ⟶ A}

/-- The base change of a stably `S`-epic morphism `e` along `f` is an isomorphism, when `e` and
`f` have the same kernel pair. -/
theorem isPullback_id_stablySEpi {P : 𝒞} {pA : P ⟶ A} {φ : P ⟶ Q}
    (hPB : IsPullback pA φ f m) (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ e = f₂ ≫ e)
    (hk : e ≫ m = f) (hse : StablySEpi e) : IsPullback (𝟙 A) e f m := by
  set σ := hPB.lift (𝟙 A) e (by rw [Category.id_comp, hk]) with hσ
  have hσ₁ : σ ≫ pA = 𝟙 A := hPB.lift_fst _ _ _
  have hσ₂ : σ ≫ φ = e := hPB.lift_snd _ _ _
  have hsplit : IsSplitMono σ := ⟨⟨pA, hσ₁⟩⟩
  have : IsIso σ :=
    hse f₂ (f₁ ≫ σ) φ (isPullback_kernelPair_along_section hf hq₁ hk hPB) f₁ σ hsplit rfl
  have hpA : pA = inv σ := by
    rw [← Category.id_comp pA, ← IsIso.inv_hom_id σ, Category.assoc, hσ₁, Category.comp_id]
  refine hPB.of_iso (asIso σ).symm (Iso.refl A) (Iso.refl Q) (Iso.refl B) ?_ ?_ ?_ ?_
  · simpa using hpA
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv]
    rw [← hσ₂]
    simp
  · simp
  · simp

/-- **The mono lemma, from one pullback**: if `f = e ≫ m` with `e` stably `S`-epic and `e` and `f`
having the same kernel pair, then `m` is a monomorphism. The only limits used are a pullback of
`f` and `m` (`hPB`) and a kernel pair of `m` (`hkp`); no `HasPullbacks` is assumed. Some pullback
of `f` and `m` is needed: `StablySEpi e` speaks only of the base changes of `e` that exist, and the
proof uses the base change of `e` along the first projection of the kernel pair of `m`, whose
apex is a pullback of `f` and `m`. -/
theorem mono_of_stablySEpi_of_comp_of_isPullback {P : 𝒞} {pA : P ⟶ A} {φ : P ⟶ Q}
    (hPB : IsPullback pA φ f m) {Rm : 𝒞} {m₁ m₂ : Rm ⟶ Q} (hkp : IsKernelPair m m₁ m₂)
    (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ e = f₂ ≫ e) (hk : e ≫ m = f)
    (hse : StablySEpi e) : Mono m := by
  have hP : IsPullback (𝟙 A) e f m := isPullback_id_stablySEpi hPB hf hq₁ hk hse
  let Δ := hkp.lift (𝟙 Q) (𝟙 Q) rfl
  have hΔ₁ : Δ ≫ m₁ = 𝟙 Q := hkp.lift_fst _ _ _
  have hsplit : IsSplitMono Δ := ⟨⟨m₁, hΔ₁⟩⟩
  have : IsIso Δ := hse (𝟙 A) (e ≫ Δ) m₁ (isPullback_diagonal hk hkp hP) e Δ hsplit rfl
  have : IsIso m₁ := by
    have h : m₁ = inv Δ := by
      rw [← Category.id_comp m₁, ← IsIso.inv_hom_id Δ, Category.assoc, hΔ₁, Category.comp_id]
    rw [h]; infer_instance
  exact hkp.mono_of_isIso_fst

/-- **The mono lemma, with the pullback of `f` and `m` and the kernel pair of `m` as instances**
(`mono_of_stablySEpi_of_comp_of_isPullback`). -/
theorem mono_of_stablySEpi_of_comp_of_hasPullback [HasPullback f m] [HasPullback m m]
    (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ e = f₂ ≫ e) (hk : e ≫ m = f)
    (hse : StablySEpi e) : Mono m :=
  mono_of_stablySEpi_of_comp_of_isPullback (IsPullback.of_hasPullback f m)
    (IsKernelPair.of_hasPullback m) hf hq₁ hk hse

/-- **If `f = e ≫ m` with `e` stably `S`-epic and `e` and `f` having the same kernel pair, then
`m` is a monomorphism** (in a category with pullbacks; a corollary of
`mono_of_stablySEpi_of_comp_of_isPullback`). -/
theorem mono_of_stablySEpi_of_comp [HasPullbacks 𝒞] (hf : IsKernelPair f f₁ f₂)
    (hq₁ : f₁ ≫ e = f₂ ≫ e) (hk : e ≫ m = f) (hse : StablySEpi e) : Mono m :=
  mono_of_stablySEpi_of_comp_of_hasPullback hf hq₁ hk hse

end StablySEpiMono

end SectionEpi



/-! ## Coequalizers of kernel pairs and the factorization -/

/-- Every kernel pair has a coequalizer. -/
def HasCoequalizersOfKernelPairs (𝒞 : Type u) [Category.{v} 𝒞] [HasPullbacks 𝒞] : Prop :=
  ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), HasCoequalizer (pullback.fst f f) (pullback.snd f f)

namespace SectionEpi

variable {𝒞 : Type u} [Category.{v} 𝒞] [HasPullbacks 𝒞]

/-- **Every morphism factors as a regular epimorphism followed by a monomorphism** when regular
epimorphisms are stably `S`-epic. -/
theorem exists_regularEpi_mono_factorization_of_regularEpiStablySEpi
    (hkc : HasCoequalizersOfKernelPairs 𝒞) (h : RegularEpiStablySEpi 𝒞) {X Y : 𝒞} (f : X ⟶ Y) :
    ∃ (I : 𝒞) (e : X ⟶ I) (m : I ⟶ Y), IsRegularEpi e ∧ Mono m ∧ e ≫ m = f := by
  have := hkc f
  let hq := coequalizerIsCoequalizer (pullback.fst f f) (pullback.snd f f)
  let m : coequalizer (pullback.fst f f) (pullback.snd f f) ⟶ Y :=
    Cofork.IsColimit.desc hq f pullback.condition
  have hqm : coequalizer.π (pullback.fst f f) (pullback.snd f f) ≫ m = f :=
    Cofork.IsColimit.π_desc' hq f pullback.condition
  have hπ : IsRegularEpi (coequalizer.π (pullback.fst f f) (pullback.snd f f)) :=
    ⟨⟨RegularEpi.mk (pullback f f) (pullback.fst f f) (pullback.snd f f)
      (coequalizer.condition (pullback.fst f f) (pullback.snd f f)) hq⟩⟩
  -- the mono lemma (`mono_of_stablySEpi_of_comp`): the coequalizer of the kernel pair of `f` has
  -- the kernel pair of `f`, and it is a regular, hence stably `S`-epic, epimorphism
  exact ⟨_, coequalizer.π _ _, m, hπ, mono_of_stablySEpi_of_comp (IsKernelPair.of_hasPullback f)
    (coequalizer.condition _ _) hqm (h _ hπ), hqm⟩

end SectionEpi

/-! ## `S`-extremal epimorphisms for a class `S` of monomorphisms -/

namespace ClassEpi

variable {𝒞 : Type u} [Category.{v} 𝒞] (S : MorphismProperty 𝒞)

/-- `f` is an **`S`-extremal epimorphism**: in every factorization `f = k ≫ s` of `f` through a
morphism `s` of `S`, `s` is an isomorphism. -/
def IsSEpi {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ ⦃M : 𝒞⦄ (k : X ⟶ M) (s : M ⟶ Y), S s → k ≫ s = f → IsIso s

/-- `f` is a **stably `S`-extremal epimorphism**: each base change of `f` is `S`-extremal. -/
def StablySEpi {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ ⦃P Z : 𝒞⦄ (fst : P ⟶ X) (snd : P ⟶ Z) (g : Z ⟶ Y), IsPullback fst snd f g → IsSEpi S snd

/-- The class of **sections** (split monomorphisms). -/
def sections : MorphismProperty 𝒞 := fun _ _ s => IsSplitMono s

/-- `S` **contains the sections**. -/
def ContainsSections : Prop := sections ≤ S

variable {S}

/-- An `S`-extremal epimorphism is extremal for any smaller class. -/
theorem IsSEpi.anti {S' : MorphismProperty 𝒞} (hS : S' ≤ S) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : IsSEpi S f) : IsSEpi S' f :=
  fun _ k s hs hks => hf k s (hS _ hs) hks

/-- A stably `S`-extremal epimorphism is stably extremal for any smaller class. -/
theorem StablySEpi.anti {S' : MorphismProperty 𝒞} (hS : S' ≤ S) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : StablySEpi S f) : StablySEpi S' f :=
  fun _ _ fst snd g h => (hf fst snd g h).anti hS

/-- For the class of sections, `S`-extremal epimorphisms are `SectionEpi.IsSEpi`. -/
theorem isSEpi_sections_iff {X Y : 𝒞} (f : X ⟶ Y) :
    IsSEpi sections f ↔ SectionEpi.IsSEpi f := Iff.rfl

/-- For the class of sections, stably `S`-extremal epimorphisms are `SectionEpi.StablySEpi`. -/
theorem stablySEpi_sections_iff {X Y : 𝒞} (f : X ⟶ Y) :
    StablySEpi sections f ↔ SectionEpi.StablySEpi f := Iff.rfl

/-- If `S` contains the sections, a stably `S`-extremal epimorphism is stably section-extremal. -/
theorem StablySEpi.sectionEpi (hS : ContainsSections S) {X Y : 𝒞} {f : X ⟶ Y}
    (hf : StablySEpi S f) : SectionEpi.StablySEpi f :=
  (stablySEpi_sections_iff f).1 (hf.anti hS)

/-- **The mono lemma for a class `S` containing the sections, from one pullback**: if
`f = e ≫ m`, `e` and `f` have the same kernel pair and `e` is stably `S`-extremal, then `m` is a
monomorphism; the limits used are a pullback of `f` and `m` and a kernel pair of `m`. -/
theorem mono_of_stablySEpi_of_comp_of_isPullback (hS : ContainsSections S)
    {A B Q Rf P Rm : 𝒞} {f : A ⟶ B} {e : A ⟶ Q} {m : Q ⟶ B} {f₁ f₂ : Rf ⟶ A}
    {pA : P ⟶ A} {φ : P ⟶ Q} (hPB : IsPullback pA φ f m) {m₁ m₂ : Rm ⟶ Q}
    (hkp : IsKernelPair m m₁ m₂) (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ e = f₂ ≫ e)
    (hk : e ≫ m = f) (hse : StablySEpi S e) : Mono m :=
  SectionEpi.mono_of_stablySEpi_of_comp_of_isPullback hPB hkp hf hq₁ hk (hse.sectionEpi hS)

/-- **The mono lemma for a class `S` containing the sections**: if `f = e ≫ m`, `e` and `f` have
the same kernel pair and `e` is stably `S`-extremal, then `m` is a monomorphism. -/
theorem mono_of_stablySEpi_of_comp [HasPullbacks 𝒞] (hS : ContainsSections S)
    {A B Q Rf : 𝒞} {f : A ⟶ B} {e : A ⟶ Q} {m : Q ⟶ B} {f₁ f₂ : Rf ⟶ A}
    (hf : IsKernelPair f f₁ f₂) (hq₁ : f₁ ≫ e = f₂ ≫ e) (hk : e ≫ m = f)
    (hse : StablySEpi S e) : Mono m :=
  SectionEpi.mono_of_stablySEpi_of_comp hf hq₁ hk (hse.sectionEpi hS)

/-- The hypothesis that **every regular epimorphism is stably `S`-extremal**. -/
def RegularEpiStablySEpi (S : MorphismProperty 𝒞) : Prop :=
  ∀ ⦃X Y : 𝒞⦄ (f : X ⟶ Y), IsRegularEpi f → StablySEpi S f

/-- If `S` contains the sections and every regular epimorphism is stably `S`-extremal, then every
regular epimorphism is stably section-extremal. -/
theorem RegularEpiStablySEpi.sectionEpi (hS : ContainsSections S)
    (h : RegularEpiStablySEpi S) : SectionEpi.RegularEpiStablySEpi 𝒞 :=
  fun _ _ f hf => (h f hf).sectionEpi hS

/-- **Every morphism factors as a regular epimorphism followed by a monomorphism** when kernel
pairs have coequalizers and regular epimorphisms are stably `S`-extremal for a class `S`
containing the sections. -/
theorem exists_regularEpi_mono_factorization [HasPullbacks 𝒞]
    (hkc : HasCoequalizersOfKernelPairs 𝒞) (hS : ContainsSections S)
    (h : RegularEpiStablySEpi S) {X Y : 𝒞} (f : X ⟶ Y) :
    ∃ (I : 𝒞) (e : X ⟶ I) (m : I ⟶ Y), IsRegularEpi e ∧ Mono m ∧ e ≫ m = f :=
  SectionEpi.exists_regularEpi_mono_factorization_of_regularEpiStablySEpi hkc
    (h.sectionEpi hS) f

end ClassEpi

end UlmerBialgebras
