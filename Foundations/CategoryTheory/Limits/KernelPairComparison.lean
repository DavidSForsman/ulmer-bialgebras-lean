module

public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ExtremalEpi
public import Foundations.CategoryTheory.Factorization.LiftedFactorizationSystem

/-!
# Comparison morphisms of a square and of its kernel-pair extension

Let `𝒞` be a category with pullbacks and let

```
  A --f--> B
  |        |
  u        v
  v        v
  C --g--> D
```

be a commutative square. Extending it *horizontally* by the kernel pairs `f₁, f₂ : Rf ⇉ A` of
`f` and `g₁, g₂ : Rg ⇉ C` of `g` produces the induced morphism `w : Rf ⟶ Rg` and two further
commutative squares with the *same* vertical morphisms `w` and `u`, namely the squares
`(f₁, g₁)` and `(f₂, g₂)`.

Write `P` for the pullback of `g` and `v` and `c : A ⟶ P` for the comparison morphism of the
original square; write `P₁` for the pullback of `g₁` and `u` and `c₁ : Rf ⟶ P₁` for the
comparison morphism of the first kernel-pair square. There is a canonical morphism
`φ : P₁ ⟶ P` between the two pullback objects, obtained from the universal property of `P`.
Similarly, write `P₂` for the pullback of `g₂` and `u`, `c₂ : Rf ⟶ P₂` for the second comparison,
and `φ₂ : P₂ ⟶ P` for the canonical morphism.

This file proves that the comparison squares are pullbacks:

* `UlmerBialgebras.KernelPairComparison.isPullback_pullbackObjHom` — the square relating the
  morphism `φ` between the two pullback objects and the top morphism `f`, exhibiting `φ` as a
  base change of `f`;
* `UlmerBialgebras.KernelPairComparison.isPullback_comparison` — the square relating the two
  comparison morphisms, exhibiting `c₁` as a base change of `c`;
* `UlmerBialgebras.KernelPairComparison.isPullback_comparison₂` — the square relating `c₂` and `c`.

The consequences drawn here are:

1. **Monomorphisms are reflected and preserved**: if one of `c, c₁, c₂` is a monomorphism, all
   three are (`mono_comparison_of_mono`, `mono_kernelPairComparison_of_mono`,
   `mono_iff_mono_kernelPairComparison`,
   `mono_kernelPairComparison_iff_mono_kernelPairComparison₂`);
2. `UlmerBialgebras.KernelPairComparison.isPullback_kernelPair_square` (and
   `isIso_kernelPairComparison_of_isIso`) — if the original square is a pullback, then so are the
   squares of kernel pairs;
3. `UlmerBialgebras.KernelPairComparison.isExtremalEpi_comparison_of_isExtremalEpi` — if the top
   morphism `f` is a *stably* extremal epimorphism, then extremal epimorphy is reflected from
   `c₁` to `c`, and hence (`isIso_comparison_of_isIso`) isomorphy is reflected as well.

This result, the pullback comparison lemma, is due to D. Forsman. It was announced by the author
and will appear in a forthcoming preprint.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic]
* [M. Barr, *Exact Categories*][Ba]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits LiftedOFS

variable {𝒞 : Type u} [Category.{v} 𝒞]

/-! ## Generalities on extremal epimorphisms -/

/-- A monic extremal epimorphism is an isomorphism. -/
theorem isIso_of_isExtremalEpi_of_mono {X Y : 𝒞} {f : X ⟶ Y} (hf : ExtremalEpi f) [Mono f] :
    IsIso f :=
  hf.isIso (𝟙 X) f (Category.id_comp f)

/-- A split epimorphism is an extremal epimorphism. -/
theorem isExtremalEpi_of_isSplitEpi {X Y : 𝒞} (f : X ⟶ Y) [IsSplitEpi f] : ExtremalEpi f where
  isIso {Z} e m fac hm := by
    have : IsSplitEpi m := ⟨⟨section_ f ≫ e, by rw [Category.assoc, fac, IsSplitEpi.id]⟩⟩
    exact isIso_of_mono_of_isSplitEpi m

/-- A right factor of an extremal epimorphism is an extremal epimorphism. -/
theorem isExtremalEpi_of_comp {X Y Z : 𝒞} (h : X ⟶ Y) (c : Y ⟶ Z)
    (hc : ExtremalEpi (h ≫ c)) : ExtremalEpi c where
  toEpi := epi_of_epi h c
  isIso {W} e m fac hm := by
    have : (h ≫ e) ≫ m = h ≫ c := by rw [Category.assoc, fac]
    exact hc.isIso (h ≫ e) m this

/-- **Extremal epimorphisms compose** (in a category with pullbacks). -/
theorem isExtremalEpi_comp [HasPullbacks 𝒞] {X Y Z : 𝒞} {e₁ : X ⟶ Y} {e₂ : Y ⟶ Z}
    (h₁ : ExtremalEpi e₁) (h₂ : ExtremalEpi e₂) : ExtremalEpi (e₁ ≫ e₂) where
  toEpi := epi_comp e₁ e₂
  isIso {W} t m hcomp hm := by
    have : Mono (pullback.fst e₂ m) := pullback.fst_of_mono
    have hlift : pullback.lift e₁ t hcomp.symm ≫ pullback.fst e₂ m = e₁ := pullback.lift_fst _ _ _
    have : IsIso (pullback.fst e₂ m) := h₁.isIso _ _ hlift
    refine h₂.isIso (inv (pullback.fst e₂ m) ≫ pullback.snd e₂ m) m ?_
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

/-- A morphism is **stably extremal epic** if each of its base changes is an extremal
epimorphism. -/
def StablyExtremalEpi {X Y : 𝒞} (f : X ⟶ Y) : Prop :=
  ∀ ⦃P Z : 𝒞⦄ (fst : P ⟶ X) (snd : P ⟶ Z) (g : Z ⟶ Y), IsPullback fst snd f g →
    IsExtremalEpi snd

/-- A stably extremal epimorphism is an extremal epimorphism. -/
theorem StablyExtremalEpi.isExtremalEpi {X Y : 𝒞} {f : X ⟶ Y} (hf : StablyExtremalEpi f) :
    IsExtremalEpi f :=
  hf (𝟙 X) f (𝟙 Y) (IsPullback.of_horiz_isIso ⟨by simp⟩)

namespace KernelPairComparison

/-! ## The setting

The data of the square, of the kernel pairs of its horizontal morphisms, of the two pullbacks
and of the induced morphisms. Each induced morphism is described by its components, which
determine it uniquely.
-/

variable {A B C D : 𝒞} {f : A ⟶ B} {u : A ⟶ C} {v : B ⟶ D} {g : C ⟶ D}
  {Rf Rg P P₁ : 𝒞} {f₁ f₂ : Rf ⟶ A} {g₁ g₂ : Rg ⟶ C}
  {p : P ⟶ C} {pB : P ⟶ B} {p₁ : P₁ ⟶ Rg} {q₁ : P₁ ⟶ A}
  {w : Rf ⟶ Rg} {c : A ⟶ P} {c₁ : Rf ⟶ P₁} {φ : P₁ ⟶ P}
  -- the square commutes
  (hsq : f ≫ v = u ≫ g)
  -- the kernel pairs of the two horizontal morphisms
  (hf : IsKernelPair f f₁ f₂) (hg : IsKernelPair g g₁ g₂)
  -- the induced morphism between the kernel pairs
  (hw₁ : w ≫ g₁ = f₁ ≫ u) (hw₂ : w ≫ g₂ = f₂ ≫ u)
  -- the pullback of the original square and its comparison morphism
  (hP : IsPullback p pB g v) (hc₁ : c ≫ p = u) (hc₂ : c ≫ pB = f)
  -- the pullback of the first kernel-pair square and its comparison morphism
  (hP₁ : IsPullback p₁ q₁ g₁ u) (hcc₁ : c₁ ≫ p₁ = w) (hcc₂ : c₁ ≫ q₁ = f₁)
  -- the induced morphism between the two pullback objects
  (hφ₁ : φ ≫ p = p₁ ≫ g₂) (hφ₂ : φ ≫ pB = q₁ ≫ f)

/-! ## The two pullback squares -/

include hsq hg hP hP₁ hφ₁ hφ₂ in
/-- **The square relating the two pullback objects is a pullback**: the morphism `φ : P₁ ⟶ P`
between the pullback of the kernel-pair square and the pullback of the original square is the
base change of the top morphism `f` along the projection `pB : P ⟶ B`. -/
theorem isPullback_pullbackObjHom : IsPullback φ q₁ pB f := by
  have key : ∀ s : PullbackCone pB f, (s.snd ≫ u) ≫ g = (s.fst ≫ p) ≫ g := by
    intro s
    calc (s.snd ≫ u) ≫ g = s.snd ≫ u ≫ g := by rw [Category.assoc]
      _ = s.snd ≫ f ≫ v := by rw [hsq]
      _ = (s.snd ≫ f) ≫ v := by rw [Category.assoc]
      _ = (s.fst ≫ pB) ≫ v := by rw [s.condition]
      _ = s.fst ≫ pB ≫ v := by rw [Category.assoc]
      _ = s.fst ≫ p ≫ g := by rw [hP.w]
      _ = (s.fst ≫ p) ≫ g := by rw [Category.assoc]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hφ₂
    (fun s => hP₁.lift (hg.lift (s.snd ≫ u) (s.fst ≫ p) (key s)) s.snd
      (hg.lift_fst _ _ (key s))) (fun s => ?_) (fun s => hP₁.lift_snd _ _ _)
    (fun s m hm₁ hm₂ => ?_))
  · refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hφ₁, ← Category.assoc, hP₁.lift_fst, hg.lift_snd]
    · rw [Category.assoc, hφ₂, ← Category.assoc, hP₁.lift_snd, s.condition]
  · refine hP₁.hom_ext ?_ (by rw [hm₂, hP₁.lift_snd])
    rw [hP₁.lift_fst]
    refine hg.hom_ext ?_ ?_
    · rw [Category.assoc, hP₁.w, ← Category.assoc, hm₂, hg.lift_fst]
    · rw [Category.assoc, ← hφ₁, ← Category.assoc, hm₁, hg.lift_snd]

include hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ in
/-- **The square relating the two comparison morphisms is a pullback**: the comparison
morphism `c₁` of the kernel-pair square is the base change of the comparison morphism `c` of
the original square along `φ`. -/
theorem isPullback_comparison (hw₁ : w ≫ g₁ = f₁ ≫ u) : IsPullback c₁ f₂ φ c := by
  have hcomm : c₁ ≫ φ = f₂ ≫ c := by
    refine hP.hom_ext ?_ ?_
    · rw [Category.assoc, hφ₁, ← Category.assoc, hcc₁, hw₂, Category.assoc, hc₁]
    · rw [Category.assoc, hφ₂, ← Category.assoc, hcc₂, Category.assoc, hc₂, hf.w]
  have key : ∀ s : PullbackCone φ c, (s.fst ≫ q₁) ≫ f = s.snd ≫ f := by
    intro s
    calc (s.fst ≫ q₁) ≫ f = s.fst ≫ q₁ ≫ f := by rw [Category.assoc]
      _ = s.fst ≫ φ ≫ pB := by rw [hφ₂]
      _ = (s.fst ≫ φ) ≫ pB := by rw [Category.assoc]
      _ = (s.snd ≫ c) ≫ pB := by rw [s.condition]
      _ = s.snd ≫ c ≫ pB := by rw [Category.assoc]
      _ = s.snd ≫ f := by rw [hc₂]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm
    (fun s => hf.lift (s.fst ≫ q₁) s.snd (key s)) (fun s => ?_)
    (fun s => hf.lift_snd _ _ _) (fun s m hm₁ hm₂ => ?_))
  · refine hP₁.hom_ext ?_ ?_
    · rw [Category.assoc, hcc₁]
      refine hg.hom_ext ?_ ?_
      · rw [Category.assoc, hw₁, ← Category.assoc, hf.lift_fst, Category.assoc, ← hP₁.w,
          Category.assoc]
      · rw [Category.assoc, hw₂, ← Category.assoc, hf.lift_snd, ← hc₁, ← Category.assoc,
          ← s.condition, Category.assoc, hφ₁, Category.assoc]
    · rw [Category.assoc, hcc₂, hf.lift_fst]
  · refine hf.hom_ext ?_ (by rw [hm₂, hf.lift_snd])
    rw [hf.lift_fst, ← hcc₂, ← Category.assoc, hm₁]

/-! ## Consequence 1: Monomorphisms are reflected and preserved -/

include hf hg hw₁ hw₂ hc₁ hc₂ hP₁ hcc₁ hcc₂ in
/-- **Monomorphisms are reflected.** If the comparison morphism of the kernel-pair square is a
monomorphism, then so is the comparison morphism of the original square. -/
theorem mono_comparison_of_mono (h : Mono c₁) : Mono c := by
  refine ⟨fun {X} h₁ h₂ heq => ?_⟩
  have hu : h₁ ≫ u = h₂ ≫ u := by rw [← hc₁, ← Category.assoc, heq, Category.assoc]
  have hfe : h₁ ≫ f = h₂ ≫ f := by rw [← hc₂, ← Category.assoc, heq, Category.assoc]
  have hr₁ : hf.lift h₁ h₂ hfe ≫ f₁ = h₁ := hf.lift_fst _ _ _
  have hr₂ : hf.lift h₁ h₂ hfe ≫ f₂ = h₂ := hf.lift_snd _ _ _
  have hd₁ : hf.lift h₁ h₁ rfl ≫ f₁ = h₁ := hf.lift_fst _ _ _
  have hd₂ : hf.lift h₁ h₁ rfl ≫ f₂ = h₁ := hf.lift_snd _ _ _
  have hww : hf.lift h₁ h₂ hfe ≫ w = hf.lift h₁ h₁ rfl ≫ w := by
    refine hg.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hw₁, ← Category.assoc, ← Category.assoc, hr₁, hd₁]
    · rw [Category.assoc, Category.assoc, hw₂, ← Category.assoc, ← Category.assoc, hr₂, hd₂, hu]
  have hkey : hf.lift h₁ h₂ hfe ≫ c₁ = hf.lift h₁ h₁ rfl ≫ c₁ := by
    refine hP₁.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hcc₁, hww]
    · rw [Category.assoc, Category.assoc, hcc₂, hr₁, hd₁]
  have heq' := h.right_cancellation _ _ hkey
  calc h₁ = hf.lift h₁ h₁ rfl ≫ f₂ := hd₂.symm
    _ = hf.lift h₁ h₂ hfe ≫ f₂ := by rw [heq']
    _ = h₂ := hr₂

include hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ in
/-- **Monomorphisms are preserved.** If the comparison morphism of the original square is a
monomorphism, then so is the comparison morphism of the kernel-pair square. -/
theorem mono_kernelPairComparison_of_mono (hw₁ : w ≫ g₁ = f₁ ≫ u) [Mono c] : Mono c₁ := by
  have hpb := isPullback_comparison hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ hw₁
  exact hpb.mono_fst_of_mono

include hf hg hw₁ hw₂ hc₁ hc₂ hP₁ hcc₁ hcc₂ hP hφ₁ hφ₂ in
/-- **Equivalence of monomorphism property.** The comparison morphism of the original square
is a monomorphism if and only if the comparison morphism of the first kernel-pair square is. -/
theorem mono_iff_mono_kernelPairComparison : Mono c ↔ Mono c₁ :=
  ⟨fun _ => mono_kernelPairComparison_of_mono hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ hw₁,
   fun h => mono_comparison_of_mono hf hg hw₁ hw₂ hc₁ hc₂ hP₁ hcc₁ hcc₂ h⟩

/-! ## The second kernel-pair square -/

variable {P₂ : 𝒞} {p₂ : P₂ ⟶ Rg} {q₂ : P₂ ⟶ A} {c₂ : Rf ⟶ P₂} {φ₂ : P₂ ⟶ P}
  -- the pullback of the second kernel-pair square and its comparison morphism
  (hP₂ : IsPullback p₂ q₂ g₂ u) (hcc₂₁ : c₂ ≫ p₂ = w) (hcc₂₂ : c₂ ≫ q₂ = f₂)
  -- the induced morphism between P₂ and P
  (hφ₂₁ : φ₂ ≫ p = p₂ ≫ g₁) (hφ₂₂ : φ₂ ≫ pB = q₂ ≫ f)

include hf hg hw₁ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂ in
/-- **The square relating the second comparison morphism is a pullback.** -/
theorem isPullback_comparison₂ (hw₂ : w ≫ g₂ = f₂ ≫ u) : IsPullback c₂ f₁ φ₂ c := by
  have hf_flip : IsKernelPair f f₂ f₁ := hf.flip
  have hg_flip : IsKernelPair g g₂ g₁ := hg.flip
  exact isPullback_comparison hf_flip hg_flip hw₁ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂ hw₂

include hf hg hw₁ hw₂ hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ in
/-- **Monomorphisms are reflected from the second kernel-pair square.** -/
theorem mono_comparison_of_mono₂ (h : Mono c₂) : Mono c := by
  have hf_flip : IsKernelPair f f₂ f₁ := hf.flip
  have hg_flip : IsKernelPair g g₂ g₁ := hg.flip
  exact mono_comparison_of_mono hf_flip hg_flip hw₂ hw₁ hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ h

include hf hg hw₁ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂ in
/-- **Monomorphisms are preserved to the second kernel-pair square.** -/
theorem mono_kernelPairComparison₂_of_mono (hw₂ : w ≫ g₂ = f₂ ≫ u) [Mono c] : Mono c₂ := by
  have hpb := isPullback_comparison₂ hf hg hw₁ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂ hw₂
  exact hpb.mono_fst_of_mono

include hf hg hw₁ hw₂ hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hP hφ₂₁ hφ₂₂ in
/-- **Equivalence of monomorphism property with the second kernel-pair square.** -/
theorem mono_iff_mono_kernelPairComparison₂ : Mono c ↔ Mono c₂ :=
  ⟨fun _ => mono_kernelPairComparison₂_of_mono hf hg hw₁ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂ hw₂,
   fun h => mono_comparison_of_mono₂ hf hg hw₁ hw₂ hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ h⟩

include hf hg hw₁ hw₂ hc₁ hc₂ hP₁ hcc₁ hcc₂ hP₂ hcc₂₁ hcc₂₂ hP hφ₁ hφ₂ hφ₂₁ hφ₂₂ in
/-- **Equivalence between the two kernel-pair comparison monomorphisms.** If one kernel-pair
comparison morphism is monic, so is the other. -/
theorem mono_kernelPairComparison_iff_mono_kernelPairComparison₂ : Mono c₁ ↔ Mono c₂ := by
  rw [← mono_iff_mono_kernelPairComparison hf hg hw₁ hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂,
      mono_iff_mono_kernelPairComparison₂ hf hg hw₁ hw₂ hP hc₁ hc₂ hP₂ hcc₂₁ hcc₂₂ hφ₂₁ hφ₂₂]

/-! ## Consequence 2: Pullbacks of kernel pairs -/

include hsq hf hg hw₁ hw₂ in
/-- **If the original square is a pullback, then so is the square of the first kernel-pair
projections.** -/
theorem isPullback_kernelPair_square (h : IsPullback u f g v) : IsPullback w f₁ g₁ u := by
  have key : ∀ s : PullbackCone g₁ u, (s.fst ≫ g₂) ≫ g = (s.snd ≫ f) ≫ v := by
    intro s
    calc (s.fst ≫ g₂) ≫ g = s.fst ≫ g₂ ≫ g := by rw [Category.assoc]
      _ = s.fst ≫ g₁ ≫ g := by rw [hg.w]
      _ = (s.fst ≫ g₁) ≫ g := by rw [Category.assoc]
      _ = (s.snd ≫ u) ≫ g := by rw [s.condition]
      _ = s.snd ≫ u ≫ g := by rw [Category.assoc]
      _ = s.snd ≫ f ≫ v := by rw [hsq]
      _ = (s.snd ≫ f) ≫ v := by rw [Category.assoc]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw₁
    (fun s => hf.lift s.snd (h.lift (s.fst ≫ g₂) (s.snd ≫ f) (key s))
      (h.lift_snd _ _ (key s)).symm) (fun s => ?_) (fun s => hf.lift_fst _ _ _)
    (fun s m hm₁ hm₂ => ?_))
  · refine hg.hom_ext ?_ ?_
    · rw [Category.assoc, hw₁, ← Category.assoc, hf.lift_fst, s.condition]
    · rw [Category.assoc, hw₂, ← Category.assoc, hf.lift_snd, h.lift_fst]
  · refine hf.hom_ext (by rw [hm₂, hf.lift_fst]) ?_
    rw [hf.lift_snd]
    refine h.hom_ext ?_ ?_
    · rw [h.lift_fst, Category.assoc, ← hw₂, ← Category.assoc, hm₁]
    · rw [h.lift_snd, Category.assoc, ← hf.w, ← Category.assoc, hm₂]

include hf hg hw₁ hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ in
/-- **If the original square is a pullback, then the comparison morphism of the kernel-pair
square is an isomorphism**, i.e. that square is a pullback too. -/
theorem isIso_kernelPairComparison_of_isIso (h : IsIso c) : IsIso c₁ := by
  have hpb := isPullback_comparison hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ hw₁
  refine ⟨hpb.lift (𝟙 P₁) (φ ≫ inv c) (by simp), ?_, hpb.lift_fst _ _ _⟩
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, hpb.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, hpb.lift_snd, Category.id_comp, ← Category.assoc, hpb.w,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-! ## Consequence 3: Stably extremal epimorphisms and Barr–Kock -/

include hsq hf hg hw₁ hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ in
/-- **Extremal epimorphy is reflected.** If the top morphism `f` of the square is a stably
extremal epimorphism and the comparison morphism of the kernel-pair square is an extremal
epimorphism, then so is the comparison morphism of the original square. -/
theorem isExtremalEpi_comparison_of_isExtremalEpi [HasPullbacks 𝒞] (hstab : StablyExtremalEpi f)
    (h : IsExtremalEpi c₁) : IsExtremalEpi c := by
  have hsq₂ := isPullback_pullbackObjHom (q₁ := q₁) hsq hg hP hP₁ hφ₁ hφ₂
  have hsq₁ := isPullback_comparison hf hg hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ hw₁
  have hφ : IsExtremalEpi φ := hstab q₁ φ pB hsq₂.flip
  have hcomp : IsExtremalEpi (c₁ ≫ φ) := isExtremalEpi_comp h hφ
  rw [hsq₁.w] at hcomp
  exact isExtremalEpi_of_comp f₂ c hcomp

include hsq hf hg hw₁ hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂ in
/-- **Isomorphisms are reflected.** If the top morphism `f` of the square is a stably extremal
epimorphism and the comparison morphism of the kernel-pair square is an isomorphism, then the
comparison morphism of the original square is an isomorphism, i.e. the original square is a
pullback. -/
theorem isIso_comparison_of_isIso [HasPullbacks 𝒞] (hstab : StablyExtremalEpi f)
    (h : IsIso c₁) : IsIso c := by
  have : Mono c₁ := inferInstance
  have : Mono c := mono_comparison_of_mono hf hg hw₁ hw₂ hc₁ hc₂ hP₁ hcc₁ hcc₂ inferInstance
  have hext : ExtremalEpi c :=
    isExtremalEpi_comparison_of_isExtremalEpi hsq hf hg hw₁ hw₂ hP hc₁ hc₂ hP₁ hcc₁ hcc₂ hφ₁ hφ₂
      hstab (isExtremalEpi_of_isSplitEpi c₁)
  exact isIso_of_isExtremalEpi_of_mono hext

end KernelPairComparison

end UlmerBialgebras
