module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Foundations.CategoryTheory.Grp.ProtomodularGrp
public import Foundations.CategoryTheory.Grp.GrpFiniteLimits

/-!
# Effectivity of internal equivalence relations of internal groups

Let `C` be a cartesian monoidal category with pullbacks, so that `Grp C` is pointed, finitely
complete and protomodular (`CategoryTheory.protomodular_grp`).

An internal equivalence relation `r₁, r₂ : R ⇉ X` of `Grp C` has an associated **normal
subobject**

```
K = ker r₁ = equalizer (r₁, trivial),   κ = (K ↪ R) ≫ r₂ : K ⟶ X,
```

which for `C = Set` is the normal subgroup `{x : (x, 1) ∈ R}` of `X`.  The main theorem of this
file is that the relation is *effective* — a kernel pair — as soon as `κ` is a **kernel**:

> if `q : X ⟶ Q` kills `κ` and every generalized element of `X` killed by `q` factors through
> `κ`, then `r₁, r₂` is the kernel pair of `q`.

This is the categorical content of the implication *"injectivity of the correspondence between
normal subobjects and quotients implies effectivity of internal equivalence relations"*: the
quotient `q` recovers `κ` as its kernel, and this alone forces the relation to be the kernel pair
of `q`.  Only protomodularity is used, through the two applications of the "split short five
lemma" pair `(section, kernel)`: once to see that `q` coequalizes `r₁, r₂`, once to see that the
comparison morphism to the kernel pair of `q` is invertible.

Note that transitivity and symmetry of the relation are never needed: reflexivity together with
joint monicity suffices.

## Main results

* `InternalGroups.Internal.relKernel`, `InternalGroups.Internal.relNormal`: the kernel of `r₁` and
  the normal subobject `κ` attached to the relation;
* `InternalGroups.Internal.hom_ext_of_section`: two morphisms out of `R` agreeing on a section of
  `r₁` and on `ker r₁` are equal (protomodularity);
* `InternalGroups.Internal.isKernelPair_of_relNormal_isKernel`: **effectivity** of a reflexive,
  jointly monic relation whose normal subobject is a kernel (in particular of an internal
  equivalence relation).

## References

* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
* [M. Barr, *Exact categories*][Ba]
-/

@[expose] public section

universe v u

open CategoryTheory Limits CartesianMonoidalCategory MonoidalCategory

namespace InternalGroups

namespace Internal

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

/-! ### The kernel of a morphism of internal groups -/

section Kernel

variable {R X : Grp C} (r₁ : R ⟶ X)

/-- The kernel of a morphism `r₁ : R ⟶ X` of internal groups: the equalizer of `r₁` and the
trivial morphism. -/
noncomputable def relKernel : Grp C := equalizer r₁ (0 : R ⟶ X)

/-- The inclusion of the kernel of `r₁` into its source. -/
noncomputable def relKernelι : relKernel r₁ ⟶ R := equalizer.ι _ _

/-- The inclusion of the kernel of `r₁` is a monomorphism. -/
instance : Mono (relKernelι r₁) := equalizer.ι_mono

/-- The inclusion of the kernel of `r₁`, followed by `r₁`, is the trivial morphism. -/
@[reassoc (attr := simp)]
lemma relKernelι_comp : relKernelι r₁ ≫ r₁ = (0 : relKernel r₁ ⟶ X) := by
  exact (equalizer.condition r₁ 0).trans comp_zero

/-- The universal property of the kernel: a morphism killed by `r₁` factors through it. -/
noncomputable def relKernelLift {K : Grp C} (κ : K ⟶ R) (hκ : κ ≫ r₁ = (0 : K ⟶ X)) :
    K ⟶ relKernel r₁ := equalizer.lift κ (by simpa using hκ)

/-- `relKernelLift r₁ κ hκ` followed by the inclusion `relKernelι r₁` is `κ`. -/
@[reassoc (attr := simp)]
lemma relKernelLift_comp {K : Grp C} (κ : K ⟶ R) (hκ : κ ≫ r₁ = (0 : K ⟶ X)) :
    relKernelLift r₁ κ hκ ≫ relKernelι r₁ = κ := equalizer.lift_ι _ _

/-- The kernel of `r₁` is the pullback of the trivial subobject along `r₁`. -/
theorem isPullback_relKernel :
    IsPullback (0 : relKernel r₁ ⟶ Grp.trivial C) (relKernelι r₁)
      (0 : Grp.trivial C ⟶ X) r₁ := by
  have hcomm : (0 : relKernel r₁ ⟶ Grp.trivial C) ≫ (0 : Grp.trivial C ⟶ X)
      = relKernelι r₁ ≫ r₁ := by rw [zero_comp, relKernelι_comp]
  refine IsPullback.of_isLimit (PullbackCone.isLimitAux (PullbackCone.mk _ _ hcomm)
    (fun s => relKernelLift r₁ s.snd (by simpa using s.condition.symm)) ?_ ?_ ?_)
  · intro s; exact (isTerminalGrpTrivial C).hom_ext _ _
  · intro s; exact relKernelLift_comp r₁ s.snd _
  · intro s m hm
    have h2 : m ≫ relKernelι r₁ = s.snd := hm WalkingCospan.right
    refine (cancel_mono (relKernelι r₁)).1 ?_
    rw [h2, relKernelLift_comp]

/-- **Protomodularity in the form of an extensionality principle.**  Two morphisms out of `R`
which agree on a section of `r₁` and on the kernel of `r₁` are equal. -/
theorem hom_ext_of_section {T : Grp C} (d : X ⟶ R) (hd : d ≫ r₁ = 𝟙 X) (u v : R ⟶ T)
    (hu : d ≫ u = d ≫ v) (hk : relKernelι r₁ ≫ u = relKernelι r₁ ≫ v) : u = v := by
  have hjoint :=
    CategoryTheory.Protomodular.jointlyExtremalEpiPair (C := Grp C) hd
      (isPullback_relKernel r₁)
  have hiso : IsIso (equalizer.ι u v) :=
    hjoint (equalizer.ι u v) inferInstance (equalizer.lift d hu) (equalizer.lift _ hk)
      (equalizer.lift_ι _ _) (equalizer.lift_ι _ _)
  exact (cancel_epi (equalizer.ι u v)).1 (equalizer.condition u v)

end Kernel

/-! ### The normal subobject of a relation, and effectivity -/

section Relation

variable {R X : Grp C} (r₁ r₂ : R ⟶ X)

/-- The normal subobject of `X` attached to a relation `r₁, r₂ : R ⇉ X`: the image under `r₂` of
the kernel of `r₁`.  For `C = Set` this is `{x : X | (x, 1) ∈ R}`. -/
noncomputable def relNormal : relKernel r₁ ⟶ X := relKernelι r₁ ≫ r₂

/-- The normal subobject of a jointly monic relation is a subobject. -/
theorem mono_relNormal
    (hmono : ∀ ⦃T : Grp C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b) :
    Mono (relNormal r₁ r₂) := by
  refine ⟨fun {T} a b hab => ?_⟩
  refine (cancel_mono (relKernelι r₁)).1 (hmono _ _ ?_ ?_)
  · simp
  · simpa [relNormal, Category.assoc] using hab

variable {r₁ r₂}

/-- **Effectivity from the kernel property of the normal subobject.**  Let `r₁, r₂ : R ⇉ X` be a
reflexive, jointly monic relation of internal groups and let `q : X ⟶ Q` be a morphism such that

* `q` kills the normal subobject `κ = relNormal r₁ r₂`, and
* every morphism into `X` killed by `q` factors through `κ`

(that is, `κ` *is* a kernel of `q`).  Then `r₁, r₂` is the kernel pair of `q`. -/
theorem isKernelPair_of_relNormal_isKernel
    (hrefl : ∃ d : X ⟶ R, d ≫ r₁ = 𝟙 X ∧ d ≫ r₂ = 𝟙 X)
    (hmono : ∀ ⦃T : Grp C⦄ (a b : T ⟶ R), a ≫ r₁ = b ≫ r₁ → a ≫ r₂ = b ≫ r₂ → a = b)
    {Q : Grp C} (q : X ⟶ Q)
    (hκq : relNormal r₁ r₂ ≫ q = (0 : relKernel r₁ ⟶ Q))
    (hker : ∀ ⦃T : Grp C⦄ (t : T ⟶ X), t ≫ q = (0 : T ⟶ Q) →
      ∃ w : T ⟶ relKernel r₁, w ≫ relNormal r₁ r₂ = t) :
    IsKernelPair q r₁ r₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hrefl
  -- `q` coequalizes the relation
  have hq : r₁ ≫ q = r₂ ≫ q := by
    refine hom_ext_of_section r₁ d hd₁ _ _ ?_ ?_
    · rw [← Category.assoc, hd₁, ← Category.assoc, hd₂]
    · rw [← Category.assoc, relKernelι_comp, zero_comp, ← Category.assoc]
      exact hκq.symm
  -- the comparison morphism to the kernel pair of `q`
  set S := pullback q q with hS
  set s₁ : S ⟶ X := pullback.fst q q with hs₁
  set s₂ : S ⟶ X := pullback.snd q q with hs₂
  set φ : R ⟶ S := pullback.lift r₁ r₂ hq with hφ
  have hφ₁ : φ ≫ s₁ = r₁ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ s₂ = r₂ := pullback.lift_snd _ _ _
  have hmonoφ : Mono φ := by
    refine ⟨fun {T} a b hab => hmono a b ?_ ?_⟩
    · rw [← hφ₁, ← Category.assoc, ← Category.assoc, hab]
    · rw [← hφ₂, ← Category.assoc, ← Category.assoc, hab]
  -- the diagonal of the kernel pair factors through the comparison morphism
  have hdS : (d ≫ φ) ≫ s₁ = 𝟙 X := by rw [Category.assoc, hφ₁, hd₁]
  -- the kernel of the first projection of the kernel pair factors through it too
  have hker₁ : (relKernelι s₁ ≫ s₂) ≫ q = (0 : relKernel s₁ ⟶ Q) := by
    have : s₂ ≫ q = s₁ ≫ q := (pullback.condition (f := q) (g := q)).symm
    rw [Category.assoc, this, ← Category.assoc, relKernelι_comp, zero_comp]
  obtain ⟨w, hw⟩ := hker _ hker₁
  have hψ : (w ≫ relKernelι r₁) ≫ φ = relKernelι s₁ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hφ₁, ← hs₁]
      simp
    · rw [Category.assoc, Category.assoc, hφ₂, ← hs₂]
      exact hw
  -- protomodularity: the comparison morphism is invertible
  have hjoint :=
    CategoryTheory.Protomodular.jointlyExtremalEpiPair (C := Grp C) hdS
      (isPullback_relKernel s₁)
  have hisoφ : IsIso φ :=
    hjoint φ inferInstance d (w ≫ relKernelι r₁) rfl hψ
  refine (IsKernelPair.of_hasPullback q).of_iso (asIso φ).symm (Iso.refl X) (Iso.refl X)
    (Iso.refl Q) ?_ ?_ ?_ ?_
  · simpa using (IsIso.eq_inv_comp φ).2 hφ₁
  · simpa using (IsIso.eq_inv_comp φ).2 hφ₂
  · simp
  · simp

end Relation

end Internal

end InternalGroups
