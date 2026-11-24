module

public import Foundations.CategoryTheory.Monoidal.MonadReflexive

/-!
# Reflexive coequalizers and the tensor product

Let `C` be a monoidal category in which tensoring on either side preserves the coequalizers of
reflexive pairs.  This file proves the basic fact that then the tensor square of a reflexive
coequalizer is again a coequalizer:

if `u, v : M ⇉ N` is a reflexive pair with coequalizer `q : N ⟶ Q`, then `q ⊗ₘ q` is a
coequalizer of `u ⊗ₘ u` and `v ⊗ₘ v`.

This is the key computation behind the construction of reflexive coequalizers of monoid objects,
and hence behind the exactness statements of Section 4 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*.

## Main results

* `CategoryTheory.ReflexiveTensor.isColimitWhiskerRight`,
  `CategoryTheory.ReflexiveTensor.isColimitWhiskerLeft`: whiskering a reflexive coequalizer with a
  fixed object again gives a coequalizer;
* `CategoryTheory.ReflexiveTensor.isColimitTensorHom`: `q ⊗ₘ q` is a coequalizer of `u ⊗ₘ u`,
  `v ⊗ₘ v`;
* `CategoryTheory.ReflexiveTensor.epi_tensorHom`,
  `CategoryTheory.ReflexiveTensor.epi_tensorHom_tensorHom'`: the resulting epimorphisms `q ⊗ₘ q` and
  `q ⊗ₘ q ⊗ₘ q`, used to check the monoid axioms on the coequalizer.

## References

* [D. Forsman, *On the semi-abelianness of affine group schemes*]
  [forsman2026semiabeliannessaffinegroupschemes], Section 4
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 4.16 and Corollary 4.17
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

section
open CategoryTheory

namespace CategoryTheory.ReflexiveTensor

variable {C : Type u} [Category.{v} C]

variable [MonoidalCategory C]

section Pairs

variable {M N Q : C} {u v : M ⟶ N} (hr : IsReflexivePair u v) {q : N ⟶ Q}
  {w : u ≫ q = v ≫ q}

include hr in
/-- The tensor square of a reflexive pair, `u ⊗ₘ u` and `v ⊗ₘ v`, is again a reflexive pair. -/
lemma isReflexivePair_tensorHom : IsReflexivePair (u ⊗ₘ u) (v ⊗ₘ v) := by
  obtain ⟨s, hu, hv⟩ := hr.common_section'
  exact .mk' (s ⊗ₘ s) (by rw [tensorHom_comp_tensorHom, hu, tensorHom_id, id_whiskerRight])
    (by rw [tensorHom_comp_tensorHom, hv, tensorHom_id, id_whiskerRight])

include w in
/-- `q ⊗ₘ q` coequalizes the pair `u ⊗ₘ u` and `v ⊗ₘ v`. -/
lemma tensorHom_comp_tensorHom_eq : (u ⊗ₘ u) ≫ (q ⊗ₘ q) = (v ⊗ₘ v) ≫ (q ⊗ₘ q) := by
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, w]

end Pairs

variable [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

section

variable {M N Q : C} {u v : M ⟶ N} (hr : IsReflexivePair u v) {q : N ⟶ Q}
  {w : u ≫ q = v ≫ q} (hq : IsColimit (Cofork.ofπ q w))

include hr hq

/-- Whiskering a reflexive coequalizer on the right by a fixed object gives a coequalizer. -/
noncomputable def isColimitWhiskerRight (Z : C) :
    IsColimit (Cofork.ofπ (q ▷ Z) (show (u ▷ Z) ≫ (q ▷ Z) = (v ▷ Z) ≫ (q ▷ Z) by
      rw [← comp_whiskerRight, ← comp_whiskerRight, w])) := by
  haveI : PreservesColimit (parallelPair u v) (tensorRight Z) :=
    CategoryTheory.PreservesReflexiveCoeq.preserves u v hr
  exact isColimitCoforkMapOfIsColimit (tensorRight Z) w hq

/-- The whiskering `q ▷ Z` of the coequalizer of a reflexive pair is an epimorphism. -/
lemma epi_whiskerRight (Z : C) : Epi (q ▷ Z) :=
  epi_of_isColimit_cofork (isColimitWhiskerRight hr hq Z)

variable [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

/-- Whiskering a reflexive coequalizer on the left by a fixed object gives a coequalizer. -/
noncomputable def isColimitWhiskerLeft (Z : C) :
    IsColimit (Cofork.ofπ (Z ◁ q) (show (Z ◁ u) ≫ (Z ◁ q) = (Z ◁ v) ≫ (Z ◁ q) by
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp, w])) := by
  haveI : PreservesColimit (parallelPair u v) (tensorLeft Z) :=
    CategoryTheory.PreservesReflexiveCoeq.preserves u v hr
  exact isColimitCoforkMapOfIsColimit (tensorLeft Z) w hq

omit [∀ (Z : C), PreservesReflexiveCoeq (tensorRight Z)] in
/-- The whiskering `Z ◁ q` of the coequalizer of a reflexive pair is an epimorphism. -/
lemma epi_whiskerLeft (Z : C) : Epi (Z ◁ q) :=
  epi_of_isColimit_cofork (isColimitWhiskerLeft hr hq Z)

/-- The tensor square `q ⊗ₘ q` of the coequalizer of a reflexive pair is an epimorphism. -/
lemma epi_tensorHom : Epi (q ⊗ₘ q) := by
  rw [MonoidalCategory.tensorHom_def]
  have := epi_whiskerRight hr hq N
  have := epi_whiskerLeft hr hq Q
  exact epi_comp _ _

/-- The universal property of `q ⊗ₘ q` as a coequalizer of `u ⊗ₘ u` and `v ⊗ₘ v`. -/
lemma existsUnique_desc_tensorHom {Z : C} (t : N ⊗ N ⟶ Z)
    (ht : (u ⊗ₘ u) ≫ t = (v ⊗ₘ v) ≫ t) : ∃! r : Q ⊗ Q ⟶ Z, (q ⊗ₘ q) ≫ r = t := by
  obtain ⟨s, hsu, hsv⟩ := hr.common_section'
  have h₁ := isColimitWhiskerRight hr hq N
  have h₂ := isColimitWhiskerLeft (Q := Q) hr hq Q
  have hepiM : Epi (q ▷ M) := epi_whiskerRight hr hq M
  have hepi : Epi (q ⊗ₘ q) := epi_tensorHom hr hq
  have eu₁ : (M ◁ s) ≫ (u ⊗ₘ u) = u ▷ N := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, hsu, tensorHom_id]
  have ev₁ : (M ◁ s) ≫ (v ⊗ₘ v) = v ▷ N := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, hsv, tensorHom_id]
  have eu₂ : (s ▷ M) ≫ (u ⊗ₘ u) = N ◁ u := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hsu, Category.id_comp, id_tensorHom]
  have ev₂ : (s ▷ M) ≫ (v ⊗ₘ v) = N ◁ v := by
    rw [← tensorHom_id, tensorHom_comp_tensorHom, hsv, Category.id_comp, id_tensorHom]
  have hcoeq₁ : (u ▷ N) ≫ t = (v ▷ N) ≫ t := by
    rw [← eu₁, ← ev₁, Category.assoc, Category.assoc, ht]
  obtain ⟨t₁, ht₁⟩ := Cofork.IsColimit.desc' h₁ t hcoeq₁
  simp only [Cofork.π_ofπ] at ht₁
  have hcoeq₂ : (Q ◁ u) ≫ t₁ = (Q ◁ v) ≫ t₁ := by
    rw [← cancel_epi (q ▷ M)]
    rw [← Category.assoc, ← Category.assoc, ← whisker_exchange, ← whisker_exchange,
      Category.assoc, Category.assoc, ht₁, ← eu₂, ← ev₂, Category.assoc, Category.assoc, ht]
  obtain ⟨t₂, ht₂⟩ := Cofork.IsColimit.desc' h₂ t₁ hcoeq₂
  simp only [Cofork.π_ofπ] at ht₂
  refine ⟨t₂, ?_, fun r hr' => ?_⟩
  · change (q ⊗ₘ q) ≫ t₂ = t
    rw [MonoidalCategory.tensorHom_def, Category.assoc, ht₂, ht₁]
  · rw [← cancel_epi (q ⊗ₘ q), hr', MonoidalCategory.tensorHom_def, Category.assoc, ht₂, ht₁]

/-- **Reflexive coequalizers are preserved by the tensor square.**  If `q` is the coequalizer of
a reflexive pair `u, v`, then `q ⊗ₘ q` is the coequalizer of `u ⊗ₘ u` and `v ⊗ₘ v`. -/
noncomputable def isColimitTensorHom :
    IsColimit (Cofork.ofπ (q ⊗ₘ q) (tensorHom_comp_tensorHom_eq (u := u) (v := v) (w := w))) :=
  Cofork.IsColimit.mk _
    (fun t => (existsUnique_desc_tensorHom hr hq t.π (Cofork.condition t)).choose)
    (fun t => (existsUnique_desc_tensorHom hr hq t.π (Cofork.condition t)).choose_spec.1)
    (fun t m hm => (existsUnique_desc_tensorHom hr hq t.π (Cofork.condition t)).choose_spec.2 m hm)

/-- The triple tensor `(q ⊗ₘ q) ⊗ₘ q` of the coequalizer of a reflexive pair is an
epimorphism. -/
lemma epi_tensorHom_tensorHom' : Epi ((q ⊗ₘ q) ⊗ₘ q) := by
  rw [MonoidalCategory.tensorHom_def]
  have := epi_whiskerRight (isReflexivePair_tensorHom hr) (isColimitTensorHom hr hq) N
  have := epi_whiskerLeft hr hq (Q ⊗ Q)
  exact epi_comp _ _

end

end CategoryTheory.ReflexiveTensor

end
