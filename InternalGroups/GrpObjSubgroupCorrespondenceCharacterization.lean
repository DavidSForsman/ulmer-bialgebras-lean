module

public import InternalGroups.GrpObjSubgroupCorrespondenceSurjective
public import InternalGroups.GrpObjCosetInjective

/-!
# Characterizing Newman's correspondence

For an internal group `G` of a cartesian monoidal category `C`, Newman's correspondence relates
subgroup objects of `G` to quotient `G`-modules: a subgroup `s` is sent to its coset quotient
`G / s` (`InternalGroups.SubGrp.quot`), and a quotient module `q` to the stabilizer of its base
point (`InternalGroups.stab`).  These are the two halves of the Galois connection
`InternalGroups.galoisConnection_quot_stab`, so they are monotone and inverse up to the preorder
equivalence exactly when the correspondence is a bijection on the antisymmetrizations.

This file proves the characterization of that bijectivity:

**Newman's correspondence is bijective for every internal group iff**

1. the coset relation of every subgroup object is effective (`CosetInjective C`), and
2. every categorical epi quotient `h ⟶ M` in `C^h` is a regular epi in `C^h`
   (`EveryEpiQuotientRegular C`).

Here "epi quotient" is a `QuotMod`: its structural map is an epimorphism in the module category
`C^h`, by definition.  The two halves are exposed separately: injectivity is exactly effectiveness
of the coset relations (`subgroupCorrespondence_injective_iff`), and surjectivity is exactly
regularity of all epi quotients (`subgroupCorrespondence_surjective_iff`).

The category `C` is assumed cartesian monoidal with pullbacks and reflexive coequalizers of
modules; the group object is arbitrary.  No balance, no exactness and no regularity of `C` is
assumed.

## Main definitions

* `InternalGroups.cosetQuotMod`: Newman's monotone map from subgroup objects to quotient modules;
* `InternalGroups.SubgroupCorrespondence`: its bijectivity on the antisymmetrizations;
* `InternalGroups.EveryEpiQuotientRegular`: every epi quotient is a regular epi.

## Main results

* `InternalGroups.subgroupCorrespondence_injective_iff`: injectivity of `cosetQuotMod` on
  antisymmetrizations iff `CosetInjective C`;
* `InternalGroups.CosetEffective`, `InternalGroups.cosetInjective_iff_cosetEffective`: the
  explicit effectivity form (the coset relation of every subgroup object is the kernel pair of
  its coset quotient) and its equivalence with `CosetInjective`;
* `InternalGroups.subgroupCorrespondence_injective_iff_effective`: injectivity in the explicit
  `IsKernelPair` form;
* `InternalGroups.subgroupCorrespondence_surjective_iff`: surjectivity of `cosetQuotMod` on
  antisymmetrizations iff `EveryEpiQuotientRegular C`;
* `InternalGroups.subgroupCorrespondence_iff`: the packaged equivalence.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj MonObj

attribute [local instance] CategoryTheory.ModObj.regular

namespace InternalGroups


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]

/-! ## An auxiliary transport lemma -/

omit [CartesianMonoidalCategory C] [HasPullbacks C] in
/-- A pullback square is invariant under an isomorphism of its apex that respects the two legs.
This is Mathlib's `IsPullback.of_iso'` with the two horizontal isomorphisms trivial. -/
lemma isPullback_of_apex_iso {X Y Z W W' : C} {f : X ⟶ Z} {g : Y ⟶ Z}
    {a : W ⟶ X} {b : W ⟶ Y} {a' : W' ⟶ X} {b' : W' ⟶ Y}
    (e : W' ≅ W) (ha : e.hom ≫ a = a') (hb : e.hom ≫ b = b')
    (h : IsPullback a b f g) : IsPullback a' b' f g :=
  h.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simpa using ha) (by simpa using hb)
    (by simp) (by simp)

/-! ## Newman's map and the two properties -/

/-- **Newman's monotone map** from subgroup objects to quotient modules: a subgroup is sent to its
coset quotient. -/
noncomputable def cosetQuotMod (G : C) [GrpObj G]
    [HasReflexiveCoequalizers (CategoryTheory.Mod C G)] : SubGrp G →o QuotMod G where
  toFun s := s.quot
  monotone' _ _ h := galoisConnection_quot_stab.monotone_l h

variable (C)

/-- **Newman's correspondence** for every internal group: the map `s ↦ G / s` is a bijection on
the antisymmetrizations. -/
def SubgroupCorrespondence : Prop :=
  ∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)],
    Function.Bijective (cosetQuotMod G).antisymmetrization

/-- **Every categorical epi quotient of an internal group is a regular epimorphism.**  A quotient
is a `QuotMod`, whose structural map is by definition an epimorphism of modules, i.e. a
categorical epi in `C^h`. -/
def EveryEpiQuotientRegular : Prop :=
  ∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)] (q : QuotMod G),
    IsRegularEpi q.p

/-! ## Injectivity is effectiveness of the coset relations -/

variable {C}

/-- **Injectivity of Newman's map is effectiveness of the coset relations.**  A subgroup is
recovered from its coset quotient exactly when the coset relation is effective. -/
theorem subgroupCorrespondence_injective_iff :
    (∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)],
        Function.Injective (cosetQuotMod G).antisymmetrization) ↔ CosetInjective C := by
  constructor
  · intro hinj G _ _ s
    have h₁ : s ≤ stab s.quot := le_stab_quot s
    have h₂ : s.quot ≤ (stab s.quot).quot := galoisConnection_quot_stab.monotone_l h₁
    have h₃ : (stab s.quot).quot ≤ s.quot := quot_stab_le s.quot
    have hs : AntisymmRel (· ≤ ·) s (stab s.quot) :=
      Quotient.exact (hinj G (Quotient.sound (show AntisymmRel (· ≤ ·) s.quot
        (stab s.quot).quot from ⟨h₂, h₃⟩)))
    exact hs.2
  · intro hinj G _ _
    refine Quotient.ind₂ fun s t hst => ?_
    have h : AntisymmRel (· ≤ ·) s.quot t.quot := Quotient.exact hst
    refine Quotient.sound (show AntisymmRel (· ≤ ·) s t from ⟨?_, ?_⟩)
    · exact (le_stab_quot s).trans
        ((galoisConnection_quot_stab.monotone_u h.1).trans (hinj G t))
    · exact (le_stab_quot t).trans
        ((galoisConnection_quot_stab.monotone_u h.2).trans (hinj G s))

/-! ## Effectiveness of the coset relations -/

variable (C)

/-- **Effectivity of the coset relations** of `C`: the coset relation `G ⊗ N ⇉ G` of every
subgroup object `N` of every group object `G` of `C` is the kernel pair of its coset quotient
`G ⟶ G / N`. -/
def CosetEffective : Prop :=
  ∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)] (s : SubGrp G),
    IsKernelPair (s.quot).p.hom (cosetMul s) (fst G s.N)

variable {C}

section Effectivity

variable {G : C} [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- **The coset relation of a subgroup object is effective as soon as the subgroup is recovered
from its coset quotient.**  If `stab (G / N) ≤ N`, then `N` and `stab (G / N)` contain each
other; `SubGrp.isoOfLe` gives an isomorphism over `G`, and the kernel pair
`isKernelPair_cosetMul_stab` of the coset quotient is transported along the induced isomorphism
`G ⊗ N ≅ G ⊗ stab (G / N)` of the apex. -/
theorem isKernelPair_cosetMul_of_stab_le {s : SubGrp G} (hstab : stab s.quot ≤ s) :
    IsKernelPair (s.quot).p.hom (cosetMul s) (fst G s.N) := by
  let e₀ := SubGrp.isoOfLe (s := s) (t := stab s.quot) (le_stab_quot s) hstab
  let e : s.N ≅ (stab s.quot).N := (Grp.forget C).mapIso e₀
  have he : e.hom ≫ (stab s.quot).i = s.i := by
    have h := SubGrp.isoOfLe_hom_inclGrp (s := s) (t := stab s.quot) (le_stab_quot s) hstab
    exact congrArg (fun m => m.hom.hom) h
  have hfst : (G ◁ e.hom) ≫ fst G (stab s.quot).N = fst G s.N := by
    simp
  have hsnd : (G ◁ e.hom) ≫ snd G (stab s.quot).N = snd G s.N ≫ e.hom := by
    simp
  have ha : (G ◁ e.hom) ≫ cosetMul (stab s.quot) = cosetMul s := by
    calc (G ◁ e.hom) ≫ cosetMul (stab s.quot)
        = ((G ◁ e.hom) ≫ fst G (stab s.quot).N) *
            (((G ◁ e.hom) ≫ snd G (stab s.quot).N) ≫ (stab s.quot).i) :=
            comp_cosetMul (stab s.quot) (G ◁ e.hom)
      _ = fst G s.N * (snd G s.N ≫ e.hom ≫ (stab s.quot).i) := by
            rw [hfst, hsnd]
            simp only [Category.assoc]
      _ = fst G s.N * (snd G s.N ≫ s.i) := by rw [he]
      _ = cosetMul s := rfl
  exact isPullback_of_apex_iso (MonoidalCategory.whiskerLeftIso G e) ha hfst
    (isKernelPair_cosetMul_stab (G := G) s.quot)

end Effectivity

/-- **Recovery of a subgroup from its coset quotient is equivalent to effectivity of its coset
relation.**  This is the explicit equivalence behind `subgroupCorrespondence_injective_iff`: the
recovery form `CosetInjective` and the effectivity form `CosetEffective` are the same property. -/
theorem cosetInjective_iff_cosetEffective : CosetInjective C ↔ CosetEffective C := by
  constructor
  · intro hinj G _ _ s
    exact isKernelPair_cosetMul_of_stab_le (s := s) (hinj G s)
  · intro heff G _ _ s
    exact stab_quot_le s (heff G s)

/-- **Injectivity of Newman's map is effectivity of the coset relations**, in the explicit
`IsKernelPair` form. -/
theorem subgroupCorrespondence_injective_iff_effective :
    (∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)],
        Function.Injective (cosetQuotMod G).antisymmetrization) ↔ CosetEffective C :=
  subgroupCorrespondence_injective_iff.trans cosetInjective_iff_cosetEffective

/-! ## Surjectivity is regularity of every epi quotient -/

/-- **Surjectivity of Newman's map is regularity of every epi quotient.**  A quotient module is
reached by a coset quotient exactly when it is regular, because two quotient modules that are
comparable in the preorder in both directions are isomorphic as quotients. -/
theorem subgroupCorrespondence_surjective_iff :
    (∀ (G : C) [GrpObj G] [HasReflexiveCoequalizers (CategoryTheory.Mod C G)],
        Function.Surjective (cosetQuotMod G).antisymmetrization) ↔
      EveryEpiQuotientRegular C := by
  constructor
  · intro hsur G _ _ q
    obtain ⟨s', hs⟩ := hsur G (Quotient.mk _ q)
    obtain ⟨s, rfl⟩ := Quotient.exists_rep s'
    have h : AntisymmRel (· ≤ ·) s.quot q := Quotient.exact hs
    obtain ⟨u, hu⟩ := h.1
    obtain ⟨v, hv⟩ := h.2
    have hvu : v ≫ u = 𝟙 q.V := by
      refine (cancel_epi q.p).1 ?_
      rw [Category.comp_id, ← Category.assoc, hv, hu]
    have huv : u ≫ v = 𝟙 s.quot.V := by
      refine (cancel_epi s.quot.p).1 ?_
      rw [Category.comp_id, ← Category.assoc, hu, hv]
    let e : Arrow.mk s.quot.p ≅ Arrow.mk q.p :=
      Arrow.isoMk (Iso.refl _) { hom := u, inv := v, hom_inv_id := huv, inv_hom_id := hvu }
        (by simp only [Iso.refl_hom, Category.id_comp]; exact hu.symm)
    exact ⟨⟨RegularEpi.ofArrowIso e (SubGrp.regularEpiQuot s)⟩⟩
  · intro hreg G _ _
    refine Quotient.ind fun q => ?_
    refine ⟨Quotient.mk _ (stab q), Quotient.sound ?_⟩
    exact ⟨quot_stab_le q, le_quot_stab q (hreg G q).regularEpi.some⟩

/-! ## The packaged characterization -/

/-- **Newman's correspondence is bijective for every internal group iff the coset relations are
effective and every epi quotient is a regular epi.** -/
theorem subgroupCorrespondence_iff :
    SubgroupCorrespondence C ↔ CosetInjective C ∧ EveryEpiQuotientRegular C := by
  constructor
  · intro h
    exact ⟨subgroupCorrespondence_injective_iff.1 (fun G _ _ => (h G).1),
      subgroupCorrespondence_surjective_iff.1 (fun G _ _ => (h G).2)⟩
  · rintro ⟨hinj, hsur⟩ G
    exact ⟨subgroupCorrespondence_injective_iff.2 hinj G,
      subgroupCorrespondence_surjective_iff.2 hsur G⟩


end InternalGroups
