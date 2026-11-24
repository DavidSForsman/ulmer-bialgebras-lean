module

public import InternalGroups.GrpObjCosetInjective
public import InternalGroups.GrpExactCriterion
public import InternalGroups.GrpPointsDetection
public import Foundations.CategoryTheory.Grp.GrpReflexiveCoeq
public import InternalGroups.HomomorphismDetection

/-!
# `Grp C` is exact when Newman's correspondence is injective

Let `C` be a cartesian monoidal category with finite limits and reflexive coequalizers which the
binary product preserves, so that

* `Grp C` has reflexive coequalizers, computed in `C`
  (`CategoryTheory.GrpReflexiveCoeq.hasReflexiveCoequalizers_grp`), and
* every group object `G` of `C` has its Galois connection `Sub(G) ⇆ Quot(G)` between subgroup
  objects and quotient `G`-modules (`InternalGroups/GrpObjSubgroupCorrespondence.lean`).

The correspondence is always surjective onto regular quotient modules; its **injectivity** —
`InternalGroups.CosetInjective C`, equivalently the effectivity in `C` of the coset relations
`G ⊗ N ⇉ G` — is proved here to be enough for the exactness of `Grp C`:

> **`InternalGroups.isBarrExact_grp_of_cosetInjective_of_stableRegularEpi`.**  If Newman's
> correspondence is injective for every subgroup object of every group object of `C`, and regular
> epimorphisms of `Grp C` are stable under base change, then `Grp C` is Barr exact.

(The stability hypothesis is what one expects to obtain when `C` is a regular category, by lifting
its regular epi / mono factorization system to `Grp C`; that step is not formalized here.)

Note that no effectivity of *arbitrary* internal equivalence relations of `C` is assumed: only of
the coset relations, which is strictly weaker (the effectivity of all internal equivalence
relations implies that of the coset relations).  This is the mechanism behind the pattern *"`C` is
not exact although `Grp C` is"*: a relation of group objects is determined by one normal subobject,
and a normal subobject is a subgroup object, so only coset relations need to be effective.

## The argument

Let `r₁, r₂ : R ⇉ X` be a reflexive, jointly monic relation of `Grp C`, `K = ker r₁` and
`κ = (K ↪ R) ≫ r₂ : K ⟶ X` its normal subobject, and `q : X ⟶ Q` the coequalizer of the relation
— which, the pair being reflexive, is computed in `C`.  Viewing `κ` as a subgroup object of `X`,
its coset quotient `p : X ⟶ X / K` coequalizes the relation as well: for the generic element
`ρ : R`, the element `d(r₁ρ)⁻¹ · ρ` is killed by `r₁`, hence lies in `K`, and its image under `r₂`
is `(r₁ρ)⁻¹ · (r₂ρ)`, so `r₂ρ ∈ (r₁ρ) K`.  Therefore `p` factors through `q`, and a generalized
element killed by `q` is killed by `p`, hence — this is the injectivity hypothesis — factors
through `κ`.  That is exactly `InternalGroups.Internal.RelNormalDetectsQuotient`, from which the
effectivity of internal equivalence relations of `Grp C`, and with the regularity of `Grp C`
(transferred from `C`) the Barr exactness of `Grp C`, follow.

## Main results

* `InternalGroups.relNormalDetectsQuotient_of_cosetInjective`;
* `InternalGroups.isBarrExact_grp_of_cosetInjective_of_stableRegularEpi`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras*][Newman1975]
* [M. Barr, *Exact categories*][Ba]
* [D. Bourn, *Normalization equivalence, kernel equivalence and affine categories*][Bourn1991]
* [F. Borceux, D. Bourn, *Mal'cev, protomodular, homological and semi-abelian
  categories*][BorceuxBourn2004]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj CartesianMonoidalCategory
open scoped MonoidalLeftAction ModObj Obj

namespace InternalGroups
open CategoryTheory


variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasFiniteLimits C]
  [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]
  [∀ Z : C, PreservesReflexiveCoeq (tensorRight Z)]

/-- **The quotient of a relation of `Grp C` recovers its normal subobject**, granting the
injectivity of Newman's correspondence.  See the file header for the argument. -/
theorem relNormalDetectsQuotient_of_cosetInjective (hinj : CosetInjective C) :
    Internal.RelNormalDetectsQuotient C := by
  intro R X Q r₁ r₂ q w hcolim hrefl hjm T t ht
  obtain ⟨d, hd₁, hd₂⟩ := hrefl
  have : IsReflexivePair r₁ r₂ := IsReflexivePair.mk' d hd₁ hd₂
  have : Mono (Internal.relNormal r₁ r₂) := Internal.mono_relNormal r₁ r₂ hjm
  have : Mono (Internal.relNormal r₁ r₂).hom.hom := mono_hom_of_mono _
  have := hasReflexiveCoequalizers_mod X.X
  let s : SubGrp X.X :=
    { N := (Internal.relKernel r₁).X, i := (Internal.relNormal r₁ r₂).hom.hom }
  have hsi : s.i = (Internal.relKernelι r₁).hom.hom ≫ r₂.hom.hom := rfl
  have hd₁' : d.hom.hom ≫ r₁.hom.hom = 𝟙 X.X := congr(($hd₁).hom.hom)
  have hd₂' : d.hom.hom ≫ r₂.hom.hom = 𝟙 X.X := congr(($hd₂).hom.hom)
  -- the coset quotient of the normal subobject coequalizes the relation
  have hA : r₁.hom.hom ≫ (s.quot).p.hom = r₂.hom.hom ≫ (s.quot).p.hom := by
    have hn : ((r₁.hom.hom ≫ d.hom.hom)⁻¹ * 𝟙 R.X) ≫ r₁.hom.hom = (1 : R.X ⟶ X.X) := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hd₁', Category.comp_id,
        Category.id_comp, inv_mul_cancel]
    obtain ⟨n', hn'⟩ := ConnExact.exists_relKernel_factor r₁ _ hn
    have hk : (n' ≫ (Internal.relKernelι r₁).hom.hom ≫ r₂.hom.hom)
        = r₁.hom.hom⁻¹ * r₂.hom.hom := by
      rw [← Category.assoc, hn', MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hd₂',
        Category.comp_id, Category.id_comp]
    have hkills : Kills s.quot (n' ≫ s.i) := (kills_quot_i s).comp n'
    have hmul := mul_comp_p_of_kills (q := s.quot) r₁.hom.hom hkills
    rw [hsi, hk, mul_inv_cancel_left] at hmul
    exact hmul.symm
  -- the coequalizer of the relation, computed in `C`
  have hwC : r₁.hom.hom ≫ q.hom.hom = r₂.hom.hom ≫ q.hom.hom :=
    congr(($w).hom.hom)
  have hcolimC : IsColimit (Cofork.ofπ q.hom.hom hwC) :=
    (isColimitMapCoconeCoforkEquiv (Grp.forget C) w) (isColimitOfPreserves (Grp.forget C) hcolim)
  have hwq : q.hom.hom ≫ Cofork.IsColimit.desc hcolimC (s.quot).p.hom hA = (s.quot).p.hom :=
    Cofork.IsColimit.π_desc hcolimC
  -- a generalized element killed by `q` is killed by the coset quotient
  have htC : t.hom.hom ≫ q.hom.hom = (1 : T.X ⟶ Q.X) := by
    have h : (t ≫ q).hom.hom = (0 : T ⟶ Q).hom.hom :=
      congr(($ht).hom.hom)
    rw [ConnExact.zero_hom_hom] at h
    exact h
  have hkt : Kills s.quot t.hom.hom := by
    have h1 : t.hom.hom ≫ (s.quot).p.hom = (1 : T.X ⟶ X.X) ≫ (s.quot).p.hom := by
      rw [← hwq, ← Category.assoc, htC, ← MonObj.one_comp q.hom.hom, Category.assoc]
    rw [Kills, h1]
    exact Kills.one s.quot T.X
  obtain ⟨z, hz⟩ := factors_of_kills_quot s (hinj X.X s) hkt
  have : IsMonHom (z ≫ (Internal.relNormal r₁ r₂).hom.hom) := by
    rw [show z ≫ (Internal.relNormal r₁ r₂).hom.hom = t.hom.hom from hz]
    infer_instance
  have := Internal.isMonHom_of_comp_mono z (Internal.relNormal r₁ r₂).hom.hom
  exact ⟨Grp.homMk z, Grp.hom_ext _ _ (by simpa using hz)⟩

/-- **`Grp C` is Barr exact** granting the injectivity of Newman's correspondence and the
stability of regular epimorphisms of `Grp C` under base change.

The second hypothesis is what a proper orthogonal factorization system `(E, M)` on `C` whose left
class is closed under products supplies: it lifts to `Grp C`, where it is the (regular epi, mono)
factorization system, and the stability of its left class under base change may be checked along
sections precisely because `E` is closed under products.  For `C` regular — the case `E` = regular
epimorphisms, `M` = monomorphisms — this is the case of a regular category `C`, which is not
formalized here. -/
theorem isBarrExact_grp_of_cosetInjective_of_stableRegularEpi
    (hstab : MorphismProperty.IsStableUnderBaseChange (MorphismProperty.regularEpi (Grp C)))
    (hinj : CosetInjective C) : IsBarrExact (Grp C) :=
  Internal.isBarrExact_of_relNormalDetectsQuotient
    (relNormalDetectsQuotient_of_cosetInjective hinj) hstab


end InternalGroups
