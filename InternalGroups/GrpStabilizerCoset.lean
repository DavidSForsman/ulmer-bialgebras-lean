module

public import InternalGroups.GrpStabilizer
public import InternalGroups.GrpObjSubgroupCorrespondenceRegular
public import InternalGroups.GrpKernelImage

/-!
# Every stabilizer is the stabilizer of its coset quotient

The author's observation: a stabilizer is the stabilizer of *its own* coset quotient, so the
group-level stabilizers are exactly the stabilizers of (genuine, i.e. epimorphic) quotient
modules — the general module map of `InternalGroups.GrpIsStabilizer` can always be replaced by a
quotient.

The proof does not use effectivity of the coset relation.  For `s := stabOf f` the module map `f`
coequalizes the coset relation of `s` (elements of the stabilizer act trivially on the base point),
so `f` factors through the coset quotient `s.quot`, say `f = s.quot.p.hom ≫ h`.  Then any element
killing `s.quot` kills `f`, i.e. `stab s.quot ≤ s`; and `s ≤ stab s.quot` is the unit of the Galois
connection.

## Main results

* `InternalGroups.cosetMul_comp_stabOf`: the module map coequalizes the coset relation of its
  stabilizer;
* `InternalGroups.stabOfQuotDesc`: the module map factors through the coset quotient of its
  stabilizer;
* `InternalGroups.stab_quot_stabOf_le`: the stabilizer of the coset quotient is contained in the
  stabilizer;
* `InternalGroups.SubGrp.isoOfLe`: two subgroup objects that contain each other are isomorphic over
  `G`;
* `InternalGroups.stabQuotStabOf`: the stabilizer of the coset quotient is the stabilizer, as an
  isomorphism over `G`;
* `InternalGroups.stab_quot_le_of_grpIsStabilizer`: a stabilizer is closed under the coset
  quotient/stabilizer correspondence.

Together with `InternalGroups.le_stab_quot` (`stabOf f ≤ stab (stabOf f).quot`) this shows that a
stabilizer and the stabilizer of its coset quotient contain each other;
`InternalGroups.SubGrp.isoOfLe` turns any two subgroup objects that contain each other into an
isomorphism over `G`, and `stabQuotStabOf` is the resulting isomorphism
`(stab (stabOf f).quot).toGrp ≅ (stabOf f).toGrp`, compatible with the inclusions
(`stab_quot_stabOf_hom_inclGrp`).  This is the author's observation that a stabilizer is the
stabilizer of its coset quotient; in particular the group-level stabilizers are the stabilizers of
genuine quotient modules.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits MonObj
open scoped MonObj
open CartesianMonoidalCategory

attribute [local instance] CategoryTheory.ModObj.regular

namespace InternalGroups

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-! ## Two subgroup objects that contain each other are isomorphic -/

section SubGrpIso

variable {G : C} [GrpObj G]

/-- A morphism whose composite with a monomorphism of monoid objects is a monoid morphism is a
monoid morphism. -/
lemma isMonHom_of_comp_mono {M N P : C} [MonObj M] [MonObj N] [MonObj P]
    (f : M ⟶ N) (g : N ⟶ P) (hm : Mono g) (hg : IsMonHom g) (hfg : IsMonHom (f ≫ g)) :
    IsMonHom f :=
  letI := hm
  letI := hg
  letI := hfg
  { one_hom := by
      refine (cancel_mono g).1 ?_
      rw [Category.assoc, IsMonHom.one_hom (f := f ≫ g), IsMonHom.one_hom (f := g)]
    mul_hom := by
      refine (cancel_mono g).1 ?_
      have hL : (μ[M] ≫ f) ≫ g = ((f ≫ g) ⊗ₘ (f ≫ g)) ≫ μ[P] := by
        rw [Category.assoc, IsMonHom.mul_hom (f := f ≫ g)]
      have hR : ((f ⊗ₘ f) ≫ μ[N]) ≫ g = (f ⊗ₘ f) ≫ ((g ⊗ₘ g) ≫ μ[P]) := by
        rw [Category.assoc, IsMonHom.mul_hom (f := g)]
      rw [hL, hR, ← tensorHom_comp_tensorHom, Category.assoc] }

/-- If two subgroup objects contain each other, they are isomorphic over `G`. -/
noncomputable def SubGrp.isoOfLe {s t : SubGrp G} (h₁ : s ≤ t) (h₂ : t ≤ s) :
    s.toGrp ≅ t.toGrp :=
  let u := Classical.choose h₁
  let hu : u ≫ t.i = s.i := Classical.choose_spec h₁
  let v := Classical.choose h₂
  let hv : v ≫ s.i = t.i := Classical.choose_spec h₂
  have hone : IsMonHom u :=
    isMonHom_of_comp_mono u t.i (SubGrp.mono_i t) (SubGrp.isMonHom_i t)
      (hu.symm ▸ SubGrp.isMonHom_i s)
  have honev : IsMonHom v :=
    isMonHom_of_comp_mono v s.i (SubGrp.mono_i s) (SubGrp.isMonHom_i s)
      (hv.symm ▸ SubGrp.isMonHom_i t)
  have hvu : v ≫ u = 𝟙 _ := (cancel_mono t.i).1
    ((Category.assoc v u t.i).trans ((v ≫= hu).trans (hv.trans (Category.id_comp _).symm)))
  have huv : u ≫ v = 𝟙 _ := (cancel_mono s.i).1
    ((Category.assoc u v s.i).trans ((u ≫= hv).trans (hu.trans (Category.id_comp _).symm)))
  { hom := Grp.homMk' (A := s.toGrp) (B := t.toGrp) { hom := u, isMonHom_hom := hone }
    inv := Grp.homMk' (A := t.toGrp) (B := s.toGrp) { hom := v, isMonHom_hom := honev }
    hom_inv_id := by
      apply Grp.hom_ext
      exact huv
    inv_hom_id := by
      apply Grp.hom_ext
      exact hvu }

/-- The isomorphism of `SubGrp.isoOfLe` is compatible with the inclusions. -/
lemma SubGrp.isoOfLe_hom_inclGrp {s t : SubGrp G} (h₁ : s ≤ t) (h₂ : t ≤ s) :
    (SubGrp.isoOfLe h₁ h₂).hom ≫ t.inclGrp = s.inclGrp := by
  apply Grp.hom_ext
  exact Classical.choose_spec h₁

end SubGrpIso

section Coset

variable [HasPullbacks C]
variable {G : C} [GrpObj G] {V : C} [ModObj G V] {f : G ⟶ V} [IsModHom G f]

/-- Elements of the stabilizer act trivially on the base point. -/
lemma act_stabSubIncl {T : C} (y : T ⟶ (stabOf f).N) :
    act (y ≫ (stabOf f).i) (toUnit T ≫ stabBasePoint f) = toUnit T ≫ stabBasePoint f := by
  rw [← comp_eq_act (f := f) (g := y ≫ (stabOf f).i)]
  rw [Category.assoc, stabOf_i]
  rw [stabSubIncl_comp f, ← Category.assoc,
    toUnit_unique (y ≫ toUnit _) (toUnit T)]

/-- Multiplying by an element of the stabilizer does not change the module map. -/
lemma mul_stabSubIncl_comp {T : C} (x : T ⟶ G) (y : T ⟶ (stabOf f).N) :
    (x * (y ≫ (stabOf f).i)) ≫ f = x ≫ f := by
  rw [comp_eq_act (f := f), comp_eq_act (f := f), act_mul, act_stabSubIncl]

/-- **The module map coequalizes the coset relation of its stabilizer.** -/
theorem cosetMul_comp_stabOf :
    cosetMul (stabOf f) ≫ f = fst G (stabOf f).N ≫ f := by
  exact mul_stabSubIncl_comp (fst G (stabOf f).N) (snd G (stabOf f).N)

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- **The module map factors through the coset quotient of its stabilizer.** -/
noncomputable def stabOfQuotDesc
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    (stabOf f).quot.V.X ⟶ V :=
  (isColimitCoforkQuot (stabOf f) hpres).desc (Cofork.ofπ f (cosetMul_comp_stabOf (f := f)))

/-- The factorization of the module map through the coset quotient. -/
@[reassoc (attr := simp)]
lemma stabOfQuot_p_desc
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    (stabOf f).quot.p.hom ≫ stabOfQuotDesc (f := f) hpres = f :=
  (isColimitCoforkQuot (stabOf f) hpres).fac
    (Cofork.ofπ f (cosetMul_comp_stabOf (f := f))) WalkingParallelPair.one

/-- **The stabilizer of the coset quotient is contained in the stabilizer.** -/
theorem stab_quot_stabOf_le
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    stab (stabOf f).quot ≤ stabOf f := by
  refine ⟨pullback.lift (QuotMod.subIncl (stabOf f).quot) (toUnit _) ?_, ?_⟩
  · have hbase : QuotMod.basePoint (stabOf f).quot ≫ stabOfQuotDesc (f := f) hpres =
        stabBasePoint f := by
      rw [QuotMod.basePoint, stabBasePoint, Category.assoc,
        stabOfQuot_p_desc (f := f) hpres]
    calc QuotMod.subIncl (stabOf f).quot ≫ f
        = QuotMod.subIncl (stabOf f).quot ≫ (stabOf f).quot.p.hom ≫
            stabOfQuotDesc (f := f) hpres := by
          rw [stabOfQuot_p_desc (f := f) hpres]
      _ = (QuotMod.subIncl (stabOf f).quot ≫ (stabOf f).quot.p.hom) ≫
            stabOfQuotDesc (f := f) hpres := (Category.assoc _ _ _).symm
      _ = (toUnit (QuotMod.subObj (stabOf f).quot) ≫ QuotMod.basePoint (stabOf f).quot) ≫
            stabOfQuotDesc (f := f) hpres := by
          rw [QuotMod.subIncl_comp_p isTerminalTensorUnit, InternalGroups.isTerminalTensorUnit_from]
      _ = toUnit (QuotMod.subObj (stabOf f).quot) ≫
            (QuotMod.basePoint (stabOf f).quot ≫ stabOfQuotDesc (f := f) hpres) :=
          Category.assoc _ _ _
      _ = toUnit (QuotMod.subObj (stabOf f).quot) ≫ stabBasePoint f := by rw [hbase]
  · exact pullback.lift_fst _ _ _

/-- **Every stabilizer is the stabilizer of its coset quotient.** -/
noncomputable def stabQuotStabOf
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    (stab (stabOf f).quot).toGrp ≅ (stabOf f).toGrp :=
  SubGrp.isoOfLe (stab_quot_stabOf_le (f := f) hpres) (le_stab_quot (stabOf f))

/-- The isomorphism of `stabQuotStabOf` is compatible with the inclusions. -/
@[reassoc]
lemma stab_quot_stabOf_hom_inclGrp
    (hpres : CategoryTheory.PreservesReflexiveCoeq (CategoryTheory.Mod.forget (D := C) G)) :
    (stabQuotStabOf (f := f) hpres).hom ≫ (stabOf f).inclGrp =
      (stab (stabOf f).quot).inclGrp :=
  SubGrp.isoOfLe_hom_inclGrp _ _

end Coset

end InternalGroups

/-! ## Coset closure of stabilizers -/

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
namespace InternalGroups
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [HasPullbacks C]
variable [HasReflexiveCoequalizers C] [∀ Z : C, PreservesReflexiveCoeq (tensorLeft Z)]

/-- A subgroup whose inclusion is a stabilizer is fixed by coset closure. -/
theorem stab_quot_le_of_grpIsStabilizer {G : C} [GrpObj G] (s : SubGrp G)
    (hs : GrpIsStabilizer s.inclGrp) : stab s.quot ≤ s := by
  obtain ⟨q, e, he⟩ := hs
  let t := stabOf (G := G) (V := q.right.X) q.hom.hom
  have hst : s ≤ t := ⟨e.hom.hom.hom, congr(($he).hom.hom)⟩
  have he' : e.inv ≫ s.inclGrp = t.inclGrp := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hts : t ≤ s := ⟨e.inv.hom.hom, congr(($he').hom.hom)⟩
  have ht : stab t.quot ≤ t :=
    stab_quot_stabOf_le (G := G) (V := q.right.X) (f := q.hom.hom)
      (CategoryTheory.Mod_.preservesReflexiveCoequalizers_forget (A := G)
        (fun _ => inferInstance))
  exact le_trans
    (galoisConnection_quot_stab.monotone_u (galoisConnection_quot_stab.monotone_l hst))
    (le_trans ht hts)

end InternalGroups
