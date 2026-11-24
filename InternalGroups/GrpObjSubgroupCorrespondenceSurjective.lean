module

public import InternalGroups.GrpStabilizerCoset

/-!
# Surjectivity of Newman's correspondence onto the regular quotients

Port of the surjectivity half of Newman's correspondence from the exactness development for
internal groups (the external `RequestProject` development).  The kernel pair of a quotient
module is the coset relation of the stabilizer of its base point (`isKernelPair_cosetMul_stab`);
a regular quotient module is therefore a quotient of the coset quotient of its stabilizer
(`le_quot_stab`); and every regular quotient module is the coset quotient of its stabilizer up to
the equivalence relation of the preorder (`antisymmRel_regQuot_stab`).  Consequently the map
`s ↦ G / s` from subgroup objects to regular quotient modules is surjective on the
antisymmetrized preorders (`cosetQuot_bijective`, whose injectivity half needs effectivity of the
coset relations).

The proof is stated for an **arbitrary module map** `p : G ⟶ V` (`isKernelPair_cosetMul_stabOf`),
using the stabilizer `InternalGroups.stabOf p` of `InternalGroups/GrpStabilizer.lean`; the
quotient-module case is the specialization `isKernelPair_cosetMul_stab`. Stating it at the arbitrary
map keeps the group structure of `G` applicable at implicit transparency, which the
`@[implicit_reducible] selfMod` object of a quotient module does not.

## Main results

* `InternalGroups.isKernelPair_cosetMul_stabOf`, `isKernelPair_cosetMul_stab`: the kernel pair of a
  module map is the coset relation of the stabilizer of its base point;
* `InternalGroups.le_quot_stab`: a regular quotient module is a quotient of the coset quotient of
  its stabilizer;
* `InternalGroups.antisymmRel_regQuot_stab`, `antisymmRel_stab_regQuot`: the two halves of the
  correspondence, up to the preorder equivalence;
* `InternalGroups.le_of_quot_le`, `cosetQuot_bijective`: the correspondence is bijective when the
  coset relations are effective.

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
variable {G : C} [GrpObj G]

/-- **The kernel pair of a module map is the coset relation of the stabilizer of its base
point.**  This is the exact analogue of the description, in `Set`, of the fibres of `G ⟶ G / K`
as the right cosets of the stabilizer `K` of the base point, and it holds unconditionally. -/
theorem isKernelPair_cosetMul_stabOf {V : C} [ModObj G V] (p : G ⟶ V) [IsModHom G p] :
    IsKernelPair p (cosetMul (stabOf p)) (fst G (stabOf p).N) := by
  have hcomm : cosetMul (stabOf p) ≫ p = fst G (stabOf p).N ≫ p :=
    cosetMul_comp_stabOf (f := p)
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm ?_ ?_ ?_ ?_)
  · intro c
    refine lift c.snd ?_
    refine ((killsOf_iff_factors p ((c.snd)⁻¹ * c.fst)).1 ?_).choose
    rw [killsOf_iff_act, act_mul, ← comp_eq_act, c.condition, comp_eq_act, ← act_mul,
      inv_mul_cancel, act_one]
  · intro c
    have hchoose := ((killsOf_iff_factors p ((c.snd)⁻¹ * c.fst)).1 (by
      rw [killsOf_iff_act, act_mul, ← comp_eq_act, c.condition, comp_eq_act, ← act_mul,
        inv_mul_cancel, act_one])).choose_spec
    rw [comp_cosetMul, lift_fst, lift_snd, stabOf_i, hchoose, mul_inv_cancel_left]
  · intro c
    exact lift_fst _ _
  · intro c m hm₁ hm₂
    have hchoose := ((killsOf_iff_factors p ((c.snd)⁻¹ * c.fst)).1 (by
      rw [killsOf_iff_act, act_mul, ← comp_eq_act, c.condition, comp_eq_act, ← act_mul,
        inv_mul_cancel, act_one])).choose_spec
    apply hom_ext
    · rw [hm₂, lift_fst]
    · rw [lift_snd, ← cancel_mono (stabOf p).i]
      rw [comp_cosetMul, hm₂] at hm₁
      rw [stabOf_i] at hm₁ ⊢
      rw [hchoose, ← hm₁, inv_mul_cancel_left]

/-- **The kernel pair of a quotient module is the coset relation of the stabilizer of its base
point.**  This is `isKernelPair_cosetMul_stabOf` at the module map of the quotient, using that
the stabilizer of that map is `InternalGroups.stab q`. -/
theorem isKernelPair_cosetMul_stab (q : QuotMod G) :
    IsKernelPair q.p.hom (cosetMul (stab q)) (fst G (stab q).N) := by
  let f : G ⟶ q.V.X := q.p.hom
  change IsKernelPair f (cosetMul (stab q)) (fst G (stab q).N)
  exact isKernelPair_cosetMul_stabOf (G := G) f

section Surjectivity

variable [HasReflexiveCoequalizers (CategoryTheory.Mod C G)]

/-- **A regular quotient module is a quotient of the coset quotient of its stabilizer.**  This is
the surjectivity half of Newman's correspondence: the coset quotient map and the regular quotient
map have the same kernel pair, so the regular quotient descends to the coset quotient. -/
theorem le_quot_stab (q : QuotMod G) (hq : RegularEpi q.p) : q ≤ (stab q).quot := by
  have hk := isKernelPair_cosetMul_stab q
  have hw : (hq.left.hom : hq.W.X ⟶ G) ≫ q.p.hom = (hq.right.hom : hq.W.X ⟶ G) ≫ q.p.hom := by
    rw [← CategoryTheory.Mod.comp_hom', ← CategoryTheory.Mod.comp_hom', hq.w]
  obtain ⟨t, ht₁, ht₂⟩ := hk.lift' (hq.left.hom : hq.W.X ⟶ G) (hq.right.hom : hq.W.X ⟶ G) hw
  have hcond : hq.left ≫ (stab q).quot.p = hq.right ≫ (stab q).quot.p := by
    apply CategoryTheory.Mod.Hom.ext
    rw [CategoryTheory.Mod.comp_hom', CategoryTheory.Mod.comp_hom']
    simp only [selfMod_X]
    rw [← ht₁, ← ht₂, Category.assoc, Category.assoc, cosetMul_comp_quot_p]
  exact ⟨hq.isColimit.desc (Cofork.ofπ (stab q).quot.p hcond),
    Cofork.IsColimit.π_desc hq.isColimit⟩

/-- **Every regular quotient module is the coset quotient of its stabilizer**, up to the
equivalence relation of the preorder. -/
theorem antisymmRel_regQuot_stab (q : RegQuot G) :
    AntisymmRel (· ≤ ·) (q.stab.regQuot) q :=
  ⟨quot_stab_le q.toQuotMod, le_quot_stab q.toQuotMod q.reg⟩

/-- **A subgroup object is the stabilizer of the coset quotient it determines**, provided its
coset relation is effective. -/
theorem antisymmRel_stab_regQuot (s : SubGrp G)
    (heff : IsKernelPair (s.quot).p.hom (cosetMul s) (fst G s.N)) :
    AntisymmRel (· ≤ ·) (s.regQuot.stab) s :=
  ⟨stab_quot_le s heff, le_stab_quot s⟩

/-- If the coset quotients of `s` and of `t` are comparable and the coset relation of `t` is
effective, then `s ≤ t`. -/
theorem le_of_quot_le {s t : SubGrp G}
    (heff : IsKernelPair (t.quot).p.hom (cosetMul t) (fst G t.N)) (h : s.quot ≤ t.quot) :
    s ≤ t :=
  (le_stab_quot s).trans ((galoisConnection_quot_stab.monotone_u h).trans (stab_quot_le t heff))

/-- **Newman's correspondence is bijective** on the antisymmetrizations, provided the coset
relation of every subgroup object is effective: `cosetQuot` is injective and surjective. -/
theorem cosetQuot_bijective
    (heff : ∀ s : SubGrp G, IsKernelPair (s.quot).p.hom (cosetMul s) (fst G s.N)) :
    Function.Bijective (cosetQuot (G := G)).antisymmetrization := by
  constructor
  · refine Quotient.ind₂ fun s t hst => ?_
    have h : AntisymmRel (· ≤ ·) s.regQuot t.regQuot := Quotient.exact hst
    exact Quotient.sound ⟨le_of_quot_le (heff t) h.1, le_of_quot_le (heff s) h.2⟩
  · refine Quotient.ind fun q => ?_
    exact ⟨Quotient.mk _ q.stab, Quotient.sound (antisymmRel_regQuot_stab q)⟩

end Surjectivity


end InternalGroups
