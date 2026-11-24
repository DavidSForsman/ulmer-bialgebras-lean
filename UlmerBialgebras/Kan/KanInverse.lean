module

public import UlmerBialgebras.Kan.KanComp
public import Foundations.CategoryTheory.Bicategory.StrictCoherence

/-!
# Strict creation along a 1-cell with a strict inverse

In a strict bicategory, a 1-cell `f : c ⟶ c'` with a strict inverse `g` (`f ≫ g = 𝟙 c` and
`g ≫ f = 𝟙 c'`) strictly creates every left Kan extension: pushing extensions along `f` is
bijective on objects, with inverse "push along `g`, then transport", and it is faithful. In
`CAT`, such an `f` is an isomorphism of categories. This lets strict creation pass along an
isomorphism of categories, for example from the category of models of a `Σ_Cart`-theory to the
isomorphic category of models of an equational theory.

## Main results

* `UlmerBialgebras.strictlyCreatesLeftKan_of_inv`: a 1-cell with a strict inverse strictly
  creates every left Kan extension.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 4.4
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Bicategory

variable {Obj : Type u} [Bicategory.{w, v} Obj]

variable {I X c c' : Obj}

/-- Two left extensions with the same underlying 1-cell and heterogeneously equal comparison
2-cells are equal. -/
lemma LeftExt.ext_of_heq {k : I ⟶ X} {d : I ⟶ c} {L L' : LeftExt k d} (h : L.ext = L'.ext)
    (h2 : HEq L.unit L'.unit) : L = L' := by
  obtain ⟨⟨⟨⟩⟩, e, u⟩ := L
  obtain ⟨⟨⟨⟩⟩, e', u'⟩ := L'
  cases h
  cases h2
  rfl

/-- Right whiskering respects heterogeneous equality of the whiskered 2-cells. -/
lemma whiskerRight_congr_heq {a b c₀ : Obj} {f f' g g' : a ⟶ b} (hf : f = f') (hg : g = g')
    {α : f ⟶ g} {α' : f' ⟶ g'} (h : HEq α α') (k : b ⟶ c₀) : HEq (α ▷ k) (α' ▷ k) := by
  subst hf hg
  cases h
  rfl

variable [Bicategory.Strict Obj]

/-- Right whiskering by a 1-cell equal to an identity is the identity, up to heterogeneous
equality. -/
lemma whiskerRight_heq_of_eq_id {a b : Obj} {f g : a ⟶ b} (α : f ⟶ g) {h : b ⟶ b}
    (hh : h = 𝟙 b) : HEq (α ▷ h) α := by
  subst hh
  exact Bicategory.Strict.whiskerRight_id_heq α

/-- Whiskering by `f` and then by a right inverse `g` of `f` is the identity, up to
heterogeneous equality. -/
lemma whiskerRight_whiskerRight_heq {a b : Obj} {f₀ g₀ : a ⟶ b} (α : f₀ ⟶ g₀) {f : b ⟶ c}
    {g : c ⟶ b} (hfg : f ≫ g = 𝟙 b) : HEq ((α ▷ f) ▷ g) α :=
  (Bicategory.Strict.whiskerRight_comp_heq α f g).symm.trans (whiskerRight_heq_of_eq_id α hfg)

section Inverse

variable (k : I ⟶ X) (d : I ⟶ c) {f : c ⟶ c'} {g : c' ⟶ c} (hfg : f ≫ g = 𝟙 c)
  (hgf : g ≫ f = 𝟙 c')

include hfg in
/-- The comparison `(d ≫ f) ≫ g = d` for a right inverse `g` of `f`. -/
lemma comp_comp_eq_of_inv : (d ≫ f) ≫ g = d := by
  rw [Category.assoc, hfg, Category.comp_id]

/-- The inverse of pushing along `f`: push along `g`, then transport along `(d ≫ f) ≫ g = d`. -/
def LeftExt.pushInv : LeftExt k (d ≫ f) ⥤ LeftExt k d :=
  LeftExt.push k (d ≫ f) g ⋙ LeftExt.reindex k (comp_comp_eq_of_inv d hfg)

include hfg in
/-- Pushing along `f` and then along its inverse gives back the extension. -/
lemma LeftExt.pushInv_push_obj (L : LeftExt k d) :
    (LeftExt.pushInv k d hfg).obj ((LeftExt.push k d f).obj L) = L := by
  refine LeftExt.ext_of_heq (comp_comp_eq_of_inv L.ext hfg) ?_
  simp only [LeftExt.pushInv, Functor.comp_obj, LeftExt.reindex_obj_unit, LeftExt.push_obj_unit,
    Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  refine (eqToHom_comp_heq _ _).trans ?_
  refine (comp_eqToHom_heq _ _).trans ?_
  refine (comp_eqToHom_heq _ _).trans ?_
  exact whiskerRight_whiskerRight_heq L.unit hfg

include hgf in
/-- Pushing along the inverse and then along `f` gives back the extension. -/
lemma LeftExt.push_pushInv_obj (L : LeftExt k (d ≫ f)) :
    (LeftExt.push k d f).obj ((LeftExt.pushInv k d hfg).obj L) = L := by
  refine LeftExt.ext_of_heq (comp_comp_eq_of_inv L.ext hgf) ?_
  simp only [LeftExt.pushInv, Functor.comp_obj, LeftExt.reindex_obj_unit, LeftExt.push_obj_unit]
  refine (comp_eqToHom_heq _ _).trans ?_
  refine (whiskerRight_congr_heq (comp_comp_eq_of_inv d hfg).symm ?_
    ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)) f).trans ?_
  · exact (Category.assoc _ _ _).symm
  exact whiskerRight_whiskerRight_heq L.unit hgf

include hfg in
/-- Pushing along a 1-cell with a right inverse is faithful. -/
lemma LeftExt.push_map_injective {L L' : LeftExt k d} {α β : L ⟶ L'}
    (h : (LeftExt.push k d f).map α = (LeftExt.push k d f).map β) : α = β := by
  have h1 : LeftExt.homCell α ▷ f = LeftExt.homCell β ▷ f := LeftExt.hom_ext_iff.mp h
  apply LeftExt.hom_ext
  exact eq_of_heq ((whiskerRight_whiskerRight_heq (LeftExt.homCell α) hfg).symm.trans
    ((heq_of_eq (congr($h1 ▷ g))).trans
      (whiskerRight_whiskerRight_heq (LeftExt.homCell β) hfg)))

end Inverse

/-- **A 1-cell with a strict inverse strictly creates every left Kan extension.** -/
theorem strictlyCreatesLeftKan_of_inv (k : I ⟶ X) (d : I ⟶ c) {f : c ⟶ c'} {g : c' ⟶ c}
    (hfg : f ≫ g = 𝟙 c) (hgf : g ≫ f = 𝟙 c') : StrictlyCreatesLeftKan k d f := by
  intro b hb
  set P := LeftExt.push k d f
  set Q := LeftExt.pushInv k d hfg
  have hPQ : P.obj (Q.obj b) = b := LeftExt.push_pushInv_obj k d hfg hgf b
  refine ⟨⟨Q.obj b, hPQ, fun a ha => ?_⟩, fun a ha => ?_⟩
  · rw [← ha]; exact (LeftExt.pushInv_push_obj k d hfg a).symm
  · obtain ⟨hb⟩ := hb
    have hQ : Q.obj (P.obj a) = a := LeftExt.pushInv_push_obj k d hfg a
    refine ⟨Limits.IsInitial.ofUniqueHom (fun x => eqToHom hQ.symm ≫
        Q.map (eqToHom ha ≫ hb.to (P.obj x)) ≫ eqToHom (LeftExt.pushInv_push_obj k d hfg x))
      (fun x m => ?_)⟩
    apply LeftExt.push_map_injective k d hfg
    apply (cancel_epi (eqToHom ha.symm)).1
    exact hb.hom_ext _ _

end UlmerBialgebras
