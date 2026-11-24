module

public import UlmerBialgebras.Density.RetractDense

/-!
# The 1-cell half of density: 2-cells have to be representable by 1-cells

`RetractDense.lean` shows that the **2-cell half** of density (local 2-full-faithfulness of
the restricted Yoneda 2-functor) follows from the retract condition `UlmerBialgebras.ARetractive`
alone, in any 2-category.  The **1-cell half** needs more, and this file explains exactly what.

A pseudonatural family `UlmerBialgebras.AHomFamily` carries comparison isomorphisms indexed by the
*1-cells* `u : x ⟶ y` of `A`, but no compatibility with *2-cells* `u ⟶ u'`.  The candidate
representing 1-cell built from a retract, `g = r ≫ F_a(s)`, has a comparison
`k ≫ g ≅ F_x(k)` whose definition uses the comparison of the family at the 1-cell `k ≫ r`,
so the parameter `k` sits in the *index* slot and naturality of the comparison in `k` is
exactly the missing 2-cell axiom.  Accordingly:

* `UlmerBialgebras.AHomFamily.IsCellCompatible` — the missing axiom: the comparison isomorphisms are
  compatible with 2-cells between the indexing 1-cells.
* `UlmerBialgebras.AHomFamily.retractRepresentation` — **the general construction**: under the
  retract condition, a cell-compatible family is represented by the 1-cell `r ≫ F_a(s)`.

The axiom is necessary (a family induced by a 1-cell satisfies it, so no hypothesis on `K`
alone can give the 1-cell half), and it is vacuous in a locally thin 2-category; these facts,
the reduction to *generic* 2-cells in the presence of arrow objects, and the construction of
non-trivial dense classes from reduction operators are not formalized in this file.

In `CAT_V` the arrow objects are the free `V`-categories on an arrow, whose construction is
the only place where the absorbing initial object of `V` is used; the concrete closure
conditions consumed by that reconstruction are packaged in `VProbeSystem.lean` and satisfied
by the very small class of `VCatTinyDense.lean`.

## Main results

* `UlmerBialgebras.AHomFamily.IsCellCompatible`: the comparison isomorphisms of a pseudonatural
  family are compatible with 2-cells between the indexing 1-cells.
* `UlmerBialgebras.AHomFamily.retractRepresentation`: under the retract condition
  `UlmerBialgebras.ARetractive`, a cell-compatible family is represented by the 1-cell built from a
  retract.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 7.1 and Appendix A
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Cell-compatibility -/

/-- A pseudonatural family on the `A`-representables is **cell-compatible** when its
comparison isomorphisms are compatible with 2-cells between the indexing 1-cells.  This is
the axiom of a pseudonatural transformation that `UlmerBialgebras.AHomFamily` omits. -/
def AHomFamily.IsCellCompatible {A : ObjectProperty Obj} {d c : Obj} (G : AHomFamily A d c) :
  Prop :=
  ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) {u u' : x ⟶ y} (δ : u ⟶ u') (m : y ⟶ d),
    (G.fn hx).map (δ ▷ m) ≫ (G.nat hx hy u').hom.app m
      = (G.nat hx hy u).hom.app m ≫ (δ ▷ (G.fn hy).obj m)

namespace AHomFamily

variable {A : ObjectProperty Obj} {d c : Obj}

end AHomFamily

/-! ## Two lemmas on the comparison isomorphism of a retract -/

namespace Retract

variable {a d : Obj} (R : Retract a d)

/-- The isomorphism `(k ≫ r) ≫ s ≅ k` is natural in `k`. -/
lemma factorIso_naturality {x : Obj} {k k' : x ⟶ d} (α : k ⟶ k') :
    ((α ▷ R.ret) ▷ R.sec) ≫ (R.factorIso k').hom = (R.factorIso k).hom ≫ α := by
  rw [factorIso, factorIso]
  simp only [Iso.trans_hom, eqToIso.hom, keyIso_hom, Category.assoc]
  rw [Bicategory.Strict.whiskerRight_comp' α R.ret R.sec]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (α ▷ (R.ret ≫ R.sec)), ← Bicategory.whisker_exchange,
    Bicategory.Strict.whiskerRight_id α]
  simp

/-- The isomorphism `(k ≫ r) ≫ s ≅ k` is compatible with pre-composition. -/
lemma factorIso_comp {x y : Obj} (u : x ⟶ y) (k : y ⟶ d) :
    (R.factorIso (u ≫ k)).hom
      = eqToHom (by rw [Category.assoc u k R.ret, Category.assoc u (k ≫ R.ret) R.sec]) ≫
          (u ◁ (R.factorIso k).hom) := by
  rw [factorIso, factorIso]
  simp only [Iso.trans_hom, eqToIso.hom, keyIso_hom, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom]
  rw [Bicategory.Strict.comp_whiskerLeft u k R.iso.hom]
  simp

end Retract

/-! ## The 1-cell half from the retract condition and cell-compatibility -/

namespace AHomFamily

variable {A : ObjectProperty Obj} {d c : Obj} (G : AHomFamily A d c) {a : Obj} (ha : A a)
  (R : Retract a d)

/-- The comparison isomorphism between post-composition with the 1-cell `r ≫ F_a(s)` built
from a retract and the value of the family, at a 1-cell `k : x ⟶ d`. -/
def retractIsoApp {x : Obj} (hx : A x) (k : x ⟶ d) :
    (postcomp x (G.retractOneCell ha R)).obj k ≅ (G.fn hx).obj k :=
  eqToIso (Category.assoc k R.ret ((G.fn ha).obj R.sec)).symm ≪≫
    ((G.nat hx ha (k ≫ R.ret)).app R.sec).symm ≪≫ (G.fn hx).mapIso (R.factorIso k)

/-- The comparison isomorphism is natural in `k`; this is where cell-compatibility is used. -/
lemma retractIsoApp_naturality (hcc : G.IsCellCompatible) {x : Obj} (hx : A x)
    {k k' : x ⟶ d} (α : k ⟶ k') :
    (postcomp x (G.retractOneCell ha R)).map α ≫ (G.retractIsoApp ha R hx k').hom
      = (G.retractIsoApp ha R hx k).hom ≫ (G.fn hx).map α := by
  have key : ((α ▷ R.ret) ▷ (G.fn ha).obj R.sec) ≫ (G.nat hx ha (k' ≫ R.ret)).inv.app R.sec
      = (G.nat hx ha (k ≫ R.ret)).inv.app R.sec ≫ (G.fn hx).map ((α ▷ R.ret) ▷ R.sec) := by
    rw [← cancel_epi ((G.nat hx ha (k ≫ R.ret)).hom.app R.sec),
      ← Category.assoc (obj := _ ⟶ _),
      ← hcc hx ha (α ▷ R.ret) R.sec]
    simp
  rw [retractIsoApp, retractIsoApp]
  unfold retractOneCell
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    postcomp_map, Category.assoc]
  rw [Bicategory.Strict.whiskerRight_comp α R.ret ((G.fn ha).obj R.sec)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((α ▷ R.ret) ▷ (G.fn ha).obj R.sec), key,
    Category.assoc (obj := _ ⟶ _),
    ← Functor.map_comp, ← Functor.map_comp, R.factorIso_naturality α]

/-- The comparison isomorphism is compatible with the pseudonaturality isomorphisms of the
family. -/
lemma retractIsoApp_nat {x y : Obj} (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d) :
    (G.retractIsoApp ha R hx (u ≫ k)).hom ≫ (G.nat hx hy u).hom.app k
      = eqToHom (Category.assoc u k (G.retractOneCell ha R)) ≫
        (u ◁ (G.retractIsoApp ha R hy k).hom) := by
  have hcong := G.nat_congr hx ha (Category.assoc u k R.ret) R.sec
  have hcomp := G.nat_comp hx hy ha u (k ≫ R.ret) R.sec
  have hnatu := (G.nat hx hy u).hom.naturality (R.factorIso k).hom
  simp only [Functor.comp_map, precomp_map] at hnatu
  have core : (G.nat hx ha ((u ≫ k) ≫ R.ret)).inv.app R.sec ≫
      (G.fn hx).map (R.factorIso (u ≫ k)).hom ≫ (G.nat hx hy u).hom.app k
        = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.assoc]) ≫
          (u ◁ (G.nat hy ha (k ≫ R.ret)).inv.app R.sec) ≫
          (u ◁ (G.fn hy).map (R.factorIso k).hom) := by
    rw [← cancel_epi ((G.nat hx ha ((u ≫ k) ≫ R.ret)).hom.app R.sec)]
    rw [← Category.assoc (obj := _ ⟶ _), Iso.hom_inv_id_app,
      Category.id_comp, R.factorIso_comp u k, Functor.map_comp, eqToHom_map,
      ]
    simp only [Category.assoc, hnatu, hcong, hcomp]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Bicategory.whiskerLeft_comp]
    simp
  rw [retractIsoApp, retractIsoApp]
  unfold retractOneCell
  simp only [Iso.trans_hom, eqToIso.hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc, Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom]
  rw [core]
  simp

/-- The representation of a cell-compatible family by the 1-cell built from a retract. -/
def retractRepresentation (hcc : G.IsCellCompatible) : G.Representation where
  g := G.retractOneCell ha R
  iso := fun _ hx => NatIso.ofComponents (fun k => G.retractIsoApp ha R hx k)
    (fun α => G.retractIsoApp_naturality ha R hcc hx α)
  iso_nat := fun _ _ hx hy u k => G.retractIsoApp_nat ha R hx hy u k

end AHomFamily

end UlmerBialgebras
