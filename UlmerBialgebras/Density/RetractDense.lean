module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import UlmerBialgebras.Density.ADense

/-!
# Constructing non-trivial dense classes: retracts

This file isolates a set of assumptions on a 2-category `K` and a class `A` of its objects
towards the density of `A`, which are weak enough to be satisfied by *proper* classes `A`
(so that the resulting dense class is non-trivial, unlike the class of **all** objects, which
is dense in any 2-category by the Yoneda argument).  "Dense" is the bi-density of
Definition 7.1 of the paper.

The assumption is a *retract* condition:

* `UlmerBialgebras.Retract a c` — `c` is a retract of `a` up to isomorphism: 1-cells `s : a ⟶ c`,
  `r : c ⟶ a` and an invertible 2-cell `r ≫ s ≅ 𝟙 c`.  In particular an equivalence
  `a ≃ c` gives a retract, and so does an isomorphism of objects.
* `UlmerBialgebras.ARetractive A` — every object of `K` is a retract of an object of `A`.

The results are:

* `UlmerBialgebras.isACellDense_of_aRetractive` — **the local half of density holds under the
  retract condition alone**, in an arbitrary 2-category: a compatible family of 2-cells on the
  `A`-representables comes from a unique 2-cell.  The 2-cell is the conjugate, by the
  retraction isomorphism, of the component of the family at the section.
* `UlmerBialgebras.AHomFamily.retractOneCell` — the candidate representing 1-cell `r ≫ G(s)` of a
  pseudonatural family for the 1-cell half of density; that it represents the family under a
  cell-compatibility hypothesis is shown in `CellCompatDense.lean`.

## Main results

* `UlmerBialgebras.Retract`: `c` is a retract of `a` up to an invertible 2-cell.
* `UlmerBialgebras.ARetractive`: every object of `K` is a retract of an object of `A`.
* `UlmerBialgebras.aRetractive_true`: the class of all objects is retractive.
* `UlmerBialgebras.isACellDense_of_aRetractive`: a retractive class is locally dense
  (`UlmerBialgebras.IsACellDense`, the 2-cell half of Definition 7.1).
* `UlmerBialgebras.AHomFamily.retractOneCell`: the candidate representing 1-cell `r ≫ G(s)` of a
  pseudonatural family.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in Bicategories*][Street1980FibrationsBicategories], (1.9)
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Retracts -/

/-- `c` is a **retract** of `a` (up to isomorphism): a section `s : a ⟶ c`, a retraction
`r : c ⟶ a` and an invertible 2-cell `r ≫ s ≅ 𝟙 c`. -/
structure Retract (a c : Obj) where
  /-- The section. -/
  sec : a ⟶ c
  /-- The retraction. -/
  ret : c ⟶ a
  /-- The retraction isomorphism. -/
  iso : ret ≫ sec ≅ 𝟙 c

namespace Retract

/-- Every object is a retract of itself. -/
def refl (c : Obj) : Retract c c where
  sec := 𝟙 c
  ret := 𝟙 c
  iso := eqToIso (Category.id_comp _)

variable {a c : Obj} (R : Retract a c)

/-- The retraction isomorphism whiskered by a 1-cell `k : y ⟶ c`. -/
@[simps]
def keyIso {y : Obj} (k : y ⟶ c) : k ≫ (R.ret ≫ R.sec) ≅ k where
  hom := (k ◁ R.iso.hom) ≫ eqToHom (Category.comp_id k)
  inv := eqToHom (Category.comp_id k).symm ≫ (k ◁ R.iso.inv)
  hom_inv_id := by
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Bicategory.whiskerLeft_comp, R.iso.hom_inv_id, Bicategory.whiskerLeft_id]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (k ◁ R.iso.inv), ← Bicategory.whiskerLeft_comp,
      R.iso.inv_hom_id, Bicategory.whiskerLeft_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

/-- The retraction isomorphism whiskered by a 1-cell `k : y ⟶ c`, in the form of an
isomorphism `(k ≫ r) ≫ s ≅ k`. -/
def factorIso {y : Obj} (k : y ⟶ c) : (k ≫ R.ret) ≫ R.sec ≅ k :=
  eqToIso (Category.assoc k R.ret R.sec) ≪≫ R.keyIso k

/-- The **conjugate by the retraction** of a 2-cell `s ≫ p ⟶ s ≫ q`: a 2-cell `p ⟶ q`. -/
def conj {d : Obj} {p q : c ⟶ d} (β : R.sec ≫ p ⟶ R.sec ≫ q) : p ⟶ q :=
  eqToHom (Category.id_comp p).symm ≫ (R.iso.inv ▷ p) ≫ eqToHom (Category.assoc R.ret R.sec p) ≫
    (R.ret ◁ β) ≫ eqToHom (Category.assoc R.ret R.sec q).symm ≫ (R.iso.hom ▷ q) ≫
      eqToHom (Category.id_comp q)

/-- Conjugating the whiskering of a 2-cell by the section gives the 2-cell back: a 2-cell
`p ⟶ q` is determined by its whiskering `s ≫ p ⟶ s ≫ q` by the section. -/
lemma conj_whiskerLeft {d : Obj} {p q : c ⟶ d} (α : p ⟶ q) : R.conj (R.sec ◁ α) = α := by
  rw [conj, Bicategory.Strict.comp_whiskerLeft' R.ret R.sec α]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((R.ret ≫ R.sec) ◁ α), Bicategory.whisker_exchange,
    Bicategory.Strict.id_whiskerLeft α]
  simp only [← Category.assoc, ← Bicategory.comp_whiskerRight, Iso.inv_hom_id,
    Bicategory.id_whiskerRight]
  simp

/-- Whiskering a conjugate by a 1-cell `k : y ⟶ c`: the result is, up to the canonical
isomorphism `(k ≫ r) ≫ s ≅ k`, the whiskering of the original 2-cell by `k ≫ r`. -/
lemma whiskerLeft_conj {d : Obj} {p q : c ⟶ d} (β : R.sec ≫ p ⟶ R.sec ≫ q) {y : Obj}
    (k : y ⟶ c) :
    ((R.factorIso k).hom ▷ p) ≫ (k ◁ R.conj β)
      = eqToHom (Category.assoc (k ≫ R.ret) R.sec p) ≫ ((k ≫ R.ret) ◁ β) ≫
        eqToHom (Category.assoc (k ≫ R.ret) R.sec q).symm ≫ ((R.factorIso k).hom ▷ q) := by
  rw [conj, factorIso]
  simp only [Iso.trans_hom, eqToIso.hom, keyIso_hom, Category.assoc, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Bicategory.comp_whiskerRight, Bicategory.eqToHom_whiskerRight]
  rw [Bicategory.Strict.whisker_assoc k R.iso.inv p, Bicategory.Strict.comp_whiskerLeft' k R.ret β,
    Bicategory.Strict.whisker_assoc k R.iso.hom q]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((k ◁ R.iso.hom) ▷ p), ← Bicategory.comp_whiskerRight,
    ← Bicategory.whiskerLeft_comp,
    R.iso.hom_inv_id, Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight, Category.id_comp]
  simp

end Retract

/-- The class `A` is **retractive**: every object of the 2-category is a retract of an object
of `A`.  For instance every object is equivalent to an object of `A`. -/
def ARetractive (A : ObjectProperty Obj) : Prop :=
  ∀ c : Obj, ∃ a : Obj, A a ∧ Nonempty (Retract a c)

/-- The class of all objects is retractive. -/
theorem aRetractive_true : ARetractive (⊤ : ObjectProperty Obj) :=
  fun c => ⟨c, trivial, ⟨Retract.refl c⟩⟩

/-! ## The local half of density -/

namespace ACellFamily

variable {A : ObjectProperty Obj} {c d : Obj} {p q : c ⟶ d}

end ACellFamily

/-- **The local half of density under the retract condition**, in an arbitrary 2-category:
if every object is a retract of an object of `A`, then every compatible family of 2-cells on
the `A`-representables comes from a unique 2-cell. -/
theorem isACellDense_of_aRetractive {A : ObjectProperty Obj} (h : ARetractive A) : IsACellDense
  A := by
  intro c d p q Φ
  obtain ⟨a, ha, ⟨R⟩⟩ := h c
  refine ⟨R.conj ((Φ.app ha).app R.sec), ?_, ?_⟩
  · intro y hy
    ext k
    have hnat := (Φ.app hy).naturality ((R.factorIso k).hom)
    simp only [postcomp_map, postcomp_obj] at hnat
    rw [← cancel_epi ((R.factorIso k).hom ▷ p)]
    change ((R.factorIso k).hom ▷ p) ≫ k ◁ R.conj ((Φ.app ha).app R.sec) = _
    rw [Retract.whiskerLeft_conj, Φ.naturality hy ha (k ≫ R.ret) R.sec, hnat]
    simp
  · intro α hα
    conv_lhs => rw [← R.conj_whiskerLeft α]
    congr 1
    exact congrArg (fun ψ => NatTrans.app ψ R.sec) (hα ha)

/-! ## The 1-cell half, for locally thin 2-categories -/

/-- Under the retract condition a pseudonatural family of functors on the `A`-representables
from `d` to `c` produces a 1-cell `d ⟶ c`: apply the family, at the object of `A` that `d`
retracts onto, to the section, and pre-compose with the retraction. -/
def AHomFamily.retractOneCell {A : ObjectProperty Obj} {d c : Obj} (G : AHomFamily A d c) {a : Obj}
    (ha : A a) (R : Retract a d) : d ⟶ c :=
  R.ret ≫ (G.fn ha).obj R.sec

/-! ## Non-triviality -/

end UlmerBialgebras
