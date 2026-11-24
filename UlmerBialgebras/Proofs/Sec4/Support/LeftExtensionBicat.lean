module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import Mathlib.CategoryTheory.Bicategory.Kan.IsKan

/-!
# Left extensions in the Mathlib bicategory

Comparison of the project's category of left extensions with Mathlib's bicategorical
left-extension category for the same 1-cells.

## Main results

* `UlmerBialgebras.LeftExt.bicatEquiv`: the project's category of left extensions of `d` along `k`
  is equivalent to Mathlib's `Bicategory.LeftExtension k d`.
* `UlmerBialgebras.LeftExt.isInitial_iff_isKan`: a left extension is initial iff its image is a Kan
  extension in Mathlib's sense.
* `UlmerBialgebras.LeftExt.isAbsoluteLeftKan_iff`: the project's absolute left Kan predicate agrees
  with Mathlib's `Bicategory.LeftExtension.IsAbsKan`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 4.2 and Corollary 4.10
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable {I X c : AsBicat.{u, v, w} Obj} (k : I ⟶ X) (d : I ⟶ c)

/-- Regard a local left extension as Mathlib's bicategorical left extension. -/
def LeftExt.toBicat : LeftExt (Obj := Obj) k d ⥤ Bicategory.LeftExtension k d where
  obj L := Bicategory.LeftExtension.mk L.ext L.unit
  map α := Bicategory.LeftExtension.homMk (LeftExt.homCell α) (LeftExt.w α)

/-- Regard a Mathlib bicategorical left extension as a local left extension. -/
def LeftExt.ofBicat : Bicategory.LeftExtension k d ⥤ LeftExt (Obj := Obj) k d where
  obj L := LeftExt.mk L.extension L.unit
  map α := LeftExt.homMk α.right (Bicategory.LeftExtension.w α)

/-- The comparison `toBicat` is the identity on objects: `LeftExt k d` is Mathlib's
`Bicategory.LeftExtension k d`, and an extension has the same 1-cell and 2-cell on both sides. -/
theorem LeftExt.toBicat_obj (L : LeftExt (Obj := Obj) k d) :
    (LeftExt.toBicat k d).obj L = L := rfl

/-- The comparison `toBicat` is the identity on morphisms. -/
theorem LeftExt.toBicat_map {L L' : LeftExt (Obj := Obj) k d} (α : L ⟶ L') :
    (LeftExt.toBicat k d).map α = α :=
  LeftExt.hom_ext rfl

instance : (LeftExt.toBicat k d).Faithful where
  map_injective h := LeftExt.hom_ext (congrArg StructuredArrow.Hom.right h)

instance : (LeftExt.toBicat k d).Full where
  map_surjective α := ⟨LeftExt.homMk α.right (Bicategory.LeftExtension.w α), rfl⟩

instance : (LeftExt.toBicat k d).EssSurj where
  mem_essImage L := ⟨(LeftExt.ofBicat k d).obj L, ⟨eqToIso rfl⟩⟩

instance : (LeftExt.toBicat k d).IsEquivalence where

/-- The local and Mathlib categories of left extensions are equivalent. -/
noncomputable def LeftExt.bicatEquiv : LeftExt (Obj := Obj) k d ≌ Bicategory.LeftExtension k d :=
  (LeftExt.toBicat k d).asEquivalence

/-- Initiality of a local left extension is equivalent to Mathlib's Kan property. -/
theorem LeftExt.isInitial_iff_isKan (L : LeftExt (Obj := Obj) k d) :
    Nonempty (Limits.IsInitial L) ↔
      Nonempty (Bicategory.LeftExtension.IsKan ((LeftExt.toBicat k d).obj L)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨isInitialObjOfFullyFaithful (LeftExt.toBicat k d)
      (fun L => ⟨(LeftExt.ofBicat k d).obj L, rfl⟩) h⟩
  · rintro ⟨h⟩
    exact ⟨isInitialOfFullyFaithful (LeftExt.toBicat k d) h⟩

/-- Translating a pushed left extension agrees with bicategorical whiskering. -/
lemma LeftExt.toBicat_push (L : LeftExt (Obj := Obj) k d) {c' : Obj} (f : c ⟶ c') :
    (LeftExt.toBicat k (d ≫ f)).obj ((LeftExt.push k d f).obj L) =
      ((LeftExt.toBicat k d).obj L).whisker f := by
  dsimp [LeftExt.toBicat, LeftExt.push, Bicategory.LeftExtension.whisker]
  rw [Bicategory.Strict.associator_eqToIso]
  rfl

/-- The project's absolute Kan predicate agrees with Mathlib's bicategorical one. -/
theorem LeftExt.isAbsoluteLeftKan_iff (L : LeftExt (Obj := Obj) k d) :
    Paper.IsAbsoluteLeftKan k d L ↔
      Nonempty (Bicategory.LeftExtension.IsAbsKan ((LeftExt.toBicat k d).obj L)) := by
  constructor
  · intro h
    classical
    refine ⟨fun f => ?_⟩
    rw [← LeftExt.toBicat_push]
    exact ((LeftExt.isInitial_iff_isKan k (d ≫ f) ((LeftExt.push k d f).obj L)).mp
      (h.2 f)).some
  · rintro ⟨h⟩
    refine ⟨(LeftExt.isInitial_iff_isKan k d L).mpr ⟨h.isKan⟩, ?_⟩
    intro c' f
    exact (LeftExt.isInitial_iff_isKan k (d ≫ f) ((LeftExt.push k d f).obj L)).mpr
      ⟨by simpa only [LeftExt.toBicat_push] using h f⟩

end UlmerBialgebras
