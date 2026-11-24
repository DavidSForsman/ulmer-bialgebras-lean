module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import Mathlib.CategoryTheory.Bicategory.Kan.IsKan
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Right extensions in the Mathlib bicategory

Comparison of the project's right-extension category with Mathlib's bicategorical
right-extension category for the same 1-cells.

## Main results

* `UlmerBialgebras.RightExt.bicatEquiv`: the project's category of right extensions of `d` along `k`
  is equivalent to Mathlib's `Bicategory.RightExtension k d`.
* `UlmerBialgebras.RightExt.isTerminal_iff_isKan`: a right extension is terminal iff its image is a
  Kan extension in Mathlib's sense.
* `UlmerBialgebras.RightExt.isAbsoluteRightKan_iff`: the project's absolute right Kan predicate
  holds iff the extension and each of its post-compositions are Kan in Mathlib's sense.

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

/-- Regard a local right extension as Mathlib's bicategorical right extension. -/
def RightExt.toBicat : RightExt (Obj := Obj) k d ⥤ Bicategory.RightExtension k d where
  obj R := Bicategory.RightExtension.mk R.ext R.counit
  map α := Bicategory.RightExtension.homMk (RightExt.homCell α) (RightExt.w α)

/-- Regard a Mathlib bicategorical right extension as a local right extension. -/
def RightExt.ofBicat : Bicategory.RightExtension k d ⥤ RightExt (Obj := Obj) k d where
  obj R := RightExt.mk R.extension R.counit
  map α := RightExt.homMk α.left (Bicategory.RightExtension.w α)

/-- The comparison `toBicat` is the identity on objects: `RightExt k d` is Mathlib's
`Bicategory.RightExtension k d`, and an extension has the same 1-cell and 2-cell on both sides. -/
theorem RightExt.toBicat_obj (R : RightExt (Obj := Obj) k d) :
    (RightExt.toBicat k d).obj R = R := rfl

/-- The comparison `toBicat` is the identity on morphisms. -/
theorem RightExt.toBicat_map {R R' : RightExt (Obj := Obj) k d} (α : R ⟶ R') :
    (RightExt.toBicat k d).map α = α :=
  RightExt.hom_ext rfl

instance : (RightExt.toBicat k d).Faithful where
  map_injective h := RightExt.hom_ext (congrArg CostructuredArrow.Hom.left h)

instance : (RightExt.toBicat k d).Full where
  map_surjective α := ⟨RightExt.homMk α.left (Bicategory.RightExtension.w α), rfl⟩

instance : (RightExt.toBicat k d).EssSurj where
  mem_essImage R := ⟨(RightExt.ofBicat k d).obj R, ⟨eqToIso rfl⟩⟩

instance : (RightExt.toBicat k d).IsEquivalence where

/-- The local and Mathlib categories of right extensions are equivalent. -/
noncomputable def RightExt.bicatEquiv : RightExt (Obj := Obj) k d ≌ Bicategory.RightExtension k d :=
  (RightExt.toBicat k d).asEquivalence

/-- Terminality of a local right extension is equivalent to Mathlib's Kan property. -/
theorem RightExt.isTerminal_iff_isKan (R : RightExt (Obj := Obj) k d) :
    Nonempty (Limits.IsTerminal R) ↔
      Nonempty (Bicategory.RightExtension.IsKan ((RightExt.toBicat k d).obj R)) :=
  (Limits.IsTerminal.isTerminalIffObj (RightExt.toBicat k d) R).nonempty_congr

/-- The local absolute right Kan predicate in terms of Mathlib's Kan predicate for
itself and for each local post-composition. -/
theorem RightExt.isAbsoluteRightKan_iff (R : RightExt (Obj := Obj) k d) :
    Paper.IsAbsoluteRightKan k d R ↔
      Nonempty (Bicategory.RightExtension.IsKan ((RightExt.toBicat k d).obj R)) ∧
      ∀ ⦃c' : Obj⦄ (f : c.down ⟶ c'),
        Nonempty (Bicategory.RightExtension.IsKan
          ((RightExt.toBicat k (d ≫ f)).obj ((RightExt.push k d f).obj R))) := by
  constructor
  · intro h
    refine ⟨(RightExt.isTerminal_iff_isKan k d R).mp h.1, ?_⟩
    intro c' f
    exact (RightExt.isTerminal_iff_isKan k (d ≫ f) ((RightExt.push k d f).obj R)).mp (h.2 f)
  · intro h
    refine ⟨(RightExt.isTerminal_iff_isKan k d R).mpr h.1, ?_⟩
    intro c' f
    exact (RightExt.isTerminal_iff_isKan k (d ≫ f) ((RightExt.push k d f).obj R)).mpr (h.2 f)

end UlmerBialgebras
