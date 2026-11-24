module

public import Mathlib.CategoryTheory.Presentable.Uniformization

/-!
# Accessible functors preserve presentable objects at sharply larger cardinals

An accessible functor `F : C ⥤ D` between accessible categories is `λ`-accessible for
arbitrarily large regular cardinals `λ`, but it does *not* in general take `λ`-presentable
objects to `λ`-presentable objects for every such `λ`. It does so, however, along the sharp
inequality `κ ⊲ λ` once it takes `κ`-presentable objects to `λ`-presentable objects.

The resulting uniformization theorem (a single regular `λ` for which `C`, `D` are
`λ`-accessible and `F` is `λ`-accessible and preserves `λ`-presentable objects) is Mathlib's
`CategoryTheory.IsCardinalAccessibleCategory.uniformization` (with `uniformization_pair` for two
functors), which the closure of accessible categories under inserters and equifiers uses
(`AccClosure.lean`). The step lemma below is Mathlib's
`CategoryTheory.IsCardinalAccessibleCategory.uniformization_aux` without its hypothesis that the
target `D` is `κ`-accessible: only `LocallySmall.{w} D` is assumed. It gives the explicit cardinals
of the accessibility clauses of Theorems 5.11 and 7.7 (`AccExplicit.lean`).

## Main results

* `UlmerBialgebras.isCardinalPresentable_map_of_generator`: if `F` takes the objects of a
  `κ`-filtered generator to `λ`-presentable objects, it takes all `κ`-presentable objects to
  `λ`-presentable objects.
* `UlmerBialgebras.isCardinalPresentable_map_of_sharplyLT`: if `κ ⊲ λ` and `F` takes `κ`-presentable
  objects to `λ`-presentable objects, then it takes `λ`-presentable objects to
  `λ`-presentable objects. (Every `λ`-presentable object is a retract of a `λ`-small
  `κ`-directed colimit of `κ`-presentable objects, by Mathlib's
  `Cardinal.SharplyLT.exists_retract_of_isCardinalPresentable`.)

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc]

/-- If `F` takes the objects of a `κ`-filtered generator to `λ`-presentable objects, it
takes all `κ`-presentable objects to `λ`-presentable objects. -/
lemma isCardinalPresentable_map_of_generator (F : C ⥤ Dc)
    {kap lam : Cardinal.{w}} [Fact kap.IsRegular] [Fact lam.IsRegular]
    {P : ObjectProperty C} (hP : P.IsCardinalFilteredGenerator kap)
    (hgen : ∀ a : C, P a → IsCardinalPresentable (F.obj a) lam)
    (a : C) (ha : IsCardinalPresentable a kap) :
    IsCardinalPresentable (F.obj a) lam := by
  have : (_root_.CategoryTheory.isCardinalPresentable C kap) a := ha
  rw [hP.isPresentable_eq_retractClosure] at this
  obtain ⟨Y, hY, ⟨r⟩⟩ := this
  have := hgen Y hY
  exact (r.map F).isCardinalPresentable lam

/-- **Accessible functors preserve presentable objects at sharply larger cardinals.**  If
`C` is `κ`-accessible, `F` is `κ`-accessible and takes `κ`-presentable objects to
`λ`-presentable objects, and `κ ⊲ λ`, then `F` takes `λ`-presentable objects to
`λ`-presentable objects. This is the argument of Mathlib's
`CategoryTheory.IsCardinalAccessibleCategory.uniformization_aux`, without its hypothesis that
`Dc` is `κ`-accessible. -/
theorem isCardinalPresentable_map_of_sharplyLT (F : C ⥤ Dc)
    {kap lam : Cardinal.{w}} [Fact kap.IsRegular] [Fact lam.IsRegular] [LocallySmall.{w} Dc]
    [IsCardinalAccessibleCategory.{w} C kap] [F.IsCardinalAccessible kap]
    (hsharp : kap.SharplyLT lam)
    (hgen : ∀ a : C, IsCardinalPresentable a kap → IsCardinalPresentable (F.obj a) lam)
    (X : C) (hX : IsCardinalPresentable X lam) :
    IsCardinalPresentable (F.obj X) lam := by
  obtain ⟨Y, r, J, _, _, hJ, ⟨p⟩⟩ := hsharp.exists_retract_of_isCardinalPresentable X
  have := F.preservesColimitsOfShape_of_isCardinalAccessible kap J
  have (j : J) : IsCardinalPresentable ((p.diag ⋙ F).obj j) lam := hgen _ (p.prop_diag_obj j)
  have : IsCardinalPresentable (F.obj Y) lam :=
    isCardinalPresentable_of_isColimit _ (isColimitOfPreserves F p.isColimit) _
      ((hasCardinalLT_arrow_iff_of_isThin _ _ (Cardinal.IsRegular.aleph0_le Fact.out)).2 hJ)
  exact (r.map F).isCardinalPresentable lam

end UlmerBialgebras
