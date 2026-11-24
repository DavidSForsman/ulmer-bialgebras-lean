module

public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import UlmerBialgebras.Basic.AccPresFunctor
public import UlmerBialgebras.Basic.AccClosure

/-!
# Presentable objects of an inserter at a sharply larger cardinal

Let `F, G : C ⥤ D` be `λ`-accessible functors on a `λ`-accessible category `C`, and let `F` take
`λ`-presentable objects to `λ`-presentable objects. For `λ ⊲ κ`, the inserter `Ins(F, G)` is
`κ`-accessible (`UlmerBialgebras.Ins.isCardinalAccessibleCategory_general`), and its
`κ`-presentable objects are the retracts of the objects `⟨x, ψ⟩` with `x` and `F x`
`κ`-presentable (the generators of the Makkai–Paré generation step). Hence the forgetful functor
`Ins(F, G) ⥤ C`, and its composite with `F`, preserve `κ`-presentable objects. This is the input
needed to iterate the generation step once more, for an equifier over the inserter, with
explicit cardinals.

## Main results

* `UlmerBialgebras.Ins.isCardinalPresentable_pt_of_sharplyLT`: a `κ`-presentable object `⟨x, ψ⟩`
  of the inserter has `x` and `F x` `κ`-presentable.
* `UlmerBialgebras.Ins.forget_preservesCardinalPresentable_of_sharplyLT`,
  `UlmerBialgebras.Ins.forget_comp_preservesCardinalPresentable_of_sharplyLT`: the forgetful
  functor of the inserter, and its composite with `F`, preserve `κ`-presentable objects.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3,
  Theorems 5.11 and 7.7
* [M. Makkai, R. Paré, *Accessible Categories: The Foundations of Categorical Model
  Theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], 2.72 Theorem
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

namespace Ins

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc] {F G : C ⥤ Dc}
  {lam kappa : Cardinal.{w}} [Fact lam.IsRegular] [Fact kappa.IsRegular]
  [IsCardinalAccessibleCategory.{w} C lam] [F.IsCardinalAccessible lam]
  [G.IsCardinalAccessible lam] [LocallySmall.{w} Dc]

/-- **Presentable objects of an inserter at a sharply larger cardinal.** Let `C` be
`λ`-accessible, `F, G : C ⥤ D` `λ`-accessible, `D` locally `w`-small, let `F` take
`λ`-presentable objects to `λ`-presentable objects, and let `λ ⊲ κ`. Then every `κ`-presentable
object `⟨x, ψ⟩` of `Ins(F, G)` has `x` and `F x` `κ`-presentable. -/
lemma isCardinalPresentable_pt_of_sharplyLT
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) (x : Ins F G) [IsCardinalPresentable x kappa] :
    IsCardinalPresentable x.pt kappa ∧ IsCardinalPresentable (F.obj x.pt) kappa := by
  have : IsCardinalAccessibleCategory.{w} C kappa := hsharp.isCardinalAccessibleCategory C
  have : F.IsCardinalAccessible kappa := Functor.isCardinalAccessible_of_le F hsharp.le
  have : G.IsCardinalAccessible kappa := Functor.isCardinalAccessible_of_le G hsharp.le
  have hg : (gen F G kappa).IsCardinalFilteredGenerator kappa :=
    { le_isCardinalPresentable := by
        rintro y ⟨h₁, h₂⟩
        exact Ins.isCardinalPresentable y
      exists_colimitsOfShape := exists_colimitsOfShape_general hF hsharp }
  have hx : (_root_.CategoryTheory.isCardinalPresentable (Ins F G) kappa) x := by
    assumption
  rw [hg.isPresentable_eq_retractClosure] at hx
  obtain ⟨y, ⟨h₁, h₂⟩, ⟨r⟩⟩ := hx
  have : IsCardinalPresentable ((forget F G).obj y) kappa := h₁
  have : IsCardinalPresentable ((forget F G ⋙ F).obj y) kappa := h₂
  exact ⟨(r.map (forget F G)).isCardinalPresentable kappa,
    (r.map (forget F G ⋙ F)).isCardinalPresentable kappa⟩

/-- Under the hypotheses of `UlmerBialgebras.Ins.isCardinalPresentable_pt_of_sharplyLT`, the
forgetful functor `Ins(F, G) ⥤ C` preserves `κ`-presentable objects. -/
lemma forget_preservesCardinalPresentable_of_sharplyLT
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) : (forget F G).PreservesCardinalPresentable kappa where
  le_inverseImage_isCardinalPresentable x hx := by
    have : IsCardinalPresentable x kappa := hx
    exact (isCardinalPresentable_pt_of_sharplyLT hF hsharp x).1

/-- Under the hypotheses of `UlmerBialgebras.Ins.isCardinalPresentable_pt_of_sharplyLT`, the
composite `Ins(F, G) ⥤ C ⥤ D` of the forgetful functor with `F` preserves `κ`-presentable
objects. -/
lemma forget_comp_preservesCardinalPresentable_of_sharplyLT
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) : (forget F G ⋙ F).PreservesCardinalPresentable kappa where
  le_inverseImage_isCardinalPresentable x hx := by
    have : IsCardinalPresentable x kappa := hx
    exact (isCardinalPresentable_pt_of_sharplyLT hF hsharp x).2

end Ins

end UlmerBialgebras
