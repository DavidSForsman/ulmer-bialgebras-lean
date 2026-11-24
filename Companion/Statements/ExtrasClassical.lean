module

public import Companion.Statements.DefsClassical
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Classical theories against Mathlib's internal monoids and groups (addition beyond the paper)

Not a result of the paper; a check of the definitions of `MSLanguage`, `Theory.ModelCat` and
`Theory.cartThy` against Mathlib's independent definitions. For a cartesian monoidal category
`C : Type u` with `Category.{v} C` (`u`, `v` independent), the categories of models of the
single-sorted theories of monoids, commutative monoids and groups are **isomorphic** to Mathlib's
`Mon C`, `CommMon C` and `Grp C`, over `C`. For `CommMon C`, the braiding of `C` is Mathlib's
`BraidedCategory.ofCartesianMonoidalCategory`, a local instance (Mathlib makes it a `def`; any two
braidings agree, `Subsingleton (BraidedCategory C)`).

Isomorphisms of categories are stated as a pair of functors that are inverse up to equality of
functors, and that commute with the forgetful functors up to equality. The forgetful functor of
`T.ModelCat C` lands in `Unit → C`; `Pi.eval _ ()` identifies it with `C`.

* `monTheory_modelCat_iso`, `cmonTheory_modelCat_iso`, `grpTheory_modelCat_iso`: models in `C`.
* `cmon_mon_forget`: Mathlib's `CommMon.forget₂Mon` is the functor induced by the morphism of
  theories `monCMonMorphism : T_Mon → T_CMon` (the inclusion `monTheory ⊆ cmonTheory`).
* `grp_mon_forget`: Mathlib's `Grp.forget₂Mon` is the functor induced by the morphism of theories
  `monGrpMorphism : T_Mon → T_Grp` (the language of groups without the inverse).
* `monTheory_cartThy_iso`, `cmonTheory_cartThy_iso`, `grpTheory_cartThy_iso`: the same for the
  `Σ_Cart`-models `C^{T'}` (with `AsSmall C` as in `modelCat_iso_cartThy_univ`); corollaries of
  `modelCat_iso_cartThy_univ`.

## Main results

* `UlmerBialgebras.Paper.monTheory_modelCat_iso`
* `UlmerBialgebras.Paper.cmonTheory_modelCat_iso`
* `UlmerBialgebras.Paper.grpTheory_modelCat_iso`
* `UlmerBialgebras.Paper.cmon_mon_forget`
* `UlmerBialgebras.Paper.grp_mon_forget`
* `UlmerBialgebras.Paper.monTheory_cartThy_iso`
* `UlmerBialgebras.Paper.cmonTheory_cartThy_iso`
* `UlmerBialgebras.Paper.grpTheory_cartThy_iso`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapter 1
-/

@[expose] public section

universe v u w

namespace UlmerBialgebras.Paper

open CategoryTheory Limits MonoidalCategory MSLanguage

variable (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C]

/-- **Models of the theory of monoids are Mathlib's internal monoids** (addition beyond
[forsman2026syntactic]): `Mod_C(T_Mon) ≅ Mon C` over `C`. -/
theorem monTheory_modelCat_iso :
    ∃ (F : monTheory.ModelCat C ⥤ Mon C) (G : Mon C ⥤ monTheory.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Mon.forget C = Theory.ModelCat.forget C monTheory ⋙ Pi.eval (fun _ => C) () :=
  sorry

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory in
/-- **Models of the theory of commutative monoids are Mathlib's internal commutative monoids**
(addition beyond [forsman2026syntactic]): `Mod_C(T_CMon) ≅ CommMon C` over `C`. -/
theorem cmonTheory_modelCat_iso :
    ∃ (F : cmonTheory.ModelCat C ⥤ CommMon C) (G : CommMon C ⥤ cmonTheory.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ CommMon.forget₂Mon C ⋙ Mon.forget C =
          Theory.ModelCat.forget C cmonTheory ⋙ Pi.eval (fun _ => C) () :=
  sorry

/-- **Models of the theory of groups are Mathlib's internal groups** (addition beyond
[forsman2026syntactic]): `Mod_C(T_Grp) ≅ Grp C` over `C`, for the single-sorted theory of groups
`grpEqTheory Unit`. -/
theorem grpTheory_modelCat_iso :
    ∃ (F : (grpEqTheory Unit).ModelCat C ⥤ Grp C) (G : Grp C ⥤ (grpEqTheory Unit).ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Grp.forget C = Theory.ModelCat.forget C (grpEqTheory Unit) ⋙ Pi.eval (fun _ => C) () :=
  sorry

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory in
/-- **Mathlib's forgetful functor `CommMon C ⥤ Mon C` is induced by the morphism of theories**
`T_Mon → T_CMon` (addition beyond [forsman2026syntactic]): the isomorphisms of
`monTheory_modelCat_iso` and `cmonTheory_modelCat_iso` can be chosen compatibly with
`CommMon.forget₂Mon` and the functor `monCMonMorphism.modelFunctor C` induced by the inclusion
`monTheory ⊆ cmonTheory`. -/
theorem cmon_mon_forget :
    ∃ (F : monTheory.ModelCat C ⥤ Mon C) (G : Mon C ⥤ monTheory.ModelCat C)
      (F' : cmonTheory.ModelCat C ⥤ CommMon C) (G' : CommMon C ⥤ cmonTheory.ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧ F' ⋙ G' = 𝟭 _ ∧ G' ⋙ F' = 𝟭 _ ∧
        F ⋙ Mon.forget C = Theory.ModelCat.forget C monTheory ⋙ Pi.eval (fun _ => C) () ∧
        F' ⋙ CommMon.forget₂Mon C = monCMonMorphism.modelFunctor C ⋙ F :=
  sorry

/-- **Mathlib's forgetful functor `Grp C ⥤ Mon C` is induced by the morphism of theories**
`T_Mon → T_Grp` (addition beyond [forsman2026syntactic]): the isomorphisms of
`monTheory_modelCat_iso` and `grpTheory_modelCat_iso` can be chosen compatibly with
`Grp.forget₂Mon` and the functor `monGrpMorphism.modelFunctor C` induced by the sublanguage
inclusion that forgets the inverse. -/
theorem grp_mon_forget :
    ∃ (F : monTheory.ModelCat C ⥤ Mon C) (G : Mon C ⥤ monTheory.ModelCat C)
      (F' : (grpEqTheory Unit).ModelCat C ⥤ Grp C) (G' : Grp C ⥤ (grpEqTheory Unit).ModelCat C),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧ F' ⋙ G' = 𝟭 _ ∧ G' ⋙ F' = 𝟭 _ ∧
        F ⋙ Mon.forget C = Theory.ModelCat.forget C monTheory ⋙ Pi.eval (fun _ => C) () ∧
        F' ⋙ Grp.forget₂Mon C = monGrpMorphism.modelFunctor C ⋙ F :=
  sorry

section CartThy

variable (C : Type (max v w)) [Category.{v} C] [CartesianMonoidalCategory C]

/-- **The `Σ_Cart`-models of the theory of monoids are Mathlib's internal monoids** (addition
beyond [forsman2026syntactic]): `C^{T_Mon'} ≅ Mon C` over `C`, for `C` with objects in
`Type (max v w)` and morphisms in `Type v`. -/
theorem monTheory_cartThy_iso :
    ∃ (F : Theory.cartThy.{v, w, 0} C monTheory ⥤ Mon C)
      (G : Mon C ⥤ Theory.cartThy.{v, w, 0} C monTheory),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Mon.forget C =
          Theory.cartThyForget.{v, w, 0} C monTheory ⋙ Pi.eval (fun _ => C) () :=
  sorry

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory in
/-- **The `Σ_Cart`-models of the theory of commutative monoids are Mathlib's internal
commutative monoids** (addition beyond [forsman2026syntactic]): `C^{T_CMon'} ≅ CommMon C`
over `C`. -/
theorem cmonTheory_cartThy_iso :
    ∃ (F : Theory.cartThy.{v, w, 0} C cmonTheory ⥤ CommMon C)
      (G : CommMon C ⥤ Theory.cartThy.{v, w, 0} C cmonTheory),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ CommMon.forget₂Mon C ⋙ Mon.forget C =
          Theory.cartThyForget.{v, w, 0} C cmonTheory ⋙ Pi.eval (fun _ => C) () :=
  sorry

/-- **The `Σ_Cart`-models of the theory of groups are Mathlib's internal groups** (addition
beyond [forsman2026syntactic]): `C^{T_Grp'} ≅ Grp C` over `C`. -/
theorem grpTheory_cartThy_iso :
    ∃ (F : Theory.cartThy.{v, w, 0} C (grpEqTheory Unit) ⥤ Grp C)
      (G : Grp C ⥤ Theory.cartThy.{v, w, 0} C (grpEqTheory Unit)),
      F ⋙ G = 𝟭 _ ∧ G ⋙ F = 𝟭 _ ∧
        F ⋙ Grp.forget C =
          Theory.cartThyForget.{v, w, 0} C (grpEqTheory Unit) ⋙ Pi.eval (fun _ => C) () :=
  sorry

end CartThy

end UlmerBialgebras.Paper
