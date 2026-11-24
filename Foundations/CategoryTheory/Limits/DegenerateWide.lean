module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Absolute wide limits and colimits with at most one leg

An empty or singleton wide pushout shape has a terminal object; the dual wide pullback
shape has an initial object. Every functor preserves diagrams of these shapes.

## Main results

* `CategoryTheory.Limits.widePushoutShape_exists_isTerminal`: the terminal vertex for at most
  one leg.
* `CategoryTheory.Limits.widePullbackShape_exists_isInitial`: the dual initial vertex.
* `CategoryTheory.Limits.preservesColimitsOfShape_of_isTerminal`: terminal-indexed colimits
  are absolute.
* `CategoryTheory.Limits.preservesLimitsOfShape_of_isInitial`: initial-indexed limits are absolute.

## References

* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998], Chapter V
-/

@[expose] public section

namespace CategoryTheory.Limits

/-- A wide pushout with at most one leg has a terminal vertex. -/
theorem widePushoutShape_exists_isTerminal (K : Type*) [Subsingleton K] :
    ∃ j : WidePushoutShape K, Nonempty (IsTerminal j) := by
  classical
  by_cases h : Nonempty K
  · let k : K := h.some
    refine ⟨some k, ⟨IsTerminal.ofUniqueHom (fun j => ?_)
      (fun _ _ => Subsingleton.elim _ _)⟩⟩
    cases j with
    | none => exact WidePushoutShape.Hom.init k
    | some k' => exact eqToHom (congrArg some (Subsingleton.elim k' k))
  · have : IsEmpty K := ⟨fun k => h ⟨k⟩⟩
    refine ⟨none, ⟨IsTerminal.ofUniqueHom (fun j => ?_)
      (fun _ _ => Subsingleton.elim _ _)⟩⟩
    cases j with
    | none => exact 𝟙 _
    | some k => exact isEmptyElim k

/-- A wide pullback with at most one leg has an initial vertex. -/
theorem widePullbackShape_exists_isInitial (K : Type*) [Subsingleton K] :
    ∃ j : WidePullbackShape K, Nonempty (IsInitial j) := by
  classical
  by_cases h : Nonempty K
  · let k : K := h.some
    refine ⟨some k, ⟨IsInitial.ofUniqueHom (fun j => ?_)
      (fun _ _ => Subsingleton.elim _ _)⟩⟩
    cases j with
    | none => exact WidePullbackShape.Hom.term k
    | some k' => exact eqToHom (congrArg some (Subsingleton.elim k k'))
  · have : IsEmpty K := ⟨fun k => h ⟨k⟩⟩
    refine ⟨none, ⟨IsInitial.ofUniqueHom (fun j => ?_)
      (fun _ _ => Subsingleton.elim _ _)⟩⟩
    cases j with
    | none => exact 𝟙 _
    | some k => exact isEmptyElim k

/-- Every functor preserves colimits indexed by a category with a specified terminal object. -/
theorem preservesColimitsOfShape_of_isTerminal {J C D : Type*}
    [Category J] [Category C] [Category D] {j : J} (hj : IsTerminal j) (F : C ⥤ D) :
    PreservesColimitsOfShape J F where
  preservesColimit {K} := preservesColimit_of_preserves_colimit_cocone
    (colimitOfDiagramTerminal hj K) (colimitOfDiagramTerminal hj (K ⋙ F))

/-- Every functor preserves limits indexed by a category with a specified initial object. -/
theorem preservesLimitsOfShape_of_isInitial {J C D : Type*}
    [Category J] [Category C] [Category D] {j : J} (hj : IsInitial j) (F : C ⥤ D) :
    PreservesLimitsOfShape J F where
  preservesLimit {K} := preservesLimit_of_preserves_limit_cone
    (limitOfDiagramInitial hj K) (limitOfDiagramInitial hj (K ⋙ F))

end CategoryTheory.Limits
