module

public import UlmerBialgebras.Kan.Kan
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Definitions 4.1 and 4.3 against Mathlib

The paper's subterminal and quotient initial objects (Definition 4.1) are Mathlib's subterminal
objects (`CategoryTheory.IsSubterminal`) in `C` and in `Cᵒᵖ`, and a functor preserves terminal
(initial) objects in the sense of Definition 4.3 exactly when it preserves the limit (colimit) of
the empty diagram in Mathlib's sense. `Subterminal` is an abbreviation for `IsSubterminal`; the
other definitions of the paper stay in their own words, and these lemmas are the bridges to
Mathlib.

## Main results

* `UlmerBialgebras.subterminal_iff_isSubterminal`, `UlmerBialgebras.quotientInitial_iff`;
* `UlmerBialgebras.preservesTerminal_iff`, `UlmerBialgebras.preservesInitial_iff`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.1 and 4.3
-/

@[expose] public section

namespace UlmerBialgebras

open CategoryTheory Limits Opposite

variable {A : Type*} [Category A] {B : Type*} [Category B]

/-- **Definition 4.1 against Mathlib:** subterminality is Mathlib's `IsSubterminal` (by
definition, since `Subterminal` is an abbreviation for it). -/
theorem subterminal_iff_isSubterminal (a : A) : Subterminal a ↔ IsSubterminal a :=
  Iff.rfl

/-- **Definition 4.1 against Mathlib:** a quotient initial object is a subterminal object of the
opposite category. -/
theorem quotientInitial_iff (a : A) : QuotientInitial a ↔ IsSubterminal (op a) :=
  ⟨fun h _ f g => Quiver.Hom.unop_inj ((h _).elim f.unop g.unop),
    fun h _ => ⟨fun f g => Quiver.Hom.op_inj (h f.op g.op)⟩⟩

/-- **Definition 4.3 against Mathlib:** a functor preserves terminal objects if and only if it
preserves the limit of the empty diagram. -/
theorem preservesTerminal_iff (F : A ⥤ B) :
    PreservesTerminal F ↔ PreservesLimit (Functor.empty.{0} A) F := by
  constructor
  · intro h
    refine ⟨fun {c} hc => ?_⟩
    have ht : IsTerminal c.pt := isLimitEmptyConeEquiv A c (asEmptyCone c.pt) (Iso.refl _) hc
    exact (h c.pt ⟨ht⟩).map fun ht' =>
      isLimitEmptyConeEquiv B (asEmptyCone (F.obj c.pt)) (F.mapCone c) (Iso.refl _) ht'
  · intro _ a ⟨ha⟩
    exact ⟨ha.isTerminalObj F a⟩

/-- **Definition 4.3 against Mathlib:** a functor preserves initial objects if and only if it
preserves the colimit of the empty diagram. -/
theorem preservesInitial_iff (F : A ⥤ B) :
    PreservesInitial F ↔ PreservesColimit (Functor.empty.{0} A) F := by
  constructor
  · intro h
    refine ⟨fun {c} hc => ?_⟩
    have ht : IsInitial c.pt := isColimitEmptyCoconeEquiv A c (asEmptyCocone c.pt) (Iso.refl _) hc
    exact (h c.pt ⟨ht⟩).map fun ht' =>
      isColimitEmptyCoconeEquiv B (asEmptyCocone (F.obj c.pt)) (F.mapCocone c) (Iso.refl _) ht'
  · intro _ a ⟨ha⟩
    exact ⟨ha.isInitialObj F a⟩

end UlmerBialgebras
