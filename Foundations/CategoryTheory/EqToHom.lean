module

public import Mathlib.CategoryTheory.EqToHom

/-!
# Conjugating by `eqToHom`

Solving an equation `eqToHom p ≫ u ≫ eqToHom q = v` for `u`. It complements Mathlib's
`CategoryTheory.eqToHom_comp_iff` and `CategoryTheory.conj_eqToHom_iff_heq`.

## Main results

* `CategoryTheory.eqToHom_conj`: `u = eqToHom p.symm ≫ v ≫ eqToHom q.symm` from
  `eqToHom p ≫ u ≫ eqToHom q = v`.

## References

* S. Mac Lane, *Categories for the Working Mathematician* (1998)
-/

@[expose] public section

namespace CategoryTheory

/-- Solving a conjugation equation between morphisms transported along equalities. -/
lemma eqToHom_conj {C : Type*} [Category C] {X Y X' Y' : C} {p : X' = X} {q : Y = Y'}
    {u : X ⟶ Y} {v : X' ⟶ Y'} (h : eqToHom p ≫ u ≫ eqToHom q = v) :
    u = eqToHom p.symm ≫ v ≫ eqToHom q.symm := by
  subst p; subst q; simpa using h

end CategoryTheory
