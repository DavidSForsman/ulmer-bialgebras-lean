module

public import Mathlib.Data.Fin.VecNotation

/-!
# Two-element vectors

Small facts about vectors `![a, b] : Fin 2 → α`: mapping a function over one, and comparing two
that differ in one entry.

## Main results

* `Matrix.map_vecTwo`: `(fun i => f (![a, b] i)) = ![f a, f b]`.
* `Matrix.vecTwo_eq_of_ne_zero`, `Matrix.vecTwo_eq_of_ne_one`: vectors that differ only in the
  entry `0` (resp. `1`) agree at every other index.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 3.2
  (terms of a binary functor symbol)
-/

@[expose] public section

universe u v

namespace Matrix

variable {α : Type u} {β : Type v}

/-- Mapping a function over a two-element vector. -/
lemma map_vecTwo (f : α → β) (a b : α) : (fun i => f (![a, b] i)) = ![f a, f b] :=
  funext fun
    | 0 => rfl
    | 1 => rfl

/-- Two-element vectors with the same entry `1` agree away from `0`. -/
lemma vecTwo_eq_of_ne_zero (a a' b : α) : ∀ j : Fin 2, j ≠ 0 → ![a, b] j = ![a', b] j
  | 0, h => absurd rfl h
  | 1, _ => rfl

/-- Two-element vectors with the same entry `0` agree away from `1`. -/
lemma vecTwo_eq_of_ne_one (a b b' : α) : ∀ j : Fin 2, j ≠ 1 → ![a, b] j = ![a, b'] j
  | 0, _ => rfl
  | 1, h => absurd rfl h

end Matrix
