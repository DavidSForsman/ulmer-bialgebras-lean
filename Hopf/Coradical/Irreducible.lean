module

public import Mathlib.Algebra.Order.Ring.Star
public import Hopf.Coradical.Simple

/-!
# Wedge powers and irreducible components

For a subcoalgebra `X` (typically a simple subcoalgebra, such as the line spanned by a
group-like element `g`) we introduce the iterated wedge powers and the **irreducible component**

```
C_X = ⨆ₙ X^{∧(n+1)}
```

and show that it is a subcoalgebra containing `X`. These components are the summands of Kostant's
decomposition theorem.

## Main results

* `Coalgebra.Coradical.wedgePow`, `Coalgebra.Coradical.irrComponent` — the definitions;
* `Coalgebra.Coradical.isSubcoalgebra_wedgePow`, `Coalgebra.Coradical.wedgePow_mono`,
  `Coalgebra.Coradical.directed_wedgePow`;
* `Coalgebra.Coradical.isSubcoalgebra_irrComponent`, `Coalgebra.Coradical.le_irrComponent`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapters 8–9
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The iterated wedge power `X^{∧(n+1)}`: `wedgePow X 0 = X` and
`wedgePow X (n+1) = (wedgePow X n) ∧ X`. -/
noncomputable def wedgePow (X : Submodule k C) : ℕ → Submodule k C
  | 0 => X
  | (n + 1) => wedge (wedgePow X n) X

/-- `∧⁰ X = X`. -/
@[simp] theorem wedgePow_zero (X : Submodule k C) : wedgePow X 0 = X := rfl

/-- `∧ⁿ⁺¹ X = (∧ⁿ X) ∧ X`. -/
theorem wedgePow_succ (X : Submodule k C) (n : ℕ) :
    wedgePow X (n + 1) = wedge (wedgePow X n) X := rfl

/-- The wedge powers of a subcoalgebra are subcoalgebras. -/
theorem isSubcoalgebra_wedgePow {X : Submodule k C} (hX : IsSubcoalgebra X) :
    ∀ n, IsSubcoalgebra (wedgePow X n)
  | 0 => hX
  | (n + 1) => isSubcoalgebra_wedge (isSubcoalgebra_wedgePow hX n) hX

/-- For a subcoalgebra `X`, the wedge powers increase: `X^{∧(n+1)} ≤ X^{∧(n+2)}`. -/
theorem wedgePow_le_succ {X : Submodule k C} (hX : IsSubcoalgebra X) (n : ℕ) :
    wedgePow X n ≤ wedgePow X (n + 1) :=
  left_le_wedge (isSubcoalgebra_wedgePow hX n) _

/-- The wedge powers of a subcoalgebra form an increasing sequence. -/
theorem wedgePow_mono {X : Submodule k C} (hX : IsSubcoalgebra X) :
    Monotone (wedgePow X) :=
  monotone_nat_of_le_succ (wedgePow_le_succ hX)

/-- The **irreducible component** of a subcoalgebra `X`: the union of all its wedge powers. -/
noncomputable def irrComponent (X : Submodule k C) : Submodule k C := ⨆ n, wedgePow X n

/-- `X` is contained in its irreducible component. -/
theorem le_irrComponent (X : Submodule k C) : X ≤ irrComponent X :=
  le_iSup (wedgePow X) 0

/-- Each wedge power of `X` is contained in the irreducible component of `X`. -/
theorem wedgePow_le_irrComponent (X : Submodule k C) (n : ℕ) :
    wedgePow X n ≤ irrComponent X := le_iSup (wedgePow X) n

/-- The irreducible component of a subcoalgebra is a subcoalgebra. -/
theorem isSubcoalgebra_irrComponent {X : Submodule k C} (hX : IsSubcoalgebra X) :
    IsSubcoalgebra (irrComponent X) := by
  rw [irrComponent, iSup]
  exact isSubcoalgebra_sSup (by rintro _ ⟨n, rfl⟩; exact isSubcoalgebra_wedgePow hX n)

/-- The wedge powers of a subcoalgebra form a directed family. -/
theorem directed_wedgePow {X : Submodule k C} (hX : IsSubcoalgebra X) :
    Directed (· ≤ ·) (wedgePow X) :=
  Monotone.directed_le (wedgePow_mono hX)

end Coalgebra.Coradical
