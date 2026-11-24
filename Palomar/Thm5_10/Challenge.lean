module

-- The Mathlib modules whose declarations this file uses, without those that another import
-- already brings.
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

/-!
# A Syntactic Approach to Ulmer's Bialgebras: Theorem 5.10

This file states results of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*,
the numbers follow version 2 of the paper (version 1 is arXiv:2607.19587).

## What this file checks

* Theorem 5.10 (Accessible Adjoint Functor Theorem): `UlmerBialgebras.Paper.thm_5_10_1`,
  `UlmerBialgebras.Paper.thm_5_10_2`.

## How to read it

* The definitions come first, in the order in which Lean needs them, grouped by topic:
  each section heading says what the section defines. The statements come last, under
  the heading *The statements*.
* Each statement is proved by `sorry`. This is the format of a challenge: the
  matching solution file proves the same statements, and Lean's Comparator checks
  that it proves exactly these, with the axioms `propext`, `Quot.sound` and
  `Classical.choice` only.
* The docstring of each statement quotes the paper's statement, says how its notions are
  read in Lean (*Reading*), and lists the differences from the paper (*Deviations*).
* Every notion used here and not defined here is Mathlib's.

## Notation and Lean conventions

* Universes: `[Category.{v} C]` on `C : Type u` has objects in `u` and morphisms in `v`.
-/

set_option autoImplicit false

@[expose] public section

/-! ## The statements: Section 5: free algebras, monadicity, local presentability -/

section
universe u w u' v'

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section AAFT

/-- **Theorem 5.10 (1)** ([forsman2026syntactic], §5).

```latex
Let $F\colon \C\to \D$ be a functor with $\C$ locally presentable. Then the following hold:
```

```latex
\item If $F$ preserves colimits and $\D$ is locally small, then $F$ is a left adjoint.
```

**Reading.**
* "$\C$ locally presentable" ↦ `IsLocallyPresentable C`.
* "$F$ preserves colimits and $\D$ is locally small" ↦ `PreservesColimitsOfSize.{w, w} F` with
  `D : Type u'` and `[Category.{v'} D]` (locally small).
* "$F$ is a left adjoint" ↦ `F.IsLeftAdjoint`.

**Deviations.** none recorded.
-/
theorem thm_5_10_1 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{v'} D]
    [IsLocallyPresentable.{w} C] [LocallySmall.{w} D] (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F] : F.IsLeftAdjoint := sorry

/-- **Theorem 5.10 (2)** ([forsman2026syntactic], §5).

```latex
Let $F\colon \C\to \D$ be a functor with $\C$ locally presentable. Then the following hold:
```

```latex
\item If $F$ is continuous and accessible, then $F$ is a right adjoint.
```

**Reading.**
* "$\C$ locally presentable" ↦ `IsLocallyPresentable C`.
* "$F$ is continuous and accessible" ↦ `PreservesLimitsOfSize.{w, w} F` and
  `Functor.IsAccessible.{w} F`.
* "accessible" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w} F` plus `IsAccessibleCategory.{w} D` (`C` is locally presentable);
  Mathlib's predicate does not include the latter.
* "$F$ is a right adjoint" ↦ `F.IsRightAdjoint`.

**Deviations.** none recorded.
-/
theorem thm_5_10_2 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]
    [IsLocallyPresentable.{w} C] [IsAccessibleCategory.{w} D] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w} F] [Functor.IsAccessible.{w} F] : F.IsRightAdjoint := sorry
end AAFT
end UlmerBialgebras.Paper
end
