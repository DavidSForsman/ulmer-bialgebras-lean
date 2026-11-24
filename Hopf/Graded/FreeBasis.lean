module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Hopf.Coradical.IrrComponentSubalgebra
public import Hopf.Coradical.PointedComponents
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import Mathlib.Tactic.Group
public import Hopf.Coradical.Transfer
public import Foundations.RingTheory.FilteredFreeLift
public import Hopf.Coradical.WedgeComm

/-!
# Sweedler bases and the reduction of Sweedler's freeness theorem to a graded statement

Sweedler's freeness theorem states that a pointed irreducible cocommutative Hopf algebra is free
as a left module over any of its sub-Hopf algebras.  In the form relevant here: for an injection
`f : K →ₐc[k] H` of Hopf algebras with `H` cocommutative, the irreducible component
`H₁ = glComponent 1` of the unit is a free left module over `A = f(K₁)`.

This file isolates the *graded* content of that theorem.  The irreducible component `H₁` carries
the coradical filtration

```
Fₙ = (k · 1)^{∧ n} ,        H₁ = ⋃ₙ Fₙ ,
```

(`Coalgebra.Coradical.oneFiltration`), which is an algebra filtration, and the subalgebra `A`
carries the induced filtration `A ⊓ Fₙ`. A **Sweedler basis** of `H₁` over `A`
(`HopfAlgebra.Commutative.Cocomm.HasGradedFreeBasis`) is a family `b : ι → H` of elements with
assigned degrees `d : ι → ℕ` such that

* `b j ∈ F (d j)`;
* (*graded spanning*) `Fₙ ⊆ Σⱼ (A ⊓ F (n - d j)) · b j` for every `n`;
* (*graded independence*) a combination `Σⱼ aⱼ bⱼ` with `aⱼ ∈ A ⊓ F (n + 1 - d j)` which lands in
  `Fₙ` already has all its coefficients in `A ⊓ F (n - d j)`, and a combination with
  `aⱼ ∈ A ⊓ F (- d j)` which vanishes has all coefficients zero.

Equivalently: the images of the `b j` form a homogeneous basis of the associated graded module
`gr H₁` over the associated graded algebra `gr A`.  This is exactly the object Sweedler constructs
(from divided-power sequences) in his proof.

So the whole remaining content of Sweedler's theorem is the *graded* freeness statement; the
lifting from the graded to the filtered level is carried out here, in
`Foundations/RingTheory/FilteredFreeLift.lean`.

## Main results

* `Coalgebra.Coradical.oneFiltration`: the filtration `Fₙ = (k · 1)^{∧ n}`, whose union is `H₁`
  (`Coalgebra.Coradical.iSup_oneFiltration`).
* `Coalgebra.Coradical.comm_oneFiltration_le`: commutators drop the filtration degree,
  `[Fₘ, Fₙ] ⊆ F_{m+n-1}`.
* `HopfAlgebra.Commutative.Cocomm.HasGradedFreeBasis`: the existence of a Sweedler basis of `H₁`
  over a subalgebra `A`.

## References

* [M. E. Sweedler,
  *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [D. E. Radford,
  *Pointed Hopf algebras are free over Hopf subalgebras*][radfordPointedHopfAlgebras1977]
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Chapter 5
-/

@[expose] public section

open TensorProduct Coalgebra Coalgebra.Coradical

universe u

namespace Coalgebra.Coradical

variable (k H : Type u) [Field k] [Ring H] [HopfAlgebra k H]

/-- The coradical filtration of the irreducible component of the unit: `Fₙ = (k · 1)^{∧ n}`. -/
noncomputable def oneFiltration : ℕ → Submodule k H :=
  wedgePow (Submodule.span k {((1 : GroupLike k H) : H)})

variable {k H}

/-- The filtration `n ↦ (k · 1)^{∧ n}` is increasing. -/
theorem oneFiltration_monotone : Monotone (oneFiltration k H) :=
  wedgePow_mono (isSubcoalgebra_span_groupLike (1 : GroupLike k H).2)

/-- The union of the filtration `(k · 1)^{∧ n}` is the irreducible component `H₁` of the unit (true
by definition). -/
theorem iSup_oneFiltration : ⨆ n, oneFiltration k H n = glComponent (1 : GroupLike k H) := rfl

/-- Each step `(k · 1)^{∧ n}` of the filtration lies in the irreducible component `H₁` of the unit.
-/
theorem oneFiltration_le_glComponent_one (n : ℕ) :
    oneFiltration k H n ≤ glComponent (1 : GroupLike k H) :=
  wedgePow_le_irrComponent _ n

/-- **The associated graded algebra of the coradical filtration of `H₁` is commutative**:
commutators drop the filtration degree, `[Fₘ, Fₙ] ⊆ F_{m+n-1}`. -/
theorem comm_oneFiltration_le (m n : ℕ) :
    Cmm (oneFiltration k H m) (oneFiltration k H n) (oneFiltration k H (m + n - 1)) := by
  have h1 : ((1 : GroupLike k H) : H) = 1 := GroupLike.val_one
  have hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra (Submodule.span k {(1 : H)}) := by
    rw [← h1]
    exact isSubcoalgebra_span_groupLike (1 : GroupLike k H).2
  simpa only [oneFiltration, h1] using comm_wedgePow_span_one_le hX m n

end Coalgebra.Coradical

section
open Module.FilteredFree
section
namespace HopfAlgebra.Commutative.Cocomm

open Module.FilteredFree

variable {k K H : Type u} [Field k] [Ring K] [Ring H] [HopfAlgebra k K] [HopfAlgebra k H]

/-- A **graded free basis** (a *Sweedler basis*, after Sweedler [sweedlerHopfAlgebrasOne1967]) of
the irreducible component `H₁` of the unit of `H` over a subalgebra `A ⊆ H₁`: a family of elements
with assigned filtration degrees whose images form a homogeneous basis of the associated graded
module of `H₁` over the associated graded algebra of `A`. -/
def HasGradedFreeBasis (A : Subalgebra k H) : Prop :=
  ∃ (ι : Type u) (b : ι → H) (d : ι → ℕ),
    (∀ j, b j ∈ oneFiltration k H (d j)) ∧
    (∀ n, oneFiltration k H n ≤ ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j))
        (coefSub A (oneFiltration k H) d n j)) ∧
    (∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A (oneFiltration k H) d 0 j) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0) ∧
    (∀ (n : ℕ) (s : Finset ι) (a : ι → H),
      (∀ j ∈ s, a j ∈ coefSub A (oneFiltration k H) d (n + 1) j) →
      ∑ j ∈ s, a j * b j ∈ oneFiltration k H n →
      ∀ j ∈ s, a j ∈ coefSub A (oneFiltration k H) d n j)

/-! ### A degenerate case -/

end HopfAlgebra.Commutative.Cocomm
end
end
