module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Adjunction
public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Kan.ColimKan
public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Examples.MonEquiv
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Density.AAdjointRep

/-!
# Challenge: auxiliary definitions

Further definitions used by the statements of the challenge.  Like
`UlmerBialgebras/Paper/Sec3Defs.lean`,
this file is part of the trusted base and must be reviewed against the paper.

## Main results

* `UlmerBialgebras.Paper.IsMonadic2`, `UlmerBialgebras.Paper.IsComonadic2`: monadic and comonadic
  1-cells in a 2-category (Definition 5.1).
* `UlmerBialgebras.Paper.HasChainColimitsUpTo`: `κ_≤`-cocompleteness (Definition 5.4).
* `UlmerBialgebras.Paper.OrthogonalLE1`: `e ⊥_! m`, at most one diagonal filler (Definition 6.1).
* `UlmerBialgebras.Paper.HasUniqueLiftedOFS`: the lifted pair is an orthogonal factorization system
  on `M^T` and the unique one preserved by `U : M^T → M₀` (Corollary 6.7).
* `UlmerBialgebras.Paper.PreservesWidePushoutsOfRegEpis`: preservation of `K`-indexed wide pushouts
  of regular epimorphisms (Corollary 4.18, Theorem 4.19).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 5.1, 5.4, 6.1, Corollaries 4.18, 4.21, 6.7, 6.9, Theorem 4.19
-/

@[expose] public section

universe u v w u' v' uu₁ uu₂ uu₃ s s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- Two objects over `c` are **isomorphic over `c`**. -/
def IsoOver {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] {p q c : Obj} (up : p ⟶
  c)
    (uq : q ⟶ c) : Prop :=
  ∃ (φ : p ⟶ q) (ψ : q ⟶ p), φ ≫ ψ = 𝟙 p ∧ ψ ≫ φ = 𝟙 q ∧ φ ≫ uq = up

end UlmerBialgebras.Paper

/-! ## Corollary 6.9: sub-1-signatures and sub-theories

(Definitions from `UlmerBialgebras/Proofs/Sec6/SubSigExact.lean`; [forsman2026syntactic], Corollary
6.9.) -/

namespace UlmerBialgebras

end UlmerBialgebras
