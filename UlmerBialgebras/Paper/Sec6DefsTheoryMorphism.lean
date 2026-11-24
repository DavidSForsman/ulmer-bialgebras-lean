module

public import UlmerBialgebras.Paper.Sec6DefsAlgTheory
public import UlmerBialgebras.UniversalAlgebra.TheoryMorphism

/-!
# The language of groups with further function symbols

The morphisms of equational theories (`UlmerBialgebras.Paper.MSLanguage.TheoryMorphism`, in
`UlmerBialgebras/UniversalAlgebra/TheoryMorphism.lean`) are library definitions. This file keeps in
the trusted base the part that the statements of Corollary 6.11 use and that depends on the
theory of groups of `UlmerBialgebras/Paper/Sec6DefsGrp.lean`:

* `UniversalAlgebra.grpExtLanguage`: the language of groups in each sort, with further function
  symbols;
* `UniversalAlgebra.grpInl`: the inclusion of the language of groups into it.

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.grpExtLanguage`
* `UlmerBialgebras.Paper.UniversalAlgebra.grpInl`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11
-/

@[expose] public section

universe u₁

/-! ## The language of groups with further function symbols -/

namespace UlmerBialgebras.Paper.UniversalAlgebra

open Cart MSLanguage

variable (S : Type u₁) (Fn' : Type u₁) (arity' : Fn' → ℕ) (argSorts' : ∀ f, Fin (arity' f) → S)
  (resSort' : Fn' → S)

/-- **The language of groups in each sort of `S`, with further function symbols `Fn'`**, with
their given arities, argument sorts and result sorts. -/
def grpExtLanguage : MSLanguage.{u₁, u₁} where
  Sorts := S
  Functions := (S × GrpFn) ⊕ Fn'
  arity := Sum.elim (grpLanguage S).arity arity'
  argSorts := fun f => match f with
    | .inl f => (grpLanguage S).argSorts f
    | .inr f => argSorts' f
  resSort := Sum.elim (grpLanguage S).resSort resSort'

/-- The inclusion of the language of groups into `grpExtLanguage`: the identity on sorts, and each
group symbol to itself. -/
def grpInl : LangMorphism (grpLanguage S) (grpExtLanguage S Fn' arity' argSorts' resSort') where
  sortMap s := s
  funMap f := .func (L := grpExtLanguage S Fn' arity' argSorts' resSort') (.inl f)
    (fun i => .var i)

end UlmerBialgebras.Paper.UniversalAlgebra
