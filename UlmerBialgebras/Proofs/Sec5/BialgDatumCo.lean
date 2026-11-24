module

public import UlmerBialgebras.Proofs.Sec4.Sec4
public import UlmerBialgebras.Kan.CoKan

/-!
# Corollary 4.8, right half, by duality

The right half of Corollary 4.8 is the left half applied to the dual bialgebraic datum in
`K^co`: the inserter of `(g, f)` in `K^co` is the inserter of `(f, g)` in `K`, the equifier is
the same, and right Kan extensions in `K` are left Kan extensions in `K^co` (`UlmerBialgebras.Co`).

## Main results

* `UlmerBialgebras.Paper.BialgDatum.co`: the dual bialgebraic datum `(c, g, f, g', f', α, β)` in
  `K^co`.
* `UlmerBialgebras.Paper.Equifier.co`: an equifier of `B.α, B.β` as an equifier for the dual datum.
* `UlmerBialgebras.Paper.BialgDatum.uB_co`: the forgetful 1-cell of the dual datum is
  `Co.hom (B.uB E)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.8
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3, 3.4
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Paper

/-- The dual of a bialgebraic datum: the datum `(c, g, f, g', f', α, β)` in `K^co`. -/
def BialgDatum.co (B : BialgDatum (Obj := Obj)) : BialgDatum (Obj := Co Obj) where
  c := Co.op B.c
  x := Co.op B.x
  y := Co.op B.y
  f := Co.hom B.g
  g := Co.hom B.f
  f' := Co.hom B.g'
  g' := Co.hom B.f'
  ins := Co.inserter (f := B.g) (g := B.f) B.ins
  α := Co.cell B.α
  β := Co.cell B.β

/-- An object of bialgebras of `B` is an object of bialgebras of the dual datum. -/
def Equifier.co {B : BialgDatum (Obj := Obj)} (E : Equifier B.α B.β) : Equifier B.co.α B.co.β :=
  Co.equifier E

/-- The dual bialgebraic datum has the same forgetful 1-cell. -/
lemma BialgDatum.uB_co (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) :
    B.co.uB (Equifier.co E) = Co.hom (B.uB E) := rfl

end Paper

end UlmerBialgebras
