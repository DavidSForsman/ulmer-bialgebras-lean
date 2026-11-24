module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import UlmerBialgebras.Models.Induced
public import UlmerBialgebras.Models.LaxComp
public import UlmerBialgebras.Models.OplaxComp
public import UlmerBialgebras.Kan.Kan
public import UlmerBialgebras.Basic.HomCat
public import UlmerBialgebras.Models.CatPIE
public import UlmerBialgebras.Basic.InsEqCat
public import UlmerBialgebras.Monadicity.RelAdjoint
public import Foundations.CategoryTheory.Factorization.OFS
public import Foundations.CategoryTheory.Factorization.RegularExact
public import UlmerBialgebras.Models.AlgebraObject
public import UlmerBialgebras.Models.BicatTwoCat
public import UlmerBialgebras.Density.ADense
public import UlmerBialgebras.Kan.KanModel

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Challenge: definitions

Definitions of *A Syntactic Approach to Ulmer's Bialgebras* (version 2 of the paper)
that the library `UlmerBialgebras/` does not provide, or provides in a form that differs from
the current paper.

All other notions are taken from `UlmerBialgebras/`:

* strict 2-categories (Mathlib's `CategoryTheory.Bicategory` with `Bicategory.Strict`), PIE limits
  `UlmerBialgebras.Product`,
  `UlmerBialgebras.Inserter`, `UlmerBialgebras.Equifier`, and PIE-complete_s
  `UlmerBialgebras.PIEComplete.{s}`: chosen products of `Type s`-indexed families
  (`UlmerBialgebras.HasChosenProductsOfSize.{s}`), chosen finite products, inserters and equifiers
  (Definition 2.1 of the paper);
* the syntax `UlmerBialgebras.TwoSig`, `UlmerBialgebras.OneSig`, the term graph
  `UlmerBialgebras.OneSig.Arr`, `UlmerBialgebras.OneSig.Path`, theories `UlmerBialgebras.Theory`
  (Section 3.2);
* models `UlmerBialgebras.Model`, lax morphisms `UlmerBialgebras.LaxMor`, `M^σ`
  (`UlmerBialgebras.Model.sigObj`) and `M^T` (`UlmerBialgebras.Model.thyObj`) (Section 3.3);
* categories of extensions `UlmerBialgebras.LeftExt`, `UlmerBialgebras.RightExt` and the
  preservation and strict creation predicates of Section 4;
* the inserter and equifier categories `UlmerBialgebras.Ins`, `UlmerBialgebras.Equif` in `CAT`;
* orthogonal factorization systems `UlmerBialgebras.OFS` (Section 6).

Regular and exact categories (Definition 6.4) are Mathlib's regular categories
`CategoryTheory.Regular` and the Barr-exact categories `CategoryTheory.BarrExact` of
`Foundations/CategoryTheory/Factorization/ExactCategory.lean` (a regular category in which every
Mathlib
equivalence relation `CategoryTheory.IsEquivalenceRelation` is effective). The checked statements
`def_6_4_regular` and `def_6_4_exact` show that they agree with the paper's definitions through
orthogonal factorization systems, which the proofs use (`UlmerBialgebras.IsRegularCat`,
`UlmerBialgebras.IsExactCat`).

These files are the trusted base of the challenge: every definition used in a statement of
`Challenge/Statements*.lean` must be reviewed against the paper.

## Main results

* `UlmerBialgebras.Paper.BialgDatum`: a bialgebraic datum on an object `c` (Definition 3.1).
* `UlmerBialgebras.Paper.RelLeftAdj2`: `r : c ⟶ c` is an `f`-relative left adjoint of `g : c ⟶ x`
  (Remark 3.2).
* `UlmerBialgebras.Paper.modelDatum`: the bialgebraic datum `B_{M,T}` of Proposition 3.15.
* `UlmerBialgebras.Paper.IsBiDense`: bi-density of a class `A` of objects (Definition 7.1).
* `UlmerBialgebras.Paper.IsAComplete`, `UlmerBialgebras.Paper.IsARightAdjoint`,
  `UlmerBialgebras.Paper.IsCalAComplete`, `UlmerBialgebras.Paper.IsRightALocPres`,
  `UlmerBialgebras.Paper.IsLeftALocPres`: the `A`-properties and `𝒜`-local presentability of
  Definitions 7.2 and 7.3.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 2.1, 3.1, 4.2–4.4, 7.1–7.3, Remark 3.2, Proposition 3.15
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras]
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
-/

universe u v w u₁ v₁ u₂ v₂ uu₁ uu₂ uu₃ sι s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Definition 4.1–4.4 complements -/

section Kan

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- A left Kan extension of `d` along `k` is **absolute** if every 1-cell out of `c`
preserves it (Section 4.2). -/
def IsAbsoluteLeftKan {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) (L : LeftExt k d) : Prop :=
  Nonempty (IsInitial L) ∧ ∀ ⦃c' : Obj⦄ (f : c ⟶ c'),
    Nonempty (IsInitial ((LeftExt.push k d f).obj L))

/-- A right Kan extension is **absolute** if every 1-cell out of `c` preserves it. -/
def IsAbsoluteRightKan {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) (R : RightExt k d) : Prop :=
  Nonempty (IsTerminal R) ∧ ∀ ⦃c' : Obj⦄ (f : c ⟶ c'),
    Nonempty (IsTerminal ((RightExt.push k d f).obj R))

end Kan

end UlmerBialgebras.Paper
