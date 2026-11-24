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

/-! ## Definition 7.1: bi-density -/

section BiDense

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- A pseudonatural transformation `K(-, d)|_{A^op} ⟹ K(-, c)|_{A^op}` between restricted
representables, as a 2-functor on the full sub-2-category spanned by `A`: an
`UlmerBialgebras.AHomFamily` (components and pseudonaturality isomorphisms for 1-cells, with the
unit and cocycle conditions) whose pseudonaturality isomorphisms are moreover natural in the
2-cells of `A`. -/
structure PsFamily (A : ObjectProperty Obj) (d c : Obj) extends AHomFamily A d c where
  /-- Compatibility with 2-cells `σ : u ⟹ u'` between 1-cells of `A`. -/
  nat₂ : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) {u u' : x ⟶ y} (σ : u ⟶ u') (k : y ⟶ d),
    (toAHomFamily.fn hx).map (σ ▷ k) ≫ (toAHomFamily.nat hx hy u').hom.app k
      = (toAHomFamily.nat hx hy u).hom.app k ≫ (σ ▷ (toAHomFamily.fn hy).obj k)

/-- **Definition 7.1** ([forsman2026syntactic]; cf. Hofstra–Karvonen
[hofstraInnerAutoequivalencesGeneral2024], Definition 6.2, and Street
[Street1980FibrationsBicategories], (1.9)). A class `A` of objects is **bi-dense** in `K` if for all
objects `c, d` the functor `K(c, d) → [K(-, c)|_{A^op}, K(-, d)|_{A^op}]_Psd`, `f ↦ f_*`, is an
equivalence of categories: it is fully faithful (2-cells correspond bijectively to
modifications, `UlmerBialgebras.IsACellDense`) and essentially surjective (every pseudonatural
transformation is isomorphic, by an invertible modification, to one induced by a 1-cell). -/
structure IsBiDense (A : ObjectProperty Obj) : Prop where
  /-- Full faithfulness. -/
  cell : IsACellDense A
  /-- Essential surjectivity. -/
  hom : ∀ ⦃d c : Obj⦄ (G : PsFamily A d c), Nonempty G.toAHomFamily.Representation

end BiDense

/-! ## Definitions 7.2 and 7.3: `A`-properties and `𝒜`-local presentability

The properties of the hom-categories `K(a, c)` refer to `w₀`-small (co)limits and to
`w₀`-accessibility, for a size universe `w₀` that is independent of the universes of `K`:
the paper's "small" is the Grothendieck universe `U`, while `K(a, c)` is in general a large,
locally small category. (Tying `w₀` to the universe of 2-cells would make every complete
hom-category thin, by Freyd's argument, in the 2-categories `CAT` and `V-CAT`.) -/

section AProperties

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 7.2** ([forsman2026syntactic]) for completeness: `K(a, c)` has all `w₀`-small
limits for every `a ∈ A`. -/
def IsAComplete.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃, v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃a : Obj⦄, A a → HasLimitsOfSize.{w₀, w₀} (a ⟶ c)

/-- **Definition 7.2** ([forsman2026syntactic]) for cocompleteness: `K(a, c)` has all `w₀`-small
colimits for every `a ∈ A`. -/
def IsACocomplete.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃, v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃a : Obj⦄, A a → HasColimitsOfSize.{w₀, w₀} (a ⟶ c)

/-- **Definition 7.2** ([forsman2026syntactic]) for accessibility of an object: `K(a, c)` is
`w₀`-accessible for every `a ∈ A`. -/
def IsAAccessibleObj.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃a : Obj⦄, A a → IsAccessibleCategory.{w₀} (a ⟶ c)

/-- **Definition 7.2** ([forsman2026syntactic]) for accessibility of a 1-cell: each `K(a, f)`,
`a ∈ A`, is an accessible functor between accessible categories (Section 5.3: an accessible functor
has accessible domain and codomain). -/
def IsAAccessibleMor'.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → IsAccessibleCategory.{w₀} (a ⟶ c) ∧ IsAccessibleCategory.{w₀} (a ⟶ d) ∧
    Functor.IsAccessible.{w₀} (postcomp a f)

/-- **Definition 7.2** ([forsman2026syntactic]) for continuity of a 1-cell: each `K(a, f)`, `a ∈ A`,
preserves `w₀`-small limits. -/
def IsAContinuous.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃, v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → PreservesLimitsOfSize.{w₀, w₀} (postcomp a f)

/-- **Definition 7.2** ([forsman2026syntactic]) for cocontinuity of a 1-cell: each `K(a, f)`,
`a ∈ A`, preserves `w₀`-small colimits. -/
def IsACocontinuous.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → PreservesColimitsOfSize.{w₀, w₀} (postcomp a f)

/-- **Definition 7.2** ([forsman2026syntactic]) for having left adjoints: every `K(a, f)`, `a ∈ A`,
is a right adjoint (`f` is an `A`-right adjoint). -/
def IsARightAdjoint (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → (postcomp a f).IsRightAdjoint

/-- **Definition 7.2** ([forsman2026syntactic]) for having right adjoints: every `K(a, f)`,
`a ∈ A`, is a left adjoint (`f` is an `A`-left adjoint). -/
def IsALeftAdjoint (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  ∀ ⦃a : Obj⦄, A a → (postcomp a f).IsLeftAdjoint

/-- `c` has right Kan extensions along every 1-cell of `𝒜`. -/
def HasARightKan (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (d : i ⟶ c),
    ∃ R : RightExt k d, Nonempty (IsTerminal R)

/-- `c` has left Kan extensions along every 1-cell of `𝒜`. -/
def HasALeftKan (A : ObjectProperty Obj) (c : Obj) : Prop :=
  ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (d : i ⟶ c),
    ∃ L : LeftExt k d, Nonempty (IsInitial L)

/-- **Definition 7.3** ([forsman2026syntactic]): `c` is `𝒜`-complete. -/
def IsCalAComplete.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  IsAComplete.{w₀} A c ∧ HasARightKan A c

/-- **Definition 7.3** ([forsman2026syntactic]): `c` is `𝒜`-cocomplete. -/
def IsCalACocomplete.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  IsACocomplete.{w₀} A c ∧ HasALeftKan A c

/-- **Definition 7.3** ([forsman2026syntactic]): `c` is right `𝒜`-locally presentable. -/
def IsRightALocPres.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  IsAAccessibleObj.{w₀} A c ∧ IsCalAComplete.{w₀} A c

/-- **Definition 7.3** ([forsman2026syntactic]): `c` is left `𝒜`-locally presentable. -/
def IsLeftALocPres.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) (c : Obj) : Prop :=
  IsAAccessibleObj.{w₀} A c ∧ IsCalACocomplete.{w₀} A c

/-- **Definition 7.3** ([forsman2026syntactic]): `f` is `𝒜`-continuous (preserves `𝒜`-limits). -/
def IsCalAContinuous.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  IsAContinuous.{w₀} A f ∧ ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ c),
    PreservesRightKan k e f

/-- **Definition 7.3** ([forsman2026syntactic]): `f` is `𝒜`-cocontinuous
(preserves `𝒜`-colimits). -/
def IsCalACocontinuous.{w₀, u₃, v₃, w₃} {Obj : Type u₃} [Bicategory.{w₃,
  v₃} Obj] [Bicategory.Strict Obj]
    (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d) : Prop :=
  IsACocontinuous.{w₀} A f ∧ ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ c),
    PreservesLeftKan k e f

end AProperties

end UlmerBialgebras.Paper
