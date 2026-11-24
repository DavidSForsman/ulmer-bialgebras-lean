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

/-- `e ⊥_! m` (Definition 6.1 of [forsman2026syntactic]): every commutative square from `e` to `m`
has at most one diagonal filler. -/
def OrthogonalLE1 {C : Type u} [Category.{v} C] {a b c d : C} (e : a ⟶ b) (m : c ⟶ d) : Prop :=
  ∀ (f : a ⟶ c) (g : b ⟶ d), f ≫ m = e ≫ g → ∀ h h' : b ⟶ c,
    e ≫ h = f → h ≫ m = g → e ≫ h' = f → h' ≫ m = g → h = h'

/-- `C` has coequalizers of kernel pairs. -/
def HasCoequalizersOfKernelPairs (C : Type u) [Category.{v} C] : Prop :=
  ∀ ⦃R x y : C⦄ (f : x ⟶ y) (r s : R ⟶ x), IsKernelPair f r s → HasCoequalizer r s

/-! ## Corollary 6.7: componentwise preservation of the classes of factorization systems -/

section ComponentwiseOFS

variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, max u v})
  (S : ∀ c : Sg.Cat, OFS (M.obj c : Type (max u v)))

/-- `M(B)` preserves the left classes componentwise: for each argument `i` and each choice
`x` of the other arguments, `M(B)(x₁, …, -, …, xₙ)` maps `E_{cᵢ}` into `E_d`. -/
def PreservesLeftClassComponentwise (B : Sg.Fun) : Prop :=
  ∀ (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type (max u v)))
    ⦃a b : (M.obj (Sg.art B i) : Type (max u v))⦄ (e : a ⟶ b), (S (Sg.art B i)).E e →
      (S (Sg.fcod B)).E ((updateFunctor x i ⋙
        (M.fn B).toFunctor).map e)

/-- `M(B)` preserves the right classes componentwise. -/
def PreservesRightClassComponentwise (B : Sg.Fun) : Prop :=
  ∀ (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type (max u v)))
    ⦃a b : (M.obj (Sg.art B i) : Type (max u v))⦄ (m : a ⟶ b), (S (Sg.art B i)).M m →
      (S (Sg.fcod B)).M ((updateFunctor x i ⋙
        (M.fn B).toFunctor).map m)

end ComponentwiseOFS

section LiftedOFS

variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, u})
  (S : ∀ c : Sg.Cat, OFS (M.obj c : Type u))

/-- The pair `(U⁻¹(∏ₛ E_{c_s}), U⁻¹(∏ₛ M_{c_s}))` is an orthogonal factorization system on
`M^T`, and it is the unique one preserved by `U : M^T → M₀` (Corollary 6.7 of
[forsman2026syntactic]). -/
def HasUniqueLiftedOFS (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] : Prop :=
  ∃ P : OFS (M.thyObj sg T : Type u),
    (∀ ⦃x y : (M.thyObj sg T : Type u)⦄ (f : x ⟶ y), P.E f ↔ ∀ s : sg.Srt,
      (S (sg.sty s)).E ((M.thyForget sg T ≫ (M.P0 sg).π s).toFunctor.map f)) ∧
    (∀ ⦃x y : (M.thyObj sg T : Type u)⦄ (f : x ⟶ y), P.M f ↔ ∀ s : sg.Srt,
      (S (sg.sty s)).M ((M.thyForget sg T ≫ (M.P0 sg).π s).toFunctor.map f)) ∧
    ∀ P' : OFS (M.thyObj sg T : Type u),
      (∀ ⦃x y : (M.thyObj sg T : Type u)⦄ (f : x ⟶ y), P'.E f → ∀ s : sg.Srt,
        (S (sg.sty s)).E ((M.thyForget sg T ≫ (M.P0 sg).π s).toFunctor.map f)) →
      (∀ ⦃x y : (M.thyObj sg T : Type u)⦄ (f : x ⟶ y), P'.M f → ∀ s : sg.Srt,
        (S (sg.sty s)).M ((M.thyForget sg T ≫ (M.P0 sg).π s).toFunctor.map f)) → P' = P

end LiftedOFS

end UlmerBialgebras.Paper

/-! ## Corollary 6.9: sub-1-signatures and sub-theories

(Definitions from `UlmerBialgebras/Proofs/Sec6/SubSigExact.lean`; [forsman2026syntactic], Corollary
6.9.) -/

namespace UlmerBialgebras

variable {Sg : TwoSig.{uu₁, uu₂, uu₃}}

namespace OneSig

/-! ## Sub-1-signatures on the same sorts -/

/-- The sub-1-signature obtained from `sg` by restricting the function symbols along
`jFn : Fn₁ → sg.Fn`. -/
@[implicit_reducible]
def restrictFn (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg) {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn) :
    OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg where
  Srt := sg.Srt
  sty := sg.sty
  Fn := Fn₁
  fnty f := sg.fnty (jFn f)
  fndom f := sg.fndom (jFn f)
  fncod f := sg.fncod (jFn f)

/-- Every arrow of `sg.restrictFn jFn` translates to an arrow of `sg`. -/
def Arr.ofRestrictFn {sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg} {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn) :
    ∀ {c : Sg.Cat} {t t' : sg.CTrm c},
      (sg.restrictFn jFn).Arr t t' → sg.Arr t t'
  | _, _, _, .fn f => Arr.fn (sg := sg) (jFn f)
  | _, _, _, .tr a sub => Arr.tr (sg := sg) a sub
  | _, _, _, .app B i args args' hne g =>
      Arr.app (sg := sg) B i args args' hne (ofRestrictFn jFn g)

/-- Every path of `sg.restrictFn jFn` translates to a path of `sg`. -/
def Path.ofRestrictFn {sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg} {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn)
    {c : Sg.Cat} :
    ∀ {t t' : sg.CTrm c},
      (sg.restrictFn jFn).Path t t' → sg.Path t t'
  | _, _, .nil t => Path.nil (sg := sg) t
  | _, _, .cons g p => Path.cons (sg := sg) (Arr.ofRestrictFn jFn g) (ofRestrictFn jFn p)

end OneSig

/-- The theory over a sub-1-signature `sg.restrictFn jFn` obtained by restricting a `sg`-theory `T`
along `jEq : E → T.Eqn` together with lifts `lhs₁`, `rhs₁` of the equation paths to
`sg.restrictFn jFn`. -/
def Theory.restrictSig {sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg}
    (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg) {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn)
    {E : Type s₃} (jEq : E → T.Eqn)
    (lhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r)))
    (rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r))) :
    Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} (sg.restrictFn jFn) where
  Eqn := E
  eqty r := T.eqty (jEq r)
  dom r := T.dom (jEq r)
  cod r := T.cod (jEq r)
  lhs := lhs₁
  rhs := rhs₁

/-- A sub-theory over a sub-1-signature of an algebraic theory is algebraic. -/
theorem Theory.IsAlgebraic.restrictSig {sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg}
    {T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg} (h : T.IsAlgebraic)
    {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn) {E : Type s₃} (jEq : E → T.Eqn)
    (lhs₁ rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r))) :
    (T.restrictSig jFn jEq lhs₁ rhs₁).IsAlgebraic :=
  ⟨fun f => h.1 (jFn f), fun r => h.2 (jEq r)⟩

end UlmerBialgebras
