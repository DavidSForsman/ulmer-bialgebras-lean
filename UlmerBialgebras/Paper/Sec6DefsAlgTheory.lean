module

public import UlmerBialgebras.UniversalAlgebra.Basic
public import UlmerBialgebras.Paper.Sec6DefsGrp

/-!
# The translation of many-sorted equational theories to `Σ_Cart`, and the theory of groups

The many-sorted algebraic languages `MSLanguage`, their equational theories and their models in a
category with finite products are library definitions
(`UlmerBialgebras/UniversalAlgebra/Basic.lean`, following Adámek–Rosický–Vitale [ARV, Ch. 1
and 14]). This file keeps in the trusted base the part
that relates them to the paper:

**Translation `T ↦ T'`** relative to `Σ_Cart`: `prodTrm`, `MSLanguage.toCartSig`,
`MSLanguage.Term.toPath`, `MSLanguage.Theory.toCartTheory`, and the category `C^{T'}`
(`MSLanguage.Theory.cartThy`) with its forgetful functor.

**Size.** `C^{T'}` for a language `MSLanguage.{s, s}` needs the products of size `s` of `CAT`.
They exist in `Cat.{max s v, max s v w}` (`catOfSizeHom`), so `MSLanguage.Theory.cartThy` takes
`C : Type (max s v w)` with `Category.{max s v} C`. For an arbitrary `C : Type u` with
`Category.{v} C` one can use Mathlib's `AsSmall.{s} C`, with the cartesian structure
`asSmallCartesian` from the finite products of `C`.

**The theory of groups** in each sort, over the group symbols `GrpFn` and equations `GrpEqn` of
`UlmerBialgebras/Paper/Sec6DefsGrp.lean`: `grpLanguage`, `grpEquation`, `grpEqTheory`.

## Main results

* `UlmerBialgebras.Paper.MSLanguage.Theory.toCartTheory`: the translated `Σ_Cart`-theory `T'`.
* `UlmerBialgebras.Paper.MSLanguage.Theory.cartThy`: the category `C^{T'}`.
* `UlmerBialgebras.Paper.grpLanguage`, `UlmerBialgebras.Paper.grpEqTheory`: the theory of groups in
  each sort.

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19, Definitions 3.5–3.14, Corollaries 5.9 and 6.11
-/

@[expose] public section

universe v u w u₄ u₅ uF uR s t

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cart

namespace MSLanguage

/-! ## The translation to `Σ_Cart` -/

section Translation

/-! A 1-signature has its sorts, function symbols and equations in one universe `s`, so the
translation is for languages `MSLanguage.{s, s}`. -/

variable (L : MSLanguage.{s, s}) {S : Type s}

/-- The **product term** `a₀ □ (a₁ □ (⋯ □ aₙ₋₁))` of `Σ_Cart`, with `I` for `n = 0` and `a₀` for
`n = 1`. -/
def prodTrm : ∀ {n : ℕ}, (Fin n → S) → Trm cartFunSig (fun _ : S => ()) ()
  | 0, _ => cartUnit
  | 1, a => .var (a 0)
  | _ + 2, a => cartTens (.var (a 0)) (prodTrm (Fin.tail a))

/-- **The 1-signature `σ'` relative to `Σ_Cart`** of a language: one sort of type `c` per sort,
and one function symbol `prodTrm (argSorts f) → resSort f` per function symbol. -/
def toCartSig : OneSig.{0, 0, 0, s, s} sigCart where
  Srt := L.Sorts
  sty := fun _ => ()
  Fn := L.Functions
  fnty := fun _ => ()
  fndom f := prodTrm (L.argSorts f)
  fncod f := .var (L.resSort f)

variable {L}

/-- The projection `prodTrm a → aᵢ` of the term graph, built from `p₁` and `p₂`. -/
def projPath : ∀ {n : ℕ} (a : Fin n → L.Sorts) (i : Fin n),
    L.toCartSig.Path (prodTrm a) (.var (a i))
  | 0, _, i => i.elim0
  | 1, _, ⟨0, _⟩ => .nil _
  | _ + 2, a, ⟨0, _⟩ => fstPath (sg := L.toCartSig) (.var (a 0)) (prodTrm (Fin.tail a))
  | _ + 2, a, ⟨k + 1, h⟩ =>
      OneSig.Path.comp (sndPath (sg := L.toCartSig) (.var (a 0)) (prodTrm (Fin.tail a)))
        (projPath (Fin.tail a) ⟨k, Nat.lt_of_succ_lt_succ h⟩)

/-- The tupling `t → prodTrm b` of paths `t → bⱼ`: `!` for the empty tuple, the path itself for
a single one, and pairing `⟨p₀, ⟨p₁, …⟩⟩` (through the diagonal) otherwise. -/
def tuplePath {t : L.toCartSig.CTrm ()} :
    ∀ {m : ℕ} {b : Fin m → L.Sorts}, (∀ j, L.toCartSig.Path t (.var (b j))) →
      L.toCartSig.Path t (prodTrm b)
  | 0, _, _ => toUnitPath t
  | 1, _, p => p 0
  | _ + 2, _, p => liftPath (p 0) (tuplePath (fun j => p j.succ))

/-- **The path of a term**: a term `t : Term Γ s` becomes a path `prodTrm Γ → s` of the term
graph of `σ'`. A variable is a projection; `f(t₀, …)` is the tuple of the paths of the `tᵢ`
followed by the function symbol `f`. -/
def Term.toPath {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts}, L.Term Γ s → L.toCartSig.Path (prodTrm Γ) (.var s)
  | _, .var i => projPath Γ i
  | _, .func f ts => OneSig.Path.comp (tuplePath (fun j => Term.toPath (ts j)))
      (arrPath (OneSig.Arr.fn (sg := L.toCartSig) f))

/-- **The σ'-theory `T'` relative to `Σ_Cart`** of an equational theory `T`: one equation
`prodTrm (ctx φ) → sort φ` per equation `φ ∈ T`, between the paths of its two sides. -/
def Theory.toCartTheory (T : L.Theory) : UlmerBialgebras.Theory L.toCartSig where
  Eqn := T
  eqty := fun _ => ()
  dom φ := prodTrm φ.1.ctx
  cod φ := .var φ.1.sort
  lhs φ := φ.1.lhs.toPath
  rhs φ := φ.1.rhs.toPath

end Translation

/-! ## The category `C^{T'}` -/

section CartThy

variable {L : MSLanguage.{s, s}} (C : Type (max s v w)) [Category.{max s v} C]
  [CartesianMonoidalCategory C] (T : L.Theory)

attribute [local instance] catOfSizeHom in
/-- **The category `C^{T'}`** of `T'`-models in the `Σ_Cart`-model `C` (Definition 3.14 of
[forsman2026syntactic], in `CAT`). `C` has objects in `Type (max s v w)` and morphisms in
`Type (max s v)`; the products of size `s` it needs are those of `Cat.{max s v, max s v w}`
(`catOfSizeHom`). -/
abbrev Theory.cartThy : Type (max s v w) :=
  ((cartModel C).thyObj L.toCartSig T.toCartTheory : Cat.{max s v, max s v w})

attribute [local instance] catOfSizeHom in
/-- The forgetful functor `C^{T'} ⥤ C^S`, the 1-cell `e_M ≫ u_M : M^{T'} → M^{σ'} → M₀`. -/
def Theory.cartThyForget : T.cartThy C ⥤ (L.Sorts → C) :=
  ((cartModel C).e L.toCartSig T.toCartTheory ≫ (cartModel C).u L.toCartSig).toFunctor

end CartThy

end MSLanguage

open MSLanguage

/-! ## The theory of groups -/

section Grp

variable (S : Type u)

/-- The **language of groups** in each sort of `S`: for each `s`, a binary `mul`, a constant
`one` and a unary `inv`, all of sort `s`. -/
def grpLanguage : MSLanguage where
  Sorts := S
  Functions := S × GrpFn
  arity := fun | (_, .mul) => 2 | (_, .one) => 0 | (_, .inv) => 1
  argSorts f _ := f.1
  resSort f := f.1

variable {S}

/-- `x * y` at the sort `s`. -/
abbrev grpMul {n : ℕ} {Γ : Fin n → S} (s : S) (x y : (grpLanguage S).Term Γ s) :
    (grpLanguage S).Term Γ s :=
  .func (L := grpLanguage S) (s, .mul) ![x, y]

/-- `1` at the sort `s`. -/
abbrev grpOne {n : ℕ} {Γ : Fin n → S} (s : S) : (grpLanguage S).Term Γ s :=
  .func (L := grpLanguage S) (s, .one) (fun j => (j : Fin 0).elim0)

/-- `x⁻¹` at the sort `s`. -/
abbrev grpInv {n : ℕ} {Γ : Fin n → S} (s : S) (x : (grpLanguage S).Term Γ s) :
    (grpLanguage S).Term Γ s :=
  .func (L := grpLanguage S) (s, .inv) ![x]

/-- The variable `xᵢ` of the context `Fin n → S` constant at `s`. -/
abbrev grpVar {n : ℕ} (s : S) (i : Fin n) : (grpLanguage S).Term (fun _ : Fin n => s) s :=
  .var (L := grpLanguage S) i

variable (S)

/-- The group axioms at a sort `s`, as equations: `(x * y) * z = x * (y * z)`, `x * 1 = x`,
`1 * x = x`, `x⁻¹ * x = 1`, `x * x⁻¹ = 1`. -/
def grpEquation : S × GrpEqn → (grpLanguage S).Equation
  | (s, .assoc) => ⟨3, fun _ => s, s,
      grpMul s (grpMul s (grpVar s 0) (grpVar s 1)) (grpVar s 2),
      grpMul s (grpVar s 0) (grpMul s (grpVar s 1) (grpVar s 2))⟩
  | (s, .mulOne) => ⟨1, fun _ => s, s, grpMul s (grpVar s 0) (grpOne s), grpVar s 0⟩
  | (s, .oneMul) => ⟨1, fun _ => s, s, grpMul s (grpOne s) (grpVar s 0), grpVar s 0⟩
  | (s, .invMul) => ⟨1, fun _ => s, s, grpMul s (grpInv s (grpVar s 0)) (grpVar s 0), grpOne s⟩
  | (s, .mulInv) => ⟨1, fun _ => s, s, grpMul s (grpVar s 0) (grpInv s (grpVar s 0)), grpOne s⟩

/-- **The equational theory of groups** in each sort of `S` [ARV, Ch. 1 and 14]. -/
def grpEqTheory : (grpLanguage S).Theory := Set.range (grpEquation S)

end Grp

end UlmerBialgebras.Paper
