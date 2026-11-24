module

public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism
public import Companion.UlmerBialgebras.UniversalAlgebra.FirstOrder

/-!
# `Σ_Cart`-theories as universal algebra

Definitions for an addition beyond the paper.

**Part 1, `Σ_Cart` to universal algebra** (the converse of `MSLanguage.Theory.toCartTheory`). For a
1-signature `sg` relative to `Σ_Cart` and a `sg`-theory `T`:
* `factors t`: the list of sorts of a closed term `t` of `Σ_Cart`, with `□` flattened and `I` the
  empty list.
* `toMSLanguage sg`: the many-sorted language with the sorts of `sg` and, for each function symbol
  `B : t₁ → t₂`, one operation `(B, j)` of arity `factors t₁` and result sort the `j`-th factor of
  `t₂` (a map into a product is a tuple of maps).
* `arrTuple`, `pathTuple`: an arrow or path `t₁ → t₂` of the term graph `G_σ` as a tuple of terms
  in the variables `factors t₁`, one for each factor of `t₂`. The structural arrows `δ, p₁, p₂, !`
  are tuples of variables, and `□` acts slotwise.
* `toMSTheory T`: one equation for each equation `p = q` of `T` and each factor of its codomain.
* `thyCat C sg T`, `thyCatForget`: the category `C^T` of Definition 3.14 and its forgetful functor.

**Part 2, single-sorted universal algebra to first-order logic**: `MSLanguage.toFOLanguage`,
`MSLanguage.Theory.toFO` and `FOModelCat` are library definitions
(`Companion/UlmerBialgebras/UniversalAlgebra/FirstOrder.lean`).

## Main results

* `UlmerBialgebras.Paper.CartToAlg.toMSLanguage`, `UlmerBialgebras.Paper.CartToAlg.toMSTheory`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.19, Definitions 3.5–3.7
-/

@[expose] public section

universe v u w s t u₄ u₅

namespace UlmerBialgebras.Paper

open CategoryTheory Limits Cart MSLanguage

/-! ## Part 1: `Σ_Cart`-theories as universal algebra -/

namespace CartToAlg

variable {sg : OneSig.{0, 0, 0, s, s} sigCart}

/-- The **sort factors** of a closed term of `Σ_Cart`: `x ↦ [x]`, `a □ b ↦ factors a ++ factors b`,
`I ↦ []`, as a length and a family of sorts. -/
def factors : ∀ {c : Unit}, sg.CTrm c → Σ n : ℕ, Fin n → sg.Srt
  | _, .var x => ⟨1, fun _ => x⟩
  | _, .app CartFun.tens args => ⟨(factors (args 0)).1 + (factors (args 1)).1,
      Fin.append (factors (args 0)).2 (factors (args 1)).2⟩
  | _, .app CartFun.unit _ => ⟨0, Fin.elim0⟩

variable (sg) in
/-- **The language `σ'` of a `Σ_Cart`-signature**: the sorts of `sg`, and for each function symbol
`B : t₁ → t₂` and each factor `j` of `t₂` an operation `(B, j)` from the factors of `t₁` to the
`j`-th factor of `t₂`. -/
def toMSLanguage : MSLanguage.{s, s} where
  Sorts := sg.Srt
  Functions := Σ f : sg.Fn, Fin (factors (sg.fncod f)).1
  arity f := (factors (sg.fndom f.1)).1
  argSorts f := (factors (sg.fndom f.1)).2
  resSort f := (factors (sg.fncod f.1)).2 f.2

/-- A term moved along an equality of sorts. -/
def castSort {n : ℕ} {Γ : Fin n → sg.Srt} {a b : sg.Srt} (h : a = b)
    (t : (toMSLanguage sg).Term Γ a) : (toMSLanguage sg).Term Γ b :=
  h ▸ t

/-- The **tuples** `t₁ → t₂`: a term in the factors of `t₁` for each factor of `t₂`. -/
abbrev Tuple {c : Unit} (t₁ t₂ : sg.CTrm c) : Type s :=
  ∀ j : Fin (factors t₂).1, (toMSLanguage sg).Term (factors t₁).2 ((factors t₂).2 j)

/-- The identity tuple. -/
def Tuple.id {c : Unit} (t : sg.CTrm c) : Tuple t t := fun j => .var j

/-- The identity tuple between equal terms. -/
def Tuple.ofEq {c : Unit} {t t' : sg.CTrm c} (h : t = t') : Tuple t t' := h ▸ Tuple.id t

/-- The composite of tuples, by substitution. -/
def Tuple.comp {c : Unit} {t₁ t₂ t₃ : sg.CTrm c} (p : Tuple t₁ t₂) (q : Tuple t₂ t₃) :
    Tuple t₁ t₃ :=
  fun j => (q j).subst p

/-- The variables of the left part of a context `Fin.append a b`. -/
def projL {m n : ℕ} (a : Fin m → sg.Srt) (b : Fin n → sg.Srt) (i : Fin m) :
    (toMSLanguage sg).Term (Fin.append a b) (a i) :=
  castSort (Fin.append_left a b i) (.var (Fin.castAdd n i))

/-- The variables of the right part of a context `Fin.append a b`. -/
def projR {m n : ℕ} (a : Fin m → sg.Srt) (b : Fin n → sg.Srt) (i : Fin n) :
    (toMSLanguage sg).Term (Fin.append a b) (b i) :=
  castSort (Fin.append_right a b i) (.var (Fin.natAdd m i))

/-- Pairing: a family of terms for `a` and one for `b` give one for `Fin.append a b`. -/
def pairTerms {k m n : ℕ} {Γ : Fin k → sg.Srt} {a : Fin m → sg.Srt} {b : Fin n → sg.Srt}
    (p : ∀ i, (toMSLanguage sg).Term Γ (a i)) (q : ∀ i, (toMSLanguage sg).Term Γ (b i)) :
    ∀ j, (toMSLanguage sg).Term Γ (Fin.append a b j) :=
  Fin.addCases (fun i => castSort (Fin.append_left a b i).symm (p i))
    (fun i => castSort (Fin.append_right a b i).symm (q i))

/-- **The tuple of an arrow** of the term graph: a function symbol `B` is the tuple of the
operations `(B, j)`; `δ` is the pair of identities; `p₁`, `p₂` are the two blocks of variables;
`!` is the empty tuple; `□` acts on the slot of the arrow and is the identity on the other. -/
def arrTuple : ∀ {c : Unit} {t₁ t₂ : sg.CTrm c}, sg.Arr t₁ t₂ → Tuple t₁ t₂
  | _, _, _, .fn f => fun j => .func (L := toMSLanguage sg) ⟨f, j⟩ (fun i => .var i)
  | _, _, _, .tr CartTr.diag _ => pairTerms (fun i => .var i) (fun i => .var i)
  | _, _, _, .tr CartTr.proj₁ _ => projL _ _
  | _, _, _, .tr CartTr.proj₂ _ => projR _ _
  | _, _, _, .tr CartTr.term _ => fun j => j.elim0
  | _, _, _, .app CartFun.tens ⟨0, _⟩ _ _ hne g =>
      pairTerms (fun j => (arrTuple g j).subst (projL _ _))
        (fun j => (Tuple.ofEq (hne 1 (Fin.ne_of_val_ne Nat.one_ne_zero)) j).subst (projR _ _))
  | _, _, _, .app CartFun.tens ⟨1, _⟩ _ _ hne g =>
      pairTerms
        (fun j => (Tuple.ofEq (hne 0 (Fin.ne_of_val_ne Nat.zero_ne_one)) j).subst (projL _ _))
        (fun j => (arrTuple g j).subst (projR _ _))
  | _, _, _, .app CartFun.unit i _ _ _ _ => i.elim0

/-- **The tuple of a path** of the term graph: the composite of the tuples of its arrows. -/
def pathTuple : ∀ {c : Unit} {t₁ t₂ : sg.CTrm c}, sg.Path t₁ t₂ → Tuple t₁ t₂
  | _, _, _, .nil t => Tuple.id t
  | _, _, _, .cons g p => (arrTuple g).comp (pathTuple p)

/-- **The theory `T'` of a `Σ_Cart`-theory**: for each equation `p = q : t₁ → t₂` of `T` and each
factor `j` of `t₂`, the equation `p_j = q_j` in the variables `factors t₁`. -/
def toMSTheory (T : Theory.{0, 0, 0, s, s, s} sg) : (toMSLanguage sg).Theory :=
  Set.range fun x : Σ e : T.Eqn, Fin (factors (T.cod e)).1 =>
    (⟨_, (factors (T.dom x.1)).2, (factors (T.cod x.1)).2 x.2, pathTuple (T.lhs x.1) x.2,
      pathTuple (T.rhs x.1) x.2⟩ : (toMSLanguage sg).Equation)

section ThyCat

variable (C : Type (max s v w)) [Category.{max s v} C] [CartesianMonoidalCategory C]
  (sg : OneSig.{0, 0, 0, s, s} sigCart) (T : Theory.{0, 0, 0, s, s, s} sg)

attribute [local instance] catOfSizeHom in
/-- **The category `C^T`** of `T`-models in the `Σ_Cart`-model `C` (Definition 3.14 of
[forsman2026syntactic], in `CAT = Cat.{max s v, max s v w}`, with the products of size `s` of
`catOfSizeHom`). -/
abbrev thyCat : Type (max s v w) :=
  ((cartModel C).thyObj sg T : Cat.{max s v, max s v w})

attribute [local instance] catOfSizeHom in
/-- The forgetful functor `C^T ⥤ C^S`, the 1-cell `e_M ≫ u_M`. -/
def thyCatForget : thyCat C sg T ⥤ (sg.Srt → C) :=
  ((cartModel C).e sg T ≫ (cartModel C).u sg).toFunctor

end ThyCat

end CartToAlg

end UlmerBialgebras.Paper
