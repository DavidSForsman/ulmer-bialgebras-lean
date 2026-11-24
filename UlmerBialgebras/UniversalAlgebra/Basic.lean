module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.ModelTheory.Semantics
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Many-sorted equational theories and their models in a category

Mathlib's model theory (`FirstOrder.Language`, `FirstOrder.Language.Structure`,
`FirstOrder.Language.Term.realize`, `FirstOrder.Language.Theory.Model` with notation `M ⊨ T`,
`FirstOrder.Language.Theory.ModelType`) is single-sorted and interprets languages in types only.
This file gives the **many-sorted, algebraic (relation-free)** analogue, interpreted in a
category with finite products, with the same vocabulary, following
Adámek–Rosický–Vitale [ARV, Ch. 1 and 14]. The bridge `MSLanguage.ofLanguage` shows the
single-sorted Set case is Mathlib's notion (`ofLanguage_model_iff`, `ofLanguage_isHom_iff` in
`Companion/Statements/ExtrasAlgTheory.lean`).

These definitions were in `UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean`; they moved here, with
their names, so
that the trusted base holds the translation to `Σ_Cart` and the statements only. The import of
`Mathlib.Combinatorics.Quiver.ReflQuiver` keeps the instance path of `⟶` (through
`catToReflQuiver`) that the definitions had there, so their elaborated terms, and the cone
fingerprints of the statements that use them, are unchanged.

**Syntax.**
* `MSLanguage`: sorts, function symbols `f` with argument sorts `argSorts f : Fin (arity f) → Sorts`
  and a result sort `resSort f`. (Mathlib's `L.Functions n` corresponds to the symbols of
  arity `n`, see `ofLanguage`.)
* `MSLanguage.Term Γ s`: terms of sort `s` in a finite context `Γ : Fin n → Sorts`, with
  constructors `var` and `func` as in Mathlib's `FirstOrder.Language.Term`.
* `MSLanguage.Equation`: a sentence `∀ x̄ : Γ, t₁ = t₂`. `MSLanguage.Theory := Set L.Equation`
  (Mathlib: `L.Theory := Set L.Sentence`).

**Semantics in a category `C` with finite products.**
* `MSLanguage.Structure M` for `M : Sorts → C`: morphisms
  `funMap f : ∏ᶜ i, M (argSorts f i) ⟶ M (resSort f)`.
* `MSLanguage.Term.realize M t : ∏ᶜ i, M (Γ i) ⟶ M s`.
* `MSLanguage.Theory.Model M T`, written `M ⊨ T`: every equation of `T` holds.
* `MSLanguage.Hom M N`: families of morphisms commuting with `funMap`.
* `MSLanguage.Theory.ModelCat T C`: the category `Mod_C(T)` of bundled models (Mathlib's
  `ModelType`, without nonemptiness), with `ModelCat.forget : T.ModelCat C ⥤ (Sorts → C)`.
  Set-valued models are the instance `C := Type w`.

**Size.** For an arbitrary `C : Type u` with `Category.{v} C` one can use Mathlib's
`AsSmall.{s} C`, with the cartesian structure `asSmallCartesian` from the finite products of `C`.

## Main results

* `UlmerBialgebras.Paper.MSLanguage`, `UlmerBialgebras.Paper.MSLanguage.Theory`: many-sorted
  algebraic languages and equational theories.
* `UlmerBialgebras.Paper.MSLanguage.Theory.ModelCat`: the category `Mod_C(T)` of models in `C`.
* `UlmerBialgebras.Paper.MSLanguage.ofLanguage`: a single-sorted Mathlib language as an
  `MSLanguage`, with `Theory.toFOTheory` to Mathlib first-order theories.

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe v u w u₄ u₅ uF uR s

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Syntax -/

/-- A **many-sorted algebraic (relation-free) first-order language** [ARV, Ch. 14]: sorts, and
function symbols `f` with argument sorts `argSorts f` and result sort `resSort f`. Like Mathlib's
`FirstOrder.Language.{u, v}`, it carries its own universes: sorts in `Type u₄`, function symbols in
`Type u₅`, independent of the universes of its models. Mathlib's `FirstOrder.Language` is
single-sorted; see `MSLanguage.ofLanguage`. -/
structure MSLanguage : Type (max (u₄ + 1) (u₅ + 1)) where
  /-- The sorts. -/
  Sorts : Type u₄
  /-- The function symbols. -/
  Functions : Type u₅
  /-- The number of arguments of a function symbol. -/
  arity : Functions → ℕ
  /-- The sorts of the arguments of a function symbol. -/
  argSorts : ∀ f : Functions, Fin (arity f) → Sorts
  /-- The result sort of a function symbol. -/
  resSort : Functions → Sorts

namespace MSLanguage

section General

variable (L : MSLanguage.{u₄, u₅})

/-- **Terms** of sort `s` in the finite context `x₀ : Γ 0, …, xₙ₋₁ : Γ (n-1)`
(cf. Mathlib's `FirstOrder.Language.Term`). -/
inductive Term {n : ℕ} (Γ : Fin n → L.Sorts) : L.Sorts → Type (max u₄ u₅)
  /-- The variable `xᵢ`, of sort `Γ i`. -/
  | var (i : Fin n) : Term Γ (Γ i)
  /-- The term `f(t₀, …, tₘ₋₁)`. -/
  | func (f : L.Functions) (ts : ∀ i : Fin (L.arity f), Term Γ (L.argSorts f i)) :
      Term Γ (L.resSort f)

/-- An **equation**, the sentence `∀ x̄ : Γ, lhs = rhs`, between two terms of the same sort in a
finite context `Γ`. -/
structure Equation where
  /-- The length of the context. -/
  ctxLen : ℕ
  /-- The context. -/
  ctx : Fin ctxLen → L.Sorts
  /-- The sort of the two sides. -/
  sort : L.Sorts
  /-- The left-hand side. -/
  lhs : L.Term ctx sort
  /-- The right-hand side. -/
  rhs : L.Term ctx sort

/-- A **(many-sorted, finitary) equational theory**: a set of equations (cf. Mathlib's
`FirstOrder.Language.Theory := Set L.Sentence`). -/
abbrev Theory : Type (max u₄ u₅) := Set L.Equation

/-! ## Semantics in a category with finite products -/

section Semantics

variable {L} {C : Type u} [Category.{v} C] [HasFiniteProducts C]

variable (L) in
/-- An **`L`-structure** on a family `M : Sorts → C`: a morphism
`funMap f : ∏ᵢ M(argSorts f i) ⟶ M(resSort f)` for each function symbol (cf. Mathlib's
`FirstOrder.Language.Structure`). -/
class Structure (M : L.Sorts → C) where
  /-- The interpretation of a function symbol. -/
  funMap : ∀ f : L.Functions, (∏ᶜ fun i => M (L.argSorts f i)) ⟶ M (L.resSort f)

export Structure (funMap)

/-- Two structures on the same family are equal when they interpret every function symbol by the
same morphism. -/
@[ext] lemma Structure.ext {M : L.Sorts → C} {S S' : L.Structure M}
    (h : ∀ f, S.funMap f = S'.funMap f) : S = S' := by
  cases S
  cases S'
  congr 1
  exact funext h

variable (M : L.Sorts → C) [L.Structure M]

/-- The **realization of a term** `t : Term Γ s` in `M`, a morphism `∏ᵢ M(Γ i) ⟶ M s`: a variable
is a product projection, and `f(t₀, …)` is `⟨t₀, …⟩ ≫ funMap f`
(cf. Mathlib's `FirstOrder.Language.Term.realize`). -/
noncomputable def Term.realize {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts}, L.Term Γ s → ((∏ᶜ fun i => M (Γ i)) ⟶ M s)
  | _, .var i => Pi.π _ i
  | _, .func f ts => Pi.lift (fun i => Term.realize (ts i)) ≫ funMap f

/-- A variable realizes to its product projection. -/
lemma Term.realize_var {n : ℕ} {Γ : Fin n → L.Sorts} (i : Fin n) :
    (Term.var (L := L) (Γ := Γ) i).realize M = Pi.π _ i := rfl

/-- `f(t₀, …)` realizes to the tuple of the realizations of the `tᵢ` followed by `funMap f`. -/
lemma Term.realize_func {n : ℕ} {Γ : Fin n → L.Sorts} (f : L.Functions)
    (ts : ∀ i, L.Term Γ (L.argSorts f i)) :
    (Term.func f ts).realize M = Pi.lift (fun i => (ts i).realize M) ≫ funMap f := rfl

/-- An equation is **realized** in `M` if its two sides have the same realization. -/
def Equation.Realize (φ : L.Equation) : Prop := φ.lhs.realize M = φ.rhs.realize M

/-- An equation is realized in `M` exactly when its two sides have the same realization. -/
lemma Equation.realize_iff (φ : L.Equation) :
    φ.Realize M ↔ φ.lhs.realize M = φ.rhs.realize M := Iff.rfl

/-- `M` is a **model** of `T`, written `M ⊨ T`, if every equation of `T` is realized in `M`
(cf. Mathlib's `FirstOrder.Language.Theory.Model`). -/
class Theory.Model (T : L.Theory) : Prop where
  realize_of_mem : ∀ φ ∈ T, φ.Realize M

@[inherit_doc Theory.Model]
scoped infixl:51 " ⊨ " => Theory.Model

variable (N : L.Sorts → C) [L.Structure N]

/-- A **homomorphism** of `L`-structures: a morphism for each sort commuting with the
interpretations of the function symbols (cf. Mathlib's `FirstOrder.Language.Hom`). -/
@[ext]
structure Hom where
  /-- The component at a sort. -/
  toFun : ∀ s, M s ⟶ N s
  /-- Commutation with the function symbols. -/
  map_fun' : ∀ f : L.Functions, funMap f ≫ toFun (L.resSort f) =
    Limits.Pi.map (fun i => toFun (L.argSorts f i)) ≫ funMap f

variable (C) in
/-- The **category `Mod_C(T)` of models** of `T` in `C`, as bundled models (cf. Mathlib's
`FirstOrder.Language.Theory.ModelType`, here without nonemptiness) [ARV, Ch. 1 and 14]. -/
structure Theory.ModelCat (T : L.Theory) where
  /-- The family of underlying objects. -/
  Carrier : L.Sorts → C
  [struc : L.Structure Carrier]
  [is_model : Theory.Model Carrier T]

attribute [instance] Theory.ModelCat.struc Theory.ModelCat.is_model

variable {T : L.Theory}

/-- The category of models of `T` in `C`, with all homomorphisms. -/
noncomputable instance : Category (T.ModelCat C) where
  Hom A B := L.Hom A.Carrier B.Carrier
  id A := ⟨fun _ => 𝟙 _, fun f => by simp⟩
  comp g h := ⟨fun s => g.toFun s ≫ h.toFun s, fun f => by
    rw [← Category.assoc, g.map_fun', Category.assoc, h.map_fun', ← Category.assoc,
      Limits.Pi.map_comp_map]⟩

variable (T C) in
/-- The forgetful functor `Mod_C(T) ⥤ C^S` sending a model to its family of objects. -/
noncomputable def Theory.ModelCat.forget : T.ModelCat C ⥤ (L.Sorts → C) where
  obj A := A.Carrier
  map g := Hom.toFun g

end Semantics

end General

/-! ## Single-sorted Mathlib languages -/

section OfLanguage

open FirstOrder

variable (L' : FirstOrder.Language.{uF, uR})

/-- A single-sorted Mathlib language, as a many-sorted algebraic language with one sort: its
function symbols are those of all arities (its relation symbols are dropped). -/
def ofLanguage : MSLanguage.{0, uF} where
  Sorts := Unit
  Functions := Σ n, L'.Functions n
  arity f := f.1
  argSorts _ _ := ()
  resSort _ := ()

variable {L'}

/-- A term of `ofLanguage L'` as a Mathlib term with variables `Empty ⊕ Fin n`, the form used in
bounded formulas. -/
def Term.toFOTerm {n : ℕ} {Γ : Fin n → Unit} :
    ∀ {s : Unit}, (ofLanguage L').Term Γ s → L'.Term (Empty ⊕ Fin n)
  | _, .var i => .var (Sum.inr i)
  | _, .func f ts => .func f.2 (fun i => Term.toFOTerm (ts i))

/-- An equation of `ofLanguage L'` as the Mathlib sentence `∀ x̄, lhs = rhs`. -/
def Equation.toSentence (φ : (ofLanguage L').Equation) : L'.Sentence :=
  (φ.lhs.toFOTerm.bdEqual φ.rhs.toFOTerm).alls

/-- An equational theory of `ofLanguage L'` as a Mathlib first-order theory. -/
def Theory.toFOTheory (T : (ofLanguage L').Theory) : L'.Theory :=
  Equation.toSentence '' T

/-- A Mathlib `L'`-structure on a type `M`, as an `ofLanguage L'`-structure on the one-sorted
family `M` in `Type w`: `funMap f` precomposed with `∏ᶜ ≅ (Fin n → M)`. -/
noncomputable instance ofStructure (M : Type w) [L'.Structure M] :
    (ofLanguage L').Structure (C := Type w) (fun _ : Unit => M) where
  funMap f := (Types.productIso.{0, w} fun _ : Fin f.1 => M).hom ≫
    TypeCat.ofHom fun x => FirstOrder.Language.Structure.funMap f.2 x

/-- The interpretation of a function symbol in `ofStructure M` is Mathlib's `funMap`, precomposed
with `∏ᶜ ≅ (Fin n → M)`. -/
lemma ofStructure_funMap (M : Type w) [L'.Structure M] (f : (ofLanguage L').Functions) :
    funMap (M := fun _ : Unit => M) f = (Types.productIso.{0, w} fun _ : Fin f.1 => M).hom ≫
      TypeCat.ofHom fun x => FirstOrder.Language.Structure.funMap f.2 x := rfl

end OfLanguage

end MSLanguage

/-! ## Arbitrary universes: `AsSmall` -/

/-- `AsSmall C` has finite products when `C` does (along `AsSmall.equiv`). -/
instance asSmall_hasFiniteProducts (C : Type u) [Category.{v} C] [HasFiniteProducts C] :
    HasFiniteProducts (AsSmall.{w} C) :=
  ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence
    (AsSmall.equiv.{v, u, w} (C := C)).inverse⟩

/-- The cartesian monoidal structure on `AsSmall C`, from its finite products. -/
noncomputable instance asSmallCartesian (C : Type u) [Category.{v} C] [HasFiniteProducts C] :
    CartesianMonoidalCategory (AsSmall.{w} C) :=
  .ofHasFiniteProducts

/-- The functor `C^S ⥤ (AsSmall C)^S` relabelling each component along `AsSmall.up`. -/
def asSmallUpPi (S : Type s) (C : Type u) [Category.{v} C] :
    (S → C) ⥤ (S → AsSmall.{w} C) :=
  Functor.pi fun _ => AsSmall.up

end UlmerBialgebras.Paper
