module

public import UlmerBialgebras.UniversalAlgebra.Basic

/-!
# Morphisms of equational theories and the induced functors on models

Definitions for an addition beyond the paper. A morphism of many-sorted equational
theories `T₁ → T₂` sends sorts to sorts and function symbols of `L₁` to **terms** of `L₂` (derived
operations), such that each translated axiom of `T₁` is **derivable** from `T₂`. It induces a
functor `φ^* : Mod_C(T₂) ⥤ Mod_C(T₁)` for every category `C` with finite products, which commutes
strictly with the forgetful functors to `C^S`, reindexed along the sort map.

* `Term.subst`: simultaneous substitution of terms for the variables of a context.
* `LangMorphism L₁ L₂`: a sort map and a term of `L₂` for each function symbol of `L₁`;
  `LangMorphism.translate`, `LangMorphism.translateEquation`; `LangMorphism.id`,
  `LangMorphism.comp`.
* `Theory.Derives T a b`: `a = b` is derivable from `T` in equational logic (axioms, substitution
  instances, reflexivity, symmetry, transitivity, congruence). Contexts are explicit, so empty
  sorts are allowed; the calculus is sound in every category with finite products
  (`Theory.Derives.realize_eq`).
* `TheoryMorphism T₁ T₂`: a language morphism whose translated axioms are derivable.
* `LangMorphism.reindexStructure`: an `L₂`-structure on `M` gives an `L₁`-structure on
  `M ∘ sortMap`, interpreting each symbol by the realization of its term.
* `TheoryMorphism.modelFunctor φ C : T₂.ModelCat C ⥤ T₁.ModelCat C`, the functor `φ^*`.
* Special cases: `TheoryMorphism.ofMem` (axioms go to axioms), `TheoryMorphism.ofLE`
  (inclusion of theories over one language).

## Main results

* `UlmerBialgebras.Paper.MSLanguage.TheoryMorphism`
* `UlmerBialgebras.Paper.MSLanguage.TheoryMorphism.modelFunctor`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe v u u₁ u₂ u₃ u₄ u₅ u₆

namespace UlmerBialgebras.Paper.MSLanguage

open CategoryTheory Limits

/-! ## Substitution -/

section Subst

variable {L : MSLanguage.{u₁, u₂}}

/-- **Simultaneous substitution**: replace the variable `xᵢ` of the context `Δ` by the term
`σ i` in the context `Γ`. -/
def Term.subst {n m : ℕ} {Γ : Fin n → L.Sorts} {Δ : Fin m → L.Sorts}
    (σ : ∀ i, L.Term Γ (Δ i)) : ∀ {s : L.Sorts}, L.Term Δ s → L.Term Γ s
  | _, .var i => σ i
  | _, .func f ts => .func f (fun j => Term.subst σ (ts j))

/-- Substituting the variables for themselves is the identity. -/
lemma Term.subst_var {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts} (t : L.Term Γ s), t.subst (fun i => .var i) = t
  | _, .var _ => rfl
  | _, .func f ts => congr(Term.func f $(funext fun j => Term.subst_var (ts j)))

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] (M : L.Sorts → C) [L.Structure M]

/-- Realizing a substitution instance is precomposing with the tuple of the substituted
terms. -/
lemma Term.realize_subst {n m : ℕ} {Γ : Fin n → L.Sorts} {Δ : Fin m → L.Sorts}
    (σ : ∀ i, L.Term Γ (Δ i)) :
    ∀ {s : L.Sorts} (t : L.Term Δ s),
      (t.subst σ).realize M = Pi.lift (fun i => (σ i).realize M) ≫ t.realize M
  | _, .var i => (Pi.lift_comp_π (fun i => (σ i).realize M) i).symm
  | _, .func f ts => by
    simp only [Term.subst, Term.realize, ← Category.assoc]
    congr 1
    exact Pi.hom_ext _ _ fun j => by simp [Term.realize_subst σ (ts j)]

end Subst

/-! ## Derivability -/

section Derives

variable {L : MSLanguage.{u₁, u₂}}

/-- **Equational logic**: `T.Derives a b` says that `a = b` (in the context `Γ`) is derivable from
the axioms of `T` by substitution instances, reflexivity, symmetry, transitivity and
congruence. -/
inductive Theory.Derives (T : L.Theory) :
    ∀ {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts}, L.Term Γ s → L.Term Γ s → Prop
  /-- A substitution instance of an axiom. -/
  | ax {n : ℕ} {Γ : Fin n → L.Sorts} (φ : L.Equation) (hφ : φ ∈ T)
      (σ : ∀ i, L.Term Γ (φ.ctx i)) : Derives T (φ.lhs.subst σ) (φ.rhs.subst σ)
  /-- Reflexivity. -/
  | refl {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts} (a : L.Term Γ s) : Derives T a a
  /-- Symmetry. -/
  | symm {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts} {a b : L.Term Γ s} :
      Derives T a b → Derives T b a
  /-- Transitivity. -/
  | trans {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts} {a b c : L.Term Γ s} :
      Derives T a b → Derives T b c → Derives T a c
  /-- Congruence. -/
  | congr {n : ℕ} {Γ : Fin n → L.Sorts} (f : L.Functions)
      {ts ts' : ∀ i, L.Term Γ (L.argSorts f i)} :
      (∀ i, Derives T (ts i) (ts' i)) → Derives T (.func f ts) (.func f ts')

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- **Soundness of equational logic** in a category with finite products: derivable equations
hold in every model. -/
lemma Theory.Derives.realize_eq {T : L.Theory} (M : L.Sorts → C) [L.Structure M] [M ⊨ T]
    {n : ℕ} {Γ : Fin n → L.Sorts} {s : L.Sorts} {a b : L.Term Γ s} (h : T.Derives a b) :
    a.realize M = b.realize M := by
  induction h with
  | ax φ hφ σ =>
    rw [Term.realize_subst, Term.realize_subst, Theory.Model.realize_of_mem (M := M) φ hφ]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr f _ ih => exact congr(Pi.lift $(funext ih) ≫ funMap f)

end Derives

/-! ## Morphisms of languages and theories -/

/-- A **morphism of languages** `L₁ → L₂` (an interpretation): a map of sorts, and for each
function symbol of `L₁` a term of `L₂` (a derived operation) in the translated context. -/
structure LangMorphism (L₁ : MSLanguage.{u₁, u₂}) (L₂ : MSLanguage.{u₃, u₄}) where
  /-- The map of sorts. -/
  sortMap : L₁.Sorts → L₂.Sorts
  /-- The derived operation interpreting a function symbol. -/
  funMap : ∀ f : L₁.Functions,
    L₂.Term (fun i => sortMap (L₁.argSorts f i)) (sortMap (L₁.resSort f))

namespace LangMorphism

variable {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}} {L₃ : MSLanguage.{u₅, u₆}}

/-- The **translation of a term** along a language morphism: each function symbol is replaced by
its derived operation. -/
def translate (F : LangMorphism L₁ L₂) {n : ℕ} {Γ : Fin n → L₁.Sorts} :
    ∀ {s : L₁.Sorts}, L₁.Term Γ s → L₂.Term (fun i => F.sortMap (Γ i)) (F.sortMap s)
  | _, .var i => .var i
  | _, .func f ts => (F.funMap f).subst (fun i => translate F (ts i))

/-- The translation of an equation along a language morphism. -/
def translateEquation (F : LangMorphism L₁ L₂) (φ : L₁.Equation) : L₂.Equation :=
  ⟨φ.ctxLen, fun i => F.sortMap (φ.ctx i), F.sortMap φ.sort, F.translate φ.lhs,
    F.translate φ.rhs⟩

variable (L₁) in
/-- The identity morphism of a language: each symbol is the term `f(x₀, …, xₙ₋₁)`. -/
def id : LangMorphism L₁ L₁ where
  sortMap s := s
  funMap f := .func f (fun i => .var i)

/-- Translating along the identity is the identity. -/
lemma translate_id {n : ℕ} {Γ : Fin n → L₁.Sorts} :
    ∀ {s : L₁.Sorts} (t : L₁.Term Γ s), (LangMorphism.id L₁).translate t = t
  | _, .var _ => rfl
  | _, .func f ts => congr(Term.func f $(funext fun j => translate_id (ts j)))

/-- Translating an equation along the identity is the identity. -/
lemma translateEquation_id (φ : L₁.Equation) : (LangMorphism.id L₁).translateEquation φ = φ := by
  obtain ⟨n, Γ, s, a, b⟩ := φ
  simp only [translateEquation, translate_id]
  rfl

/-- The composite of language morphisms: translate the derived operations of `F` along `G`. -/
def comp (G : LangMorphism L₂ L₃) (F : LangMorphism L₁ L₂) : LangMorphism L₁ L₃ where
  sortMap s := G.sortMap (F.sortMap s)
  funMap f := G.translate (F.funMap f)

/-- `F` is a **morphism of theories** `T₁ → T₂`: each translated axiom of `T₁` is derivable from
`T₂`. -/
def IsTheoryMorphism (F : LangMorphism L₁ L₂) (T₁ : L₁.Theory) (T₂ : L₂.Theory) : Prop :=
  ∀ φ ∈ T₁, T₂.Derives (F.translate φ.lhs) (F.translate φ.rhs)

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

/-- The **reindexed structure**: an `L₂`-structure on `M` gives an `L₁`-structure on
`M ∘ sortMap`, interpreting each symbol of `L₁` by the realization of its derived operation. -/
@[implicit_reducible]
noncomputable def reindexStructure (F : LangMorphism L₁ L₂) (M : L₂.Sorts → C) [L₂.Structure M] :
    L₁.Structure (fun s => M (F.sortMap s)) where
  funMap f := (F.funMap f).realize M

/-- Realizing a translated term is realizing the term in the reindexed structure. -/
lemma realize_translate (F : LangMorphism L₁ L₂) (M : L₂.Sorts → C) [L₂.Structure M]
    {n : ℕ} {Γ : Fin n → L₁.Sorts} :
    ∀ {s : L₁.Sorts} (t : L₁.Term Γ s),
      (F.translate t).realize M =
        (letI := F.reindexStructure M; t.realize (fun s => M (F.sortMap s)))
  | _, .var _ => rfl
  | _, .func f ts => by
    rw [translate, Term.realize_subst]
    exact congr(Pi.lift $(funext fun i => realize_translate F M (ts i)) ≫ (F.funMap f).realize M)

/-- Homomorphisms commute with the realization of terms. -/
lemma realize_comp_hom {L : MSLanguage.{u₁, u₂}} {M N : L.Sorts → C} [L.Structure M]
    [L.Structure N] (g : L.Hom M N) {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts} (t : L.Term Γ s),
      t.realize M ≫ g.toFun s = Limits.Pi.map (fun i => g.toFun (Γ i)) ≫ t.realize N
  | _, .var i => (Limits.Pi.map_π (fun i => g.toFun (Γ i)) i).symm
  | _, .func f ts => by
    rw [Term.realize, Category.assoc, g.map_fun', ← Category.assoc, Term.realize,
      ← Category.assoc]
    congr 1
    exact Pi.hom_ext _ _ fun j => by simp [realize_comp_hom g (ts j)]

end LangMorphism

/-- A **morphism of theories** `T₁ → T₂`: a morphism of languages (sorts to sorts,
function symbols to terms) whose translated axioms of `T₁` are derivable from `T₂`. -/
structure TheoryMorphism {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}}
    (T₁ : L₁.Theory) (T₂ : L₂.Theory) extends LangMorphism L₁ L₂ where
  /-- The translated axioms of `T₁` are derivable from `T₂`. -/
  isTheoryMorphism : toLangMorphism.IsTheoryMorphism T₁ T₂

namespace TheoryMorphism

variable {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}} {T₁ : L₁.Theory} {T₂ : L₂.Theory}

/-- A language morphism sending the axioms of `T₁` to axioms of `T₂` is a morphism of
theories. -/
def ofMem (F : LangMorphism L₁ L₂) (h : ∀ φ ∈ T₁, F.translateEquation φ ∈ T₂) :
    TheoryMorphism T₁ T₂ where
  toLangMorphism := F
  isTheoryMorphism φ hφ := by
    have h' := Theory.Derives.ax (T := T₂) _ (h φ hφ) (fun i => .var i)
    simp only [Term.subst_var] at h'
    exact h'

/-- The **inclusion** `T ⊆ T'` of theories over one language, as a morphism of theories (the
identity of the language). -/
def ofLE {L : MSLanguage.{u₁, u₂}} {T T' : L.Theory} (h : T ⊆ T') : TheoryMorphism T T' :=
  ofMem (LangMorphism.id L) fun φ hφ => by
    rw [LangMorphism.translateEquation_id]
    exact h hφ

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]

variable (C) in
/-- **The functor induced by a morphism of theories**, `φ^* : Mod_C(T₂) ⥤ Mod_C(T₁)`: a model `M`
of `T₂` gives the model `M ∘ sortMap` of `T₁` with the reindexed structure, and a homomorphism
its components at the translated sorts. -/
noncomputable def modelFunctor (φ : TheoryMorphism T₁ T₂) : T₂.ModelCat C ⥤ T₁.ModelCat C where
  obj A :=
    letI := φ.reindexStructure A.Carrier
    @Theory.ModelCat.mk L₁ C _ _ T₁ (fun s => A.Carrier (φ.sortMap s)) _ ⟨fun ψ hψ =>
      ((φ.realize_translate A.Carrier ψ.lhs).symm.trans
        ((φ.isTheoryMorphism ψ hψ).realize_eq A.Carrier)).trans
        (φ.realize_translate A.Carrier ψ.rhs)⟩
  map {A B} g := @Hom.mk L₁ C _ _ (fun s => A.Carrier (φ.sortMap s))
    (φ.reindexStructure A.Carrier) (fun s => B.Carrier (φ.sortMap s))
    (φ.reindexStructure B.Carrier) (fun s => g.toFun (φ.sortMap s))
    (fun f => LangMorphism.realize_comp_hom g (φ.funMap f))
  map_id _ := rfl
  map_comp _ _ := rfl

end TheoryMorphism

section Restrict

variable (L : MSLanguage.{u₁, u₂})

/-- The **sublanguage** of `L` with the function symbols satisfying `P`, and all sorts. -/
@[reducible] def restrict (P : L.Functions → Prop) : MSLanguage.{u₁, u₂} where
  Sorts := L.Sorts
  Functions := {f // P f}
  arity f := L.arity f.1
  argSorts f := L.argSorts f.1
  resSort f := L.resSort f.1

variable {L}

/-- The inclusion of a sublanguage, as a morphism of languages: each symbol is itself. -/
def LangMorphism.ofRestrict (P : L.Functions → Prop) : LangMorphism (L.restrict P) L where
  sortMap s := s
  funMap f := .func f.1 (fun i => .var i)

end Restrict

namespace TheoryMorphism

variable {L : MSLanguage.{u₁, u₂}}

/-- The **identity** morphism of a theory. -/
def id (T : L.Theory) : TheoryMorphism T T := ofLE subset_rfl

/-- The **reduct along a sublanguage**: the inclusion of a sublanguage, for theories whose
translated axioms are axioms. -/
def ofRestrict {P : L.Functions → Prop} {T : (L.restrict P).Theory} {T' : L.Theory}
    (h : ∀ φ ∈ T, (LangMorphism.ofRestrict P).translateEquation φ ∈ T') :
    TheoryMorphism T T' :=
  ofMem _ h

end TheoryMorphism

end UlmerBialgebras.Paper.MSLanguage
