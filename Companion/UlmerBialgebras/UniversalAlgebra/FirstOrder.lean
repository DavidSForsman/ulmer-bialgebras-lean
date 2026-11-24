module

public import UlmerBialgebras.UniversalAlgebra.Basic

/-!
# Single-sorted universal algebra as first-order logic

These definitions were Part 2 of `Companion/Statements/DefsAlgTranslations.lean`; they moved here,
with their
names. For a language `L`:
* `toFOLanguage L`: the Mathlib first-order language with the function symbols of `L` (by arity)
  and no relation symbols, so `IsAlgebraic`.
* `Theory.toFO T`: the universal closures of the equations of `T`.
* `FOModelCat L' T`: Mathlib structures satisfying `T`, with Mathlib homomorphisms `M →[L'] N`.
  Unlike Mathlib's `Theory.ModelType`, carriers may be empty (models of universal algebra may
  be).

## Main results

* `UlmerBialgebras.Paper.MSLanguage.toFOLanguage`, `UlmerBialgebras.Paper.FOModelCat`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe w u₄ u₅

namespace UlmerBialgebras.Paper

open CategoryTheory

namespace MSLanguage

variable (L : MSLanguage.{u₄, u₅})

/-- **The first-order language of `L`** (sorts forgotten): the function symbols of `L` of arity
`n` are the `n`-ary function symbols, and there are no relation symbols. -/
def toFOLanguage : FirstOrder.Language.{u₅, 0} where
  Functions n := {f : L.Functions // L.arity f = n}
  Relations _ := Empty

instance : (toFOLanguage L).IsAlgebraic := fun _ => inferInstanceAs (IsEmpty Empty)

variable {L}

/-- A term of `L` as a first-order term with variables `Empty ⊕ Fin n`, the form used in bounded
formulas. -/
def Term.toFO {n : ℕ} {Γ : Fin n → L.Sorts} :
    ∀ {s : L.Sorts}, L.Term Γ s → (toFOLanguage L).Term (Empty ⊕ Fin n)
  | _, .var i => .var (Sum.inr i)
  | _, .func f ts => .func (L := toFOLanguage L) ⟨f, rfl⟩ (fun i => Term.toFO (ts i))

/-- An equation of `L` as the first-order sentence `∀ x̄, lhs = rhs`. -/
def Equation.toFOSentence (φ : L.Equation) : (toFOLanguage L).Sentence :=
  (φ.lhs.toFO.bdEqual φ.rhs.toFO).alls

/-- **The first-order theory of an equational theory**: the universal closures of its
equations. -/
def Theory.toFO (T : L.Theory) : (toFOLanguage L).Theory :=
  Equation.toFOSentence '' T

end MSLanguage

/-- **The category of models of a first-order theory**: Mathlib structures satisfying `T` (possibly
empty, unlike Mathlib's `Theory.ModelType`), with Mathlib homomorphisms `M →[L'] N`. -/
structure FOModelCat (L' : FirstOrder.Language.{u₄, u₅}) (T : L'.Theory) where
  /-- The underlying type. -/
  Carrier : Type w
  [struc : L'.Structure Carrier]
  [is_model : FirstOrder.Language.Theory.Model Carrier T]

attribute [instance] FOModelCat.struc FOModelCat.is_model

namespace FOModelCat

variable {L' : FirstOrder.Language.{u₄, u₅}} {T : L'.Theory}

/-- Models of a first-order theory with Mathlib homomorphisms. -/
instance : Category (FOModelCat.{w} L' T) where
  Hom A B := FirstOrder.Language.Hom L' A.Carrier B.Carrier
  id A := @FirstOrder.Language.Hom.id L' A.Carrier _
  comp f g := g.comp f
  id_comp f := FirstOrder.Language.Hom.comp_id f
  comp_id f := FirstOrder.Language.Hom.id_comp f
  assoc f g h := (FirstOrder.Language.Hom.comp_assoc f g h).symm

variable (L' T) in
/-- The forgetful functor to types. -/
def forget : FOModelCat.{w} L' T ⥤ Type w where
  obj A := A.Carrier
  map {A B} f :=
    TypeCat.ofHom fun x => (show FirstOrder.Language.Hom L' A.Carrier B.Carrier from f) x

/-- Two first-order models on the same carrier with equal structures are equal. -/
lemma mk_eq {X : Type w} (s₁ s₂ : L'.Structure X) (h : s₁ = s₂)
    (m₁ : @FirstOrder.Language.Theory.Model L' X s₁ T)
    (m₂ : @FirstOrder.Language.Theory.Model L' X s₂ T) :
    @FOModelCat.mk L' T X s₁ m₁ = @FOModelCat.mk L' T X s₂ m₂ := by
  subst h
  rfl

/-- A morphism of first-order models as a function on the carriers. -/
abbrev app {A B : FOModelCat.{w} L' T} (f : A ⟶ B) : A.Carrier → B.Carrier :=
  (show FirstOrder.Language.Hom L' A.Carrier B.Carrier from f)

/-- Two morphisms of first-order models are equal if their functions agree. -/
lemma app_ext {A B : FOModelCat.{w} L' T} {f g : A ⟶ B} (h : ∀ x, app f x = app g x) : f = g :=
  DFunLike.ext (F := FirstOrder.Language.Hom L' A.Carrier B.Carrier) _ _ h

/-- The function of a composite of morphisms of first-order models is the composite of their
functions. -/
lemma app_comp {A B D : FOModelCat.{w} L' T} (f : A ⟶ B) (g : B ⟶ D) (x : A.Carrier) :
    app (f ≫ g) x = app g (app f x) := rfl

/-- The function of an `eqToHom` between first-order models is a cast. -/
lemma app_eqToHom {A B : FOModelCat.{w} L' T} (h : A = B) (x : A.Carrier) :
    app (eqToHom h) x = cast congr(FOModelCat.Carrier $h) x := by
  subst h
  rfl

end FOModelCat

end UlmerBialgebras.Paper
