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

section TwoCat

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Section 2.2: PIE reflection candidate functors -/

namespace Product

/-- The candidate comparison functor `K(x, pt) ⥤ ∀ i, K(x, c i)` for a candidate product cone. -/
@[simps]
def candHomFunctor {ι : Type sι} {c : ι → Obj} (pt : Obj) (π : ∀ i, pt ⟶ c i) (x : Obj) :
    (x ⟶ pt) ⥤ (∀ i, (x ⟶ c i)) where
  obj h i := h ≫ π i
  map α i := α ▷ π i
  map_id h := funext fun i => Bicategory.id_whiskerRight h (π i)
  map_comp α β := funext fun i => Bicategory.comp_whiskerRight α β (π i)

end Product

namespace Inserter

variable {a b : Obj} {f g : a ⟶ b}

/-- The structure 2-cell of a candidate inserter cone, transported to the hom-category. -/
def candHomCell {pt : Obj} (u : pt ⟶ a) (φ : u ≫ f ⟶ u ≫ g) (x : Obj) (k : x ⟶ pt) :
    (postcomp x f).obj (k ≫ u) ⟶ (postcomp x g).obj (k ≫ u) :=
  eqToHom (Category.assoc k u f) ≫ (k ◁ φ) ≫ eqToHom (Category.assoc k u g).symm

/-- The candidate comparison functor `K(x, pt) ⥤ Ins(f ∘ -, g ∘ -)` for a candidate inserter cone.
-/
@[simps]
def candHomFunctor (pt : Obj) (u : pt ⟶ a) (φ : u ≫ f ⟶ u ≫ g) (x : Obj) :
    (x ⟶ pt) ⥤ Ins (postcomp x f) (postcomp x g) where
  obj k := ⟨k ≫ u, candHomCell u φ x k⟩
  map α := ⟨α ▷ u, UlmerBialgebras.Inserter.cell_naturality x u φ α⟩
  map_id k := Ins.hom_ext (Bicategory.id_whiskerRight k u)
  map_comp α β := Ins.hom_ext (Bicategory.comp_whiskerRight α β u)

end Inserter

namespace Equifier

variable {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g}

/-- The candidate comparison functor `K(x, pt) ⥤ Eq(η ∘ -, θ ∘ -)` for a candidate equifier cone. -/
@[simps]
def candHomFunctor (pt : Obj) (e : pt ⟶ a) (hcond : e ◁ η = e ◁ θ) (x : Obj) :
    (x ⟶ pt) ⥤ Equif (postcompNat x η) (postcompNat x θ) where
  obj k := ⟨k ≫ e, UlmerBialgebras.Equifier.equifProp_comp x e hcond k⟩
  map α := ObjectProperty.homMk (α ▷ e)
  map_id k := ObjectProperty.hom_ext _ (Bicategory.id_whiskerRight k e)
  map_comp α β := ObjectProperty.hom_ext _ (Bicategory.comp_whiskerRight α β e)

end Equifier

/-! ## Definition 3.1: bialgebraic data -/

/-- **Definition 3.1** ([forsman2026syntactic]; after Ulmer [Ulmer1977Bialgebras]).
A bialgebraic datum on an object `c`:
supports `f, g : c ⟶ x` and `f', g' : c ⟶ y`, the inserter `(u', φ)` of `f` and `g`, and the
equations `α, β : f' u' ⟹ g' u'` (written `u' ≫ f'` in diagrammatic order). -/
structure BialgDatum where
  /-- The base object `c`. -/
  c : Obj
  /-- The codomain of the function supports. -/
  x : Obj
  /-- The codomain of the equational supports. -/
  y : Obj
  /-- The function arity support. -/
  f : c ⟶ x
  /-- The function coarity support. -/
  g : c ⟶ x
  /-- The equational arity support. -/
  f' : c ⟶ y
  /-- The equational coarity support. -/
  g' : c ⟶ y
  /-- The object of pre-bialgebras: the inserter of `f` and `g`. -/
  ins : Inserter f g
  /-- The first equation. -/
  α : ins.u ≫ f' ⟶ ins.u ≫ g'
  /-- The second equation. -/
  β : ins.u ≫ f' ⟶ ins.u ≫ g'

/-- **Definition 3.1 (2), (3)** ([forsman2026syntactic]). An object of bialgebras of a bialgebraic
datum `B` is an equifier `E` of `α, β`; the canonical morphism `u_B : Bialg(B) → c` is `e ≫ u'`. -/
abbrev BialgDatum.uB (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) : E.pt ⟶ B.c :=
  E.e ≫ B.ins.u

/-- **Remark 3.2**, footnote ([forsman2026syntactic]): `r : c ⟶ c` is an `f`-relative left adjoint
of `g : c ⟶ x` in `K`: the hom-functors `K(z, c)(r ∘ -, -)` and `K(z, x)(f ∘ -, g ∘ -)` are
naturally isomorphic, naturally in `z` (defined via representables). -/
structure RelLeftAdj2 {c x : Obj} (f g : c ⟶ x) (r : c ⟶ c) where
  /-- The bijection on 2-cells, for 1-cells `p, q : z ⟶ c`. -/
  equiv : ∀ {z : Obj} (p q : z ⟶ c), (p ≫ r ⟶ q) ≃ (p ≫ f ⟶ q ≫ g)
  /-- Naturality in the first variable (pre-composition with a 2-cell). -/
  nat_left : ∀ {z : Obj} {p p' q : z ⟶ c} (σ : p' ⟶ p) (γ : p ≫ r ⟶ q),
    equiv p' q ((σ ▷ r) ≫ γ) = (σ ▷ f) ≫ equiv p q γ
  /-- Naturality in the second variable. -/
  nat_right : ∀ {z : Obj} {p q q' : z ⟶ c} (γ : p ≫ r ⟶ q) (τ : q ⟶ q'),
    equiv p q' (γ ≫ τ) = equiv p q γ ≫ (τ ▷ g)
  /-- Naturality in `z` (pre-composition with a 1-cell). -/
  nat_z : ∀ {z z' : Obj} (h : z' ⟶ z) {p q : z ⟶ c} (γ : p ≫ r ⟶ q),
    equiv (h ≫ p) (h ≫ q) (eqToHom (Category.assoc h p r) ≫ (h ◁ γ))
      = eqToHom (Category.assoc h p f) ≫ (h ◁ equiv p q γ) ≫ eqToHom (Category.assoc h q g).symm

end TwoCat

/-! ## Proposition 3.15: the bialgebraic datum `B_{M,T}` -/

section ModelDatum

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj]
variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
  (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]
variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- The bialgebraic datum `B_{M,T}` of **Proposition 3.15** ([forsman2026syntactic]): the function
supports are the 1-cells `M(t)` for the function arity and coarity terms, the equational supports
the 1-cells `M(t)` for the equational arity and coarity terms, the inserter is `M^σ`, and the
equations are `(p̄_M)_{(p,q)}` and `(q̄_M)_{(p,q)}`. -/
noncomputable def modelDatum : BialgDatum (Obj := Obj) where
  c := (M.P0 sg).pt
  x := (M.Pfn sg).pt
  y := (M.Peq sg T).pt
  f := M.domCell sg
  g := M.codCell sg
  f' := (M.Peq sg T).lift (fun r => M.tm sg (T.dom r))
  g' := (M.Peq sg T).lift (fun r => M.tm sg (T.cod r))
  ins := M.sigIns sg
  α := eqToHom (M.sigCell_eq sg T T.dom) ≫ M.lhsCell sg T ≫
    eqToHom (M.sigCell_eq sg T T.cod).symm
  β := eqToHom (M.sigCell_eq sg T T.dom) ≫ M.rhsCell sg T ≫
    eqToHom (M.sigCell_eq sg T T.cod).symm

end ModelDatum

end UlmerBialgebras.Paper
