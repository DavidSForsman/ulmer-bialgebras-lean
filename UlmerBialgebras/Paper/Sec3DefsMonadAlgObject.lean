module

public import UlmerBialgebras.Paper.Sec3DefsLaxLimit
public import UlmerBialgebras.Models.ThyRepCatEval
public import UlmerBialgebras.Models.ThyRepCat
public import UlmerBialgebras.Examples.MonadModelK

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The universal property of `M^T` (Remark 3.17)

Remark 3.17 of the paper: "By the 2-categorical Yoneda lemma, `M^T` is characterized up to
isomorphism by an isomorphism of categories `K(x, M^T) ≅ K(x, M)^T`, natural in `x`, where `K(x, M)`
is the `Σ`-model in `CAT` induced by `M`." The universal property needs no assumption on `K`
beyond what a `Σ`-model needs: chosen finite products (`HasChosenFinProducts`, which chooses a
product of every `Fin n`-family, the nullary product included).

* `UlmerBialgebras.Paper.IsThyRep M sg T E Φ`: `(E, Φ)` represents `M^T`. Each
  `Φ x : K(x, E) ⥤ K(x, M)^T` is an isomorphism of categories (bijective on objects, full and
  faithful), and `Φ` is strictly 2-natural in `x`: precomposition with `k : x' → x` corresponds
  to `K(k, M)^T` (`Model.homThyMap`), and whiskering with `α : k ⇒ k'` to `K(α, M)^T`
  (`Model.homThyMap₂`).

Here `K(x, M)` is `Model.homModel M x`, a model in `Cat.{w, v}` (the hom-categories of `K`), and
`K(x, M)^T` is formed in `Cat.{w, v}` with chosen products, inserters and equifiers of `Cat.{w, v}`,
taken as hypotheses on `Cat` (not on `K`).

The Eilenberg–Moore example uses the `Σ_Mnd`-model of a monad, `MndK.model`, its algebra
equations `MndK.IsAlg`, and the `T_Lax`-algebra `MndK.emAlg` of a pair `(u, η)` satisfying them.

## Main definitions

* `UlmerBialgebras.Paper.IsThyRep`: `(E, Φ)` represents `M^T` (Remark 3.17).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Remark 3.17,
  Examples 3.20 (4)
* [R. Street, *The formal theory of monads*][STREET1972149]
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
  {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{w, v}] [HasChosenProductsOfSize.{s₂} Cat.{w, v}]
  [HasChosenInserters Cat.{w, v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{w, v}] [HasChosenEquifiers Cat.{w, v}]

/-- **`(E, Φ)` represents `M^T`** (Remark 3.17 of [forsman2026syntactic]): each
`Φ x : K(x, E) ⥤ K(x, M)^T` is an isomorphism of categories (bijective on objects, full and
faithful), strictly 2-natural in `x`: precomposition with `k : x' → x` followed by `Φ x'` is
`Φ x` followed by `K(k, M)^T`, and for a 2-cell `α : k ⇒ k'` and `a : x → E`, `Φ x'` sends
`α ▷ a` to the component of `K(α, M)^T` (`Model.homThyMap₂`) at `Φ x a`. The second equation is
up to the identifications of the endpoints given by the first (`ConjEq u v`:
`u = eqToHom _ ≫ v ≫ eqToHom _`). Only chosen finite products (nullary ones included) are
assumed of `K`, as a `Σ`-model needs; `K(x, M)^T` is formed in `Cat.{w, v}`. -/
def IsThyRep (E : Obj) (Φ : ∀ x : Obj, Cat.of (x ⟶ E) ⟶ (M.homModel x).thyObj sg T) : Prop :=
  (∀ x : Obj, Function.Bijective (Φ x).toFunctor.obj ∧ (Φ x).toFunctor.Full ∧
      (Φ x).toFunctor.Faithful) ∧
    (∀ {x x' : Obj} (k : x' ⟶ x), (precomp k E).toCatHom ≫ Φ x' = Φ x ≫ M.homThyMap x sg T k) ∧
    ∀ {x x' : Obj} {k k' : x' ⟶ x} (α : k ⟶ k') (a : x ⟶ E),
      ConjEq ((Φ x').toFunctor.map (α ▷ a))
        ((M.homThyMap₂ x sg T α).toNatTrans.app ((Φ x).toFunctor.obj a))

end UlmerBialgebras.Paper
