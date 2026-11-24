module

public import UlmerBialgebras.Paper.Sec4DefsExt
public import Foundations.CategoryTheory.Limits.PushoutDescInl

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# The pushout endofunctor of Lemma 5.6

Let `f : c ⟶ c` be a 1-cell of a 2-category and `N` an inserter of `f` and `𝟙 c`, with
universal 2-cell `φ : f u ⟹ u`. For a span `X ←k— I —d→ N.pt`, write `A = u d`. Lemma 5.6
considers, for left Kan extensions `e₁ = (l₁, η₁)` of `A` and `e₂ = (l₂, η₂)` of `f A` along
`k`, the endofunctor `H = (l₁, η₁) +_{l₂} f_*(-)` of `LE(A, k)`.

## Main definitions

* `UlmerBialgebras.Inserter.phiAtId N m : f u m ⟹ u m`: the universal 2-cell `φ m` of an inserter of
  `f` and `𝟙 c` at a 1-cell `m` into it, with `𝟙 c` composed away.
* `UlmerBialgebras.LeftExt.pull k ψ : LE(e, k) ⥤ LE(e', k)`, `(l, η) ↦ (l, η • ψ)`, for a 2-cell
  `ψ : e' ⟹ e`. For `ψ = φ d` this is the functor `id_*` of Lemma 4.6 (2), up to the identity
  `l id = l`.
* `UlmerBialgebras.LeftExt.pushoutStep k ψ e₁ he₂ : LE(A, k) ⥤ LE(A, k)`, for `ψ : f A ⟹ A`: the
  endofunctor `H`. Its value at `(l', η')` is the pushout in `K(X, c)` of `α : l₂ ⟹ l₁` and
  `α' : l₂ ⟹ f l'`, the 2-cells induced by `η₁ • ψ` and `f η'` out of the initial `e₂`, with unit
  `η₁` followed by the coprojection of `l₁`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6 (with Lemma 4.6 (2))
* [G. M. Kelly, *A unified treatment of transfinite constructions for free algebras, free
  monoids, colimits, associated sheaves, and so on*][kellyUnifiedTreatmentTransfinite1980]
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- For an inserter `N` of `f : c ⟶ c` and `𝟙 c`, the universal 2-cell at a 1-cell
`m : x ⟶ N.pt`, `φ m : f u m ⟹ u m`: the 2-cell `N.phiAt m` with `𝟙 c` composed away. -/
def Inserter.phiAtId {c : Obj} {f : c ⟶ c} (N : Inserter f (𝟙 c)) {x : Obj}
    (m : x ⟶ N.pt) : (m ≫ N.u) ≫ f ⟶ m ≫ N.u :=
  N.phiAt m ≫ eqToHom (Category.comp_id _)

/-- Pulling a left extension back along a 2-cell `ψ : e' ⟹ e`: the functor
`LE(e, k) ⥤ LE(e', k)`, `(l, η) ↦ (l, η • ψ)`. -/
@[simps]
def LeftExt.pull {I X c : Obj} (k : I ⟶ X) {e e' : I ⟶ c} (ψ : e' ⟶ e) :
    LeftExt k e ⥤ LeftExt k e' where
  obj L := LeftExt.mk L.ext (ψ ≫ L.unit)
  map {L L'} α := LeftExt.homMk (LeftExt.homCell (L := L) (L' := L') α)
    ((Category.assoc ψ _ _).trans (congrArg (ψ ≫ ·) (LeftExt.w α)))

/-- **The endofunctor `H = (l₁, η₁) +_{l₂} f_*(-)` of Lemma 5.6** ([forsman2026syntactic]). Let
`ψ : f A ⟹ A`, let `e₁ = (l₁, η₁)` be a left extension of `A` and `e₂ = (l₂, η₂)` an initial left
extension of `f A` along `k`. The value of `H` at `(l', η')` is the pushout `l₁ +_{l₂} f l'` in
`K(X, c)` of the 2-cells `α : l₂ ⟹ l₁` and `α' : l₂ ⟹ f l'` out of `e₂` (to `(l₁, η₁ • ψ)` and to
`f_*(l', η')`), with unit `η₁` followed by the coprojection of `l₁`. -/
noncomputable def LeftExt.pushoutStep {I X c : Obj} (k : I ⟶ X) {f : c ⟶ c} {A : I ⟶ c}
    (ψ : A ≫ f ⟶ A) (e₁ : LeftExt k A) {e₂ : LeftExt k (A ≫ f)} (he₂ : IsInitial e₂)
    [HasPushouts (X ⟶ c)] : LeftExt k A ⥤ LeftExt k A where
  obj x := LeftExt.mk (pushout (LeftExt.homCell (he₂.to ((LeftExt.pull k ψ).obj e₁)))
      (LeftExt.homCell (he₂.to ((LeftExt.push k A f).obj x))))
    (e₁.unit ≫ k ◁ pushout.inl _ _)
  map {x x'} g := LeftExt.homMk (pushout.desc (pushout.inl _ _)
      ((LeftExt.homCell (L := x) (L' := x') g ▷ f) ≫ pushout.inr _ _)
      (pushout_condition_of_comp _ _ _ _ (congrArg LeftExt.homCell
        (he₂.hom_ext (he₂.to ((LeftExt.push k A f).obj x) ≫ (LeftExt.push k A f).map g)
          (he₂.to ((LeftExt.push k A f).obj x'))))))
    ((Category.assoc _ _ _).trans (congrArg (e₁.unit ≫ ·)
      ((Bicategory.whiskerLeft_comp k _ _).symm.trans (congrArg (k ◁ ·) (pushout.inl_desc _ _ _)))))
  map_id x := LeftExt.hom_ext
    (pushout_desc_inl_id _ _ (Bicategory.id_whiskerRight x.ext f) _)
  map_comp g g' := LeftExt.hom_ext
    (pushout_desc_inl_comp _ _ _ _ _ _
      (Bicategory.comp_whiskerRight (LeftExt.homCell g) (LeftExt.homCell g') f) _ _ _)

end UlmerBialgebras
