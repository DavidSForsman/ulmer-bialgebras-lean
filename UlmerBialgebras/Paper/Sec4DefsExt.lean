module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Kan.KanProduct
public import UlmerBialgebras.Kan.KanInserter
public import UlmerBialgebras.Kan.KanEquifier
public import UlmerBialgebras.Basic.InsEqCat

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Categories of extensions: definitions for Remark 4.5 and Lemma 4.6

`LeftExt k d` is the category `LE(d, k)` of left extensions of `d : I → c` along `k : I → X`
(Definition 4.2). Its objects are pairs `(l, η : d ⟹ l k)`, written `⟨l, η : d ⟶ k ≫ l⟩` in the
library's diagrammatic order. `LeftExt.push k d f` is the functor
`f_* : LE(d, k) → LE(f d, k)` of Definition 4.4.

## Main definitions

* `UlmerBialgebras.LeftExt.forget k d : LE(d, k) ⥤ K(X, c)`, `(l, η) ↦ l`.
* `UlmerBialgebras.LeftExt.pushTwisted k d ψ : LE(d, k) ⥤ LE(f d, k)`, `(l, η) ↦ (g l, (g η) • ψ)`,
  post-composition with `g` twisted by a 2-cell `ψ : f d ⟹ g d`.
* `UlmerBialgebras.Inserter.twistedPush`: the functor `g_*` of Lemma 4.6 (2), twisted by the
  inserter cell `φ d`. `UlmerBialgebras.Inserter.leftExtToIns`: the comparison
  `LE(d, k) ⥤ Ins(f_*, g_*)`, `(l, η) ↦ ((u l, u η), φ l)`.
* `UlmerBialgebras.LeftExt.whiskerHom γ L : f_* L ⟶ (g, γ d)_* L`: whiskering a 2-cell `γ : f ⟹ g`
  by the extending 1-cell of `L`.
* `UlmerBialgebras.Equifier.twistedPush`: the functor `g_*` of Lemma 4.6 (3), twisted by `η e d`.
  `UlmerBialgebras.Equifier.pushNat₁` and `UlmerBialgebras.Equifier.pushNat₂` are
  `η_*, θ_* : f_* ⟹ g_*`. `UlmerBialgebras.Equifier.leftExtToEquif` is the comparison
  `LE(d, k) ⥤ Eq(η_*, θ_*)`, `(l, η) ↦ (e l, e η)`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions 4.2, 4.4, Remark 4.5, Lemma 4.6
* [R. Street, R. Walters, *Yoneda structures on 2-categories*]
  [streetYonedaStructures2categories1978]
-/

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## The forgetful functor and the twisted push -/

/-- The forgetful functor `LE(d, k) ⥤ K(X, c)`, `(l, η) ↦ l`. -/
@[simps]
def LeftExt.forget {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) : LeftExt k d ⥤ (X ⟶ c) where
  obj L := L.ext
  map α := LeftExt.homCell α

/-- Post-composition with `g`, twisted by a 2-cell `ψ : d ≫ f ⟶ d ≫ g`: the functor
`LE(d, k) ⥤ LE(f d, k)`, `(l, η) ↦ (g l, (g η) • ψ)`. -/
@[simps]
def LeftExt.pushTwisted {I X a b : Obj} (k : I ⟶ X) (d : I ⟶ a) {f g : a ⟶ b}
    (ψ : d ≫ f ⟶ d ≫ g) : LeftExt k d ⥤ LeftExt k (d ≫ f) where
  obj L := LeftExt.mk (L.ext ≫ g) (ψ ≫ (L.unit ▷ g) ≫ eqToHom (Category.assoc k L.ext g))
  map α := LeftExt.homMk (LeftExt.homCell α ▷ g)
    ((Category.assoc ψ _ _).trans (congrArg (ψ ≫ ·) (LeftExt.w ((LeftExt.push k d g).map α))))
  map_id L := LeftExt.hom_ext (Bicategory.id_whiskerRight L.ext g)
  map_comp _ _ := LeftExt.hom_ext (Bicategory.comp_whiskerRight _ _ g)

/-! ## Lemma 4.6 (2): inserters -/

section Ins

variable {a b : Obj} {f g : a ⟶ b}

/-- The functor `g_* : LE(u d, k) ⥤ LE(f u d, k)` of Lemma 4.6 (2),
`(l', η') ↦ (g l', (g η') • (φ d))`, twisted by the inserter cell `φ d = Inserter.strCell J d`. -/
abbrev Inserter.twistedPush (J : Inserter f g) {I X : Obj} (k : I ⟶ X) (d : I ⟶ J.pt) :
    LeftExt k (d ≫ J.u) ⥤ LeftExt k ((d ≫ J.u) ≫ f) :=
  LeftExt.pushTwisted k (d ≫ J.u) (Inserter.strCell J d)

/-- The comparison functor `F : LE(d, k) ⥤ Ins(f_*, g_*)` of Lemma 4.6 (2) of
[forsman2026syntactic],
`(l, η) ↦ ((u l, u η), φ l)`. -/
@[simps]
def Inserter.leftExtToIns (J : Inserter f g) {I X : Obj} (k : I ⟶ X) (d : I ⟶ J.pt) :
    LeftExt k d ⥤ Ins (LeftExt.push k (d ≫ J.u) f) (Inserter.twistedPush J k d) where
  obj L := ⟨(LeftExt.push k d J.u).obj L,
      LeftExt.homMk (Inserter.strCell J L.ext) (Inserter.strCell_isHom J k d L)⟩
  map {_ _} α := ⟨(LeftExt.push k d J.u).map α,
    LeftExt.hom_ext (Inserter.strCell_nat J (LeftExt.homCell α))⟩
  map_id L := Ins.hom_ext ((LeftExt.push k d J.u).map_id L)
  map_comp α β := Ins.hom_ext ((LeftExt.push k d J.u).map_comp α β)

end Ins

/-! ## Lemma 4.6 (3): equifiers -/

section Equif

variable {a b : Obj} {f g : a ⟶ b}

/-- Whiskering a 2-cell `γ : f ⟹ g` by the extending 1-cell of a left extension `L` is a morphism
of left extensions `f_* L ⟶ (g, γ d)_* L`. -/
def LeftExt.whiskerHom {I X : Obj} (k : I ⟶ X) {d : I ⟶ a} (γ : f ⟶ g) (L : LeftExt k d) :
    (LeftExt.push k d f).obj L ⟶ (LeftExt.pushTwisted k d (d ◁ γ)).obj L :=
  LeftExt.homMk (L.ext ◁ γ) (LeftExt.unit_whiskerLeft_whiskerLeft k γ L)

variable {η θ : f ⟶ g}

/-- The functor `g_* : LE(e d, k) ⥤ LE(f e d, k)` of Lemma 4.6 (3),
`(l', η') ↦ (g l', (g η') • (η e d))`. -/
abbrev Equifier.twistedPush (E : Equifier η θ) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt) :
    LeftExt k (d ≫ E.e) ⥤ LeftExt k ((d ≫ E.e) ≫ f) :=
  LeftExt.pushTwisted k (d ≫ E.e) ((d ≫ E.e) ◁ η)

/-- The natural transformation `η_* : f_* ⟹ g_*` of Lemma 4.6 (3), with components `η l'`. -/
@[simps]
def Equifier.pushNat₁ (E : Equifier η θ) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt) :
    LeftExt.push k (d ≫ E.e) f ⟶ Equifier.twistedPush E k d where
  app L := LeftExt.whiskerHom k η L
  naturality _ _ α := LeftExt.hom_ext (Eq.symm <| Bicategory.whisker_exchange (LeftExt.homCell α) η)

/-- The natural transformation `θ_* : f_* ⟹ g_*` of Lemma 4.6 (3), with components `θ l'`. It
lands in `g_*` because `e` equifies `η` and `θ`. -/
@[simps]
def Equifier.pushNat₂ (E : Equifier η θ) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt) :
    LeftExt.push k (d ≫ E.e) f ⟶ Equifier.twistedPush E k d where
  app L := LeftExt.homMk (L.ext ◁ θ)
    ((LeftExt.w (LeftExt.whiskerHom k θ L)).trans (congrArg (· ≫ _) (Equifier.cond_comp E d).symm))
  naturality _ _ α :=
    LeftExt.hom_ext (Eq.symm <| Bicategory.whisker_exchange (LeftExt.homCell α) θ)

/-- The comparison functor `F : LE(d, k) ⥤ Eq(η_*, θ_*)` of Lemma 4.6 (3) of
[forsman2026syntactic],
`(l, η) ↦ (e l, e η)`. -/
def Equifier.leftExtToEquif (E : Equifier η θ) {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt) :
    LeftExt k d ⥤ Equif (Equifier.pushNat₁ E k d) (Equifier.pushNat₂ E k d) :=
  Equif.liftFunctor (LeftExt.push k d E.e)
    (NatTrans.ext (funext fun L => LeftExt.hom_ext (Equifier.cond_comp E L.ext)))

end Equif

end UlmerBialgebras
