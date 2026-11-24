module

public import UlmerBialgebras.Monadicity.HomCatComp
public import UlmerBialgebras.Models.BicatTwoCat

/-!
# Density of a class of objects in a 2-category

The `A`-properties of Definition 7.2 measure an object `c` of a 2-category `K` through its
hom-categories `K(a, c)` for `a` in a class `A` of "small" objects.  For that to determine `c`
one needs `A` to be **dense** (adequate) in `K`: the restricted Yoneda 2-functor

```
  K ⟶ Ps[A^op, CAT],   c ↦ K(-, c)|_A
```

should be 2-fully faithful.  This file writes that condition out elementarily, in two
halves, and both halves are stated *componentwise* so that no coherence is hidden in
2-categorical notation.

* `UlmerBialgebras.ACellFamily A p q` — a family of natural transformations
  `K(x, p) ⟶ K(x, q)`, `x ∈ A`, compatible with pre-composition; every 2-cell `p ⟶ q`
  gives one (`UlmerBialgebras.ACellFamily.ofCell`).
* `UlmerBialgebras.IsACellDense A` — **local 2-full-faithfulness**: every such family comes from a
  unique 2-cell.
* `UlmerBialgebras.AHomFamily A d c` — a *pseudonatural* family of functors
  `K(x, d) ⥤ K(x, c)`, `x ∈ A`: functors together with comparison isomorphisms for
  pre-composition, subject to the unit and cocycle coherence conditions.  Every 1-cell
  `g : d ⟶ c` gives one, with identity comparisons (`UlmerBialgebras.AHomFamily.ofOneCell`).
* `UlmerBialgebras.AHomFamily.Representation` — a 1-cell inducing a given family, i.e. an object of
  the essential fibre of the restricted Yoneda 2-functor over it.
* `UlmerBialgebras.IsAHomDense A` — **essential surjectivity on 1-cells**: every pseudonatural
  family is induced by a 1-cell.
* `UlmerBialgebras.IsADense A` — density: both halves.

`AAdjoint.lean` uses density to prove the `A`-accessible adjoint functor theorems, and
`VCatCellDense.lean` verifies the local half for `CAT_V` and the small `V`-categories.

## Main results

* `UlmerBialgebras.ACellFamily`: a family of natural transformations `K(x, p) ⟶ K(x, q)`, `x ∈ A`,
  compatible with pre-composition.
* `UlmerBialgebras.IsACellDense`: every `UlmerBialgebras.ACellFamily` comes from a unique 2-cell.
* `UlmerBialgebras.AHomFamily`: a pseudonatural family of functors `K(x, d) ⥤ K(x, c)`, `x ∈ A`.
* `UlmerBialgebras.IsAHomDense`: every `UlmerBialgebras.AHomFamily` is induced by a 1-cell of `K`.
* `UlmerBialgebras.IsADense`: both halves together. This is strictly stronger than the bi-density
  of Definition 7.1 (which only requires an equivalence of categories).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Families of 2-cells -/

/-- A **family of 2-cells on the `A`-representables** from `p` to `q`: for every `x ∈ A` a
natural transformation `K(x, p) ⟶ K(x, q)`, compatible with pre-composition along the
1-cells of `K` whose source and target lie in `A`.

The compatibility is stated componentwise: at `k : y ⟶ c` and `u : x ⟶ y` it says that
whiskering the component at `k` by `u` is the component at `u ≫ k`, modulo associativity. -/
structure ACellFamily (A : ObjectProperty Obj) {c d : Obj} (p q : c ⟶ d) where
  /-- The component at an object of `A`. -/
  app : ∀ ⦃x : Obj⦄, A x → (postcomp x p ⟶ postcomp x q)
  /-- Compatibility with pre-composition. -/
  naturality : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ c),
    u ◁ ((app hy).app k)
      = eqToHom (Category.assoc u k p).symm ≫ (app hx).app (u ≫ k) ≫ eqToHom (Category.assoc u k q)

namespace ACellFamily

variable {A : ObjectProperty Obj} {c d : Obj} {p q : c ⟶ d}

/-- The family of 2-cells induced by a 2-cell of `K`. -/
@[simps]
def ofCell (α : p ⟶ q) : ACellFamily A p q where
  app x _ := postcompNat x α
  naturality := fun _ _ _ _ u k => by
    simp

end ACellFamily

/-- **The local half of density**: a 2-cell of `K` is the same thing as a compatible family
of 2-cells on the `A`-representables. -/
def IsACellDense (A : ObjectProperty Obj) : Prop :=
  ∀ ⦃c d : Obj⦄ ⦃p q : c ⟶ d⦄ (Φ : ACellFamily A p q),
    ∃! α : p ⟶ q, ∀ ⦃x : Obj⦄ (hx : A x), postcompNat x α = Φ.app hx

namespace IsACellDense

variable {A : ObjectProperty Obj}

/-- Two 2-cells with the same image on the `A`-representables are equal. -/
theorem cell_ext (h : IsACellDense A) {c d : Obj} {p q : c ⟶ d} {α β : p ⟶ q}
    (hαβ : ∀ ⦃x : Obj⦄, A x → postcompNat x α = postcompNat x β) : α = β := by
  obtain ⟨γ, _, huniq⟩ := h (ACellFamily.ofCell (A := A) β)
  rw [huniq α (fun x hx => by rw [hαβ hx]; rfl), huniq β (fun _ _ => rfl)]

end IsACellDense

/-! ## Pseudonatural families of functors -/

/-- A **pseudonatural family of functors** on the `A`-representables from `d` to `c`: for
every `x ∈ A` a functor `K(x, d) ⥤ K(x, c)`, together with comparison isomorphisms with
pre-composition, subject to the unit and cocycle conditions.

This is written out componentwise. It carries the 1-cell comparison isomorphisms and their
coherence laws, but not the 2-cell axiom of a genuine pseudonatural transformation:
`UlmerBialgebras.Paper.PsFamily` (Definition 7.1) extends it with that axiom, `nat₂`, and the
definition of bi-density uses `PsFamily`. -/
structure AHomFamily (A : ObjectProperty Obj) (d c : Obj) where
  /-- The functor at an object of `A`. -/
  fn : ∀ ⦃x : Obj⦄, A x → ((x ⟶ d) ⥤ (x ⟶ c))
  /-- The comparison isomorphism for pre-composition along `u : x ⟶ y`. -/
  nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y),
    precomp u d ⋙ fn hx ≅ fn hy ⋙ precomp u c
  /-- The comparison for an identity is the identity. -/
  nat_id : ∀ ⦃x : Obj⦄ (hx : A x) (k : x ⟶ d),
    (nat hx hx (𝟙 x)).hom.app k
      = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.id_comp])
  /-- The comparisons compose. -/
  nat_comp : ∀ ⦃x y z : Obj⦄ (hx : A x) (hy : A y) (hz : A z) (u : x ⟶ y) (v : y ⟶ z)
      (k : z ⟶ d),
    (nat hx hz (u ≫ v)).hom.app k
      = eqToHom (by simp only [Functor.comp_obj, precomp_obj, Category.assoc]) ≫
          (nat hx hy u).hom.app (v ≫ k) ≫
          (u ◁ (nat hy hz v).hom.app k) ≫ eqToHom (Category.assoc u v ((fn hz).obj k)).symm

namespace AHomFamily

variable {A : ObjectProperty Obj} {d c : Obj}

/-- The pseudonatural family induced by a 1-cell `g : d ⟶ c`: post-composition with `g`,
with identity comparisons. -/
def ofOneCell (A : ObjectProperty Obj) (g : d ⟶ c) : AHomFamily A d c where
  fn x _ := postcomp x g
  nat := fun _ _ _ _ u => eqToIso (postcomp_comp_precomp u g).symm
  nat_id := fun _ _ _ => by
    simp only [eqToIso.hom, eqToHom_app]
  nat_comp := fun _ _ _ _ _ _ u v k => by
    simp only [eqToIso.hom, eqToHom_app]
    rw [Bicategory.whiskerLeft_eqToHom]
    simp

/-- The comparison isomorphisms of a pseudonatural family are compatible with equalities of
1-cells. -/
lemma nat_congr (G : AHomFamily A d c) ⦃x y : Obj⦄ (hx : A x) (hy : A y) {u u' : x ⟶ y}
    (h : u = u') (k : y ⟶ d) :
    (G.nat hx hy u).hom.app k
      = eqToHom (by rw [h]) ≫ (G.nat hx hy u').hom.app k ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The comparison isomorphisms of a pseudonatural family are compatible with equalities of
the 1-cell at which they are evaluated. -/
lemma nat_app_congr (G : AHomFamily A d c) ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y)
    {k k' : y ⟶ d} (h : k = k') :
    (G.nat hx hy u).hom.app k
      = eqToHom (by rw [h]) ≫ (G.nat hx hy u).hom.app k' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- A **representation** of a pseudonatural family: a 1-cell of `K` inducing it. -/
structure Representation (G : AHomFamily A d c) where
  /-- The representing 1-cell. -/
  g : d ⟶ c
  /-- The comparison of the family with post-composition by `g`. -/
  iso : ∀ ⦃x : Obj⦄ (hx : A x), postcomp x g ≅ G.fn hx
  /-- The comparison is compatible with the pseudonaturality isomorphisms. -/
  iso_nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d),
    (iso hx).hom.app (u ≫ k) ≫ (G.nat hx hy u).hom.app k
      = eqToHom (Category.assoc u k g) ≫ (u ◁ (iso hy).hom.app k)

/-- The tautological representation of the family induced by a 1-cell. -/
def ofOneCellRepresentation (g : d ⟶ c) : (ofOneCell A g).Representation where
  g := g
  iso := fun x _ => Iso.refl (postcomp x g)
  iso_nat := fun _ _ _ _ u k => by
    simp only [ofOneCell, eqToIso.hom, eqToHom_app, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
    rw [show u ◁ 𝟙 ((postcomp _ g).obj k) = 𝟙 _ from Bicategory.whiskerLeft_id u _]
    simp

end AHomFamily

/-- **The 1-cell half of density**: every pseudonatural family of functors on the
`A`-representables is induced by a 1-cell of `K`. -/
def IsAHomDense (A : ObjectProperty Obj) : Prop :=
  ∀ ⦃d c : Obj⦄ (G : AHomFamily A d c), Nonempty G.Representation

/-- **`A` is dense in `K`** (a variation of [hofstraInnerAutoequivalencesGeneral2024],
Definition 6.2; strictly stronger than Definition 7.1 of [forsman2026syntactic]): the restricted
Yoneda 2-functor `c ↦ K(-, c)|_A` is 2-fully faithful, i.e. 2-cells are exactly the compatible
families of 2-cells on the `A`-representables (`UlmerBialgebras.IsACellDense`) and every
pseudonatural family of functors between `A`-representables is induced by a 1-cell
(`UlmerBialgebras.IsAHomDense`). -/
structure IsADense (A : ObjectProperty Obj) : Prop where
  /-- Density on 2-cells. -/
  cell : IsACellDense A
  /-- Density on 1-cells. -/
  hom : IsAHomDense A

end UlmerBialgebras
