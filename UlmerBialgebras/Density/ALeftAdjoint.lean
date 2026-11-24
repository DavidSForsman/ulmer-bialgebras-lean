module

public import UlmerBialgebras.Density.AAdjointRep

/-!
# The `A`-accessible adjoint functor theorem for left adjoints

`AAdjoint.lean` proves that a pseudonatural family of right adjoints for the representables
of a 1-cell `f : c ⟶ d`, represented by a 1-cell, produces a right adjoint of `f` in `K`.
This file proves the mirror-image statement for a pseudonatural family of *left* adjoints.

* `UlmerBialgebras.ALeftAdjointFamily` — a pseudonatural family (`UlmerBialgebras.AHomFamily`) of
  functors `K(x, d) ⥤ K(x, c)`, `x ∈ A`, each *left* adjoint to `K(x, f)`, whose pseudonaturality
  isomorphisms are the mates of the identity squares (stated through the units);
* `UlmerBialgebras.ALeftAdjointFamily.counit_nat` — the corresponding compatibility of the counits,
  derived from the compatibility of the units by the triangle identities;
* `UlmerBialgebras.ALeftAdjointFamily.toARightAdjointFamily` — once the family is represented by a
  1-cell `g`, post-composition with `f` is a family of right adjoints for the representables
  of `g`;
* `UlmerBialgebras.ALeftAdjointFamily.exists_twoAdj_left_of_representation` — the adjoint functor
  theorem: for `A` locally dense, `f` has a left adjoint in `K`.

The proof reduces to the right-adjoint case: once the family is represented by a 1-cell
`g`, the transported adjunctions `K(x, g) ⊣ K(x, f)` exhibit post-composition with `f` as a
pseudonatural family of right adjoints for the representables of `g`.

## Main results

* `UlmerBialgebras.ALeftAdjointFamily`: a pseudonatural family of functors on the
  `A`-representables, each left adjoint to post-composition with `f`, compatibly with the units.
* `UlmerBialgebras.ALeftAdjointFamily.toARightAdjointFamily`: for a family represented by a 1-cell
  `g`, post-composition with `f` is a family of right adjoints of the representables of `g`.
* `UlmerBialgebras.ALeftAdjointFamily.exists_twoAdj_left_of_representation`: if `A` is locally
  dense, the representing 1-cell `g` is left adjoint to `f` in `K` (the density step of the proof of
  Theorem 7.4).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-! ## Compatible families of left adjoints -/

/-- A **compatible family of left adjoints** for the representables of `f : c ⟶ d`: a
pseudonatural family of functors `K(x, d) ⥤ K(x, c)`, `x ∈ A`, each left adjoint to
`K(x, f)`, whose pseudonaturality isomorphisms are the mates of the identity squares — the
last condition being expressed as their compatibility with the units. -/
structure ALeftAdjointFamily (A : ObjectProperty Obj) {c d : Obj} (f : c ⟶ d)
    extends AHomFamily A d c where
  /-- Each functor of the family is left adjoint to the corresponding representable. -/
  adj : ∀ ⦃x : Obj⦄ (hx : A x), fn hx ⊣ postcomp x f
  /-- The pseudonaturality isomorphisms are the mates: they are compatible with the
  units. -/
  unit_nat : ∀ ⦃x y : Obj⦄ (hx : A x) (hy : A y) (u : x ⟶ y) (k : y ⟶ d),
    (adj hx).unit.app (u ≫ k) ≫ ((nat hx hy u).hom.app k ▷ f)
      = (u ◁ (adj hy).unit.app k) ≫ eqToHom (Category.assoc u ((fn hy).obj k) f).symm

namespace ALeftAdjointFamily

variable {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}

/-- The counits of a compatible family of left adjoints are compatible with
pre-composition. -/
theorem counit_nat (F : ALeftAdjointFamily A f) ⦃x y : Obj⦄ (hx : A x) (hy : A y)
    (u : x ⟶ y) (k : y ⟶ c) :
    (F.fn hx).map (eqToHom (Category.assoc u k f)) ≫ (F.nat hx hy u).hom.app (k ≫ f) ≫
        (u ◁ (F.adj hy).counit.app k)
      = (F.adj hx).counit.app (u ≫ k) := by
  have hR : ((F.adj hx).unit.app ((u ≫ k) ≫ f) ≫
      (postcomp x f).map ((F.adj hx).counit.app (u ≫ k))) = 𝟙 _ :=
    (F.adj hx).right_triangle_components (u ≫ k)
  have hnat : (F.adj hx).unit.app ((u ≫ k) ≫ f) ≫
      (postcomp x f).map ((F.fn hx).map (eqToHom (Category.assoc u k f)))
      = eqToHom (Category.assoc u k f) ≫ (F.adj hx).unit.app (u ≫ (k ≫ f)) :=
    ((F.adj hx).unit.naturality (eqToHom (Category.assoc u k f))).symm
  have hry : (F.adj hy).unit.app (k ≫ f) ≫ ((F.adj hy).counit.app k ▷ f) = 𝟙 _ :=
    (F.adj hy).right_triangle_components k
  refine ((F.adj hx).homEquiv ((u ≫ k) ≫ f) (u ≫ k)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hR, Functor.map_comp]
  simp only [reassoc_of% hnat]
  simp only [postcomp_map, Bicategory.comp_whiskerRight]
  rw [← Category.assoc ((F.adj hx).unit.app (u ≫ (k ≫ f))), F.unit_nat hx hy u (k ≫ f),
    Bicategory.Strict.whisker_assoc' u ((F.adj hy).counit.app k) f]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (u ◁ (F.adj hy).unit.app (k ≫ f)), ← Bicategory.whiskerLeft_comp, hry]
  simp

end ALeftAdjointFamily

/-! ## From a representation to an adjunction in `K` -/

section Transport

variable {C D : Type*} [Category C] [Category D] {L L' : C ⥤ D} {R : D ⥤ C}

/-- The counit of an adjunction transported along an isomorphism of the left adjoints. -/
lemma counit_ofNatIsoLeft (adj : L ⊣ R) (h : L ≅ L') (X : D) :
    (adj.ofNatIsoLeft h).counit.app X = h.inv.app (R.obj X) ≫ adj.counit.app X := by
  simp [Adjunction.ofNatIsoLeft]

end Transport

namespace ALeftAdjointFamily

variable {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d}
variable (F : ALeftAdjointFamily A f) (P : F.toAHomFamily.Representation)

/-- The adjunction `K(x, g) ⊣ K(x, f)` obtained by transporting the given adjunction along
the comparison isomorphism of the representation. -/
def adjRep ⦃x : Obj⦄ (hx : A x) : postcomp x P.g ⊣ postcomp x f :=
  (F.adj hx).ofNatIsoLeft (P.iso hx).symm

/-- The counit of `adjRep` at `k` is the comparison isomorphism at `k ≫ f`, followed by
the counit of the given adjunction. -/
lemma counit_adjRep_app ⦃x : Obj⦄ (hx : A x) (k : x ⟶ c) :
    (F.adjRep P hx).counit.app k
      = (P.iso hx).hom.app (k ≫ f) ≫ (F.adj hx).counit.app k :=
  counit_ofNatIsoLeft (F.adj hx) (P.iso hx).symm k

/-- Post-composition with `f`, as a compatible family of right adjoints for the
representables of the representing 1-cell `g`: this is the family of adjunctions
`K(x, g) ⊣ K(x, f)`, and its Beck–Chevalley condition is the compatibility of the counits
with pre-composition. -/
def toARightAdjointFamily : ARightAdjointFamily A P.g where
  toAHomFamily := AHomFamily.ofOneCell A f
  adj _ hx := F.adjRep P hx
  counit_nat := by
    intro x y hx hy u k
    have hcx := F.counit_adjRep_app P hx (u ≫ k)
    have hcy := F.counit_adjRep_app P hy k
    have hcn := F.counit_nat hx hy u k
    have hiso := (P.iso hx).hom.naturality (eqToHom (Category.assoc u k f))
    simp only [AHomFamily.ofOneCell, eqToIso.inv, eqToHom_app, Bicategory.eqToHom_whiskerRight,
      hcx, hcy, ← hcn, postcomp_map] at *
    rw [← Category.assoc ((P.iso hx).hom.app ((u ≫ k) ≫ f)), ← hiso,
        Category.assoc (obj := _ ⟶ _),
      ← Category.assoc ((P.iso hx).hom.app (u ≫ (k ≫ f))), P.iso_nat hx hy u (k ≫ f)]
    simp [Bicategory.whiskerLeft_comp]

/-- **The `A`-accessible adjoint functor theorem for left adjoints, with a representation
given**: if `A` is locally dense and the compatible family of representable left adjoints of
`f` is induced by a 1-cell `g`, then `g ⊣ f` in `K`. -/
theorem exists_twoAdj_left_of_representation (hA : IsACellDense A) :
    Nonempty (TwoAdj P.g f) :=
  exists_twoAdj_of_isACellDense_of_representation hA (F.toARightAdjointFamily P)
    (AHomFamily.ofOneCellRepresentation f)

end ALeftAdjointFamily

namespace ALeftAdjointFamily

variable {A : ObjectProperty Obj} {c d : Obj} {f : c ⟶ d} {g : d ⟶ c}

end ALeftAdjointFamily

end UlmerBialgebras
