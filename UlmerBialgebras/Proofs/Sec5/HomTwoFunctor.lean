module

public import UlmerBialgebras.Paper.Sec3DefsTwoFun
public import UlmerBialgebras.Density.StrictOp
public import Foundations.CategoryTheory.Bicategory.StrictCoherence

/-!
# The hom 2-functors on the opposite of a full sub-2-category

For a class `A` of objects of a strict 2-category `K` and an object `c`, the representable
`K(−, c)` is a strict 2-functor `𝒜ᵒᵖ → Cat`, where `𝒜` is the full sub-2-category of `K` on `A`.
Post-composition with a 1-cell `g : d ⟶ c` is a 2-natural transformation `K(−, d) ⇒ K(−, c)`.
These are the local data of Theorem 7.4.

## Main definitions

* `UlmerBialgebras.Paper.FullSubOp`: the 2-category `𝒜ᵒᵖ`.
* `UlmerBialgebras.Paper.homTwoFunctor`: the strict 2-functor `K(−, c) : 𝒜ᵒᵖ → Cat`.
* `UlmerBialgebras.Paper.postcompLaxNat`: post-composition with `g`, a lax transformation with
  identity naturality cells.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 7.4
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory Bicategory TwoFun

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- The full sub-2-category of `Obj` on the objects in `A`. -/
abbrev FullSub (A : ObjectProperty Obj) : Type u :=
  InducedBicategory Obj (fun x : {x : Obj // A x} => x.1)

/-- The 1-cell opposite `𝒜ᵒᵖ` of the full sub-2-category on `A`. -/
abbrev FullSubOp (A : ObjectProperty Obj) : Type u := (FullSub A)ᵒᵖ

variable {A : ObjectProperty Obj}

/-- The underlying object of an object of `𝒜ᵒᵖ`. -/
abbrev FullSubOp.pt (x : FullSubOp A) : Obj := (show {x : Obj // A x} from x.unop).1

/-- The underlying 1-cell `pt y ⟶ pt x` of a 1-cell `x ⟶ y` of `𝒜ᵒᵖ`. -/
abbrev FullSubOp.hom {x y : FullSubOp A} (f : x ⟶ y) : FullSubOp.pt y ⟶ FullSubOp.pt x :=
  f.unop.hom

/-- The underlying 2-cell of a 2-cell of `𝒜ᵒᵖ`. -/
abbrev FullSubOp.hom₂ {x y : FullSubOp A} {f g : x ⟶ y} (η : f ⟶ g) :
    FullSubOp.hom f ⟶ FullSubOp.hom g :=
  η.unop2.hom

variable (A) in
/-- **The hom 2-functor** `K(−, c) : 𝒜ᵒᵖ → Cat`: `x ↦ K(x, c)`, and a 1-cell `u` of `𝒜` acts by
pre-composition. -/
def homTwoFunctor (c : Obj) : StrictTwoFunctor Cat.{w, v} (FullSubOp A) where
  obj x := Cat.of (FullSubOp.pt x ⟶ c)
  map f := (precomp c (FullSubOp.hom f)).toCatHom
  map₂ η := NatTrans.toCatHom₂ ((precomposing _ _ c).map (FullSubOp.hom₂ η))
  map_id x := Cat.ext (CategoryTheory.Functor.ext (fun k => Category.id_comp k)
    (fun _ _ α => Strict.id_whiskerLeft α))
  map_comp f g := Cat.ext (CategoryTheory.Functor.ext (fun k => Category.assoc _ _ k)
    (fun _ _ α => Strict.comp_whiskerLeft _ _ α))
  map₂_id f := by
    ext k
    exact id_whiskerRight _ k
  map₂_comp η θ := by
    ext k
    exact (comp_whiskerRight _ _ k)
  map₂_whiskerLeft f g h η := by
    ext k
    simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerLeft_app]
    exact Strict.whiskerRight_comp' _ _ k
  map₂_whiskerRight η h := by
    ext k
    simp only [Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app]
    exact Strict.whisker_assoc' _ _ k

/-- Post-composition with `g` commutes on the nose with pre-composition. -/
lemma postcomp_naturality {c d : Obj} (g : d ⟶ c) {x y : FullSubOp A} (f : x ⟶ y) :
    (postcomp (FullSubOp.pt x) g).toCatHom ≫ (homTwoFunctor A c).map f =
      (homTwoFunctor A d).map f ≫ (postcomp (FullSubOp.pt y) g).toCatHom :=
  Cat.ext (CategoryTheory.Functor.ext (fun k => (Category.assoc _ k g).symm)
    (fun _ _ α => Strict.whisker_assoc _ α g))

/-- Whiskering a 2-cell by a composite, up to the strict associators. -/
lemma whiskerRight_comp_eqToHom {a b c d : Obj} {f f' : a ⟶ b} (η : f ⟶ f') (k : b ⟶ c)
    (g : c ⟶ d) (h₁ : f' ≫ k ≫ g = (f' ≫ k) ≫ g) (h₂ : f ≫ k ≫ g = (f ≫ k) ≫ g) :
    η ▷ (k ≫ g) ≫ eqToHom h₁ = eqToHom h₂ ≫ (η ▷ k) ▷ g := by
  rw [Strict.whiskerRight_comp]
  simp

variable (A) in
/-- **Post-composition with `g : d ⟶ c`** as a lax transformation `K(−, d) ⇒ K(−, c)` of hom
2-functors on `𝒜ᵒᵖ`. Its naturality cells are identities: it is 2-natural. -/
def postcompLaxNat {c d : Obj} (g : d ⟶ c) : LaxNat (homTwoFunctor A d) (homTwoFunctor A c) where
  app x := (postcomp (FullSubOp.pt x) g).toCatHom
  nat f := eqToHom (by exact postcomp_naturality g f)
  nat_cell η := by
    ext k
    rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.eqToHom_app]
    exact whiskerRight_comp_eqToHom (FullSubOp.hom₂ η) k g _ _
  nat_comp f f' := by
    simp only [Bicategory.eqToHom_whiskerRight, Bicategory.whiskerLeft_eqToHom, eqToHom_trans]
  nat_id x := rfl

end UlmerBialgebras.Paper
