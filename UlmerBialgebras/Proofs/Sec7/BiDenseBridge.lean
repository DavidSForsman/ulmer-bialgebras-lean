module

public import UlmerBialgebras.Paper.Sec7DefsSec7Variant

/-!
# Bridge between Definition 7.1 and Hofstra–Karvonen bi-density

Translations between the componentwise structures of the development repository's
`UlmerBialgebras/Density/ADense`
(`UlmerBialgebras.ACellFamily`, `UlmerBialgebras.Paper.PsFamily`,
`UlmerBialgebras.AHomFamily.Representation`) and modifications and strong transformations between
restricted representables `K(ι-, c) : Aᵒᵖ ⥤ᵖ Cat`, where `ι` is the inclusion of the full
sub-2-category spanned by `A`.

## Main results

* `UlmerBialgebras.Paper.BiDenseBridge.cellFamily`: a modification between induced
  transformations gives a family of 2-cells (`UlmerBialgebras.Paper.BiDenseBridge.homOfCellFamily`
  goes back).
* `UlmerBialgebras.Paper.BiDenseBridge.ofStrongTrans`: a strong transformation between restricted
  representables gives a pseudonatural family of functors.
* `UlmerBialgebras.Paper.BiDenseBridge.toStrongTrans`: a pseudonatural family of functors gives a
  strong transformation between restricted representables.
* `UlmerBialgebras.Paper.BiDenseBridge.isoOfRepresentation`: a representation of the family of `η`
  gives an isomorphism from the transformation induced by the representing 1-cell to `η`.
* `UlmerBialgebras.Paper.BiDenseBridge.representationOfIso`: an isomorphism from an induced
  transformation to `toStrongTrans G` gives a representation of `G`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe u v w

namespace UlmerBialgebras.Paper.BiDenseBridge

open CategoryTheory Opposite Pseudofunctor StrongTrans

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] {A : ObjectProperty Obj}

/-- `(𝟙 f) ▷ k ≫ eqToHom h = eqToHom h`. -/
lemma id_whisker_eqToHom {a b e : Obj} (f : a ⟶ b) (k : b ⟶ e) {g : a ⟶ e}
    (h : f ≫ k = g) : (𝟙 f) ▷ k ≫ eqToHom h = eqToHom h := by
  rw [Bicategory.id_whiskerRight]; exact Category.id_comp _

/-- If `N ≫ eqToHom p = eqToHom q ≫ 𝟙 _ ≫ 𝟙 _`, then `N = eqToHom (q.trans p.symm)`. -/
lemma eq_eqToHom_of_comp {C : Type*} [Category C] {X Y Z : C} {N : X ⟶ Y} (p : Y = Z)
    (q : X = Z) (h : N ≫ eqToHom p = eqToHom q ≫ 𝟙 _ ≫ 𝟙 _) : N = eqToHom (q.trans p.symm) := by
  subst p; simpa using h

/-- If `N ≫ eqToHom p = eqToHom q ≫ 𝟙 ≫ f ≫ 𝟙 ≫ g ≫ 𝟙`, then
`N = eqToHom q ≫ f ≫ g ≫ eqToHom p.symm`. -/
lemma eq_of_comp_eqToHom {C : Type*} [Category C] {X X' Y Y' W : C} {N : X ⟶ Y}
    {f : X' ⟶ W} {g : W ⟶ Y'} (p : Y = Y') (q : X = X')
    (h : N ≫ eqToHom p = eqToHom q ≫ 𝟙 _ ≫ f ≫ 𝟙 _ ≫ g ≫ 𝟙 _) :
    N = eqToHom q ≫ f ≫ g ≫ eqToHom p.symm := by
  subst p; subst q; simpa using h

/-- `(eqToHom a ≫ P ≫ Q ≫ eqToHom b) ≫ eqToHom b' = eqToHom a ≫ 𝟙 ≫ P ≫ 𝟙 ≫ Q ≫ 𝟙`. -/
lemma eqToHom_sandwich {C : Type*} [Category C] {X X' W Y Y' : C} (a : X = X') (P : X' ⟶ W)
    (Q : W ⟶ Y) (b : Y = Y') (b' : Y' = Y) :
    (eqToHom a ≫ P ≫ Q ≫ eqToHom b) ≫ eqToHom b' = eqToHom a ≫ 𝟙 _ ≫ P ≫ 𝟙 _ ≫ Q ≫ 𝟙 _ := by
  subst a; subst b; simp

/-- In `AsBicat Obj` the associator is `eqToHom (Category.assoc _ _ _)`. -/
lemma asBicat_associator_hom {a b e g : Obj} (u : a ⟶ b) (k : b ⟶ e) (p : e ⟶ g) :
    (Bicategory.associator (B := AsBicat.{u, v, w} Obj) u k p).hom =
      eqToHom (Category.assoc u k p) :=
  congr(($(Bicategory.Strict.associator_eqToIso _ _ _)).hom)

variable (A) in
/-- The restricted representable `K(ι-, c)`. -/
abbrev R (c : AsBicat.{u, v, w} Obj) : Pseudofunctor (FullSubBicat A)ᵒᵖ Cat.{w, v} :=
  (fullSubBicatι A).op.comp (Bicategory.yoneda.obj c)

/-- An object of the full sub-2-category. -/
abbrev ob (x : Obj) (hx : A x) : FullSubBicat A := ⟨x, hx⟩

/-- A 1-cell of the full sub-2-category. -/
abbrev hm {x y : Obj} (hx : A x) (hy : A y) (u : x ⟶ y) : ob x hx ⟶ ob y hy :=
  Bicategory.InducedBicategory.mkHom (C := AsBicat.{u, v, w} Obj) u

variable {c d : AsBicat.{u, v, w} Obj}

/-- The component at `k` of the unitor `(R A c).mapId` is `eqToHom (Category.id_comp k)`. -/
lemma r_mapId_app (x : FullSubBicat A) (k : (x.1 : Obj) ⟶ AsBicat.down c) :
    ((R A c).mapId (op x)).hom.toNatTrans.app k = eqToHom (Category.id_comp k) := by
  have : ((R A c).mapId (op x)).hom.toNatTrans.app k =
      (𝟙 (𝟙 (x.1 : Obj))) ▷ k ≫ (Bicategory.leftUnitor k).hom := rfl
  rw [this, Bicategory.id_whiskerRight, Category.id_comp]
  exact congr(($(Bicategory.Strict.leftUnitor_eqToIso k)).hom)

/-- The component at `k` of the compositor `(R A c).mapComp` is
`eqToHom (Category.assoc u.hom u'.hom k)`. -/
lemma r_mapComp_app {x y z : FullSubBicat A} (u : x ⟶ y) (u' : y ⟶ z)
    (k : (z.1 : Obj) ⟶ AsBicat.down c) :
    ((R A c).mapComp u'.op u.op).hom.toNatTrans.app k =
      eqToHom (Category.assoc u.hom u'.hom k) := by
  have : ((R A c).mapComp u'.op u.op).hom.toNatTrans.app k =
      (𝟙 (u.hom ≫ u'.hom)) ▷ k ≫ (Bicategory.associator u.hom u'.hom k).hom := rfl
  exact this.trans ((_ ≫= asBicat_associator_hom u.hom u'.hom k).trans
    (id_whisker_eqToHom _ _ _))

/-- `r_mapId_app` with `k` taken in `(R A c).obj (op x)`. -/
lemma r_mapId_app' (x : FullSubBicat A) (k : ↑((R A c).obj (op x))) :
    ((R A c).mapId (op x)).hom.toNatTrans.app k =
      eqToHom (Category.id_comp (show (x.1 : Obj) ⟶ AsBicat.down c from k)) :=
  r_mapId_app x k

/-- `r_mapComp_app` with `k` taken in `(R A c).obj (op z)`. -/
lemma r_mapComp_app' {x y z : FullSubBicat A} (u : x ⟶ y) (u' : y ⟶ z)
    (k : ↑((R A c).obj (op z))) :
    ((R A c).mapComp u'.op u.op).hom.toNatTrans.app k =
      eqToHom (Category.assoc u.hom u'.hom (show (z.1 : Obj) ⟶ AsBicat.down c from k)) :=
  r_mapComp_app u u' k

variable (A c d) in
/-- The HK restricted Yoneda functor for the inclusion of `A`. -/
abbrev Φ := (fullSubBicatι A).restrictedYonedaFunctor c d

/-- A modification between induced transformations gives a family of 2-cells. -/
def cellFamily {p q : c ⟶ d} (Γ : (Φ A c d).obj p ⟶ (Φ A c d).obj q) :
    ACellFamily A (c := AsBicat.down c) (d := AsBicat.down d) p q where
  app x hx := (Γ.as.app (op (ob x hx))).toNatTrans
  naturality x y hx hy u k := by
    have h := congr(($(Γ.as.naturality (hm hx hy u).op)).toNatTrans.app k)
    have h1 : (Bicategory.whiskerLeft ((R A c).map (hm hx hy u).op) (Γ.as.app (op (ob x hx))) ≫
        (((Φ A c d).obj q).naturality (hm hx hy u).op).hom).toNatTrans.app k =
        (Γ.as.app (op (ob x hx))).toNatTrans.app (u ≫ k) ≫ (Bicategory.associator u k q).hom := rfl
    have h2 : ((((Φ A c d).obj p).naturality (hm hx hy u).op).hom ≫
        Bicategory.whiskerRight (Γ.as.app (op (ob y hy)))
          ((R A d).map (hm hx hy u).op)).toNatTrans.app k =
        (Bicategory.associator u k p).hom ≫ u ◁ (Γ.as.app (op (ob y hy))).toNatTrans.app k := rfl
    have h1' := h1.trans (_ ≫= asBicat_associator_hom u k q)
    have h2' := h2.trans (asBicat_associator_hom u k p =≫ _)
    exact (eqToHom_comp_iff _ _ _).1 (h1'.symm.trans (h.trans h2')).symm

/-- A family of 2-cells gives a modification between induced transformations. -/
def homOfCellFamily {p q : c ⟶ d}
    (Ψ : ACellFamily A (c := AsBicat.down c) (d := AsBicat.down d) p q) :
    (Φ A c d).obj p ⟶ (Φ A c d).obj q :=
  ⟨{ app X := NatTrans.toCatHom₂ (Ψ.app X.unop.2)
     naturality {X Y} f := by
       apply Cat.Hom₂.ext
       ext k
       have hn := Ψ.naturality Y.unop.2 X.unop.2 f.unop.hom k
       refine (_ ≫= asBicat_associator_hom _ _ _).trans ?_
       refine Eq.trans ?_ (asBicat_associator_hom _ _ _ =≫ _).symm
       refine Eq.trans ?_ (eqToHom (Category.assoc f.unop.hom k p) ≫= hn.symm)
       exact ((eqToHom_trans_assoc _ _ _).trans
         ((eqToHom_refl _ _ =≫ _).trans (Category.id_comp _))).symm }⟩

/-- A 2-cell of the full sub-2-category. -/
abbrev hm₂ {x y : Obj} (hx : A x) (hy : A y) {u u' : x ⟶ y} (σ : u ⟶ u') :
    hm hx hy u ⟶ hm hx hy u' :=
  Bicategory.InducedBicategory.mkHom₂ (C := AsBicat.{u, v, w} Obj) σ

/-- A strong transformation between restricted representables gives a pseudonatural
family of functors. -/
def ofStrongTrans (η : R A c ⟶ R A d) :
    PsFamily A (AsBicat.down c) (AsBicat.down d) where
  fn x hx := (η.app (op (ob x hx))).toFunctor
  nat x y hx hy u := Cat.Hom.toNatIso (η.naturality (hm hx hy u).op)
  nat_id x hx k := by
    have h := congr(($(η.naturality_id (op (ob x hx)))).toNatTrans.app k)
    have h1 : ((η.naturality (𝟙 (op (ob x hx)))).hom ≫
        Bicategory.whiskerLeft (η.app (op (ob x hx)))
          ((R A d).mapId (op (ob x hx))).hom).toNatTrans.app k
        = (η.naturality (hm hx hx (𝟙 x)).op).hom.toNatTrans.app k ≫
          ((R A d).mapId (op (ob x hx))).hom.toNatTrans.app
            ((η.app (op (ob x hx))).toFunctor.obj k) := rfl
    have h2 : (Bicategory.whiskerRight ((R A c).mapId (op (ob x hx))).hom (η.app (op (ob x hx))) ≫
        (Bicategory.leftUnitor _).hom ≫ (Bicategory.rightUnitor _).inv).toNatTrans.app k
        = (η.app (op (ob x hx))).toFunctor.map
            (((R A c).mapId (op (ob x hx))).hom.toNatTrans.app k) ≫
          𝟙 _ ≫ 𝟙 _ := rfl
    rw [h1, h2, r_mapId_app, r_mapId_app'] at h
    exact eq_eqToHom_of_comp _ _ (h.trans (eqToHom_map _ _ =≫ 𝟙 _ ≫ 𝟙 _))
  nat_comp x y z hx hy hz u v k := by
    have h := congr(($(η.naturality_comp (hm hy hz v).op (hm hx hy u).op)).toNatTrans.app k)
    have h1 : ((η.naturality ((hm hy hz v).op ≫ (hm hx hy u).op)).hom ≫
        Bicategory.whiskerLeft (η.app (op (ob z hz)))
          ((R A d).mapComp (hm hy hz v).op (hm hx hy u).op).hom).toNatTrans.app k
        = (η.naturality (hm hx hz (u ≫ v)).op).hom.toNatTrans.app k ≫
          ((R A d).mapComp (hm hy hz v).op (hm hx hy u).op).hom.toNatTrans.app
            ((η.app (op (ob z hz))).toFunctor.obj k) := rfl
    have h2 : (Bicategory.whiskerRight ((R A c).mapComp (hm hy hz v).op (hm hx hy u).op).hom
          (η.app (op (ob x hx))) ≫
        (Bicategory.associator _ _ _).hom ≫
        Bicategory.whiskerLeft ((R A c).map (hm hy hz v).op)
          (η.naturality (hm hx hy u).op).hom ≫
        (Bicategory.associator _ _ _).inv ≫
        Bicategory.whiskerRight (η.naturality (hm hy hz v).op).hom ((R A d).map (hm hx hy u).op) ≫
        (Bicategory.associator _ _ _).hom).toNatTrans.app k
        = (η.app (op (ob x hx))).toFunctor.map
            (((R A c).mapComp (hm hy hz v).op (hm hx hy u).op).hom.toNatTrans.app k) ≫ 𝟙 _ ≫
          (η.naturality (hm hx hy u).op).hom.toNatTrans.app (v ≫ k) ≫ 𝟙 _ ≫
          u ◁ (η.naturality (hm hy hz v).op).hom.toNatTrans.app k ≫ 𝟙 _ := rfl
    rw [h1, h2, r_mapComp_app, r_mapComp_app'] at h
    exact eq_of_comp_eqToHom _ _ (h.trans (eqToHom_map _ _ =≫ _))
  nat₂ x y hx hy u u' σ k :=
    congr(($(η.naturality_naturality
      (_root_.Bicategory.Opposite.op2 (hm₂ hx hy σ)))).toNatTrans.app k)

/-- A pseudonatural family of functors gives a strong transformation between restricted
representables. -/
def toStrongTrans (G : PsFamily A (AsBicat.down c) (AsBicat.down d)) : R A c ⟶ R A d where
  app X := (G.fn X.unop.2).toCatHom
  naturality {X Y} f := Cat.Hom.isoMk (G.nat Y.unop.2 X.unop.2 f.unop.hom)
  naturality_naturality {X Y f g} θ := by
    apply Cat.Hom₂.ext
    ext k
    exact G.nat₂ Y.unop.2 X.unop.2 θ.unop2.hom k
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext k
    have e1 := r_mapId_app (c := d) X.unop ((G.fn X.unop.2).obj k)
    have e2 := r_mapId_app (c := c) X.unop k
    have h := G.nat_id X.unop.2 k
    change (G.nat X.unop.2 X.unop.2 (𝟙 _)).hom.app k ≫
        ((R A d).mapId X).hom.toNatTrans.app ((G.fn X.unop.2).obj k) =
      (G.fn X.unop.2).map (((R A c).mapId X).hom.toNatTrans.app k) ≫ 𝟙 _ ≫ 𝟙 _
    rw [h, e1, e2]
    exact Eq.trans (by simp) (eq_whisker (eqToHom_map (G.fn X.unop.2) _) _).symm
  naturality_comp {X Y Z} f g := by
    apply Cat.Hom₂.ext
    ext k
    have e1 : ((R A d).mapComp f g).hom.toNatTrans.app ((G.fn X.unop.2).obj k) = _ :=
      r_mapComp_app (c := d) g.unop f.unop ((G.fn X.unop.2).obj k)
    have e2 : ((R A c).mapComp f g).hom.toNatTrans.app k = _ :=
      r_mapComp_app (c := c) g.unop f.unop k
    have h := G.nat_comp Z.unop.2 Y.unop.2 X.unop.2 g.unop.hom f.unop.hom k
    change (G.nat Z.unop.2 X.unop.2 (g.unop.hom ≫ f.unop.hom)).hom.app k ≫
        ((R A d).mapComp f g).hom.toNatTrans.app ((G.fn X.unop.2).obj k) =
      (G.fn Z.unop.2).map (((R A c).mapComp f g).hom.toNatTrans.app k) ≫ 𝟙 _ ≫
        (G.nat Z.unop.2 Y.unop.2 g.unop.hom).hom.app (f.unop.hom ≫ k) ≫ 𝟙 _ ≫
        g.unop.hom ◁ (G.nat Y.unop.2 X.unop.2 f.unop.hom).hom.app k ≫ 𝟙 _
    refine (h =≫ _).trans ?_
    rw [e1, e2]
    exact (eqToHom_sandwich _ _ _ _ _).trans
      (eq_whisker (eqToHom_map (G.fn Z.unop.2) _) _).symm

/-- A representation of the family of a strong transformation `η` gives an isomorphism from
the transformation induced by the representing 1-cell to `η`. -/
def isoOfRepresentation (η : R A c ⟶ R A d) (r : (ofStrongTrans η).Representation) :
    (Φ A c d).obj r.g ≅ η :=
  StrongTrans.isoMk (fun X => Cat.Hom.isoMk (r.iso X.unop.2)) (fun {X Y} f => by
    apply Cat.Hom₂.ext
    ext k
    refine Eq.trans ?_ (asBicat_associator_hom _ _ _ =≫ _).symm
    with_unfolding_all exact r.iso_nat Y.unop.2 X.unop.2 f.unop.hom k)

/-- The component of an isomorphism of strong transformations. -/
def compIso {η θ : R A c ⟶ R A d} (e : η ≅ θ) (X : (FullSubBicat A)ᵒᵖ) : η.app X ≅ θ.app X where
  hom := e.hom.as.app X
  inv := e.inv.as.app X
  hom_inv_id := congr(($(e.hom_inv_id)).as.app X)
  inv_hom_id := congr(($(e.inv_hom_id)).as.app X)

/-- An isomorphism from an induced transformation to the transformation of a pseudonatural
family gives a representation of the family. -/
def representationOfIso (G : PsFamily A (AsBicat.down c) (AsBicat.down d)) (g : c ⟶ d)
    (e : (Φ A c d).obj g ≅ toStrongTrans G) : G.toAHomFamily.Representation where
  g := g
  iso x hx := Cat.Hom.toNatIso (compIso e (op (ob x hx)))
  iso_nat _ _ hx hy u k :=
    by
      have h := congr(($(e.hom.as.naturality (hm hx hy u).op)).toNatTrans.app k)
      with_unfolding_all exact h.trans (asBicat_associator_hom _ _ _ =≫ _)

end BiDenseBridge

end Paper

end UlmerBialgebras
