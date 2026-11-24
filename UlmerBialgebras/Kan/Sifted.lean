module

public import Mathlib.CategoryTheory.Limits.Sifted

/-!
# Lemma 4.16: sifted colimits are preserved componentwise

This file formalizes Lemma 4.16 of *A Syntactic Approach to Ulmer's Bialgebras* in the binary
case (the general `n`-ary case reduces to it, as in the paper): a functor of two variables
preserves colimits of a sifted shape if and only if it preserves them in each variable
separately.

Along the way we record the componentwise description of colimits in a product of two
categories, which Mathlib only provides for products of families indexed by a type:

* `UlmerBialgebras.isColimitProd` — a cocone in `C₁ × C₂` is a colimit as soon as both of its
  components are;
* `UlmerBialgebras.isColimitFst`, `UlmerBialgebras.isColimitSnd` — conversely, the components of a
  colimit cocone are colimits;
* `UlmerBialgebras.preservesColimitsOfShape_sectL`, `UlmerBialgebras.preservesColimitsOfShape_sectR`
  — the functors `x ↦ (x, c₂)` and `y ↦ (c₁, y)` preserve colimits of connected shapes;
* `UlmerBialgebras.preservesColimitsOfShape_iff_componentwise` — **Lemma 4.16**.

The nontrivial implication uses Mathlib's `PreservesColimit₂` (a Fubini-type statement for
bifunctors) together with the finality of the diagonal `J ⥤ J × J`, which is the definition
of a sifted category.

## Main results

* `UlmerBialgebras.isColimitProd`: a cocone in `C₁ × C₂` whose components are colimits is a colimit.
* `UlmerBialgebras.isColimitFst`, `UlmerBialgebras.isColimitSnd`: the components of a colimit cocone
  in `C₁ × C₂` are colimits.
* `UlmerBialgebras.preservesColimitsOfShape_iff_componentwise`: for a sifted `J`, a functor
  `C₁ × C₂ ⥤ E` preserves `J`-colimits iff it preserves them in each variable separately
  (Lemma 4.16, binary case).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 4.16
* [J. Adámek, J. Rosický, E. M. Vitale, *What Are Sifted
  Colimits?*][AdamekRosickyVitale2010SiftedColimits]
-/

@[expose] public section

universe v₁ v₂ v₃ vj u₁ u₂ u₃ uj

namespace UlmerBialgebras

open CategoryTheory Limits Functor

variable {J : Type uj} [Category.{vj} J]
variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {E : Type u₃} [Category.{v₃} E]

/-! ## Colimits in a product of two categories -/

/-- A cocone in a product of two categories is a colimit as soon as both of its components
are. -/
def isColimitProd {D : J ⥤ C₁ × C₂} (c : Cocone D)
    (h₁ : IsColimit ((CategoryTheory.Prod.fst C₁ C₂).mapCocone c))
    (h₂ : IsColimit ((CategoryTheory.Prod.snd C₁ C₂).mapCocone c)) : IsColimit c where
  desc t := (h₁.desc ((CategoryTheory.Prod.fst C₁ C₂).mapCocone t),
    h₂.desc ((CategoryTheory.Prod.snd C₁ C₂).mapCocone t))
  fac t j := Prod.ext (h₁.fac _ j) (h₂.fac _ j)
  uniq t m hm := by
    refine Prod.ext ?_ ?_
    · exact h₁.uniq ((CategoryTheory.Prod.fst C₁ C₂).mapCocone t) m.1
        (fun j => (Prod.ext_iff.mp (hm j)).1)
    · exact h₂.uniq ((CategoryTheory.Prod.snd C₁ C₂).mapCocone t) m.2
        (fun j => (Prod.ext_iff.mp (hm j)).2)

/-- The cocone in `C₁ × C₂` obtained from a cocone on the first component of `D` and the
second component of a fixed cocone `c`. -/
@[simps]
def proj₁Aux {D : J ⥤ C₁ × C₂} (c : Cocone D) (t : Cocone (D ⋙ CategoryTheory.Prod.fst C₁ C₂)) :
    Cocone D where
  pt := (t.pt, c.pt.2)
  ι :=
    { app := fun j => (t.ι.app j, (c.ι.app j).2)
      naturality := by
        intro j j' f
        refine Prod.ext ?_ ?_
        · have h := t.w f
          simp only [const_obj_obj, prod_comp, const_obj_map, prod_id, Category.comp_id] at h ⊢
          exact h
        · have h : (D.map f).2 ≫ (c.ι.app j').2 = (c.ι.app j).2 := (Prod.ext_iff.mp (c.w f)).2
          simpa using h }

/-- The cocone in `C₁ × C₂` obtained from the first component of a fixed cocone `c` and a
cocone on the second component of `D`. -/
@[simps]
def proj₂Aux {D : J ⥤ C₁ × C₂} (c : Cocone D) (t : Cocone (D ⋙ CategoryTheory.Prod.snd C₁ C₂)) :
    Cocone D where
  pt := (c.pt.1, t.pt)
  ι :=
    { app := fun j => ((c.ι.app j).1, t.ι.app j)
      naturality := by
        intro j j' f
        refine Prod.ext ?_ ?_
        · have h : (D.map f).1 ≫ (c.ι.app j').1 = (c.ι.app j).1 := (Prod.ext_iff.mp (c.w f)).1
          simpa using h
        · have h := t.w f
          simp only [const_obj_obj, prod_comp_snd, const_obj_map, prod_id, Category.comp_id]
            at h ⊢
          exact h }

/-- The first component of a colimit cocone in a product of categories is a colimit. -/
def isColimitFst {D : J ⥤ C₁ × C₂} {c : Cocone D} (h : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.fst C₁ C₂).mapCocone c) where
  desc t := (h.desc (proj₁Aux c t)).1
  fac t j := (Prod.ext_iff.mp (h.fac (proj₁Aux c t) j)).1
  uniq t m hm := by
    have key : ((m, 𝟙 c.pt.2) : c.pt ⟶ (proj₁Aux c t).pt) = h.desc (proj₁Aux c t) := by
      exact h.uniq (proj₁Aux c t) _ (fun j => Prod.ext (hm j) (Category.comp_id _))
    exact (Prod.ext_iff.mp key).1

/-- The second component of a colimit cocone in a product of categories is a colimit. -/
def isColimitSnd {D : J ⥤ C₁ × C₂} {c : Cocone D} (h : IsColimit c) :
    IsColimit ((CategoryTheory.Prod.snd C₁ C₂).mapCocone c) where
  desc t := (h.desc (proj₂Aux c t)).2
  fac t j := (Prod.ext_iff.mp (h.fac (proj₂Aux c t) j)).2
  uniq t m hm := by
    have key : ((𝟙 c.pt.1, m) : c.pt ⟶ (proj₂Aux c t).pt) = h.desc (proj₂Aux c t) := by
      exact h.uniq (proj₂Aux c t) _ (fun j => Prod.ext (Category.comp_id _) (hm j))
    exact (Prod.ext_iff.mp key).2

/-- The functor `x ↦ (x, c₂)` preserves colimits of connected shapes. -/
instance preservesColimitsOfShape_sectL [IsConnected J] (x : C₂) :
    PreservesColimitsOfShape J (CategoryTheory.Prod.sectL C₁ x) where
  preservesColimit :=
    { preserves := fun hs => ⟨isColimitProd _ hs (isColimitConstCocone J x)⟩ }

/-- The functor `y ↦ (c₁, y)` preserves colimits of connected shapes. -/
instance preservesColimitsOfShape_sectR [IsConnected J] (x : C₁) :
    PreservesColimitsOfShape J (CategoryTheory.Prod.sectR x C₂) where
  preservesColimit :=
    { preserves := fun hs => ⟨isColimitProd _ (isColimitConstCocone J x) hs⟩ }

/-! ## Lemma 4.16 -/

/-- The comparison isomorphism between the diagonal restriction of the `J × J`-indexed
diagram `(j₁, j₂) ↦ F (D j₁, D j₂)` and the diagram `j ↦ F (D j)`. -/
@[simps!]
noncomputable def diagCompIso (F : C₁ × C₂ ⥤ E) (D : J ⥤ C₁ × C₂) :
    (diag J ⋙ uncurry.obj ((((whiskeringLeft₂ E).obj (D ⋙ CategoryTheory.Prod.fst C₁ C₂)).obj
      (D ⋙ CategoryTheory.Prod.snd C₁ C₂)).obj (curry.obj F))) ≅ D ⋙ F :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intro j j' f; simp [← Functor.map_comp])

/-- The components of the diagonal restriction of the cocone `(curry.obj F).mapCocone₂` of the
two component cocones of `c`, transported along `diagCompIso F D`, are those of
`F.mapCocone c`. -/
lemma diagCompIso_precompose_ι_app (F : C₁ × C₂ ⥤ E) {D : J ⥤ C₁ × C₂} (c : Cocone D)
    (j : J) :
    ((Cocone.precompose (diagCompIso F D).inv).obj (Cocone.whisker (diag J)
      ((curry.obj F).mapCocone₂ ((CategoryTheory.Prod.fst C₁ C₂).mapCocone c)
        ((CategoryTheory.Prod.snd C₁ C₂).mapCocone c)))).ι.app j = F.map (c.ι.app j) := by
  simp only [comp_obj, diagCompIso, diag_obj, uncurry_obj_obj,
    whiskeringLeft₂_obj_obj_obj_obj_obj, Prod.fst_obj, Prod.snd_obj, curry_obj_obj_obj,
    Cocone.precompose_obj_pt, Cocone.whisker_pt, const_obj_obj, Cocone.precompose_obj_ι,
    Cocone.whisker_ι, NatTrans.comp_app, NatIso.ofComponents_inv_app, Iso.refl_inv,
    whiskerLeft_app, mapCocone₂_ι_app, mapCocone_pt, mapCocone_ι_app, Prod.fst_map,
    curry_obj_map_app, Prod.snd_map, curry_obj_obj_map, ← F.map_comp, prod_comp,
    Category.comp_id, Category.id_comp, Prod.mk.eta]
  -- the remaining identity is on `F.obj ((D.obj j).1, (D.obj j).2)`, that is `F.obj (D.obj j)`
  exact Category.id_comp _

/-- The diagonal restriction of `(curry.obj F).mapCocone₂` of the two component cocones of `c`,
transported along `diagCompIso F D`, is `F.mapCocone c`. -/
@[simps!]
noncomputable def diagCompIsoCoconeIso (F : C₁ × C₂ ⥤ E) {D : J ⥤ C₁ × C₂} (c : Cocone D) :
    (Cocone.precompose (diagCompIso F D).inv).obj (Cocone.whisker (diag J)
      ((curry.obj F).mapCocone₂ ((CategoryTheory.Prod.fst C₁ C₂).mapCocone c)
        ((CategoryTheory.Prod.snd C₁ C₂).mapCocone c))) ≅ F.mapCocone c :=
  Cocone.ext (Iso.refl _) fun j =>
    (Category.comp_id _).trans (diagCompIso_precompose_ι_app F c j)

/-- The nontrivial half of Lemma 4.16: a functor of two variables which preserves colimits of
a sifted shape in each variable separately preserves them jointly. -/
theorem isColimit_mapCocone_of_componentwise [IsSifted J] (F : C₁ × C₂ ⥤ E)
    (h₁ : ∀ x : C₂, PreservesColimitsOfShape J (CategoryTheory.Prod.sectL C₁ x ⋙ F))
    (h₂ : ∀ x : C₁, PreservesColimitsOfShape J (CategoryTheory.Prod.sectR x C₂ ⋙ F))
    {D : J ⥤ C₁ × C₂} {c : Cocone D} (hc : IsColimit c) :
    Nonempty (IsColimit (F.mapCocone c)) := by
  have : ∀ x : C₂, PreservesColimitsOfShape J ((curry.obj F).flip.obj x) := h₁
  have : ∀ x : C₁, PreservesColimitsOfShape J ((curry.obj F).obj x) := h₂
  have key := (Functor.Final.isColimitWhiskerEquiv (diag J) _).symm
    (isColimitOfPreserves₂ (curry.obj F) (isColimitFst hc) (isColimitSnd hc))
  exact ⟨(IsColimit.equivOfNatIsoOfIso (diagCompIso F D) _ (F.mapCocone c)
    (diagCompIsoCoconeIso F c)) key⟩

/-- **Lemma 4.16** ([forsman2026syntactic]), binary case: a functor of two variables preserves
colimits of a sifted shape if and only if it preserves them in each variable separately. -/
theorem preservesColimitsOfShape_iff_componentwise [IsSifted J] (F : C₁ × C₂ ⥤ E) :
    Nonempty (PreservesColimitsOfShape J F) ↔
      ((∀ x : C₂, Nonempty (PreservesColimitsOfShape J (CategoryTheory.Prod.sectL C₁ x ⋙ F))) ∧
        (∀ x : C₁,
          Nonempty (PreservesColimitsOfShape J (CategoryTheory.Prod.sectR x C₂ ⋙ F)))) := by
  constructor
  · rintro ⟨hF⟩
    exact ⟨fun _ => ⟨inferInstance⟩, fun _ => ⟨inferInstance⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨{ preserves := fun hc =>
      isColimit_mapCocone_of_componentwise F (fun x => (h₁ x).some) (fun x => (h₂ x).some) hc }⟩⟩

end UlmerBialgebras
