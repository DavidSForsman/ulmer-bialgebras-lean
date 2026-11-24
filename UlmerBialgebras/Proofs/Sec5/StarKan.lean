module

public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.PUnit

/-!
# Colimits as left Kan extensions along `J ⥤ 1`

For `A : J ⥤ C`, the colimit of `A` exists exactly when `A` has a left Kan extension along
`Functor.star J : J ⥤ Discrete PUnit`. Used to get colimits in inserters from the
development's left Kan extension results (Theorem 5.7).

## Main results

* `UlmerBialgebras.hasLeftKanExtension_star_of_hasColimit`: if `A : J ⥤ C` has a colimit, it has a
  left Kan extension along `Functor.star J`.
* `UlmerBialgebras.hasColimit_of_hasLeftKanExtension_star`: if `A` has a left Kan extension along
  `Functor.star J`, it has a colimit.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.7
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace UlmerBialgebras

open CategoryTheory Limits Functor

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₂} C]

/-- The point of `Discrete PUnit`. -/
abbrev pt₁ : Discrete PUnit.{w + 1} := ⟨⟨⟩⟩

/-- A functor out of `Discrete PUnit` sends every endomorphism to the identity. -/
lemma discretePUnit_map_self (G : Discrete PUnit.{w + 1} ⥤ C) {x : Discrete PUnit.{w + 1}}
    (f : x ⟶ x) : G.map f = 𝟙 _ := by
  rw [Subsingleton.elim f (𝟙 x), G.map_id]

/-- Every object of `Discrete PUnit` is the point `pt₁`. -/
lemma discretePUnit_eq (x : Discrete PUnit.{w + 1}) : x = pt₁ := Subsingleton.elim _ _

/-- The cocone of `A` given by an extension of `A` along `J ⥤ 1`. -/
@[simps]
def coconeOfStar {A : J ⥤ C} (G : Discrete PUnit.{w + 1} ⥤ C) (β : A ⟶ Functor.star J ⋙ G) :
    Cocone A where
  pt := G.obj pt₁
  ι :=
    { app := fun j => β.app j
      naturality := fun i j f => by
        have := β.naturality f
        dsimp at this ⊢
        rw [this]
        exact whisker_eq _ (discretePUnit_map_self G _) }

/-- The extension of `A` along `J ⥤ 1` given by a cocone. -/
@[simps]
def extOfCocone {A : J ⥤ C} (c : Cocone A) : A ⟶ Functor.star.{w} J ⋙ (Functor.const _).obj c.pt
    where
  app j := c.ι.app j
  naturality i j f := by simp

/-- A colimit of `A` gives a left Kan extension of `A` along `J ⥤ 1`. -/
theorem hasLeftKanExtension_star_of_hasColimit (A : J ⥤ C) [HasColimit A] :
    (Functor.star.{w} J).HasLeftKanExtension A := by
  let E : Discrete PUnit.{w + 1} ⥤ C := (Functor.const _).obj (colimit A)
  let α : A ⟶ Functor.star J ⋙ E := extOfCocone (colimit.cocone A)
  have : E.IsLeftKanExtension α := by
    refine ⟨⟨IsInitial.ofUniqueHom (fun T => StructuredArrow.homMk
      { app := fun x => colimit.desc A (coconeOfStar T.right T.hom) ≫
          eqToHom (congrArg T.right.obj (discretePUnit_eq x).symm)
        naturality := fun x y f => by
          obtain rfl := discretePUnit_eq x
          obtain rfl := discretePUnit_eq y
          simp [E] } ?_) ?_⟩⟩
    · ext j
      simp only [whiskeringLeft_obj_obj, comp_obj, LeftExtension.mk_right, LeftExtension.mk_hom,
        const_obj_obj, whiskeringLeft_obj_map, NatTrans.comp_app, extOfCocone_app, colimit.cocone_x,
        colimit.cocone_ι, whiskerLeft_app, colimit.ι_desc_assoc, coconeOfStar_ι_app, E, α]
      -- the transport is along `T.right.obj pt₁ = T.right.obj ((Functor.star J).obj j)`
      exact (whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _)
    · intro T m
      apply StructuredArrow.ext
      ext x
      obtain rfl := discretePUnit_eq x
      apply colimit.hom_ext
      intro j
      -- `m` restricts to `T.hom` along the colimit cocone; the transport is along `pt₁ = pt₁`
      exact (congr_app (StructuredArrow.w m) j).trans
        ((colimit.ι_desc (coconeOfStar T.right T.hom) j).symm.trans
          (whisker_eq _ ((whisker_eq _ (eqToHom_refl _ _)).trans (Category.comp_id _))).symm)
  exact HasLeftKanExtension.mk E α

/-- A left Kan extension of `A` along `J ⥤ 1` gives a colimit of `A`. -/
theorem hasColimit_of_hasLeftKanExtension_star (A : J ⥤ C)
    [(Functor.star.{w} J).HasLeftKanExtension A] : HasColimit A := by
  let F' := (Functor.star.{w} J).leftKanExtension A
  let α := (Functor.star.{w} J).leftKanExtensionUnit A
  refine ⟨⟨⟨coconeOfStar F' α, ?_⟩⟩⟩
  exact
    { desc := fun s => (F'.descOfIsLeftKanExtension α ((Functor.const _).obj s.pt)
        (extOfCocone s)).app _
      fac := fun s j => F'.descOfIsLeftKanExtension_fac_app α ((Functor.const _).obj s.pt)
        (extOfCocone s) j
      uniq := fun s m hm => by
        let μ : F' ⟶ (Functor.const _).obj s.pt :=
          { app := fun x => eqToHom (congrArg F'.obj (discretePUnit_eq x)) ≫ m
            naturality := fun x y f => by
              obtain rfl := discretePUnit_eq x
              obtain rfl := discretePUnit_eq y
              simp }
        have h := F'.hom_ext_of_isLeftKanExtension α μ
          (F'.descOfIsLeftKanExtension α ((Functor.const _).obj s.pt) (extOfCocone s)) (by
            ext j
            have h1 := F'.descOfIsLeftKanExtension_fac_app α ((Functor.const _).obj s.pt)
              (extOfCocone s) j
            have h2 := hm j
            simp only [coconeOfStar_ι_app] at h2
            simp only [NatTrans.comp_app, whiskerLeft_app, μ, eqToHom_refl]
            exact (whisker_eq _ (Category.id_comp _)).trans (h2.trans h1.symm))
        -- `μ.app pt₁` is `m` after a transport along `pt₁ = pt₁`
        exact (Category.id_comp m).symm.trans
          ((eq_whisker (eqToHom_refl _ _).symm m).trans (congr_app h pt₁)) }

end UlmerBialgebras
