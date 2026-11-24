module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.BourbakiWitt

/-!
# Colimits over a directed cover by subsets

Let `D : α ⥤ C` be a diagram indexed by a preorder `α`, with colimit `c`, and let `𝒮` be a
family of subsets of `α` which is *directed* under inclusion and *covers* `α`.  Assume that
each restricted diagram `subDiagram D S` (`S ∈ 𝒮`) has a colimit.  Then `c` is also the
colimit of the colimits of the restricted diagrams.

This is the "regrouping" step of the generation theorem for inserters and equifiers
(Makkai–Paré). Mathlib raises the index of accessibility of a category with the analogous
`Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.isColimit`, for the family of all
`κ`-small `λ`-directed subsets.

## Main results

* `UlmerBialgebras.coverFunctor D 𝒮 : 𝒮 ⥤ C` sends `S` to the colimit of `D` restricted to `S`;
* `UlmerBialgebras.coverCocone D 𝒮 c` is the induced cocone with vertex `c.pt`;
* `UlmerBialgebras.isColimitCoverCocone` : this cocone is a colimit.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] {α : Type w} [Preorder α]

/-- The inclusion of a subset of a preorder as a full subcategory. -/
@[simps]
abbrev subInclusion (S : Set α) : {x : α // x ∈ S} ⥤ α where
  obj x := x.1
  map {x y} f := homOfLE (leOfHom f)

/-- The restriction of a diagram to a subset of its index preorder. -/
abbrev subDiagram (D : α ⥤ C) (S : Set α) : {x : α // x ∈ S} ⥤ C := subInclusion S ⋙ D

variable (D : α ⥤ C) (𝒮 : Set (Set α))
variable [∀ S : 𝒮, HasColimit (subDiagram D S.1)]

/-- The functor sending a member of the cover to the colimit of the corresponding
restricted diagram. -/
noncomputable def coverFunctor : 𝒮 ⥤ C where
  obj S := colimit (subDiagram D S.1)
  map {S T} f := colimit.desc (subDiagram D S.1)
    { pt := colimit (subDiagram D T.1)
      ι := { app := fun j => colimit.ι (subDiagram D T.1) ⟨j.1, (leOfHom f) j.2⟩
             naturality := fun j k g => by
               dsimp
               rw [Category.comp_id]
               exact colimit.w (subDiagram D T.1)
                 (homOfLE (x := (⟨j.1, (leOfHom f) j.2⟩ : {x : α // x ∈ T.1}))
                   (y := (⟨k.1, (leOfHom f) k.2⟩ : {x : α // x ∈ T.1}))
                   (show (j.1 : α) ≤ k.1 from leOfHom g)) } }
  map_id S := by refine colimit.hom_ext (fun j => ?_); simp
  map_comp {S T U} f g := by refine colimit.hom_ext (fun j => ?_); simp

/-- The transition maps of `coverFunctor D 𝒮` are induced by the inclusions of
subdiagrams. -/
@[reassoc (attr := simp)]
lemma ι_coverFunctor_map {S T : 𝒮} (f : S ⟶ T) (j : {x : α // x ∈ S.1}) :
    colimit.ι (subDiagram D S.1) j ≫ (coverFunctor D 𝒮).map f
      = colimit.ι (subDiagram D T.1) ⟨j.1, (leOfHom f) j.2⟩ := by
  simp [coverFunctor]

/-- The colimit inclusion `D j ⟶ (coverFunctor D 𝒮).obj S` of an index `j ∈ S`, typed at the
object of `coverFunctor D 𝒮`. -/
noncomputable def coverι (S : 𝒮) (j : {x : α // x ∈ S.1}) : D.obj j.1 ⟶ (coverFunctor D 𝒮).obj S :=
  colimit.ι (subDiagram D S.1) j

/-- The transition maps of `coverFunctor D 𝒮` send the inclusion of `j ∈ S` to the inclusion of
`j ∈ T`. -/
@[reassoc (attr := simp)]
lemma coverι_map {S T : 𝒮} (f : S ⟶ T) (j : {x : α // x ∈ S.1}) :
    coverι D 𝒮 S j ≫ (coverFunctor D 𝒮).map f = coverι D 𝒮 T ⟨j.1, (leOfHom f) j.2⟩ :=
  ι_coverFunctor_map D 𝒮 f j

/-- The inclusions into `(coverFunctor D 𝒮).obj S` are compatible with the maps of `D`. -/
@[reassoc (attr := simp)]
lemma coverι_w (S : 𝒮) {j k : {x : α // x ∈ S.1}} (g : j ⟶ k) :
    D.map (homOfLE (leOfHom g)) ≫ coverι D 𝒮 S k = coverι D 𝒮 S j :=
  colimit.w (subDiagram D S.1) g

/-- Two maps out of `(coverFunctor D 𝒮).obj S` agree if they agree on every inclusion. -/
@[ext]
lemma coverFunctor_hom_ext {S : 𝒮} {X : C} {f g : (coverFunctor D 𝒮).obj S ⟶ X}
    (h : ∀ j, coverι D 𝒮 S j ≫ f = coverι D 𝒮 S j ≫ g) : f = g :=
  colimit.hom_ext h

/-- The cocone on `coverFunctor D 𝒮` induced by a cocone on `D`. -/
noncomputable def coverCocone (c : Cocone D) : Cocone (coverFunctor D 𝒮) where
  pt := c.pt
  ι :=
    { app := fun S => colimit.desc (subDiagram D S.1)
        { pt := c.pt
          ι := { app := fun j => c.ι.app j.1
                 naturality := fun _ _ _ => (c.w _).trans (Category.comp_id _).symm } }
      naturality := fun _ _ f => colimit.hom_ext fun j => by
        refine (Category.assoc _ _ _).symm.trans ?_
        refine (ι_coverFunctor_map D 𝒮 f j =≫ _).trans ?_
        refine (colimit.ι_desc _ _).trans ?_
        refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
        refine (colimit.ι_desc _ _ =≫ _).trans ?_
        exact Category.comp_id _ }

/-- The components of `coverCocone D 𝒮 c` restrict on each subdiagram to the legs of `c`. -/
@[reassoc (attr := simp)]
lemma ι_coverCocone_app (c : Cocone D) (S : 𝒮) (j : {x : α // x ∈ S.1}) :
    colimit.ι (subDiagram D S.1) j ≫ (coverCocone D 𝒮 c).ι.app S = c.ι.app j.1 :=
  colimit.ι_desc _ _

/-- The components of `coverCocone D 𝒮 c` send the inclusion of `j` to the leg of `c` at `j`. -/
@[reassoc (attr := simp)]
lemma coverι_coverCocone_app (c : Cocone D) (S : 𝒮) (j : {x : α // x ∈ S.1}) :
    coverι D 𝒮 S j ≫ (coverCocone D 𝒮 c).ι.app S = c.ι.app j.1 :=
  colimit.ι_desc _ _

variable {D 𝒮}

/-- The leg of a cocone on `coverFunctor D 𝒮`, precomposed with a colimit inclusion, does
not depend on the member of the cover that is used. -/
lemma ι_comp_app_eq (hdir : ∀ S T : 𝒮, ∃ R : 𝒮, S.1 ⊆ R.1 ∧ T.1 ⊆ R.1)
    (s : Cocone (coverFunctor D 𝒮)) (j : α) (S T : 𝒮)
    (hS : j ∈ S.1) (hT : j ∈ T.1) :
    colimit.ι (subDiagram D S.1) ⟨j, hS⟩ ≫ s.ι.app S
      = colimit.ι (subDiagram D T.1) ⟨j, hT⟩ ≫ s.ι.app T := by
  obtain ⟨R, hSR, hTR⟩ := hdir S T
  have h1 : colimit.ι (subDiagram D S.1) ⟨j, hS⟩ ≫ s.ι.app S
      = colimit.ι (subDiagram D R.1) ⟨j, hSR hS⟩ ≫ s.ι.app R :=
    (coverι D 𝒮 S ⟨j, hS⟩ ≫= s.w (homOfLE hSR : S ⟶ R)).symm.trans
      (coverι_map_assoc D 𝒮 (homOfLE hSR) ⟨j, hS⟩ _)
  have h2 : colimit.ι (subDiagram D T.1) ⟨j, hT⟩ ≫ s.ι.app T
      = colimit.ι (subDiagram D R.1) ⟨j, hTR hT⟩ ≫ s.ι.app R :=
    (coverι D 𝒮 T ⟨j, hT⟩ ≫= s.w (homOfLE hTR : T ⟶ R)).symm.trans
      (coverι_map_assoc D 𝒮 (homOfLE hTR) ⟨j, hT⟩ _)
  exact h1.trans h2.symm

/-- The cocone on `D` induced by a cocone on the diagram of colimits over the cover. -/
@[simps]
noncomputable def coverDescCocone (hcover : ∀ j : α, ∃ S : 𝒮, j ∈ S.1)
    (hdir : ∀ S T : 𝒮, ∃ R : 𝒮, S.1 ⊆ R.1 ∧ T.1 ⊆ R.1)
    (s : Cocone (coverFunctor D 𝒮)) : Cocone D where
  pt := s.pt
  ι :=
    { app := fun j => colimit.ι (subDiagram D (hcover j).choose.1)
        ⟨j, (hcover j).choose_spec⟩ ≫ s.ι.app (hcover j).choose
      naturality := fun j k g => by
        obtain ⟨R, hjR, hkR⟩ := hdir (hcover j).choose (hcover k).choose
        refine Eq.trans ?_ (Category.comp_id _).symm
        refine (D.map g ≫= ι_comp_app_eq hdir s k _ R (hcover k).choose_spec
          (hkR (hcover k).choose_spec)).trans ?_
        refine Eq.trans ?_ (ι_comp_app_eq hdir s j _ R (hcover j).choose_spec
          (hjR (hcover j).choose_spec)).symm
        exact (Category.assoc _ _ _).symm.trans
          (colimit.w (subDiagram D R.1)
            (homOfLE (x := (⟨j, hjR (hcover j).choose_spec⟩ : {x : α // x ∈ R.1}))
              (y := (⟨k, hkR (hcover k).choose_spec⟩ : {x : α // x ∈ R.1}))
              (leOfHom g)) =≫ s.ι.app R) }

/-- **Colimits over a directed cover.**  If a diagram indexed by a preorder has a colimit,
and `𝒮` is a family of subsets of the index preorder which is directed under inclusion and
covers it, then the colimit is also the colimit of the colimits of the restricted
diagrams. -/
noncomputable def isColimitCoverCocone (c : Cocone D) (hc : IsColimit c)
    (hcover : ∀ j : α, ∃ S : 𝒮, j ∈ S.1)
    (hdir : ∀ S T : 𝒮, ∃ R : 𝒮, S.1 ⊆ R.1 ∧ T.1 ⊆ R.1) :
    IsColimit (coverCocone D 𝒮 c) where
  desc s := hc.desc (coverDescCocone hcover hdir s)
  fac s S := coverFunctor_hom_ext D 𝒮 fun j =>
    (coverι_coverCocone_app_assoc D 𝒮 c S j _).trans <| (hc.fac _ j.1).trans <|
      ι_comp_app_eq hdir s j.1 _ S (hcover j.1).choose_spec j.2
  uniq s m hm := hc.uniq (coverDescCocone hcover hdir s) m (fun j =>
    (ι_coverCocone_app D 𝒮 c (hcover j).choose
      ⟨j, (hcover j).choose_spec⟩ =≫ m).symm.trans
      ((Category.assoc _ _ _).trans (_ ≫= hm _)))

end UlmerBialgebras
