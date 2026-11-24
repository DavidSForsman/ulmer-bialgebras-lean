module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape

/-!
# Colimits of coalgebras of an endofunctor

For an endofunctor `S : C ⥤ C`, the category `Endofunctor.Coalgebra S` has all colimits
that `C` has, and they are created by the forgetful functor.  (No preservation assumption
on `S` is needed: the structure morphism of the colimit is obtained by the universal
property of the colimit in `C`, mapping into `S` of the colimit.)

## Main results

* `UlmerBialgebras.Coalgebra.isColimitCocone` — the explicit colimit cocone of a diagram of
  coalgebras, built on a colimit of the underlying diagram;
* `UlmerBialgebras.Coalgebra.hasColimitsOfShape` — `Coalgebra S` has colimits of shape `K`
  whenever `C` has them;
* `UlmerBialgebras.Coalgebra.preservesColimitsOfShape_forget` — the forgetful functor preserves
  them.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5 and Lemma 5.6
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w w' v u

namespace UlmerBialgebras

open CategoryTheory Limits Endofunctor

namespace Coalgebra

variable {C : Type u} [Category.{v} C] {S : C ⥤ C}
variable {K : Type w} [Category.{w'} K] (W : K ⥤ Endofunctor.Coalgebra S)

/-- The leg of `c` at `k`, as a map `(W.obj k).V ⟶ c.pt`. -/
def leg (c : Cocone (W ⋙ Endofunctor.Coalgebra.forget S)) (k : K) : (W.obj k).V ⟶ c.pt :=
  c.ι.app k

/-- The legs of `c` commute with the transition maps of `W`. -/
@[reassoc]
lemma leg_naturality (c : Cocone (W ⋙ Endofunctor.Coalgebra.forget S)) {k k' : K} (f : k ⟶ k') :
    (W.map f).f ≫ leg W c k' = leg W c k :=
  (c.ι.naturality f).trans (Category.comp_id _)

/-- The cocone, with vertex `S (colimit)`, used to define the structure morphism of a colimit
of coalgebras. -/
@[simps]
noncomputable def strCocone (c : Cocone (W ⋙ Endofunctor.Coalgebra.forget S)) :
    Cocone (W ⋙ Endofunctor.Coalgebra.forget S) where
  pt := S.obj c.pt
  ι :=
    { app k := (W.obj k).str ≫ S.map (leg W c k)
      naturality := by
        intro k k' f
        simp only [Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map, Coalgebra.forget_map,
          ← leg_naturality W c f, Functor.map_comp, Functor.const_obj_map, Category.comp_id]
        exact ((W.map f).h_assoc _).symm }

variable {W}
variable {c : Cocone (W ⋙ Endofunctor.Coalgebra.forget S)} (hc : IsColimit c)

include hc in
/-- Maps out of the colimit agree if they agree on every leg. -/
lemma colim_hom_ext {X : C} {f g : c.pt ⟶ X} (h : ∀ k, leg W c k ≫ f = leg W c k ≫ g) : f = g :=
  hc.hom_ext h

/-- The structure morphism of the colimit coalgebra. -/
noncomputable def strColim : c.pt ⟶ S.obj c.pt := hc.desc (strCocone W c)

/-- The structure morphism `strColim hc` satisfies
`leg W c k ≫ strColim hc = (W.obj k).str ≫ S.map (leg W c k)`. -/
@[reassoc (attr := simp)]
lemma ι_strColim (k : K) :
    leg W c k ≫ strColim hc = (W.obj k).str ≫ S.map (leg W c k) :=
  hc.fac (strCocone W c) k

/-- The colimit cocone in the category of coalgebras. -/
@[simps]
noncomputable def cocone : Cocone W where
  pt := ⟨c.pt, strColim hc⟩
  ι :=
    { app k := ⟨leg W c k, (ι_strColim hc k).symm⟩
      naturality := by
        intro k k' f
        ext
        exact c.ι.naturality f }

/-- The map out of the colimit induced by a cocone `s` over `W`. -/
noncomputable def descV (s : Cocone W) : c.pt ⟶ s.pt.V :=
  hc.desc ((Endofunctor.Coalgebra.forget S).mapCocone s)

/-- `descV hc s` restricts to the legs of `s`. -/
@[reassoc]
lemma leg_descV (s : Cocone W) (k : K) : leg W c k ≫ descV hc s = (s.ι.app k).f :=
  hc.fac ((Endofunctor.Coalgebra.forget S).mapCocone s) k

/-- The cocone `UlmerBialgebras.Coalgebra.cocone hc` is a colimit cocone. -/
noncomputable def isColimitCocone : IsColimit (cocone hc) where
  desc s :=
    { f := descV hc s
      h := by
        refine colim_hom_ext hc fun k => ?_
        change leg W c k ≫ strColim hc ≫ S.map (descV hc s) = leg W c k ≫ descV hc s ≫ s.pt.str
        rw [ι_strColim_assoc, ← S.map_comp, leg_descV, leg_descV_assoc]
        exact (s.ι.app k).h }
  fac s k := by
    ext
    exact leg_descV hc s k
  uniq s m hm := by
    ext
    refine colim_hom_ext hc fun k => ?_
    exact congr(($(hm k)).f).trans (leg_descV hc s k).symm

variable (S) (K)

/-- The category of coalgebras of an endofunctor `S` has colimits of shape `K` whenever the
underlying category does. -/
instance hasColimitsOfShape [HasColimitsOfShape K C] :
    HasColimitsOfShape K (Endofunctor.Coalgebra S) where
  has_colimit W := ⟨_, isColimitCocone (colimit.isColimit (W ⋙ Endofunctor.Coalgebra.forget S))⟩

/-- The forgetful functor from coalgebras of `S` preserves colimits of shape `K`. -/
instance preservesColimitsOfShape_forget [HasColimitsOfShape K C] :
    PreservesColimitsOfShape K (Endofunctor.Coalgebra.forget S) where
  preservesColimit {W} :=
    ⟨fun {s} hs => ⟨by
      refine IsColimit.ofIsoColimit ?_
        ((Cocone.functoriality W (Endofunctor.Coalgebra.forget S)).mapIso
          (hs.uniqueUpToIso
              (isColimitCocone (colimit.isColimit (W ⋙ Endofunctor.Coalgebra.forget S)))).symm)
      exact IsColimit.ofIsoColimit (colimit.isColimit (W ⋙ Endofunctor.Coalgebra.forget S))
        (Cocone.ext (Iso.refl _) fun _ => Category.comp_id _)⟩⟩

/-- The category of coalgebras of `S` has iterations of shape `J` whenever the underlying
category does. -/
instance hasIterationOfShape {J : Type w} [LinearOrder J] [HasIterationOfShape J C] :
    HasIterationOfShape J (Endofunctor.Coalgebra S) where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have := Limits.hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance

end Coalgebra

end UlmerBialgebras
