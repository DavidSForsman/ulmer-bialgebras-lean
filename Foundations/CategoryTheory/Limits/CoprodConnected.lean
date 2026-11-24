module

public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison

/-!
# Coproduct with a fixed object preserves connected colimits

The dual of `CategoryTheory.prod_preservesConnectedLimits`: for a connected index category
`J`, the functor `X ⨿ -` preserves colimits of shape `J`.  (It does not preserve
coproducts or the initial object, which are the typical disconnected colimits.)

This is the fact, used in the proof of Theorem 5.5 (1), that `W = c + F(-)` preserves those
connected colimits that `F` preserves.

## Main results

* `UlmerBialgebras.coprod_preservesConnectedColimits`: for a connected category `J`, the functor
  `X ⨿ -` preserves colimits of shape `J`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5
-/

@[expose] public section

universe w w' v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
variable {J : Type w} [Category.{w'} J]

namespace CoprodConnected

/-- (Impl). The obvious natural transformation from `K` to `X ⨿ K -`. -/
@[simps]
noncomputable def gamma₂ {K : J ⥤ C} (X : C) : K ⟶ K ⋙ coprod.functor.obj X where
  app _ := coprod.inr

/-- (Impl). The obvious natural transformation from the constant functor `X` to `X ⨿ K -`. -/
@[simps]
noncomputable def gamma₁ {K : J ⥤ C} (X : C) : (Functor.const J).obj X ⟶ K ⋙ coprod.functor.obj X
    where
  app _ := coprod.inl

/-- (Impl). Given a cocone for `X ⨿ K -`, produce a cocone for `K`. -/
@[simps]
noncomputable def forgetCocone {X : C} {K : J ⥤ C} (s : Cocone (K ⋙ coprod.functor.obj X)) : Cocone
    K where
  pt := s.pt
  ι := gamma₂ X ≫ s.ι

end CoprodConnected

open CoprodConnected

/-- The functor `X ⨿ -` preserves any connected colimit. -/
lemma coprod_preservesConnectedColimits [IsConnected J] (X : C) :
    PreservesColimitsOfShape J (coprod.functor.obj X) where
  preservesColimit {K} :=
    { preserves := fun {c} l => ⟨{
        desc := fun s => coprod.desc (coprod.inl ≫ s.ι.app (Classical.arbitrary _))
          (l.desc (forgetCocone s))
        fac := fun s j => by
          refine coprod.hom_ext ?_ ?_
          · have hconst := nat_trans_from_is_connected (gamma₁ (K := K) X ≫ s.ι)
              j (Classical.arbitrary J)
            simp only [NatTrans.comp_app, gamma₁_app, Functor.const_obj_obj] at hconst
            simp only [Functor.mapCocone_ι_app, coprod.functor_obj_map, coprod.inl_map_assoc,
              Category.id_comp]
            exact (coprod.inl_desc _ _).trans hconst.symm
          · simp only [Functor.mapCocone_ι_app, coprod.functor_obj_map, coprod.inr_map_assoc]
            refine (c.ι.app j ≫= coprod.inr_desc _ _).trans ((l.fac _ j).trans rfl)
        uniq := fun s m hm => by
          refine coprod.hom_ext ?_ ?_
          · have h := hm (Classical.arbitrary J)
            simp only [Functor.mapCocone_ι_app, coprod.functor_obj_map] at h
            refine Eq.trans ?_ (coprod.inl_desc _ _).symm
            simpa using coprod.inl ≫= h
          · have hkey : coprod.inr ≫ m = l.desc (forgetCocone s) := by
              refine l.uniq (forgetCocone s) (coprod.inr ≫ m) ?_
              intro j
              have h := hm j
              simp only [Functor.mapCocone_ι_app, coprod.functor_obj_map] at h
              rw [forgetCocone_ι]
              calc c.ι.app j ≫ coprod.inr ≫ m
                  = coprod.inr ≫ coprod.map (𝟙 X) (c.ι.app j) ≫ m := by simp
                _ = coprod.inr ≫ s.ι.app j := by rw [h]
                _ = (gamma₂ X ≫ s.ι).app j := by simp
            simp only [colimit.ι_desc]
            exact hkey }⟩ }

end UlmerBialgebras
