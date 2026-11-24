module

public import UlmerBialgebras.Monadicity.KanChainSetup

/-!
# The endofunctor `step` preserves connected colimits

Continuing `KanChainSetup.lean`.  If `C` has colimits of a connected shape `J` and `Λ`
preserves them, then so does the endofunctor `step` of the category of extensions: its
value is a pushout of the *fixed* span leg `b : p ⟶ e` against `x ⋙ Λ`, and colimits
commute with colimits, the constant part causing no trouble because `J` is connected.

This is the preservation statement for `H` in Lemma 5.6.

## Main results

* `UlmerBialgebras.KanChain.preservesColimitsOfShape_whiskeringRight`: post-composition with `Λ`
  preserves the colimits of shape `J` that `Λ` preserves.
* `UlmerBialgebras.KanChain.preservesColimitsOfShape_step`: for a connected shape `J` whose colimits
  exist in `C` and are preserved by `Λ`, `step` preserves colimits of shape `J`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6
-/

@[expose] public section

universe w w' v v₁ v₂ u u₁ u₂

namespace UlmerBialgebras

open CategoryTheory Limits Functor

variable {C : Type u} [Category.{v} C] {I : Type u₁} [Category.{v₁} I]
  {K : Type u₂} [Category.{v₂} K]

namespace KanChain

variable (Λ : C ⥤ C) (k : I ⥤ K) (A : I ⥤ C)
variable [HasLeftKanExtension k A] [HasLeftKanExtension k (A ⋙ Λ)]

/-- Postcomposition with `Λ` preserves the colimits that `Λ` preserves. -/
lemma preservesColimitsOfShape_whiskeringRight {J : Type w} [Category.{w'} J]
    [HasColimitsOfShape J C] [PreservesColimitsOfShape J Λ] :
    PreservesColimitsOfShape J ((Functor.whiskeringRight K C C).obj Λ) := by
  refine preservesColimitsOfShape_of_evaluation _ J fun x => ?_
  exact inferInstanceAs (PreservesColimitsOfShape J ((evaluation K C).obj x ⋙ Λ))

variable (ψ : A ⋙ Λ ⟶ A) [HasPushouts C] {J : Type w} [Category.{w'} J] [IsConnected J]

section

variable (W : J ⥤ Ext k A)
variable (s : Cocone (W ⋙ step Λ k A ψ ⋙ StructuredArrow.proj A ((whiskeringLeft I K C).obj k)))

/-- (Implementation) The left legs of the pushouts, as a transformation from a constant
functor. -/
@[simps]
noncomputable def sInlNat : (Functor.const J).obj (ee k A).right
    ⟶ W ⋙ step Λ k A ψ ⋙ StructuredArrow.proj A ((whiskeringLeft I K C).obj k) where
  app j := sInl Λ k A ψ (W.obj j)
  naturality _ _ _ := by simp

/-- For connected `J`, the composite `sInl (W.obj j) ≫ s.ι.app j` does not depend on `j`. -/
lemma sInl_const (j j' : J) :
    sInl Λ k A ψ (W.obj j) ≫ s.ι.app j = sInl Λ k A ψ (W.obj j') ≫ s.ι.app j' :=
  nat_trans_from_is_connected (sInlNat Λ k A ψ W ≫ s.ι) j j'

end

variable [HasColimitsOfShape J C] [PreservesColimitsOfShape J Λ]

section

variable (W : J ⥤ Ext k A) {c : Cocone W} (hc : IsColimit c)

/-- (Implementation) The colimit of the `Λ`-shifted diagram. -/
noncomputable def colimΛ :
    IsColimit (((Functor.whiskeringRight K C C).obj Λ).mapCocone
      ((StructuredArrow.proj A ((whiskeringLeft I K C).obj k)).mapCocone c)) := by
  haveI := preservesColimitsOfShape_whiskeringRight (K := K) Λ (J := J)
  exact isColimitOfPreserves _ (isColimitOfPreserves _ hc)

variable (s : Cocone (W ⋙ step Λ k A ψ ⋙ StructuredArrow.proj A ((whiskeringLeft I K C).obj k)))

/-- (Implementation) The cocone on the `Λ`-shifted diagram induced by a cocone on the
diagram of pushouts. -/
@[simps]
noncomputable def sCoconeΛ : Cocone ((W ⋙ StructuredArrow.proj A
    ((whiskeringLeft I K C).obj k)) ⋙ (Functor.whiskeringRight K C C).obj Λ) where
  pt := s.pt
  ι :=
    { app := fun j => sInr Λ k A ψ (W.obj j) ≫ s.ι.app j
      naturality := fun j j' f => by
        dsimp
        rw [Category.comp_id, ← s.w f, ← Category.assoc, ← Category.assoc]
        congr 1
        exact (sInr_step_map Λ k A ψ (W.map f)).symm }

end

/-- `step` followed by the projection to functors `K ⥤ C` preserves connected colimits. -/
lemma preservesColimitsOfShape_step_proj :
    PreservesColimitsOfShape J (step Λ k A ψ ⋙
      StructuredArrow.proj A ((whiskeringLeft I K C).obj k)) := by
  constructor
  intro W
  constructor
  intro c hc
  -- `step x` is a pushout of `ee` and `Λ x` over `pp`. Given a cocone `s` on the image of the
  -- diagram, its left legs agree (`sInl_const`, `J` connected) and its right legs form a cocone
  -- on the `Λ`-shifted diagram (`sCoconeΛ`), whose colimit `Λ` preserves (`colimΛ`); `sDesc`
  -- glues the two into the unique descending map.
  have : Nonempty J := IsConnected.is_nonempty
  set j₀ := Classical.arbitrary J with hj₀
  refine ⟨?_⟩
  refine IsColimit.ofExistsUnique fun s => ?_
  have hΛ := colimΛ Λ k A W hc
  have hcompat : bb Λ k A ψ ≫ (sInl Λ k A ψ (W.obj j₀) ≫ s.ι.app j₀)
      = (aa Λ k A c.pt).right ≫ hΛ.desc (sCoconeΛ Λ k A ψ W s) := by
    rw [← aa_naturality Λ k A (y := c.pt) (c.ι.app j₀), Category.assoc]
    have h := hΛ.fac (sCoconeΛ Λ k A ψ W s) j₀
    dsimp at h
    rw [h, sCoconeΛ_ι_app]
    exact (Category.assoc _ _ _).symm.trans
      ((eq_whisker (sq Λ k A ψ _) _).trans (Category.assoc _ _ _))
  refine ⟨sDesc Λ k A ψ (sInl Λ k A ψ (W.obj j₀) ≫ s.ι.app j₀)
    (hΛ.desc (sCoconeΛ Λ k A ψ W s)) hcompat, ?_, ?_⟩
  · intro j
    change ((step Λ k A ψ).map (c.ι.app j)).right ≫ _ = _
    apply stepObj_hom_ext
    · rw [← Category.assoc, sInl_step_map Λ k A ψ (y := c.pt) (c.ι.app j)]
      exact (sInl_sDesc _ _ _ _ _ _ _).trans (sInl_const Λ k A ψ W s j₀ j)
    · rw [← Category.assoc, sInr_step_map Λ k A ψ (y := c.pt) (c.ι.app j), Category.assoc]
      exact (whisker_eq _ (sInr_sDesc _ _ _ _ _ _ _)).trans (hΛ.fac (sCoconeΛ Λ k A ψ W s) j)
  · intro m hm
    apply stepObj_hom_ext
    · refine Eq.trans ?_ (sInl_sDesc _ _ _ _ _ _ _).symm
      rw [← sInl_step_map Λ k A ψ (y := c.pt) (c.ι.app j₀), Category.assoc]
      congr 1
      exact hm j₀
    · refine Eq.trans ?_ (sInr_sDesc _ _ _ _ _ _ _).symm
      refine hΛ.uniq (sCoconeΛ Λ k A ψ W s) _ fun j => ?_
      have h := hm j
      dsimp
      exact (Category.assoc _ _ _).symm.trans ((eq_whisker
        (sInr_step_map Λ k A ψ (y := c.pt) (c.ι.app j)).symm _).trans
          ((Category.assoc _ _ _).trans (whisker_eq _ h)))

/-- **`step` preserves connected colimits.** -/
lemma preservesColimitsOfShape_step : PreservesColimitsOfShape J (step Λ k A ψ) := by
  have := preservesColimitsOfShape_step_proj Λ k A ψ (J := J)
  exact preservesColimitsOfShape_of_reflects_of_preserves (step Λ k A ψ)
    (StructuredArrow.proj A ((whiskeringLeft I K C).obj k))

end KanChain

end UlmerBialgebras
