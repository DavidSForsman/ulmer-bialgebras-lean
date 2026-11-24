module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Proofs.Sec5.CatBridge
public import UlmerBialgebras.Kan.ColimKan
public import UlmerBialgebras.Kan.LimKan
public import Foundations.CategoryTheory.Factorization.OFS
public import Mathlib.CategoryTheory.Monad.Monadicity

/-! # General support for Sections 5–7

Auxiliary facts used in the monadicity and orthogonality proofs.

## Main results

* `UlmerBialgebras.Paper.createsColimitOfCompConservative`: if `V` is conservative and preserves
  the colimit of `Dg ⋙ G`, which exists, and `G ⋙ V` creates the colimit of `Dg`, then `G` creates
  it.
* `UlmerBialgebras.Paper.orthogonal_of_map`, `UlmerBialgebras.Paper.orthogonalLE1_of_map`: fully
  faithful functors reflect orthogonality, and faithful functors reflect uniqueness of diagonal
  fillers.
* `UlmerBialgebras.Paper.preservesColimit_of_strictlyCreatesLeftKan`,
  `UlmerBialgebras.Paper.hasColimit_of_strictlyCreatesLeftKan`: if `F` strictly creates left Kan
  extensions of `d` along `I ⟶ 1` and `d ≫ F` has a colimit, then `F` preserves the colimit of `d`
  and `d` has a colimit.
* `UlmerBialgebras.Paper.preservesLimit_of_reflect`,
  `UlmerBialgebras.Paper.preservesColimit_of_reflect`: if `U` strictly creates the relevant Kan
  extensions and `Fb ⋙ U` preserves the (co)limit of `K`, then `Fb` preserves it.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 5–7
-/

@[expose] public section

universe u v w u' v' w₀ u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section CreatesComp

variable {J A B Cc : Type*} [Category J] [Category A] [Category B] [Category Cc]

/-- If `V` is conservative and preserves the colimit of `Dg ⋙ G`, which exists, and `G ⋙ V`
creates the colimit of `Dg`, then `G` creates it. -/
@[instance_reducible]
noncomputable def createsColimitOfCompConservative (G : A ⥤ B) (V : B ⥤ Cc)
    [V.ReflectsIsomorphisms] (Dg : J ⥤ A) [HasColimit (Dg ⋙ G)] [PreservesColimit (Dg ⋙ G) V]
    [CreatesColimit Dg (G ⋙ V)] : CreatesColimit Dg G where
  reflects {_} hc := ⟨isColimitOfReflects (G ⋙ V) (isColimitOfPreserves V hc)⟩
  lifts c hc :=
    let hVc : IsColimit (V.mapCocone c) := isColimitOfPreserves V hc
    let d := liftColimit (K := Dg) (F := G ⋙ V) hVc
    haveI : ReflectsColimit (Dg ⋙ G) V := reflectsColimit_of_reflectsIsomorphisms (Dg ⋙ G) V
    let hGd : IsColimit (G.mapCocone d) :=
      isColimitOfReflects V (IsColimit.ofIsoColimit hVc
        ((liftedColimitMapsToOriginal (K := Dg) (F := G ⋙ V) hVc).symm :
          V.mapCocone c ≅ V.mapCocone (G.mapCocone d)))
    { liftedCocone := d
      validLift := hGd.uniqueUpToIso hc }

/-- Being a split pair is invariant under natural isomorphism of functors. -/
lemma isSplitPair_of_iso {F F' : A ⥤ B} (e : F ≅ F') {X Y : A} {f g : X ⟶ Y}
    (h : F'.IsSplitPair f g) : F.IsSplitPair f g := by
  obtain ⟨Z, π, ⟨q⟩⟩ := h.splittable
  have nf : F.map f = e.hom.app X ≫ F'.map f ≫ e.inv.app Y := by
    rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have ng : F.map g = e.hom.app X ≫ F'.map g ≫ e.inv.app Y := by
    rw [← Category.assoc, ← e.hom.naturality, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  refine ⟨⟨Z, e.hom.app Y ≫ π, ⟨
    { rightSection := q.rightSection ≫ e.inv.app Y
      leftSection := e.hom.app Y ≫ q.leftSection ≫ e.inv.app X
      condition := ?_, rightSection_π := ?_, leftSection_bottom := ?_,
      leftSection_top := ?_ }⟩⟩⟩
  · rw [nf, ng]; simp only [Category.assoc, Iso.inv_hom_id_app_assoc]; rw [q.condition]
  · simp
  · rw [ng]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, q.leftSection_bottom_assoc,
      Iso.hom_inv_id_app]
  · rw [nf]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, q.leftSection_top_assoc]

end CreatesComp

section Orth
variable {A : Type*} [Category A] {B' : Type*} [Category B']

/-- Orthogonality is reflected by fully faithful functors. -/
lemma orthogonal_of_map (F : A ⥤ B') [F.Full] [F.Faithful] {a b c d : A} {e : a ⟶ b}
    {m : c ⟶ d} (h : Orthogonal (F.map e) (F.map m)) : Orthogonal e m := by
  intro u v huv
  obtain ⟨k, ⟨k1, k2⟩, kuniq⟩ := h (F.map u) (F.map v) (by rw [← F.map_comp, ← F.map_comp, huv])
  refine ⟨F.preimage k, ⟨F.map_injective ?_, F.map_injective ?_⟩, ?_⟩
  · rw [F.map_comp, F.map_preimage, k1]
  · rw [F.map_comp, F.map_preimage, k2]
  · rintro k' ⟨k'1, k'2⟩
    apply F.map_injective
    rw [F.map_preimage]
    exact kuniq _ ⟨by rw [← F.map_comp, k'1], by rw [← F.map_comp, k'2]⟩

/-- Uniqueness of diagonal fillers is reflected by faithful functors. -/
lemma orthogonalLE1_of_map (F : A ⥤ B') [F.Faithful] {a b c d : A} {e : a ⟶ b}
    {m : c ⟶ d} (h : OrthogonalLE1 (F.map e) (F.map m)) : OrthogonalLE1 e m := by
  intro u v huv k k' h1 h2 h1' h2'
  apply F.map_injective
  exact h (F.map u) (F.map v) (by rw [← F.map_comp, ← F.map_comp, huv]) _ _
    (by rw [← F.map_comp, h1]) (by rw [← F.map_comp, h2])
    (by rw [← F.map_comp, h1']) (by rw [← F.map_comp, h2'])

end Orth


section ColimBridges

variable {I C D : Cat.{v, u}}

/-- If `F` strictly creates left Kan extensions of `d` along `I ⟶ 1` and `d ≫ F` has a colimit,
    then `F` preserves the colimit of `d` (colimits as left Kan extensions along `I ⟶ 1`). -/
theorem preservesColimit_of_strictlyCreatesLeftKan {X Y : Cat.{v, u}} (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesLeftKan (toOne I) d F)
    [HasColimit (d ≫ F).toFunctor] :
    PreservesColimit (d).toFunctor (F).toFunctor := by
  constructor
  intro c hc
  have hL : Nonempty (IsInitial (leftExtOfCocone c)) := ⟨isInitialLeftExtOfIsColimit hc⟩
  have h2 := preservesInitial_of_strictlyCreatesInitial _ hcr
    (b₀ := leftExtOfCocone (colimit.cocone (d ≫ F).toFunctor))
    ⟨isInitialLeftExtOfIsColimit (colimit.isColimit _)⟩ _ hL
  exact ⟨IsColimit.ofIsoColimit (isColimitCoconeOfLeftExt h2.some)
    (coconeOfLeftExtPushIso F (leftExtOfCocone c))⟩

/-- If `F` strictly creates left Kan extensions of `d` along `I ⟶ 1` and `d ≫ F` has a colimit,
    then `d` has a colimit. -/
theorem hasColimit_of_strictlyCreatesLeftKan {X Y : Cat.{v, u}} (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesLeftKan (toOne I) d F)
    [HasColimit (d ≫ F).toFunctor] :
    HasColimit (d).toFunctor := by
  obtain ⟨⟨L, hLL, -⟩, hinit⟩ := hcr
    (leftExtOfCocone (colimit.cocone (d ≫ F).toFunctor))
    ⟨isInitialLeftExtOfIsColimit (colimit.isColimit _)⟩
  exact ⟨⟨⟨_, isColimitCoconeOfLeftExt (hinit L hLL).some⟩⟩⟩

end ColimBridges

section AsSmallColim

variable {J : Type} [SmallCategory J] {X Y : Type u} [Category.{u} X] [Category.{u} Y]

end AsSmallColim

section Reflect

variable {I X Y : Cat.{v, u}}

/-- A 1-cell strictly creating the right Kan extensions of `d` along `I ⟶ 1` reflects
limits of `d`. -/
theorem isLimit_of_strictlyCreatesRightKan (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesRightKan (toOne I) d F) (c : Cone (d).toFunctor)
    (hc : IsLimit ((F).toFunctor.mapCone c)) : Nonempty (IsLimit c) := by
  obtain ⟨-, hterm⟩ := hcr _ ⟨isTerminalRightExtOfIsLimit
    (IsLimit.ofIsoLimit hc (coneOfRightExtPushIso F (rightExtOfCone c)).symm)⟩
  exact ⟨isLimitConeOfRightExt (hterm _ rfl).some⟩

/-- A 1-cell strictly creating the left Kan extensions of `d` along `I ⟶ 1` reflects
colimits of `d`. -/
theorem isColimit_of_strictlyCreatesLeftKan (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesLeftKan (toOne I) d F) (c : Cocone (d).toFunctor)
    (hc : IsColimit ((F).toFunctor.mapCocone c)) :
    Nonempty (IsColimit c) := by
  obtain ⟨-, hinit⟩ := hcr _ ⟨isInitialLeftExtOfIsColimit
    (IsColimit.ofIsoColimit hc (coconeOfLeftExtPushIso F (leftExtOfCocone c)).symm)⟩
  exact ⟨isColimitCoconeOfLeftExt (hinit _ rfl).some⟩

end Reflect

section Reflect2

variable {J : Type} [SmallCategory J] {A D Cc : Cat.{v, max u v}}

/-- If `U` strictly creates the right Kan extensions of `K ⋙ Fb` along a shape `J'` equivalent
to `J`, and `Fb ⋙ U` preserves the limit of `K`, then `Fb` preserves it. -/
theorem preservesLimit_of_reflect (K : J ⥤ (A : Type (max u v))) (Fb : A ⟶ D) (U : D ⟶ Cc)
    (J' : Cat.{v, max u v}) (e : J ≌ (J' : Type (max u v)))
    (hcr : StrictlyCreatesRightKan (toOne J')
      (e.inverse ⋙ K ⋙ Fb.toFunctor).toCatHom U)
    [PreservesLimit K ((Fb).toFunctor ⋙ U.toFunctor)] :
    PreservesLimit K (Fb).toFunctor := by
  constructor
  intro c hc
  have h1 : IsLimit (U.toFunctor.mapCone
      ((Fb).toFunctor.mapCone c)) :=
    isLimitOfPreserves ((Fb).toFunctor ⋙ U.toFunctor) hc
  have h2 := (h1.whiskerEquivalence e.symm).ofIsoLimit
    (Functor.mapConeWhisker U.toFunctor).symm
  obtain ⟨h3⟩ := isLimit_of_strictlyCreatesRightKan _ U hcr _ h2
  exact ⟨IsLimit.ofWhiskerEquivalence e.symm h3⟩

/-- The colimit version of `preservesLimit_of_reflect`. -/
theorem preservesColimit_of_reflect (K : J ⥤ (A : Type (max u v))) (Fb : A ⟶ D) (U : D ⟶ Cc)
    (J' : Cat.{v, max u v}) (e : J ≌ (J' : Type (max u v)))
    (hcr : StrictlyCreatesLeftKan (toOne J')
      (e.inverse ⋙ K ⋙ Fb.toFunctor).toCatHom U)
    [PreservesColimit K ((Fb).toFunctor ⋙
      U.toFunctor)] :
    PreservesColimit K (Fb).toFunctor := by
  constructor
  intro c hc
  have h1 : IsColimit (U.toFunctor.mapCocone
      ((Fb).toFunctor.mapCocone c)) :=
    isColimitOfPreserves ((Fb).toFunctor ⋙
      U.toFunctor) hc
  have h2 := (h1.whiskerEquivalence e.symm).ofIsoColimit
    (Functor.mapCoconeWhisker U.toFunctor).symm
  obtain ⟨h3⟩ := isColimit_of_strictlyCreatesLeftKan _ U hcr _ h2
  exact ⟨IsColimit.ofWhiskerEquivalence e.symm h3⟩

end Reflect2

end UlmerBialgebras.Paper
