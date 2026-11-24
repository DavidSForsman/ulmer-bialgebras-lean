module

public import UlmerBialgebras.Proofs.Sec4.Sec4
public import Foundations.CategoryTheory.Category.ThinShape
public import UlmerBialgebras.Kan.ColimKan
public import UlmerBialgebras.Kan.LimKan
public import UlmerBialgebras.Monadicity.KappaShapes
public import UlmerBialgebras.Monadicity.SubTheoryColimits

/-!
# Bridges for the kernel-pair clause of Theorem 6.6 (3)

Helper results for `thm_6_6_3_coeq` (in `UlmerBialgebras/Proofs/Sec6/Sec6Bialgebra.lean`):
translation between Kan
extensions along `I ⟶ 1` and ordinary (co)limits for a single diagram, quotient initiality and
subterminality criteria, transport along `AsSmall`, and preservation of pullbacks by `u_B`
(from Corollary 4.8, right Kan extensions), and regularity of the legs of a coequalizer.

## Main results

* `UlmerBialgebras.Paper.preservesLeftKan_of_preservesColimit`: `F` preserves the left Kan
  extensions of `d` along `I ⟶ 1` when it preserves the colimit of `d`.
* `UlmerBialgebras.Paper.preservesLimit_of_strictlyCreatesRightKan`: a 1-cell strictly creating the
  right Kan extensions of `d` along `I ⟶ 1` preserves the limit of `d` when the limit of `d ⋙ F`
  exists.
* `UlmerBialgebras.Paper.uB_preservesLimit_cospan`: `U_B` preserves pullbacks when `G` preserves
  pullbacks and `G'` preserves the joint monicness of pullback projections (via Corollary 4.8).
* `UlmerBialgebras.Paper.regularEpi_of_isColimit_walkingParallelPair`: the leg at `one` of a colimit
  cocone of shape `WalkingParallelPair` is a regular epimorphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 4.8
  and Theorem 6.6 (3)
-/

@[expose] public section

universe u v
namespace UlmerBialgebras.Paper
open CategoryTheory Limits

section Bridges

variable {I C D : Cat.{v, u}}

/-- `F` preserves the left Kan extensions of `d` along `I ⟶ 1` when it preserves the
colimit of `d`. -/
theorem preservesLeftKan_of_preservesColimit (F : C ⟶ D) (d : I ⟶ C)
    [PreservesColimit (d).toFunctor (F).toFunctor] :
    PreservesLeftKan (toOne I) d F := by
  intro L hL
  refine ⟨isInitialLeftExtOfIsColimit ?_⟩
  refine IsColimit.ofIsoColimit ?_ (coconeOfLeftExtPushIso F L).symm
  exact isColimitOfPreserves (F).toFunctor (isColimitCoconeOfLeftExt hL.some)

/-- A left extension along `I ⟶ 1` with an epimorphic unit component is quotient initial. -/
theorem quotientInitial_of_epi_unit {d : I ⟶ C} (L : LeftExt (toOne I) d) (i : (I : Type u))
    [Epi (L.unit.toNatTrans.app i)] : QuotientInitial L := by
  intro Y
  refine ⟨fun a b => (leftExtHomEquiv L Y).injective ?_⟩
  ext
  have ha := ((leftExtHomEquiv L Y) a).w i
  have hb := ((leftExtHomEquiv L Y) b).w i
  exact (cancel_epi (L.unit.toNatTrans.app i)).1 (ha.trans hb.symm)

/-- A right extension along `I ⟶ 1` whose counit components are jointly monic is
subterminal. -/
theorem subterminal_of_jointlyMono {d : I ⟶ C} (R : RightExt (toOne I) d)
    (h : ∀ ⦃y : (C : Type u)⦄ (p q : y ⟶ R.ext.toFunctor.obj One.star),
      (∀ i, p ≫ R.counit.toNatTrans.app i = q ≫ R.counit.toNatTrans.app i) → p = q) :
    Subterminal R := by
  intro Y a b
  refine (rightExtHomEquiv Y R).injective ?_
  ext
  exact h _ _ fun i => (((rightExtHomEquiv Y R) a).w i).trans (((rightExtHomEquiv Y R) b).w i).symm

/-- A 1-cell strictly creating the right Kan extensions of `d` along `I ⟶ 1` preserves the
limit of `d`, as soon as the limit of `d ⋙ F` exists. -/
theorem preservesLimit_of_strictlyCreatesRightKan {X Y : Cat.{v, u}} (d : I ⟶ X) (F : X ⟶ Y)
    (hcr : StrictlyCreatesRightKan (toOne I) d F)
    [HasLimit (d ≫ F).toFunctor] :
    PreservesLimit (d).toFunctor (F).toFunctor := by
  constructor
  intro c hc
  have hR : Nonempty (IsTerminal (rightExtOfCone c)) := ⟨isTerminalRightExtOfIsLimit hc⟩
  have h2 := preservesTerminal_of_strictlyCreatesTerminal _ hcr
    (b₀ := rightExtOfCone (limit.cone (d ≫ F).toFunctor))
    ⟨isTerminalRightExtOfIsLimit (limit.isLimit _)⟩ _ hR
  exact ⟨IsLimit.ofIsoLimit (isLimitConeOfRightExt h2.some)
    (coneOfRightExtPushIso F (rightExtOfCone c))⟩

end Bridges

section AsSmallTransport

variable {J : Type} [SmallCategory J] {X Y : Type u} [Category.{u} X] [Category.{u} Y]

/-- Preservation of the limit of `e.functor ⋙ K` gives preservation of the limit of `K`. -/
theorem preservesLimit_of_equiv {J J' : Type*} [Category J] [Category J']
    {X Y : Type*} [Category X] [Category Y] (e : J' ≌ J) (K : J ⥤ X) (F : X ⥤ Y)
    [PreservesLimit (e.functor ⋙ K) F] : PreservesLimit K F := by
  constructor
  intro c hc
  have h1 : IsLimit (c.whisker e.functor) := hc.whiskerEquivalence e
  have h2 : IsLimit (F.mapCone (c.whisker e.functor)) := isLimitOfPreserves F h1
  have h3 : IsLimit ((F.mapCone c).whisker e.functor) :=
    h2.ofIsoLimit (Functor.mapConeWhisker F)
  exact ⟨IsLimit.ofWhiskerEquivalence e h3⟩

/-- Preservation of the colimit of `e.functor ⋙ K` gives preservation of the colimit of `K`. -/
theorem preservesColimit_of_equiv {J J' : Type*} [Category J] [Category J']
    {X Y : Type*} [Category X] [Category Y] (e : J' ≌ J) (K : J ⥤ X) (F : X ⥤ Y)
    [PreservesColimit (e.functor ⋙ K) F] : PreservesColimit K F := by
  constructor
  intro c hc
  have h1 : IsColimit (c.whisker e.functor) := hc.whiskerEquivalence e
  have h2 : IsColimit (F.mapCocone (c.whisker e.functor)) := isColimitOfPreserves F h1
  have h3 : IsColimit ((F.mapCocone c).whisker e.functor) :=
    h2.ofIsoColimit (Functor.mapCoconeWhisker F)
  exact ⟨IsColimit.ofWhiskerEquivalence e h3⟩

end AsSmallTransport

section KernelPairs

/-- `U_B` preserves pullbacks when `G` preserves pullbacks and `G'` the joint monicness of
pullback projections (Corollary 4.8, right Kan extensions). -/
theorem uB_preservesLimit_cospan (B : BialgDatum (Obj := Cat.{v, max u v}))
    (E : Equifier B.α B.β)
    [HasPullbacks (B.c : Type (max u v))]
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    {x y z : (E.pt : Type (max u v))} (f : x ⟶ z) (g : y ⟶ z) :
    PreservesLimit (cospan f g) (B.uB E).toFunctor := by
  let J : Cat.{v, max u v} := cospanShapeCat
  let e : WalkingCospan ≌ (J : Type (max u v)) := cospanShapeCat.equivalence
  let dC : J ⟶ E.pt := (e.symm.functor ⋙ cospan f g).toCatHom
  have : PreservesLimitsOfShape (J : Type (max u v)) (B.g).toFunctor :=
    preservesLimitsOfShape_of_equiv e _
  have hcr : StrictlyCreatesRightKan (toOne J) dC (B.uB E) := by
    refine cor_4_8_right B E (toOne J) dC
      (preservesRightKan_of_preservesLimitsOfShape B.g (dC ≫ B.uB E)) ?_
    intro R hR
    refine subterminal_of_jointlyMono _ ?_
    intro w p q hpq
    have hc := (isLimitConeOfRightExt hR.some).whiskerEquivalence e
    exact hG' _ _ hc p q (fun j => by
      have h := hpq (e.functor.obj j)
      simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, RightExt.push_obj_ext,
        RightExt.push_obj_counit, eqToHom_refl, Category.id_comp, Cat.whiskerRight_toNatTrans,
        Functor.whiskerRight_app, Cone.whisker_pt, Cone.whisker_π, Functor.whiskerLeft_app,
        coneOfRightExt_π_app] at h ⊢
      exact h)
  have : HasLimitsOfShape (J : Type (max u v)) (B.c : Type (max u v)) :=
    hasLimitsOfShape_of_equivalence e
  have : PreservesLimit (e.symm.functor ⋙ cospan f g) (B.uB E).toFunctor :=
    preservesLimit_of_strictlyCreatesRightKan dC (B.uB E) hcr
  exact preservesLimit_of_equiv e.symm (cospan f g) (B.uB E).toFunctor

/-- The leg at `one` of a colimit cocone over a diagram of shape `WalkingParallelPair` is a
regular epimorphism. -/
theorem regularEpi_of_isColimit_walkingParallelPair {X : Type u} [Category.{v} X]
    (K : WalkingParallelPair ⥤ X) (c : Cocone K) (hc : IsColimit c) :
    Nonempty (RegularEpi (c.ι.app WalkingParallelPair.one)) := by
  have w : K.map WalkingParallelPairHom.left ≫ c.ι.app WalkingParallelPair.one =
      K.map WalkingParallelPairHom.right ≫ c.ι.app WalkingParallelPair.one :=
    (c.w WalkingParallelPairHom.left).trans (c.w WalkingParallelPairHom.right).symm
  refine ⟨⟨K.obj WalkingParallelPair.zero, _, _, w, ?_⟩⟩
  have h := (IsColimit.precomposeHomEquiv (diagramIsoParallelPair K).symm c).symm hc
  exact IsColimit.ofIsoColimit h (Cofork.ext (Iso.refl _) (by simp [Cofork.π]))

end KernelPairs

end UlmerBialgebras.Paper
