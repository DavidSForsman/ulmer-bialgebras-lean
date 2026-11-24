module

public import UlmerBialgebras.Paper.Sec4DefsEx420
public import UlmerBialgebras.Proofs.Sec4.WidePushoutSifted
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutModel
public import UlmerBialgebras.Kan.SiftedModel

/-!
# Example 4.20 (2): wide pushouts from the conditions of the closing remark

For a `Σ`-model `M` in `CAT` whose categories have kernel pairs and whose functors preserve sifted
colimits componentwise, the forgetful functor `U : M^T → M₀` strictly creates wide pushouts of
families of morphisms that `U` sends to regular epimorphisms
(`UlmerBialgebras.Paper.thy_strictlyCreates_widePushouts_of_regularEpi`).

* With at least two legs, this is Theorem 4.19 (`RegEpiWide.thy_strictlyCreates_widePushouts`).
  Its hypothesis, that each `M(B)` preserves wide pushouts of regular epis componentwise, follows
  from the sifted shape `MultiReflexivePair` (`preservesWidePushoutsOfRegEpis_of_kernelPairs`):
  the index type is reindexed to a `u`-small one, as `WidePushoutShape K ≌ J` with `J` in
  `Type u` makes `K` `u`-small.
* With at most one leg, the shape has a terminal object, so it is filtered, hence sifted
  (Corollary 4.17, `thy_strictlyCreates_colimits`).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section

universe v u w u₁ u₂ u₃ s₁ s₂ s₃

open CategoryTheory Limits

attribute [local instance] uliftCategory

namespace UlmerBialgebras.Paper

section Shapes

/-- A wide pushout shape with at most one leg is filtered: it has a terminal object. -/
theorem isFiltered_widePushoutShape_of_subsingleton (K : Type w) [Subsingleton K] :
    IsFiltered (WidePushoutShape K) := by
  have thin : ∀ (x y : WidePushoutShape K) (f g : WidePushoutShape.Hom x y), f = g := by
    intro x y f g
    cases f <;> cases g <;> rfl
  rcases isEmpty_or_nonempty K with hK | ⟨⟨j⟩⟩
  · have t : IsTerminal (C := WidePushoutShape K) none :=
      IsTerminal.ofUniqueHom (C := WidePushoutShape K) (fun x => match x with
        | none => WidePushoutShape.Hom.id none
        | some k => (hK.false k).elim) fun _ _ => thin _ _ _ _
    exact IsFiltered.of_isTerminal _ t
  · have t : IsTerminal (C := WidePushoutShape K) (some j) :=
      IsTerminal.ofUniqueHom (C := WidePushoutShape K) (fun x => match x with
        | none => WidePushoutShape.Hom.init j
        | some k => (Subsingleton.elim k j) ▸ WidePushoutShape.Hom.id (some k)) fun _ _ =>
          thin _ _ _ _
    exact IsFiltered.of_isTerminal _ t

/-- The index type of a wide pushout shape equivalent to a category with objects in `Type u` is
`u`-small. -/
theorem small_of_widePushoutShape_equiv {K : Type w} {J : Type u} [Category J]
    (e : WidePushoutShape K ≌ J) : Small.{u} K := by
  refine small_of_injective (f := fun j => e.functor.obj (some j)) fun j k h => ?_
  have i : @Iso (WidePushoutShape K) _ (some j) (some k) :=
    e.fullyFaithfulFunctor.preimageIso (eqToIso h)
  obtain _ | _ := (i.hom : WidePushoutShape.Hom (some j) (some k))
  rfl

end Shapes

variable [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
  (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{v, u}]

omit [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₃} Cat.{v, u}] in
/-- If the function symbols of `M` preserve small sifted colimits componentwise, and the sifted
category `S` (of any size) is equivalent to a small category `J : Type v`, then each
`updateFunctor x i ⋙ M.fn B` preserves colimits of shape `S`. -/
theorem preservesColimitsOfShape_of_sifted (h : M.SiftedColimitsComponentwise)
    {S : Type*} [Category S] [IsSifted S] (J : Type v) [SmallCategory J] (E : S ≌ J)
    (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)) :
    PreservesColimitsOfShape S (updateFunctor x i ⋙ (M.fn B).toFunctor) := by
  have : IsSifted J := IsSifted.isSifted_of_equiv E.symm
  obtain ⟨p⟩ := (h J).2 B i x
  exact preservesColimitsOfShape_of_equiv E.symm _

omit [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₃} Cat.{v, u}] in
/-- The componentwise preservation of a sifted shape `S` of any size that is equivalent to a small
one. -/
theorem preservesColimitsComponentwise_of_sifted (h : M.SiftedColimitsComponentwise)
    {S : Type*} [Category S] [IsSifted S] (J : Type v) [SmallCategory J] (E : S ≌ J)
    (B : Sg.Fun) : PreservesColimitsComponentwise M S B :=
  fun i x => ⟨preservesColimitsOfShape_of_sifted M h J E B i x⟩

/-- **Example 4.20 (2), wide pushouts**: if `M` has sifted colimits componentwise and its
categories have kernel pairs, `U : M^T → M₀` strictly creates the wide pushout of any family of
morphisms that `U` sends to regular epimorphisms. -/
theorem thy_strictlyCreates_widePushouts_of_regularEpi (h : M.SiftedColimitsComponentwise)
    (hk : M.HasKernelPairs)
    (K : Type v) (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
      (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (M.e sg T ≫ M.u sg) := by
  classical
  by_cases hK : Nontrivial K
  · refine RegEpiWide.thy_strictlyCreates_widePushouts M sg T K (fun c a b f hf => ?_)
      (fun B i x => ?_) J e d hd
    · have := hk c f
      exact ⟨pullback f f, pullback.fst f f, pullback.snd f f,
        IsKernelPair.isReflexivePair (IsPullback.of_hasPullback f f), pullback.condition,
        ⟨IsKernelPair.toCoequalizer (IsPullback.of_hasPullback f f) hf.some⟩⟩
    · let F := updateFunctor x i ⋙ (M.fn B).toFunctor
      have : PreservesColimitsOfShape WalkingReflexivePair F :=
        preservesColimitsOfShape_of_sifted M h _
          (ULiftHomULiftCategory.equiv.{v, v} WalkingReflexivePair) B i x
      have : PreservesColimitsOfShape (MultiReflexivePair K) F :=
        preservesColimitsOfShape_of_sifted M h _
          (ULiftHomULiftCategory.equiv.{v, v} (MultiReflexivePair K)) B i x
      exact preservesWidePushoutsOfRegEpis_of_kernelPairs F K fun f => hk _ f
  · have : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
    have : IsFiltered (WidePushoutShape K) := isFiltered_widePushoutShape_of_subsingleton K
    have : IsFiltered (J : Type u) := IsFiltered.of_equivalence e
    have : IsSifted (J : Type u) := IsFiltered.isSifted
    exact thy_strictlyCreates_colimits M sg T J
      (preservesColimitsComponentwise_of_sifted M h _ e.symm) d

end UlmerBialgebras.Paper
