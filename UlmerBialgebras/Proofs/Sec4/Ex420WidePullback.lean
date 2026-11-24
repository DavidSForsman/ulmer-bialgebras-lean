module

public import UlmerBialgebras.Proofs.Sec4.Ex420WidePushout
public import UlmerBialgebras.Proofs.Sec4.HopfModelLimits
public import UlmerBialgebras.Proofs.Sec4.OpTranslateWide
public import UlmerBialgebras.Proofs.Sec4.Support.RegMonoCoreflexive
public import UlmerBialgebras.Proofs.Sec4.RegMonoWidePullbackModel
public import UlmerBialgebras.Kan.CosiftedModel

/-!
# Example 4.20 (2): joint pullbacks from the conditions of the closing remark

For a `Σ`-model `M` in `CAT` whose categories have cokernel pairs and whose functors preserve
finite cosifted limits componentwise, the forgetful functor `U : M^T → M₀` strictly creates the
joint pullback of a finite family of morphisms that `U` sends to regular monomorphisms
(`UlmerBialgebras.Paper.thy_strictlyCreates_widePullbacks_of_regularMono`). This is the dual of
`thy_strictlyCreates_widePushouts_of_regularEpi`.

* With at least two legs, this is the dual of Theorem 4.19
  (`RegMonoWide.thy_strictlyCreates_widePullbacks`). Its hypothesis follows, in the opposite
  categories, from `preservesWidePushoutsOfRegEpis_of_kernelPairs` for the finite sifted shape
  `MultiReflexivePair (Fin n)`: its opposite is a finite cosifted shape.
* With at most one leg, the shape has an initial object, so it is cofiltered, hence cosifted.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 4.20
-/

@[expose] public section

universe v u w u₁ u₂ u₃ s₁ s₂ s₃

open CategoryTheory Limits

namespace UlmerBialgebras.Paper

/-- A wide pullback shape with at most one leg is cofiltered: it has an initial object. -/
theorem isCofiltered_widePullbackShape_of_subsingleton (K : Type w) [Subsingleton K] :
    IsCofiltered (WidePullbackShape K) := by
  have thin : ∀ (x y : WidePullbackShape K) (f g : WidePullbackShape.Hom x y), f = g := by
    intro x y f g
    cases f <;> cases g <;> rfl
  rcases isEmpty_or_nonempty K with hK | ⟨⟨j⟩⟩
  · have t : IsInitial (C := WidePullbackShape K) none :=
      IsInitial.ofUniqueHom (C := WidePullbackShape K) (fun x => match x with
        | none => WidePullbackShape.Hom.id none
        | some k => (hK.false k).elim) fun _ _ => thin _ _ _ _
    exact IsCofiltered.of_isInitial _ t
  · have t : IsInitial (C := WidePullbackShape K) (some j) :=
      IsInitial.ofUniqueHom (C := WidePullbackShape K) (fun x => match x with
        | none => WidePullbackShape.Hom.term j
        | some k => (Subsingleton.elim k j) ▸ WidePullbackShape.Hom.id (some k)) fun _ _ =>
          thin _ _ _ _
    exact IsCofiltered.of_isInitial _ t

variable [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, u})
  (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{v, u}]

omit [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
  [HasChosenProductsOfSize.{s₃} Cat.{v, u}] in
/-- From finite cosifted limits componentwise, the functors `M(B)`, in the opposite categories,
preserve colimits of the opposite `S` of a finite cosifted shape. -/
theorem op_preservesColimitsOfShape_of_finCosifted (h : M.FinCosiftedLimitsComponentwise)
    (S : Type) [SmallCategory S] [FinCategory S] [IsSifted S]
    (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)) :
    PreservesColimitsOfShape S (updateFunctor x i ⋙ (M.fn B).toFunctor).op := by
  have : IsCosifted Sᵒᵖ := IsSifted.isSifted_of_equiv (opOpEquivalence S)
  obtain ⟨p⟩ := (h Sᵒᵖ).2 B i x
  have := (OpTranslate.preservesLimitsOfShape_iff_op Sᵒᵖ _).1 p
  exact preservesColimitsOfShape_of_equiv (opOpEquivalence S) _

/-- **Example 4.20 (2), joint pullbacks**: if `M` has finite cosifted limits componentwise and its
categories have cokernel pairs, `U : M^T → M₀` strictly creates the joint pullback of any finite
family of morphisms that `U` sends to regular monomorphisms. -/
theorem thy_strictlyCreates_widePullbacks_of_regularMono (h : M.FinCosiftedLimitsComponentwise)
    (hc : M.HasCokernelPairs)
    (K : Type v) [Finite K] (J : Cat.{v, u}) (e : WidePullbackShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularMono ((d ≫ M.e sg T ≫ M.u sg).toFunctor.map
      (e.functor.map (WidePullbackShape.Hom.term j))))) :
    StrictlyCreatesRightKan (toOne J) d (M.e sg T ≫ M.u sg) := by
  classical
  let σ : K ≃ Fin (Nat.card K) := Finite.equivFin K
  by_cases hK : Nontrivial K
  -- At least two legs: enumerate them and use the regular-mono wide pullbacks.
  · refine RegMonoWide.thy_strictlyCreates_widePullbacks M sg T K
      (fun c => RegMonoWide.regularMonosAreCoreflexiveEqualizers_of_hasCokernelPairs
        fun _ _ m => hc c m) (fun B i x => ?_) J e d hd
    let F := updateFunctor x i ⋙ (M.fn B).toFunctor
    refine (OpTranslate.preservesWidePullbacks_iff_op_in F).2
      ((OpTranslate.preservesWidePushouts_iff_in F.op).1 ?_)
    let L := Fin (Nat.card K)
    have : PreservesColimitsOfShape WalkingReflexivePair F.op :=
      op_preservesColimitsOfShape_of_finCosifted M h WalkingReflexivePair B i x
    have : PreservesColimitsOfShape (MultiReflexivePair L) F.op :=
      op_preservesColimitsOfShape_of_finCosifted M h (MultiReflexivePair L) B i x
    have hL : PreservesWidePushoutsOfRegEpis L F.op :=
      preservesWidePushoutsOfRegEpis_of_kernelPairs F.op L fun f =>
        (hasPullback_op_iff_hasPushout f.unop f.unop).2 (hc _ f.unop)
    intro dg hdg
    let E := WidePushoutShape.equivalenceOfEquiv L σ
    have : PreservesColimit (E.inverse ⋙ dg) F.op := hL _ fun j => hdg (σ.symm j)
    exact Functor.Final.preservesColimit_of_comp E.inverse
  -- At most one leg: the wide pullback is trivial.
  · have : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
    have : Subsingleton (Fin (Nat.card K)) := σ.symm.subsingleton
    let E : (J : Type u) ≌ WidePullbackShape (Fin (Nat.card K)) :=
      e.symm.trans (WidePullbackShape.equivalenceOfEquiv _ σ)
    have : IsCofiltered (WidePullbackShape (Fin (Nat.card K))) :=
      isCofiltered_widePullbackShape_of_subsingleton _
    have : IsCofiltered (J : Type u) := IsCofiltered.of_equivalence E.symm
    have : IsCosifted (J : Type u) := IsFiltered.isSifted
    have : IsCosifted (WidePullbackShape (Fin (Nat.card K))) := IsFiltered.isSifted
    refine thy_strictlyCreates_limits M sg T J (fun B i x => ?_) d
    obtain ⟨p⟩ := (h (WidePullbackShape (Fin (Nat.card K)))).2 B i x
    exact ⟨preservesLimitsOfShape_of_equiv E.symm _⟩

end UlmerBialgebras.Paper
