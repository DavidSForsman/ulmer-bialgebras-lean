module

public import Mathlib.CategoryTheory.Monad.Monadicity
public import UlmerBialgebras.Monadicity.RelAdjoint
public import UlmerBialgebras.Monadicity.InducedFreeKappa
public import UlmerBialgebras.Monadicity.SplitCreate
public import UlmerBialgebras.Monadicity.KanChainMain

/-!
# The big monadicity theorem for inserters and equifiers

Theorem 5.5 of *A Syntactic Approach to Ulmer's Bialgebras*, with the Kan extension
clause of Lemma 5.6.

Let `κ` be an infinite cardinal and let `F, G : C ⥤ D` be functors with `C` *chain
cocomplete up to `κ`*, i.e. `C` has the colimits of all well-ordered chains of cardinality
at most `κ` (`UlmerBialgebras.HasChainColimitsLE`).  Assume that `G` has an `F`-relative left
adjoint `L : C ⥤ C` (`UlmerBialgebras.RelLeftAdjoint`: a natural bijection
`(L x ⟶ y) ≃ (F x ⟶ G y)`).

* **Part (1).**  If `C` has finite coproducts and `F` preserves the colimits of `κ`-chains,
  then the forgetful functor `U : Ins(F, G) ⥤ C` is monadic
  (`UlmerBialgebras.Ins.monadicRightAdjointForget`); and if moreover `C` has pushouts, then
  `Ins(F, G)` has those left Kan extensions of `d : I ⥤ Ins(F, G)` along `k : I ⥤ K` for
  which `U d` and `U d ⋙ L` have left Kan extensions along `k`
  (`UlmerBialgebras.Ins.hasLeftKanExtension_of_rel`).
* **Part (2).**  Let `α, β : F ⟶ G`.  If `C` has coequalizers and `F` preserves the colimits
  of `κ`-chains, then the forgetful functor `U : Eq(α, β) ⥤ C` has a left adjoint
  (`UlmerBialgebras.Equif.forget_isRightAdjoint_of_rel`) and creates the coequalizers of `U`-split
  pairs (`UlmerBialgebras.Equif.createsColimitOfIsSplitPair`), so it is monadic by Beck's theorem.
   The detection of colimits (if `F` preserves joint epicness of colimiting cocones, then `U`
  creates every colimit which exists in `C`) is not formalized in this file.

The proofs go through the reduction of the relative situation to the absolute one
(`RelAdjoint.lean`): transposing the structure morphisms identifies `Ins(F, G)` with
`Ins(L, 𝟭 C)` over `C`, and `𝟭 C` is its own left adjoint, so the transfinite construction
of free objects of `FreeInsTransfinite.lean` and `FreeEquifTransfinite.lean` applies with
the chain of length `κ`.  Monadicity is then Beck's theorem: the forgetful functors create
the coequalizers of `U`-split pairs (`SplitCreate.lean`), split coequalizers being
absolute, so no hypothesis on `F` is needed for that step.

The Kan extension clause is proved in `KanChainSetup.lean`, `KanChainColim.lean`,
`KanChainAlg.lean` and `KanChainMain.lean`: extensions of `d` along `k` are the algebras of
an endofunctor `step` of the category of extensions of the underlying diagram, built from a
pushout, and `step` preserves connected colimits, so its initial algebra is obtained by the
transfinite chain of length `κ`.

## Main results

* `UlmerBialgebras.HasChainColimitsLE`: chain cocompleteness up to `κ`.
* `UlmerBialgebras.Ins.monadicRightAdjointForget`: if `κ` is infinite, `C` is chain cocomplete up
  to `κ` and has finite coproducts, `G` has an `F`-relative left adjoint `L` and `F` preserves
  colimits of `κ`-chains, the forgetful functor `Ins(F, G) ⥤ C` is monadic (Theorem 5.5 (1)).
* `UlmerBialgebras.Ins.hasLeftKanExtension_of_rel`: under the same hypotheses, with pushouts in
  place of finite coproducts, `Ins(F, G)` has the left Kan extension of `d` along `k` when `U d` and
  `U d ⋙ L` have left Kan extensions along `k` (Lemma 5.6).
* `UlmerBialgebras.Equif.forget_isRightAdjoint_of_rel`: under the same hypotheses, with coequalizers
  in place of finite coproducts, the forgetful functor `Eq(α, β) ⥤ C` has a left adjoint (towards
  Theorem 5.5 (2)).
* `UlmerBialgebras.Equif.createsColimitOfIsSplitPair`: the forgetful functor `Eq(α, β) ⥤ C` creates
  the coequalizers of `U`-split pairs.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.5 and Lemma 5.6
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
* [F. Ulmer, *Properties of dense and relative adjoint functors*][ulmerPropertiesDenseRelative1968]
-/

@[expose] public section

universe w w' v v' v₁ v₂ u u' u₁ u₂

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

section ChainCocomplete

variable (κ : Cardinal.{w}) (C : Type u) [Category.{v} C]

/-- `C` is **chain cocomplete up to `κ`**: it has the colimits of all well-ordered chains
of cardinality at most `κ`. -/
def HasChainColimitsLE : Prop :=
  ∀ (J : Type w) [LinearOrder J] [WellFoundedLT J] [Nonempty J],
    Cardinal.mk J ≤ κ → HasColimitsOfShape J C

end ChainCocomplete

namespace Kappa

variable {κ : Cardinal.{w}}

/-- The chain of length `κ` has a least element as soon as `κ` is nonzero. -/
@[instance_reducible]
noncomputable def orderBotOfPos (hκ : ℵ₀ ≤ κ) : OrderBot (shape κ) :=
  have : Nonempty (shape κ) :=
    Cardinal.nonempty_ord_toType (lt_of_lt_of_le aleph0_pos hκ).ne'
  WellFoundedLT.toOrderBot (shape κ)

/-- Chain cocompleteness up to `κ` provides the colimits needed to run a chain of
length `κ`. -/
lemma hasIterationOfShape_of_chain {C : Type u} [Category.{v} C] (hκ : ℵ₀ ≤ κ)
    (hch : HasChainColimitsLE κ C) :
    letI := orderBotOfPos hκ
    HasIterationOfShape (shape κ) C := by
  let := orderBotOfPos hκ
  have : HasColimitsOfShape (shape κ) C := hch _ mk_shape_le
  refine ⟨fun j hj => ?_, inferInstance⟩
  have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
  exact hch _ ((Cardinal.mk_subtype_le _).trans mk_shape_le)

end Kappa

open Kappa

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-! ## Part (1): the inserter -/

namespace Ins

variable {F G : C ⥤ D} {L : C ⥤ C}

/-- **Free objects for the inserter, relative case.**  If `κ` is infinite, `C` is chain
cocomplete up to `κ` and has finite coproducts, `G` has an `F`-relative left adjoint `L`
and `F` preserves the colimits of `κ`-chains, then the forgetful functor
`U : Ins(F, G) ⥤ C` has a left adjoint. -/
theorem forget_isRightAdjoint_of_rel {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ)
    (ra : RelLeftAdjoint F G L) [HasFiniteCoproducts C]
    (hch : HasChainColimitsLE κ C)
    (hF : PreservesColimitsOfShape (shape κ) F) :
    (Ins.forget F G).IsRightAdjoint := by
  let := orderBotOfPos hκ
  have := Cardinal.noMaxOrder hκ
  have := hasIterationOfShape_of_chain hκ hch
  have : IsFiltered (shape κ) := inferInstance
  have : IsConnected (shape κ) := IsFiltered.isConnected _
  have := hF
  have : PreservesColimitsOfShape (shape κ) L := ra.preservesColimitsOfShape
  refine ra.ins_forget_isRightAdjoint ?_
  exact Ins.forget_isRightAdjoint_of_shape (F := L) (G := 𝟭 C) (L := 𝟭 C) Adjunction.id
    (shape κ) (fun j => not_isMax j)

/-- The forgetful functor of an inserter creates the coequalizers of `U`-split pairs. -/
noncomputable instance createsColimitOfIsSplitPair :
    Monad.CreatesColimitOfIsSplitPair (Ins.forget F G) where
  out f g _ := Ins.createsColimitParallelPair f g

/-- **Part (1) of the theorem: `U : Ins(F, G) ⥤ C` is monadic** (Theorem 5.5 (1) of
[forsman2026syntactic]; free algebras as in [Adamek1974]). -/
@[instance_reducible]
noncomputable def monadicRightAdjointForget {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ)
    (ra : RelLeftAdjoint F G L) [HasFiniteCoproducts C]
    (hch : HasChainColimitsLE κ C)
    (hF : PreservesColimitsOfShape (shape κ) F) :
    MonadicRightAdjoint (Ins.forget F G) := by
  haveI := forget_isRightAdjoint_of_rel hκ ra hch hF
  exact Monad.monadicOfCreatesGSplitCoequalizers (Adjunction.ofIsRightAdjoint _)

/-- **The Kan extension clause of part (1).**  Assume moreover that `C` has pushouts.  Then
`Ins(F, G)` has those left Kan extensions of `d : I ⥤ Ins(F, G)` along `k : I ⥤ K` for which
the underlying diagram `U d` and its composite `U d ⋙ L` have left Kan extensions along
`k` (cf. Lemma 5.6 of [forsman2026syntactic]). -/
theorem hasLeftKanExtension_of_rel {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ)
    (ra : RelLeftAdjoint F G L) (hch : HasChainColimitsLE κ C) [HasPushouts C]
    (hF : PreservesColimitsOfShape (shape κ) F)
    {I : Type u₁} [Category.{v₁} I] {K : Type u₂} [Category.{v₂} K]
    (d : I ⥤ Ins F G) (k : I ⥤ K)
    [k.HasLeftKanExtension (d ⋙ Ins.forget F G)]
    [k.HasLeftKanExtension ((d ⋙ Ins.forget F G) ⋙ L)] :
    k.HasLeftKanExtension d := by
  let := orderBotOfPos hκ
  have := Cardinal.noMaxOrder hκ
  have := hasIterationOfShape_of_chain hκ hch
  have : HasColimitsOfShape (shape κ) C := hch _ mk_shape_le
  have : IsConnected (shape κ) := IsFiltered.isConnected _
  have := hF
  have : PreservesColimitsOfShape (shape κ) L := ra.preservesColimitsOfShape
  exact KanChain.hasLeftKanExtension_ins k ra d (J := shape κ) (fun j => not_isMax j)

end Ins

/-! ## Part (2): the equifier -/

/-- Transport of the existence of a left adjoint for the inclusion of a full subcategory
along an equality of object properties. -/
lemma ObjectProperty.isRightAdjoint_ι_of_eq {P Q : ObjectProperty C} (h : P = Q)
    (hQ : Q.ι.IsRightAdjoint) : P.ι.IsRightAdjoint := by
  subst h; exact hQ

namespace Equif

variable {F G : C ⥤ D} {L : C ⥤ C} {α β : F ⟶ G}

/-- **Free objects for the equifier, relative case.**  If `κ` is infinite, `C` is chain
cocomplete up to `κ` and has coequalizers, `G` has an `F`-relative left adjoint `L` and `F`
preserves the colimits of `κ`-chains, then the forgetful functor `U : Eq(α, β) ⥤ C` has a
left adjoint. -/
theorem forget_isRightAdjoint_of_rel {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ)
    (ra : RelLeftAdjoint F G L) (α β : F ⟶ G) [HasCoequalizers C]
    (hch : HasChainColimitsLE κ C)
    (hF : PreservesColimitsOfShape (shape κ) F) :
    (Equif.forget α β).IsRightAdjoint := by
  let := orderBotOfPos hκ
  have := Cardinal.noMaxOrder hκ
  have := hasIterationOfShape_of_chain hκ hch
  have := hF
  have : PreservesColimitsOfShape (shape κ) L := ra.preservesColimitsOfShape
  refine ObjectProperty.isRightAdjoint_ι_of_eq (ra.equifProp_eq α β) ?_
  exact Equif.forget_isRightAdjoint_of_shape (F := L) (G := 𝟭 C) (L := 𝟭 C) Adjunction.id
    (ra.transposeNat α) (ra.transposeNat β) (shape κ)

/-- The forgetful functor of an equifier creates the coequalizer of every parallel pair
which is split downstairs. -/
@[instance_reducible]
noncomputable def createsColimitParallelPair {x y : Equif α β} (f g : x ⟶ y)
    [HasSplitCoequalizer ((Equif.forget α β).map f) ((Equif.forget α β).map g)] :
    CreatesColimit (parallelPair f g) (Equif.forget α β) := by
  haveI : PreservesColimit (parallelPair f g ⋙ Equif.forget α β) F := by
    have := preservesColimit_parallelPair_of_hasSplitCoequalizer
      ((Equif.forget α β).map f) ((Equif.forget α β).map g) F
    exact preservesColimit_of_iso_diagram F (parallelPairComp f g (Equif.forget α β)).symm
  haveI : HasColimit (parallelPair f g ⋙ Equif.forget α β) := by
    rw [hasColimit_iff_of_iso (parallelPairComp f g (Equif.forget α β))]
    exact inferInstanceAs
      (HasColimit (parallelPair ((Equif.forget α β).map f) ((Equif.forget α β).map g)))
  exact Equif.createsColimit (parallelPair f g)

/-- The forgetful functor of an equifier creates the coequalizers of `U`-split pairs. -/
noncomputable instance createsColimitOfIsSplitPair :
    Monad.CreatesColimitOfIsSplitPair (Equif.forget α β) where
  out f g _ := Equif.createsColimitParallelPair f g

/-! ### Detection of colimits -/

end Equif

end UlmerBialgebras
