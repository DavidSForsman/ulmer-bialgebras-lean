module

public import UlmerBialgebras.Monadicity.KanChainAlg
public import UlmerBialgebras.Monadicity.KanChainColim
public import UlmerBialgebras.Monadicity.CoalgChainIteration

/-!
# Left Kan extensions into an inserter, via the transfinite chain

Assembling `KanChainSetup.lean`, `KanChainColim.lean` and `KanChainAlg.lean`: the initial
`step`-algebra is produced by the transfinite chain of `InitialAlgebraChain.lean` (the base
stage is the initial extension `e`, so the base condition is automatic), and it is a left
Kan extension of `d : I ⥤ Ins F G` along `k`.

The main result of this file is `UlmerBialgebras.KanChain.hasLeftKanExtension_ins`: if `L` is an
`F`-relative left adjoint of `G`, `C` has pushouts and the colimits of a well-ordered chain
`J` without maximal element which `L` preserves, and if the underlying diagram `U d` and
`U d ⋙ L` have left Kan extensions along `k`, then so has `d`.  This is the last part of
Lemma 5.6, in the form used for the last part of Theorem 5.7.

## Main results

* `UlmerBialgebras.KanChain.initAlgebra`, `UlmerBialgebras.KanChain.isInitialInitAlgebra`: the
  initial `step`-algebra, obtained from the transfinite chain.
* `UlmerBialgebras.KanChain.hasLeftKanExtension_ins`: if `L` is an `F`-relative left adjoint of `G`,
  `C` has pushouts and the colimits of a connected well-ordered chain `J` without maximal element,
  `L` preserves the latter, and `U d` and `U d ⋙ L` have left Kan extensions along `k`, then
  `d` has a left Kan extension along `k` (Lemma 5.6).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma 5.6 and Theorem 5.7
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe w v v₁ v₂ v₃ u u₁ u₂ u₃

namespace UlmerBialgebras

open CategoryTheory Limits Functor Endofunctor

variable {C : Type u} [Category.{v} C] {I : Type u₁} [Category.{v₁} I]
  {K : Type u₂} [Category.{v₂} K]

namespace KanChain

variable (Λ : C ⥤ C) (k : I ⥤ K) (A : I ⥤ C)
variable [HasLeftKanExtension k A] [HasLeftKanExtension k (A ⋙ Λ)]
variable (ψ : A ⋙ Λ ⟶ A) [HasPushouts C]

/-- The base of the chain: the initial extension, with its unique coalgebra structure. -/
noncomputable def baseCoalg : Endofunctor.Coalgebra (step Λ k A ψ) where
  V := ee k A
  str := initial.to _

/-- The base condition: every morphism out of the initial object is the unique one. -/
lemma existsUnique_base (Z : Endofunctor.Algebra (step Λ k A ψ)) :
    ∃! g : (baseCoalg Λ k A ψ).V ⟶ Z.a,
      g = (baseCoalg Λ k A ψ).str ≫ (step Λ k A ψ).map g ≫ Z.str :=
  ⟨initial.to Z.a, initial.hom_ext _ _, fun _ _ => initial.hom_ext _ _⟩

section Chain

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  [IsConnected J] [HasIterationOfShape J C] [PreservesColimitsOfShape J Λ]

/-- The colimits needed to run the chain exist in the category of extensions. -/
instance hasIterationOfShape_ext : HasIterationOfShape J (Ext k A) := by
  constructor
  · intro j hj
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    have : HasColimitsOfShape (Set.Iio j) C :=
      Limits.hasColimitsOfShape_of_isSuccLimit C j hj
    infer_instance
  · infer_instance

/-- The transfinite chain computing the initial algebra. -/
noncomputable def chain (hmax : ∀ j : J, ¬ IsMax j) : CoalgChain (step Λ k A ψ) J :=
  coalgChain (step Λ k A ψ) hmax (baseCoalg Λ k A ψ)

omit [PreservesColimitsOfShape J Λ] in
/-- At the bottom stage of `chain`, there is a unique `g` to an algebra `Z` satisfying
`Cond Z ⊥ g`. -/
lemma chain_base (hmax : ∀ j : J, ¬ IsMax j) (Z : Endofunctor.Algebra (step Λ k A ψ)) :
    ∃! g : (chain Λ k A ψ hmax).W.obj (⊥ : J) ⟶ Z.a, (chain Λ k A ψ hmax).Cond Z ⊥ g :=
  CoalgChain.existsUnique_cond_bot_of_iso
    (coalgChainBotIso (step Λ k A ψ) hmax (baseCoalg Λ k A ψ))
    (coalgChainBotIso_str (step Λ k A ψ) hmax (baseCoalg Λ k A ψ))
    (existsUnique_base Λ k A ψ Z)

variable [HasColimitsOfShape J C]

/-- The initial `step`-algebra. -/
noncomputable def initAlgebra (hmax : ∀ j : J, ¬ IsMax j) :
    Endofunctor.Algebra (step Λ k A ψ) :=
  letI := preservesColimitsOfShape_step Λ k A ψ (J := J)
  (chain Λ k A ψ hmax).algebra

/-- `initAlgebra`, the colimit of the chain, is an initial `step`-algebra. -/
noncomputable def isInitialInitAlgebra (hmax : ∀ j : J, ¬ IsMax j) :
    IsInitial (initAlgebra Λ k A ψ hmax) :=
  letI := preservesColimitsOfShape_step Λ k A ψ (J := J)
  (chain Λ k A ψ hmax).isInitialAlgebra (chain_base Λ k A ψ hmax)

end Chain

/-! ## The left Kan extension -/

variable {D : Type u₃} [Category.{v₃} D] {F G : C ⥤ D} {L : C ⥤ C}

/-- **Left Kan extensions into an inserter** (Lemma 5.6 of [forsman2026syntactic]).  Let `L`
be an `F`-relative left adjoint of `G`.  If the underlying diagram of `d : I ⥤ Ins F G` and
its composite with `L` have left Kan extensions along `k`, if `C` has pushouts and the
colimits of a well-ordered chain `J` without maximal element, and if `L` preserves those
colimits, then `d` has a left Kan extension along `k`. -/
theorem hasLeftKanExtension_ins (ra : RelLeftAdjoint F G L) (d : I ⥤ Ins F G)
    {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
    [WellFoundedLT J] [IsConnected J] [HasIterationOfShape J C] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J L] (hmax : ∀ j : J, ¬ IsMax j)
    [HasLeftKanExtension k (dgm d)] [HasLeftKanExtension k (dgm d ⋙ L)] :
    HasLeftKanExtension k d :=
  hasLeftKanExtension_of_isInitial ra d k
    (initAlgebra L k (dgm d) (ra.insStrT d) (J := J) hmax)
    (isInitialInitAlgebra L k (dgm d) (ra.insStrT d) hmax)

end KanChain

end UlmerBialgebras
