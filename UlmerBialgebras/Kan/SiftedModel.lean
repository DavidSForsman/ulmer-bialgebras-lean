module

public import UlmerBialgebras.Kan.ColimKan
public import UlmerBialgebras.Kan.SiftedPi

/-!
# Corollary 4.17

Let `(Σ, σ)` be a signature pair with a `σ`-theory `T`, let `M` be a categorical `Σ`-model
and let `I` be a sifted category.  If `M(B)` preserves `I`-colimits componentwise for each
functor symbol `B` of `Σ`, then the forgetful functor `U : M^T → M₀` strictly creates all
`I`-indexed colimits.

This combines the `n`-ary form of Lemma 4.16 (`SiftedPi.lean`), the dictionary between
colimits and left Kan extensions along `I ⟶ 1` (`ColimKan.lean`) and Corollary 4.12
(`KanModel.lean`).

## Main results

* `UlmerBialgebras.PreservesColimitsComponentwise`: the hypothesis that `M(B)` preserves
  `I`-colimits in each variable.
* `UlmerBialgebras.preservesColimitsOfShape_fn`: for sifted `I`, componentwise preservation implies
  that `M(B)` preserves `I`-colimits (Lemma 4.16).
* `UlmerBialgebras.thy_strictlyCreates_colimits`: for sifted `I`, if every `M(B)` preserves
  `I`-colimits componentwise, then `u : M^T → M₀` strictly creates left Kan extensions along
  `I ⟶ 1` (Corollary 4.17).

The shape is an arbitrary category `(I : Type w') [Category.{w} I]`, with `w, w'` independent of
the universes of the model, which lives in `Cat.{v, u}`. Corollary 4.17 itself is about `M^T`, so
there the shape is any `I : Cat.{v, u}`, and the inserters and equifiers of `Cat.{v, u}` are
hypotheses.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 4.16,
  Corollary 4.12, Corollary 4.17
-/

@[expose] public section

universe v u w w' u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Sg : TwoSig.{u₁, u₂, u₃}}

section Components

variable (M : Model Sg Cat.{v, u})

/-- The interpretation of a functor symbol `B` **preserves `I`-colimits componentwise**, for a
category `I`: for every choice of values of all but one of its arguments, the resulting
functor of one variable preserves `I`-colimits. -/
def PreservesColimitsComponentwise (I : Type w') [Category.{w} I] (B : Sg.Fun) : Prop :=
  ∀ (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
    Nonempty (PreservesColimitsOfShape I
      (updateFunctor x i ⋙
        (M.fn B).toFunctor))

/-- **Lemma 4.16** applied to the interpretation of a functor symbol: componentwise
preservation of sifted colimits implies preservation. -/
theorem preservesColimitsOfShape_fn (I : Type w') [Category.{w} I] [IsSifted I] (B : Sg.Fun)
    (h : PreservesColimitsComponentwise M I B) :
    PreservesColimitsOfShape I
      (M.fn B).toFunctor :=
  preservesColimitsOfShape_pi_of_componentwise _ (fun i x => (h i x).some)

end Components

variable (M : Model Sg Cat.{v, u}) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
  [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]

/-- **Corollary 4.17** ([forsman2026syntactic]): if the interpretation of every functor symbol
preserves `I`-colimits componentwise, for a sifted category `I`, then the forgetful functor
`U : M^T → M₀` strictly creates all `I`-indexed colimits — that is, all left Kan extensions
along `I ⟶ 1`. -/
theorem thy_strictlyCreates_colimits (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (I : Cat.{v, u})
    [IsSifted (I : Type u)]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M I B)
    (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan (toOne I) d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_leftKan_of_fn sg T (toOne I) (fun B dd => ?_) d
  have := preservesColimitsOfShape_fn M I B (hB B)
  exact preservesLeftKan_of_preservesColimitsOfShape (M.fn B) dd

end UlmerBialgebras
