module

public import UlmerBialgebras.Kan.LimKan
public import UlmerBialgebras.Kan.CosiftedPi

/-!
# The dual of Corollary 4.17

Let `(Σ, σ)` be a signature pair with a `σ`-theory `T`, let `M` be a categorical `Σ`-model
and let `I` be a **cosifted** category.  If `M(B)` preserves `I`-limits componentwise for
each functor symbol `B` of `Σ`, then the forgetful functor `U : M^T → M₀` strictly creates
all `I`-indexed limits.

This combines the dual of the `n`-ary Lemma 4.16 (`CosiftedPi.lean`), the dictionary between
limits and right Kan extensions along `I ⟶ 1` (`LimKan.lean`) and the dual of
Corollary 4.12 (`KanModel.lean`). The n-ary input is derived from the sifted theorem in
opposite categories; only the model-level creation argument remains here.

## Main results

* `UlmerBialgebras.preservesLimitsOfShape_fn`: for a cosifted `I`, if `M(B)` preserves `I`-limits
  componentwise then it preserves `I`-limits.
* `UlmerBialgebras.thy_strictlyCreates_limits`: for a cosifted `I`, if every `M(B)` preserves
  `I`-limits componentwise, then `U : M^T → M₀` strictly creates right Kan extensions along
  `I ⟶ 1`, i.e. `I`-limits (dual form of Corollary 4.17).

As in the colimit case, the shape is an arbitrary small category `(I : Type w) [Category.{w} I]`,
with `w` independent of the universe `u` of the model.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 4.17 (dual form)
* [J. Adámek, J. Rosický, E. M. Vitale,
  *What are sifted colimits?*][AdamekRosickyVitale2010SiftedColimits]
-/

@[expose] public section

universe v u w w' u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Sg : TwoSig.{u₁, u₂, u₃}}

section Components

variable (M : Model Sg Cat.{v, u})

/-- The interpretation of a functor symbol `B` **preserves `I`-limits componentwise**, for a
small category `I`: for every choice of values of all but one of its arguments, the resulting
functor of one variable preserves `I`-limits. -/
def PreservesLimitsComponentwise (I : Type w') [Category.{w} I] (B : Sg.Fun) : Prop :=
  ∀ (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
    Nonempty (PreservesLimitsOfShape I
      (updateFunctor x i ⋙
        (M.fn B).toFunctor))

/-- The dual of **Lemma 4.16** applied to the interpretation of a functor symbol:
componentwise preservation of cosifted limits implies preservation. -/
theorem preservesLimitsOfShape_fn (I : Type w') [Category.{w} I] [IsCosifted I] (B : Sg.Fun)
    (h : PreservesLimitsComponentwise M I B) :
    PreservesLimitsOfShape I
      (M.fn B).toFunctor :=
  preservesLimitsOfShape_pi_of_componentwise _ (fun i x => (h i x).some)

end Components

variable (M : Model Sg Cat.{v, u}) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
  [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]

/-- **The dual of Corollary 4.17**: if the interpretation of every functor symbol preserves
`I`-limits componentwise, for a cosifted category `I`, then the forgetful functor
`U : M^T → M₀` strictly creates all `I`-indexed limits — that is, all right Kan extensions
along `I ⟶ 1`. -/
theorem thy_strictlyCreates_limits (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (I : Cat.{v, u}) [IsCosifted (I : Type u)]
    (hB : ∀ B : Sg.Fun, PreservesLimitsComponentwise M I B)
    (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesRightKan (toOne I) d (M.thyForget sg T) := by
  refine M.thy_strictlyCreates_rightKan_of_fn sg T (toOne I) (fun B dd => ?_) d
  have := preservesLimitsOfShape_fn M I B (hB B)
  exact preservesRightKan_of_preservesLimitsOfShape (M.fn B) dd

end UlmerBialgebras
