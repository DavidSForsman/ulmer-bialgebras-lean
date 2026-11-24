module

public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Kan.CosiftedModel
public import Foundations.CategoryTheory.Limits.SiftedShapes

/-!
# Applications of Corollary 4.17 and of its dual

Corollary 4.17 (`UlmerBialgebras.thy_strictlyCreates_colimits`) and its dual
(`UlmerBialgebras.thy_strictlyCreates_limits`) apply to any sifted, resp. cosifted, shape.  Here we
record the two standard families of such shapes, established in `SiftedShapes.lean`:

* reflexive pairs — the shape `UlmerBialgebras.walkingReflexivePairCat`, whose colimits are the
  reflexive coequalizers;
* filtered categories, and in particular nonempty directed preorders, whose colimits are
  the directed (e.g. `λ`-directed) colimits;

together with their duals: coreflexive pairs and cofiltered categories (in particular
codirected preorders).

Thus, for a categorical `Σ`-model `M` and a `σ`-theory `T`, the forgetful 1-cell
`u : M^T → M₀` strictly creates reflexive coequalizers and directed colimits as soon as the
interpretation `M(B)` of each functor symbol preserves them componentwise, and dually for
coreflexive equalizers and codirected limits.

## Main results

* `UlmerBialgebras.thy_strictlyCreates_reflexiveCoequalizers`: if each `M(B)` preserves colimits of
  shape `UlmerBialgebras.walkingReflexivePairCat` componentwise, then `u : M^T → M₀` strictly
  creates left Kan extensions along `walkingReflexivePairCat ⟶ 1` (Corollary 4.17, Example 4.20).
* `UlmerBialgebras.thy_strictlyCreates_filteredColimits`: the same for a filtered category `I`.
* `UlmerBialgebras.thy_strictlyCreates_coreflexiveEqualizers`: dually, `u` strictly creates right
  Kan extensions along `walkingCoreflexivePairCat ⟶ 1` when each `M(B)` preserves these limits
  componentwise.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 4.3,
  Corollary 4.17, Example 4.20
* [J. Adámek, J. Rosický, E. M. Vitale, *What Are Sifted
  Colimits?*][AdamekRosickyVitale2010SiftedColimits]
-/

@[expose] public section

universe u

namespace UlmerBialgebras

open CategoryTheory Limits

/-! ## The shapes -/

/-- The walking reflexive pair, as an object of `Cat.{u, u}`. -/
def walkingReflexivePairCat : Cat.{u, u} := Cat.of (AsSmall.{u} WalkingReflexivePair)

/-- The walking reflexive pair is sifted. -/
instance walkingReflexivePairCat_isSifted :
    IsSifted (walkingReflexivePairCat.{u} : Type u) :=
  (IsSifted.isSifted_iff_asSmallIsSifted (C := WalkingReflexivePair)).1 inferInstance

/-- The walking coreflexive pair, as an object of `Cat.{u, u}`. -/
def walkingCoreflexivePairCat : Cat.{u, u} := Cat.of (AsSmall.{u} WalkingCoreflexivePair)

/-- The walking coreflexive pair is cosifted. -/
instance walkingCoreflexivePairCat_isCosifted :
    IsCosifted (walkingCoreflexivePairCat.{u} : Type u) :=
  IsSifted.isSifted_of_equiv (C := WalkingCoreflexivePairᵒᵖ)
    (AsSmall.equiv (C := WalkingCoreflexivePair)).op.symm

variable {Sg : TwoSig} (M : Model Sg Cat.{u, u}) (sg : OneSig Sg)

/-! ## Reflexive coequalizers and directed colimits -/

/-- If the interpretation of every functor symbol preserves reflexive coequalizers
componentwise, then the forgetful 1-cell `u : M^T → M₀` strictly creates them. -/
theorem thy_strictlyCreates_reflexiveCoequalizers (T : Theory sg)
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M walkingReflexivePairCat.{u} B)
    (d : walkingReflexivePairCat.{u} ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan (toOne walkingReflexivePairCat.{u}) d (M.thyForget sg T) :=
  thy_strictlyCreates_colimits M sg T _ hB d

/-- If the interpretation of every functor symbol preserves `I`-colimits componentwise, for a
*filtered* category `I`, then the forgetful 1-cell `u : M^T → M₀` strictly creates them. -/
theorem thy_strictlyCreates_filteredColimits (T : Theory sg) (I : Cat.{u, u})
    [IsFiltered (I : Type u)]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M I B)
    (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan (toOne I) d (M.thyForget sg T) := by
  have : IsSifted (I : Type u) := IsFiltered.isSifted
  exact thy_strictlyCreates_colimits M sg T I hB d

/-! ## Coreflexive equalizers and codirected limits -/

/-- If the interpretation of every functor symbol preserves coreflexive equalizers
componentwise, then the forgetful 1-cell `u : M^T → M₀` strictly creates them. -/
theorem thy_strictlyCreates_coreflexiveEqualizers (T : Theory sg)
    (hB : ∀ B : Sg.Fun, PreservesLimitsComponentwise M walkingCoreflexivePairCat.{u} B)
    (d : walkingCoreflexivePairCat.{u} ⟶ M.thyObj sg T) :
    StrictlyCreatesRightKan (toOne walkingCoreflexivePairCat.{u}) d (M.thyForget sg T) :=
  thy_strictlyCreates_limits M sg T _ hB d

end UlmerBialgebras
