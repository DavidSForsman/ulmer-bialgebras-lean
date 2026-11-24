module

public import UlmerBialgebras.Paper.AppendixDefs
public import UlmerBialgebras.Appendix.ThreeObj

/-!
# The linear three-object enriched category

Composition follows the existing library convention:
`Hom(0,1) ⊗ Hom(1,2) → Hom(0,2)`.
The paper uses the reverse tensor convention; this file does not assume
a braiding to exchange the two factors.

## Main results

* `UlmerBialgebras.Paper.Appendix.threeVCat`: the linear `V`-category `𝟑_{x,y}` (Definition A.4),
  the free enriched category on a composable pair of labelled edges.
* `UlmerBialgebras.Paper.Appendix.threeVFunctor`: the `V`-functor `𝟑_{x,y} → C` determined by
  `f : x → C(c₀,c₁)` and `g : y → C(c₁,c₂)` (Lemma A.3).
* `UlmerBialgebras.Paper.Appendix.IsLinearProbe`: the class of the first three linear probes, in the
  library's tensor-order convention (Definition A.4).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma A.3, Definition A.4 (the linear `V`-category `𝟑_{x,y}`)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]


/-- The free enriched category on a composable pair of labelled edges (the linear `V`-category
`𝟑_{x,y}` of Definition A.4 of [forsman2026syntactic], via Lemma A.3), in the library's tensor
order `x ⊗ y` (cf. `paperThreeVCat` in `UlmerBialgebras/Paper/AppendixDefsReverse.lean` for the
paper's
`y ⊗ x`). -/
def threeVCat (Z : MonoidalInitial V) (x y : V) : VCat.{w, v, u} V :=
  VCat.of (ForgetEnrichment V (ThreeObj.{w, v, u} Z x y))

section Functor

variable (Z : MonoidalInitial V) (x y : V)
    {C : Type u} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The `V`-functor `𝟑_{x,y} → C` sending the generating edges to `f : x → C(c₀,c₁)` and
`g : y → C(c₁,c₂)` (the freeness of `𝟑_{x,y}` from Lemma A.3 of [forsman2026syntactic]). -/
def threeVFunctor (c₀ c₁ c₂ : C)
    (f : x ⟶ (c₀ ⟶[V] c₁)) (g : y ⟶ (c₁ ⟶[V] c₂)) :
    VFunctor V (ForgetEnrichment V (ThreeObj.{w, v, u} Z x y)) C :=
  VFunctor.ofEnriched (threeObjMap Z x y c₀ c₁ c₂) (threeEmap Z x y c₀ c₁ c₂ f g)
    (threeEmap_id Z x y c₀ c₁ c₂ f g) (threeEmap_comp Z x y c₀ c₁ c₂ f g)

end Functor


/-- The exact class of the first three linear probes (Definition A.4 of [forsman2026syntactic]; the
class `A` of Theorem A.5),
expressed in the existing library's tensor-order convention. -/
def IsLinearProbe (Z : MonoidalInitial V) (A : VCat.{w, v, u} V) : Prop :=
  A = unitVCat.{w, v, u} V ∨
    (∃ x : V, A = arrowVCat.{w, v, u} Z x) ∨
    ∃ x y : V, A = threeVCat.{w, v, u} Z x y

end UlmerBialgebras.Paper.Appendix
