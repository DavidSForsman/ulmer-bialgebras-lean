module

public import UlmerBialgebras.Paper.AppendixDefsReverse
public import UlmerBialgebras.Proofs.Appendix.AppendixThree

/-!
# Functors out of the three-object probe in the paper's convention

Over `Vᴹᵒᵖ`, a `V`-functor `3_{x,y} ⟶ C` amounts to three objects `c₀, c₁, c₂` of `C` and
morphisms `x ⟶ C(c₀, c₁)` and `y ⟶ C(c₁, c₂)` of `V` (`paperThreeFunctorDataEquiv`), as in the
description of such functors that follows Definition A.4.

## Main results

* `UlmerBialgebras.Paper.Appendix.paperThreeFunctorDataEquiv`: over `Vᴹᵒᵖ`, `V`-functors
  `3_{x,y} ⟶ C` are in bijection with triples `c₀, c₁, c₂` of objects together with morphisms
  `x ⟶ C(c₀, c₁)` and `y ⟶ C(c₁, c₂)` of `V`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition A.4 and Theorem A.5
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The free composable-pair universal property in the paper's convention.
The evaluation map takes its edge maps as morphisms of the original base `V`. -/
def paperThreeFunctorDataEquiv (Z : MonoidalInitial V) (x y : V)
    (C : PaperVCat.{w, v, u} V) :
    (paperThreeVCat.{w, v, u} Z x y ⟶ C) ≃
      (Σ c₀ : C.carrier, Σ c₁ : C.carrier, Σ c₂ : C.carrier,
        (x ⟶ unmop (c₀ ⟶[Vᴹᵒᵖ] c₁)) × (y ⟶ unmop (c₁ ⟶[Vᴹᵒᵖ] c₂))) where
  toFun F := ⟨F.obj .zero, F.obj .one, F.obj .two,
    (F.emap .zero .one).unmop, (F.emap .one .two).unmop⟩
  invFun d := threeVFunctor (reverseInitial Z) (mop x) (mop y)
    d.1 d.2.1 d.2.2.1 d.2.2.2.1.mop d.2.2.2.2.mop
  left_inv F := (threeVFunctor_reconstruct (reverseInitial Z) (mop x) (mop y) C F).symm
  right_inv d := by rcases d with ⟨c₀, c₁, c₂, f, g⟩; rfl

end UlmerBialgebras.Paper.Appendix
