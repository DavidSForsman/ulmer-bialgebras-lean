module

public import UlmerBialgebras.Paper.AppendixDefsThree
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# Translating the appendix's tensor order

A category enriched over `Vᴹᵒᵖ` in the library's convention has
composition `C(b,c) ⊗ C(a,b) → C(a,c)` after taking `unmop`.
This realizes the paper's convention for an arbitrary monoidal base,
without requiring a braiding.

## Main results

* `UlmerBialgebras.Paper.Appendix.PaperVCat`: enriched categories in the paper's composition
  convention.
* `UlmerBialgebras.Paper.Appendix.paperThreeVCat`: the three-object linear probe with composite hom
  `y ⊗ x`.
* `UlmerBialgebras.Paper.Appendix.IsPaperLinearProbe`: the class `A` of point, arrow and
  three-object linear probes (Theorem A.5).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Appendix A (Definition A.4, Theorem A.5)
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- Initiality is unchanged by the monoidal-opposite wrapper. -/
def mopIsInitial {z : V} (hz : Limits.IsInitial z) : Limits.IsInitial (mop z) :=
  Limits.IsInitial.ofUniqueHom (fun y => (hz.to y.unmop).mop)
    (fun _ _ => MonoidalOpposite.hom_ext (hz.hom_ext _ _))

/-- An absorbing initial object remains absorbing when tensor order is reversed. -/
def reverseInitial (Z : MonoidalInitial V) : MonoidalInitial Vᴹᵒᵖ where
  zero := mop Z.zero
  isInitial := mopIsInitial Z.isInitial
  zeroTensor y := mopIsInitial (Z.tensorZero y.unmop)
  tensorZero y := mopIsInitial (Z.zeroTensor y.unmop)

/-- Enriched categories in the composition convention used by the paper. -/
abbrev PaperVCat (V : Type v) [Category.{w} V] [MonoidalCategory V] :=
  VCat.{w, v, u} Vᴹᵒᵖ

/-- The three-object linear probe with the paper's `y ⊗ x` composite hom. -/
abbrev paperThreeVCat (Z : MonoidalInitial V) (x y : V) : PaperVCat.{w, v, u} V :=
  threeVCat.{w, v, u} (reverseInitial Z) (mop x) (mop y)

/-- The appendix's class `A` (Theorem A.5 of [forsman2026syntactic]) of point, arrow and
three-object linear probes. -/
abbrev IsPaperLinearProbe (Z : MonoidalInitial V) (A : PaperVCat.{w, v, u} V) : Prop :=
  IsLinearProbe.{w, v, u} (reverseInitial Z) A

end UlmerBialgebras.Paper.Appendix
