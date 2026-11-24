module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Hopf.Commutative.TensorLine
public import Hopf.Basic.HopfQuotient

/-!
# The group-like character of a line which is a subcomodule modulo a Hopf ideal

Let `H` be a commutative Hopf algebra over a field `k` and let `I` be a Hopf ideal of `H`. If a line
`k v` of a right `H`-comodule `V` is a subcomodule modulo `I`, then the coaction of `v` becomes
`v ⊗ ḡ` in `V ⊗ H/I`, and Takeuchi's Lemma 4.13
(`HopfAlgebra.Commutative.exists_groupLikeMod_of_isRelInvMod`) shows that `g` may be taken to be a
matrix coefficient of `v`, group-like modulo `I`.

This file records the resulting statement in the form required by
`Hopf/Commutative/AugSpanOfLineFunctional.lean`: the character is an honest group-like element of
the quotient Hopf algebra `H/I`.

## Main results

* `HopfAlgebra.Commutative.exists_isRelInvMod_of_isSubcomoduleMod`: a line which is a subcomodule
  modulo `I` has a character;
* `HopfAlgebra.Commutative.isGroupLikeElem_mk_of_lTensorQuot`: an element with counit `1` whose
  comultiplication is `c ⊗ c` modulo `H ⊗ I` is group-like in `H/I`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.13
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V]

/-- A line which is a subcomodule modulo `J` has a character: the coaction of the spanning vector
becomes `v ⊗ ḡ` in `V ⊗ H/J`. -/
theorem exists_isRelInvMod_of_isSubcomoduleMod {J : Ideal H} {v : V}
    (h : IsSubcomoduleMod J (k ∙ v : Submodule k V)) : ∃ g : H, IsRelInvMod k J v g := by
  obtain ⟨ρ, hρ⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) v
    ((isSubcomoduleMod_span_singleton_iff J v).1 h)
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective ρ
  exact ⟨g, hρ⟩

variable (I : Ideal H) [Fact (IsHopfIdeal k I)]

omit [Fact (IsHopfIdeal k I)] in
/-- Reducing the second factor and then both factors is reducing both factors. -/
lemma rTensor_mk_lTensorQuot (t : H ⊗[k] H) :
    LinearMap.rTensor (H ⧸ I) (Ideal.Quotient.mkₐ k I).toLinearMap (lTensorQuot I t)
      = quotMap2 k I t := by
  induction t with
  | tmul x y => rw [lTensorQuot_tmul, LinearMap.rTensor_tmul]; rfl
  | add p q hp hq => simp only [map_add, hp, hq]

/-- **An element which is group-like modulo `I` is group-like in the quotient Hopf algebra.** -/
theorem isGroupLikeElem_mk_of_lTensorQuot {c : H}
    (hcounit : Coalgebra.counit (R := k) (A := H) c = 1)
    (hcomul : lTensorQuot I (comul (R := k) (A := H) c)
      = c ⊗ₜ[k] Ideal.Quotient.mk I c) :
    IsGroupLikeElem k (Ideal.Quotient.mk I c) where
  counit_eq_one := by rw [quotCounit_mk, hcounit]
  comul_eq_tmul_self := by
    rw [quotComul_mk, ← rTensor_mk_lTensorQuot I (comul (R := k) (A := H) c), hcomul,
      LinearMap.rTensor_tmul]
    rfl

end HopfAlgebra.Commutative
end
