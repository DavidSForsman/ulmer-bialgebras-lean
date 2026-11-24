module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Hopf.Basic.ComoduleDual
public import Hopf.Commutative.RelInvTwist
public import Hopf.Basic.HopfQuotient

/-!
# The inverse character on the dual comodule, and coinvariant twists

Let `H` be a commutative Hopf algebra over a field `k` and let `I` be a Hopf ideal of `H`, so
that `H̄ = H/I` is a Hopf algebra.  Let `M` be a finite-dimensional right `H`-comodule and let
`χ : M → k` be a functional which is *colinear modulo `I` with character `g`*, i.e. all its
matrix coefficients satisfy `∑ ⟨χ, m₍₀₎⟩ m₍₁₎ ≡ ⟨χ, m⟩ g mod I`.  In the dual comodule `M*` of
`Hopf/Basic/ComoduleDual.lean`, the vector `χ` is then relatively invariant modulo `I`
with the *inverse* character `S g` (Takeuchi's Lemma 4.15).

Combined with the twisting step of `Hopf/Commutative/RelInvTwist.lean`, this turns a vector
`v` which is relatively invariant with character `g` into the **coinvariant** vector `v ⊗ χ` of
`V ⊗ M*`, which is the input required by
`HopfAlgebra.Commutative.eq_augIdeal_coinv_of_coeff_span` in
`Hopf/Commutative/ComoduleCoeff.lean`.

## Main results

* `HopfAlgebra.Commutative.dualCoactHom_eq_antipode_comoduleCoeff`: the coaction of the dual
  comodule is the antipode of the matrix coefficient map;
* `HopfAlgebra.Commutative.isRelInvMod_dual`: a functional colinear modulo `I` with character `g` is
  relatively invariant modulo `I` with character `S g`;
* `HopfAlgebra.Commutative.mk_mul_antipode_eq_one`: a group-like element modulo `I` satisfies
  `g S g ≡ 1 mod I`;
* `HopfAlgebra.Commutative.isCoinvMod_tmul_dual`: the resulting coinvariant vector `v ⊗ χ`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V M : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V]
  [AddCommGroup M] [Module k M] [RightComodule k H M]

/-- The map `m ↦ ∑ ⟨χ, m₍₀₎⟩ S (m₍₁₎)` defining the coaction of the dual comodule is the antipode
of the matrix coefficient map `m ↦ ∑ ⟨χ, m₍₀₎⟩ m₍₁₎`. -/
lemma dualCoactHom_eq_antipode_comoduleCoeff (χ : Module.Dual k M) (m : M) :
    dualCoactHom (C := H) χ m = antipode k (comoduleCoeff χ m) := by
  classical
  set r := Repr.arbitrary k H m with hr
  rw [dualCoactHom_apply_repr χ r, comoduleCoeff, contractFst, ← r.eq]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

section Quotient

variable (I : Ideal H) [Fact (IsHopfIdeal k I)]

/-- A group-like element modulo `I` is invertible modulo `I`, with inverse its antipode. -/
lemma mk_mul_antipode_eq_one {g : H}
    (hg : IsGroupLikeElem k (Ideal.Quotient.mk I g)) :
    Ideal.Quotient.mk I (g * antipode k g) = 1 := by
  rw [map_mul, ← HopfAlgebra.quotAntipode_mk]
  exact hg.mul_antipode_cancel

variable [FiniteDimensional k M]

/-- The dual comodule structure on the dual of a finite-dimensional comodule. -/
noncomputable scoped instance dualComoduleInstance : RightComodule k H (Module.Dual k M) :=
  Coalgebra.Comodule.dualComodule k M

/-- The coaction of `dualComoduleInstance` on `M*` is `Coalgebra.Comodule.dualCoact k M`
(true by definition). -/
lemma coact_dual (χ : Module.Dual k M) :
    coact (R := k) (C := H) χ = Coalgebra.Comodule.dualCoact k M χ := rfl

/-- **The dual carries the inverse character** (part of Takeuchi's Lemma 4.15).  If every matrix
coefficient of the functional `χ` is a multiple of `g` modulo `I` — that is, if `χ` is a morphism
of `H/I`-comodules from `M` onto the character `ḡ` — then `χ`, as a vector of the dual comodule
`M*`, is relatively invariant modulo `I` with character `S g`. -/
theorem isRelInvMod_dual {χ : Module.Dual k M} {g : H}
    (hχ : ∀ m : M, Ideal.Quotient.mk I (comoduleCoeff χ m)
      = χ m • Ideal.Quotient.mk I g) :
    IsRelInvMod k I χ (antipode k g) := by
  rw [IsRelInvMod]
  refine Coalgebra.Comodule.dualTensorHom_injective (M := M) (k := k) (H ⧸ I) ?_
  ext m
  rw [Coalgebra.Comodule.dualTensorHom_lTensor, coact_dual,
      Coalgebra.Comodule.dualTensorHom_dualCoact,
    dualCoactHom_eq_antipode_comoduleCoeff]
  change Ideal.Quotient.mk I (antipode k (comoduleCoeff χ m)) = _
  rw [← HopfAlgebra.quotAntipode_mk k I, hχ m, map_smul, HopfAlgebra.quotAntipode_mk]
  simp

/-- **The coinvariant twist** (Takeuchi's Lemma 4.15).  A vector `v` which is relatively
invariant modulo `I` with a group-like character `ḡ`, tensored with a functional `χ` on a
finite-dimensional comodule which is colinear modulo `I` with the same character, is coinvariant
modulo `I`. -/
theorem isCoinvMod_tmul_dual {v : V} {χ : Module.Dual k M} {g : H}
    (hv : IsRelInvMod k I v g)
    (hg : IsGroupLikeElem k (Ideal.Quotient.mk I g))
    (hχ : ∀ m : M, Ideal.Quotient.mk I (comoduleCoeff χ m)
      = χ m • Ideal.Quotient.mk I g) :
    IsCoinvMod k I (v ⊗ₜ[k] χ) :=
  isCoinvMod_tmul_of_isRelInvMod hv (isRelInvMod_dual I hχ) (mk_mul_antipode_eq_one I hg)

end Quotient

end HopfAlgebra.Commutative
end
