module

public import Hopf.Commutative.ExteriorLineEasy
public import Hopf.Commutative.AugSpanOfLineFunctional
public import Hopf.Commutative.FaithfulFlatnessUnconditional

/-!
# Takeuchi's Remark 4.14: a character functional for a *power* suffices

Let `H` be a commutative Hopf algebra over a field `k`.  The reduction of the surjectivity half of
Takeuchi's Theorem 4.3 (through his Lemmas 4.10 and 4.15) requires,
for every element `g` which is group-like modulo a normal Hopf ideal `I`, a finite-dimensional
comodule carrying a functional with character `ḡ`.  In characteristic `p` Takeuchi only produces
such a functional for a *power* of `g` (his Remark 4.14).  This file shows that this weaker input
already suffices:

> `HopfAlgebra.Commutative.HasCharacterFunctionalPow` implies the surjectivity half of Theorem 4.3
for a > noetherian `H`.

The trick is to replace the exterior line `k ω` produced by Lemma 4.10(i) by the line
`k (ω ⊗ gⁿ)` inside `(⋀ H) ⊗ H`, where `H` carries the regular comodule structure.  The element
`gⁿ` is relatively invariant modulo `I` with coefficient `gⁿ` (relative invariance in the regular
comodule is multiplicative, because `id ⊗ π` is an algebra map), so `ω ⊗ gⁿ` is relatively
invariant with the coefficient `g^(n+1)`; and Lemma 4.10(ii) for lines gives

```
N((⋀ H) ⊗ H, k (ω ⊗ gⁿ)) = N(⋀ H, k ω) + N(H, k gⁿ) ≥ I,
```

which is all that Lemma 4.15 needs.

## Main definitions

* `HopfAlgebra.Commutative.HasCharacterFunctionalPow`: the weakened character-functional input.

## Main results

* `HopfAlgebra.Commutative.isRelInvMod_self_pow`: powers of a relatively invariant element of the
  regular comodule are relatively invariant, with the corresponding powers as coefficients;
* `HopfAlgebra.Commutative.eq_augIdeal_coinv_of_hasCharacterFunctionalPow` and
  `HopfAlgebra.Commutative.normalHopfIdealEqAugSpan_of_hasCharacterFunctionalPow`: the surjectivity
  half of Theorem 4.3 for a noetherian `H`, granting only the weakened input.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 4.10 and 4.15, Remark 4.14, Theorem 4.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-! ### Relative invariance in the regular comodule is multiplicative -/

/-- The algebra map `id ⊗ π` is the linear map `id ⊗ π`. -/
lemma lTensorQuot_eq_lTensor (I : Ideal H) (z : H ⊗[k] H) :
    lTensorQuot I z = LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap z := by
  induction z with
  | tmul x y => rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq]

/-- Relative invariance of an element of `H`, viewed in the regular comodule, written with the
algebra map `id ⊗ π`. -/
lemma isRelInvMod_self_iff {I : Ideal H} {x g : H} :
    IsRelInvMod k I x g ↔
      lTensorQuot I (comul (R := k) (A := H) x) = x ⊗ₜ[k] Ideal.Quotient.mk I g := by
  rw [IsRelInvMod, lTensorQuot_eq_lTensor]
  exact Iff.rfl

/-- `1` is coinvariant in the regular comodule. -/
lemma isRelInvMod_self_one {I : Ideal H} : IsRelInvMod k I (1 : H) 1 := by
  have hone : comul (R := k) (A := H) (1 : H) = 1 := by
    simp
  rw [isRelInvMod_self_iff, hone, map_one, map_one, Algebra.TensorProduct.one_def]

/-- **Relative invariance in the regular comodule is multiplicative.** -/
lemma isRelInvMod_self_mul {I : Ideal H} {x y g g' : H}
    (hx : IsRelInvMod k I x g) (hy : IsRelInvMod k I y g') :
    IsRelInvMod k I (x * y) (g * g') := by
  rw [isRelInvMod_self_iff] at hx hy ⊢
  have hcomul : comul (R := k) (A := H) (x * y)
      = comul (R := k) (A := H) x * comul (R := k) (A := H) y := by
    simp
  rw [hcomul, map_mul, hx, hy, Algebra.TensorProduct.tmul_mul_tmul, map_mul]

/-- **Powers of a relatively invariant element of the regular comodule are relatively
invariant**, with the corresponding power as coefficient. -/
lemma isRelInvMod_self_pow {I : Ideal H} {x g : H} (h : IsRelInvMod k I x g) :
    ∀ n : ℕ, IsRelInvMod k I (x ^ n) (g ^ n)
  | 0 => by
      simp only [pow_zero]
      exact isRelInvMod_self_one
  | (n + 1) => by
      rw [pow_succ, pow_succ]
      exact isRelInvMod_self_mul (isRelInvMod_self_pow h n) h

/-! ### The weakened character-functional input -/

variable (k H) in
/-- **The remaining input of Takeuchi's Lemma 4.15, weakened as in his Remark 4.14.**  Every
element `g` of `H` which is group-like modulo a normal Hopf ideal `I` has some power `g^(n+1)`
which is carried by a functional of a finite-dimensional comodule. -/
def HasCharacterFunctionalPow : Prop :=
  ∀ I : Ideal H, IsNormalHopfIdeal k I → ∀ g : H,
    Coalgebra.counit (R := k) (A := H) g = 1 →
    lTensorQuot I (comul (R := k) (A := H) g) = g ⊗ₜ[k] Ideal.Quotient.mk I g →
    ∃ (n : ℕ) (M : Type u) (_ : AddCommGroup M) (_ : Module k M) (_ : RightComodule k H M)
      (_ : FiniteDimensional k M) (θ : Module.Dual k M) (m₀ : M),
      θ m₀ = 1 ∧ ∀ m : M, Ideal.Quotient.mk I (comoduleCoeff θ m)
        = θ m • Ideal.Quotient.mk I (g ^ (n + 1))

/-- **The surjectivity half of Takeuchi's Theorem 4.3 for a noetherian Hopf algebra**, granting
only the weakened input of Remark 4.14. -/
theorem eq_augIdeal_coinv_of_hasCharacterFunctionalPow [IsNoetherianRing H]
    (hchar : HasCharacterFunctionalPow k H) {I : Ideal H} (hI : IsNormalHopfIdeal k I) :
    I = augIdeal (coinvOfIdeal (k := k) I) := by
  classical
  have : Fact (IsHopfIdeal k I) := ⟨hI.toIsHopfIdeal⟩
  -- Lemma 4.12: `I = N(H, W)` for a finite-dimensional subspace `W`
  obtain ⟨E, W, -, -, hWfg, -, -, hNI⟩ :=
    exists_NIdeal_eq_of_isNoetherianRing (I := I) hI.toIsHopfIdeal
  have : Module.Finite k ↥W := Module.Finite.iff_fg.2 hWfg
  set n : ℕ := Module.finrank k ↥W with hn
  set b : Module.Basis (Fin n) k ↥W := Module.finBasis k ↥W with hb
  set w : Fin n → H := fun i => ((b i : ↥W) : H) with hw
  have hwli : LinearIndependent k w :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span k (Set.range w) = W := by
    have hrange : Set.range w = W.subtype '' (Set.range (fun i => b i)) := by
      rw [← Set.range_comp]; rfl
    rw [hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  -- Lemma 4.10(i): `I` is the ideal of the line spanned by `ω = w 0 ∧ ⋯ ∧ w (n-1)`
  set ω : ExteriorAlgebra k H := ExteriorAlgebra.ιMulti k n w with hω
  have hIeq : I = NIdeal H (k ∙ ω : Submodule k (ExteriorAlgebra k H)) := by
    rw [← hNI, ← hspan, hω]
    exact nIdeal_exterior_line_eq hwli
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one k
    (ExteriorAlgebra.ιMulti_ne_zero_of_linearIndependent hwli)
  rw [← hω] at hχ
  -- Lemma 4.13: the line has a group-like character
  have hsub : IsSubcomoduleMod I (k ∙ ω : Submodule k (ExteriorAlgebra k H)) := by
    rw [hIeq]
    exact isSubcomoduleMod_NIdeal _
  obtain ⟨g₀, hrel₀⟩ := exists_isRelInvMod_of_isSubcomoduleMod hsub
  obtain ⟨g, hgc, hgcomul, hrel⟩ := exists_groupLikeMod_of_isRelInvMod hrel₀ hχ
  have hgl : IsGroupLikeElem k (Ideal.Quotient.mk I g) :=
    isGroupLikeElem_mk_of_lTensorQuot I hgc hgcomul
  -- Remark 4.14: a character functional for a power `g^(m+1)`
  obtain ⟨m, M, _, _, _, _, θ, m₀, hθ1, hθ2⟩ := hchar I hI g hgc hgcomul
  -- the twisted line `k (ω ⊗ gᵐ)` of `(⋀ H) ⊗ H`
  have hgm : IsRelInvMod k I (g ^ m) (g ^ m) :=
    isRelInvMod_self_pow (isRelInvMod_self_iff.2 hgcomul) m
  have hv : IsRelInvMod k I (ω ⊗ₜ[k] (g ^ m)) (g ^ (m + 1)) := by
    have := isRelInvMod_tmul hrel hgm
    rwa [← pow_succ'] at this
  have hcount : Coalgebra.counit (R := k) (A := H) (g ^ m) = 1 := by
    have hp : (Bialgebra.counitAlgHom k H) (g ^ m) = ((Bialgebra.counitAlgHom k H) g) ^ m :=
      map_pow _ _ _
    simp only [Bialgebra.counitAlgHom_apply] at hp
    rw [hp, hgc, one_pow]
  set χ' : (ExteriorAlgebra k H) ⊗[k] H →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap ∘ₗ
      TensorProduct.map χ (Coalgebra.counit (R := k) (A := H)) with hχ'def
  have hχ' : χ' (ω ⊗ₜ[k] (g ^ m)) = 1 := by
    simp [hχ'def, hχ, hcount]
  have hIle : I ≤ NIdeal H (k ∙ (ω ⊗ₜ[k] (g ^ m)) :
      Submodule k ((ExteriorAlgebra k H) ⊗[k] H)) := by
    rw [nIdeal_tmul_line χ (Coalgebra.counit (R := k) (A := H)) hχ hcount]
    exact hIeq.le.trans le_sup_left
  have hglm : IsGroupLikeElem k (Ideal.Quotient.mk I (g ^ (m + 1))) := by
    rw [map_pow]
    exact hgl.pow
  exact eq_augIdeal_coinv_of_line_charFunctional (M := M) I hI χ' hχ' hIle hv hglm hθ2 hθ1

/-- **The surjectivity half of Takeuchi's Theorem 4.3 for a noetherian Hopf algebra**, granting
only the weakened input of Remark 4.14. -/
theorem normalHopfIdealEqAugSpan_of_hasCharacterFunctionalPow [IsNoetherianRing H]
    (hchar : HasCharacterFunctionalPow k H) : NormalHopfIdealEqAugSpan k H :=
  fun _ hI => eq_augIdeal_coinv_of_hasCharacterFunctionalPow hchar hI

end HopfAlgebra.Commutative
end
