module

public import Hopf.Commutative.TensorLine
public import Hopf.Commutative.LineGroupLike
public import Hopf.Commutative.DualWeight

/-!
# Takeuchi's Lemma 4.15 for an ideal of the form `N(V, k v)`

Let `H` be a commutative Hopf algebra over a field `k`.  Takeuchi's Lemma 4.15 (*A correspondence
between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972)) produces, for a normal
Hopf ideal `I` of a finitely generated `H` over an algebraically closed field, a comodule `V` and
a line `W = k v` with `I = N(V, W)` and `ρ v ≡ v ⊗ 1` modulo `V ⊗ I`, whence `I = K(I)⁺H` by the
computation of `Hopf/Commutative/ComoduleCoeff.lean`.

The passage from a *relatively invariant* vector to a *coinvariant* one is his twisting argument:
one replaces `V` by `V ⊗ U*` and `v` by `v ⊗ χ`, where `χ` is a functional of a finite-dimensional
comodule `U` which is colinear modulo `I` with the same group-like character.  This is legitimate
because Takeuchi's Lemma 4.10(ii) computes the ideal of the twisted line,

```
N(V ⊗ U*, k (v ⊗ χ)) = N(V, k v) + N(U*, k χ),
```

which is formalised in `Hopf/Commutative/TensorLine.lean`.

## Main result

* `HopfAlgebra.Commutative.eq_augIdeal_coinv_of_line_charFunctional`: if a normal Hopf ideal `I` is
  contained in `N(V, k v)` for a unimodular vector `v` which is relatively invariant modulo `I`
  with a group-like character `ḡ`, and if some finite-dimensional comodule carries a non-zero
  functional colinear modulo `I` with the same character, then `I = K(I)⁺H`, the conclusion of
  the surjectivity half of Takeuchi's Theorem 4.3.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 4.10(ii) and 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V M : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V]
  [AddCommGroup M] [Module k M] [RightComodule k H M] [FiniteDimensional k M]

/-- **Takeuchi's Lemma 4.15 for an ideal contained in the ideal of a line.**  Let `I` be a normal
Hopf ideal of `H`, let `v` be a unimodular vector of a right `H`-comodule `V` which is relatively
invariant modulo `I` with a group-like character `ḡ`, and suppose that `I ≤ N(V, k v)`.  If some
finite-dimensional comodule `M` carries a functional `θ` which is colinear modulo `I` with the
same character and which is non-zero at `m₀`, then `I = K(I)⁺H`. -/
theorem eq_augIdeal_coinv_of_line_charFunctional (I : Ideal H) [Fact (IsHopfIdeal k I)]
    (hI : IsNormalHopfIdeal k I) {v : V} {g : H} {θ : Module.Dual k M} {m₀ : M}
    (χ : V →ₗ[k] k) (hχ : χ v = 1)
    (hIv : I ≤ NIdeal H (k ∙ v : Submodule k V))
    (hv : IsRelInvMod k I v g) (hg : IsGroupLikeElem k (Ideal.Quotient.mk I g))
    (hθ : ∀ m : M, Ideal.Quotient.mk I (comoduleCoeff θ m) = θ m • Ideal.Quotient.mk I g)
    (hθm : θ m₀ = 1) :
    I = augIdeal (coinvOfIdeal (k := k) I) :=
  eq_augIdeal_coinv_of_NIdeal_tmul hI χ (LinearMap.applyₗ (R := k) m₀) hχ hθm hIv
    (isCoinvMod_tmul_dual I hv hg hθ)

end HopfAlgebra.Commutative
end
