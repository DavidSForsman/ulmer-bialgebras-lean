module

public import Hopf.Commutative.ComoduleCoeff

/-!
# Takeuchi's Lemma 4.13: the group-like coefficient of a relatively invariant vector

Let `H` be a commutative Hopf algebra over a field `k`, let `I` be a Hopf ideal of `H` and let
`V` be a right `H`-comodule.  A vector `v` of `V` is *relatively invariant modulo `I` with
coefficient `g`* when its coaction becomes `v ⊗ ḡ` in `V ⊗ H/I`; this is the property
`HopfAlgebra.Commutative.IsRelInvMod`, which for `g = 1` is the coinvariance
`HopfAlgebra.Commutative.IsCoinvMod` of `Hopf/Commutative/ComoduleCoeff.lean`.

Takeuchi's Lemma 4.13 (*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta
math. **7** (1972)) says that the coefficient may be taken to be an *explicit element of `H`*,
namely a matrix coefficient of `v`, and that this element is group-like modulo `I`:

> if `W = k v` is a one-dimensional subcomodule of `V` modulo `I`, then there is `g ∈ H` with
> `ε g = 1`, `Δ g ≡ g ⊗ g mod H ⊗ I` and `ρ v ≡ v ⊗ g mod V ⊗ I`.

## Main results

* `HopfAlgebra.Commutative.isRelInvMod_comoduleCoeff`: the coefficient `∑ ⟨χ, v₍₀₎⟩ v₍₁₎` of `v`
  against a functional with `⟨χ, v⟩ = 1` is again a coefficient of relative invariance for `v`;
* `HopfAlgebra.Commutative.counit_comoduleCoeff_eq_one`: it has counit `1`;
* `HopfAlgebra.Commutative.lTensorQuot_comul_comoduleCoeff`: it is group-like modulo `I`;
* `HopfAlgebra.Commutative.exists_groupLikeMod_of_isRelInvMod`: the three statements together, which
  is Takeuchi's Lemma 4.13.

This is one of the steps (Lemmas 4.10–4.15) of the surjectivity half of Takeuchi's Theorem 4.3,
which is still carried in this development as the explicit hypothesis
`HopfAlgebra.Commutative.NormalHopfIdealEqAugSpan`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.13 and Theorem 4.3
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- Contraction of the first tensor factor of `V ⊗ H/I` against a linear functional. -/
noncomputable def contractFstQuot (I : Ideal H) (χ : V →ₗ[k] k) :
    V ⊗[k] (H ⧸ I) →ₗ[k] H ⧸ I :=
  (TensorProduct.lid k (H ⧸ I)).toLinearMap ∘ₗ LinearMap.rTensor (H ⧸ I) χ

/-- `contractFstQuot I χ (u ⊗ h) = χ(u) h`. -/
@[simp] lemma contractFstQuot_tmul (I : Ideal H) (χ : V →ₗ[k] k) (u : V) (h : H ⧸ I) :
    contractFstQuot I χ (u ⊗ₜ[k] h) = χ u • h := by
  simp [contractFstQuot]

/-- Contracting and then reducing modulo `I` is the same as reducing and then contracting. -/
lemma quot_contractFst (I : Ideal H) (χ : V →ₗ[k] k) (z : V ⊗[k] H) :
    Ideal.Quotient.mk I (contractFst χ z)
      = contractFstQuot I χ
          (LinearMap.lTensor V (Ideal.Quotient.mkₐ k I).toLinearMap z) := by
  induction z with
  | tmul u h => simp [Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]

variable [RightComodule k H V]

/-- A vector `v` of a right `H`-comodule is **relatively invariant modulo `I` with coefficient
`g`** if its coaction becomes `v ⊗ ḡ` in `V ⊗ H/I`.  For `g = 1` this is
`HopfAlgebra.Commutative.IsCoinvMod`. -/
def IsRelInvMod (k : Type u) [Field k] [HopfAlgebra k H] [Module k V] [RightComodule k H V]
    (I : Ideal H) (v : V) (g : H) : Prop :=
  LinearMap.lTensor V (Ideal.Quotient.mkₐ k I).toLinearMap (coact (R := k) (C := H) v)
    = v ⊗ₜ[k] (Ideal.Quotient.mk I g)

/-- `v` is coinvariant modulo `I` iff it is relatively invariant modulo `I` with coefficient `1`. -/
lemma isCoinvMod_iff_isRelInvMod {I : Ideal H} {v : V} :
    IsCoinvMod k I v ↔ IsRelInvMod k I v 1 := by
  rw [IsCoinvMod, IsRelInvMod, map_one]

/-- **The coefficient of a relatively invariant vector is again a coefficient of relative
invariance**: if `ρ v ≡ v ⊗ g mod V ⊗ I` and `⟨χ, v⟩ = 1`, then `ρ v ≡ v ⊗ (∑ ⟨χ, v₍₀₎⟩ v₍₁₎)`. -/
theorem isRelInvMod_comoduleCoeff {I : Ideal H} {v : V} {g : H} (hv : IsRelInvMod k I v g)
    {χ : V →ₗ[k] k} (hχ : χ v = 1) : IsRelInvMod k I v (comoduleCoeff χ v) := by
  have h : Ideal.Quotient.mk I (comoduleCoeff χ v) = Ideal.Quotient.mk I g := by
    rw [comoduleCoeff, quot_contractFst, hv, contractFstQuot_tmul, hχ, one_smul]
  rw [IsRelInvMod, h]
  exact hv

/-- The coefficient against a functional with `⟨χ, v⟩ = 1` has counit `1`. -/
theorem counit_comoduleCoeff_eq_one {v : V} {χ : V →ₗ[k] k} (hχ : χ v = 1) :
    Coalgebra.counit (R := k) (A := H) (comoduleCoeff χ v) = 1 := by
  rw [counit_comoduleCoeff, hχ]

/-- **The coefficient of a relatively invariant vector is group-like modulo `I`**:
`Δ g ≡ g ⊗ g mod H ⊗ I`. -/
theorem lTensorQuot_comul_comoduleCoeff {I : Ideal H} {v : V} {g : H} (hv : IsRelInvMod k I v g)
    {χ : V →ₗ[k] k} (hχ : χ v = 1) :
    lTensorQuot I (comul (R := k) (A := H) (comoduleCoeff χ v))
      = comoduleCoeff χ v ⊗ₜ[k] Ideal.Quotient.mk I (comoduleCoeff χ v) := by
  classical
  -- write `ρ v = v ⊗ g + t` with `t ∈ V ⊗ I`
  have h0 : LinearMap.lTensor V (Ideal.Quotient.mkₐ k I).toLinearMap
      (coact (R := k) (C := H) v - v ⊗ₜ[k] g) = 0 := by
    rw [map_sub, hv]
    simp
  have ht : coact (R := k) (C := H) v - v ⊗ₜ[k] g
      ∈ LinearMap.range (LinearMap.lTensor V (I.restrictScalars k).subtype) := by
    have := TensorProduct.mem_range_lTensor_ker (M := V) (Ideal.Quotient.mkₐ k I).toLinearMap h0
    rwa [ker_quotMkₐ] at this
  obtain ⟨s, hs⟩ := ht
  have hsplit : coact (R := k) (C := H) v
      = v ⊗ₜ[k] g + LinearMap.lTensor V (I.restrictScalars k).subtype s := by
    rw [hs]; abel
  -- the coefficient is congruent to `g` modulo `I`
  have hgc : Ideal.Quotient.mk I (comoduleCoeff χ v) = Ideal.Quotient.mk I g := by
    rw [comoduleCoeff, quot_contractFst, hv, contractFstQuot_tmul, hχ, one_smul]
  -- the main computation
  have hcoassoc : (TensorProduct.assoc k V H H)
      (LinearMap.rTensor H (coact (R := k) (C := H)) (coact (R := k) (C := H) v))
      = LinearMap.lTensor V (comul (R := k) (A := H)) (coact (R := k) (C := H) v) := by
    have := congr($(Coalgebra.RightComodule.coassoc (R := k) (C := H) (M := V)) v)
    simpa using this
  have hmain : comul (R := k) (A := H) (comoduleCoeff χ v)
      = LinearMap.rTensor H (contractFst χ)
          (LinearMap.rTensor H (coact (R := k) (C := H)) (coact (R := k) (C := H) v)) := by
    rw [comoduleCoeff, comul_contractFst, ← hcoassoc]
    simp
  rw [hmain]
  nth_rewrite 1 [hsplit]
  rw [map_add, map_add, map_add, lTensorQuot_rTensor_contractFst_eq_zero, add_zero]
  simp only [LinearMap.rTensor_tmul]
  rw [lTensorQuot_tmul, hgc]
  rfl

/-- **Takeuchi's Lemma 4.13** [Takeuchi1972].  If `v` spans a one-dimensional subcomodule of `V`
modulo the Hopf ideal `I` — that is, if `ρ v ≡ v ⊗ g mod V ⊗ I` for some `g ∈ H` — then the
coefficient can be chosen so that it has counit `1` and is group-like modulo `I`. -/
theorem exists_groupLikeMod_of_isRelInvMod {I : Ideal H} {v : V} {g : H}
    (hv : IsRelInvMod k I v g) {χ : V →ₗ[k] k} (hχ : χ v = 1) :
    ∃ c : H, Coalgebra.counit (R := k) (A := H) c = 1 ∧
      lTensorQuot I (comul (R := k) (A := H) c) = c ⊗ₜ[k] Ideal.Quotient.mk I c ∧
      IsRelInvMod k I v c :=
  ⟨comoduleCoeff χ v, counit_comoduleCoeff_eq_one hχ,
    lTensorQuot_comul_comoduleCoeff hv hχ, isRelInvMod_comoduleCoeff hv hχ⟩

end HopfAlgebra.Commutative
end
