module

public import Hopf.Commutative.TensorLine
public import Hopf.Basic.ComoduleExteriorPower
public import Foundations.RingTheory.ExteriorWedgeKernel
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Takeuchi's Lemma 4.10(i) for a subspace with a basis: the hard direction

Let `H` be a commutative Hopf algebra over a field `k`, let `V` be a right `H`-comodule and let
`w : Fin n → V` be a linearly independent family spanning a subspace `W ≤ V`.  Write
`ω = w 0 ∧ ⋯ ∧ w (n-1)` for the corresponding element of the exterior algebra `⋀ V`, so that
`k · ω` is the line `⋀ⁿ W ⊆ ⋀ⁿ V`.

Takeuchi's Lemma 4.10(i) (*A correspondence between Hopf ideals and sub-Hopf algebras*,
manuscripta math. **7** (1972)) reduces his ideal `N(V, W)` to the ideal of a *line*, namely
`N(⋀ⁿ V, ⋀ⁿ W)`.  The substantial half of that statement is proved here: if the line `k · ω` is a
subcomodule of `⋀ V` modulo an ideal `J`, then `W` is a subcomodule of `V` modulo `J`.

The proof is the one sketched by HopfAlgebra.Commutative. Since the coaction of the exterior algebra
is an algebra homomorphism `Λρ`, the hypothesis says `Λρ_J(ω) = ω ⊗ ρ` for some `ρ` in `H/J`, and
the multiplicative contraction of `TensorLine` shows that `ρ` is a unit. For each basis
vector `wᵢ` we have `ι(wᵢ) · ω = 0` in `⋀ V`, hence `Λρ_J(ι wᵢ) · (ω ⊗ ρ) = 0`, and cancelling the
unit gives `Λρ_J(ι wᵢ) · (ω ⊗ 1) = 0`. That is exactly the vanishing of the coaction of `wᵢ` under
the map `v ↦ v ∧ ω`, whose kernel is `W` (`ExteriorWedgeKernel`); flatness of `H/J` as a `k`-vector
space then places the coaction of `wᵢ` in `W ⊗ H/J`.

## Main results

* `HopfAlgebra.Commutative.mem_range_rTensor_ker_of_rTensor_eq_zero`: a vector-space kernel
  computation for tensor products;
* `HopfAlgebra.Commutative.isSubcomoduleMod_of_line_exterior`: **the hard half of Lemma 4.10(i)**;
* `HopfAlgebra.Commutative.nIdeal_le_nIdeal_exterior_line`: consequently `N(V, W) ≤ N(⋀ V, k · ω)`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.10(i)
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open ExteriorAlgebra
open Coalgebra Coalgebra.Comodule HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

/-! ### A kernel computation for tensor products of vector spaces -/

section Kernel

variable {k : Type u} [Field k]

/-- If a tensor of `V ⊗ M` is killed by `ψ ⊗ 1` then it comes from `(ker ψ) ⊗ M`. -/
theorem mem_range_rTensor_ker_of_rTensor_eq_zero {V E M : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup E] [Module k E] [AddCommGroup M] [Module k M]
    (ψ : V →ₗ[k] E) {z : V ⊗[k] M} (hz : LinearMap.rTensor M ψ z = 0) :
    z ∈ LinearMap.range (LinearMap.rTensor M (LinearMap.ker ψ).subtype) := by
  set q : (V ⧸ LinearMap.ker ψ) →ₗ[k] E :=
    (LinearMap.range ψ).subtype ∘ₗ ψ.quotKerEquivRange.toLinearMap with hq
  have hqinj : LinearMap.ker q = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp ψ.quotKerEquivRange.injective
  obtain ⟨g, hg⟩ := q.exists_leftInverse_of_injective hqinj
  have hgψ : g ∘ₗ ψ = (LinearMap.ker ψ).mkQ := by
    ext v
    have hv : ψ v = q ((LinearMap.ker ψ).mkQ v) := by
      simp [hq, LinearMap.quotKerEquivRange_apply_mk]
    simp only [LinearMap.coe_comp, Function.comp_apply, hv]
    rw [← LinearMap.comp_apply, hg, LinearMap.id_apply]
  rw [TensorProduct.range_rTensor_subtype_eq_ker]
  have hzz : LinearMap.rTensor M (LinearMap.ker ψ).mkQ z
      = LinearMap.rTensor M g (LinearMap.rTensor M ψ z) := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hgψ]
  simp [LinearMap.mem_ker, hzz, hz]

end Kernel

/-! ### The coaction of the exterior algebra modulo an ideal -/

section Exterior

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V]

variable (k H V) in
/-- The canonical map `V ⊗ (H/J) → (⋀ V) ⊗ (H/J)`. -/
noncomputable def extIotaQ (J : Ideal H) :
    V ⊗[k] (H ⧸ J) →ₗ[k] (ExteriorAlgebra k V) ⊗[k] (H ⧸ J) :=
  TensorProduct.map (ExteriorAlgebra.ι k) LinearMap.id

/-- `extIotaQ (v ⊗ r) = ι v ⊗ r`. -/
@[simp] lemma extIotaQ_tmul (J : Ideal H) (v : V) (r : H ⧸ J) :
    extIotaQ k H V J (v ⊗ₜ[k] r) = (ExteriorAlgebra.ι k v) ⊗ₜ[k] r := rfl

/-- Multiplying the image of `V ⊗ H/J` in `(⋀ V) ⊗ H/J` by `ω ⊗ 1` is wedging with `ω`. -/
theorem extIotaQ_mul_omega (J : Ideal H) {n : ℕ} (w : Fin n → V) (z : V ⊗[k] (H ⧸ J)) :
    extIotaQ k H V J z * ((ExteriorAlgebra.ιMulti k n w) ⊗ₜ[k] (1 : H ⧸ J))
      = LinearMap.rTensor (H ⧸ J) (ExteriorAlgebra.wedgeRight k w) z := by
  induction z with
  | tmul v r =>
      rw [extIotaQ_tmul, Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul,
        ExteriorAlgebra.wedgeRight_apply, mul_one]
  | add p q hp hq => rw [map_add, add_mul, hp, hq, map_add]

variable [RightComodule k H V]

local notation "E" => ExteriorAlgebra k V

variable (k H V) in
/-- The coaction of the exterior algebra reduced modulo an ideal `J` of `H`, as a homomorphism of
`k`-algebras `⋀ V → (⋀ V) ⊗ (H/J)`. -/
noncomputable def extCoactQAlgHom (J : Ideal H) :
    ExteriorAlgebra k V →ₐ[k] (ExteriorAlgebra k V) ⊗[k] (H ⧸ J) :=
  (Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V)) (Ideal.Quotient.mkₐ k J)).comp
    (extCoactAlgHom k H V)

/-- `extCoactQAlgHom` is the reduction of the coaction of `⋀ V` modulo `J`. -/
theorem extCoactQAlgHom_apply (J : Ideal H) (x : ExteriorAlgebra k V) :
    extCoactQAlgHom k H V J x
      = LinearMap.lTensor (ExteriorAlgebra k V) (Ideal.Quotient.mkₐ k J).toLinearMap
          (coact (R := k) (C := H) x) := by
  have hlin : ∀ z : (ExteriorAlgebra k V) ⊗[k] H,
      (Algebra.TensorProduct.map (AlgHom.id k (ExteriorAlgebra k V)) (Ideal.Quotient.mkₐ k J)) z
        = LinearMap.lTensor (ExteriorAlgebra k V) (Ideal.Quotient.mkₐ k J).toLinearMap z := by
    intro z
    induction z with
    | tmul a h => simp
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  exact hlin _

/-- On the generators, the reduced coaction of `⋀ V` is the reduced coaction of `V`. -/
theorem extCoactQAlgHom_ι (J : Ideal H) (v : V) :
    extCoactQAlgHom k H V J (ExteriorAlgebra.ι k v)
      = extIotaQ k H V J (LinearMap.lTensor V (Ideal.Quotient.mkₐ k J).toLinearMap
          (coact (R := k) (C := H) v)) := by
  rw [extCoactQAlgHom_apply, coact_exteriorAlgebra, extCoactAlgHom_ι]
  generalize coact (R := k) (C := H) v = z
  induction z with
  | tmul u h => simp [extIota]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

/-! ### The hard direction of Takeuchi's Lemma 4.10(i) -/

/-- **If the line spanned by `ω = w₀ ∧ ⋯ ∧ w_{n-1}` is a subcomodule of `⋀ V` modulo `J`, then the
span of the `wᵢ` is a subcomodule of `V` modulo `J`.**  This is the substantial half of Takeuchi's
Lemma 4.10(i). -/
theorem isSubcomoduleMod_of_line_exterior (J : Ideal H) {n : ℕ} {w : Fin n → V}
    (hw : LinearIndependent k w) (χ : ExteriorAlgebra k V →ₗ[k] k)
    (hχ : χ (ExteriorAlgebra.ιMulti k n w) = 1)
    (h : IsSubcomoduleMod J
      (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V))) :
    IsSubcomoduleMod J (Submodule.span k (Set.range w)) := by
  classical
  set ω : ExteriorAlgebra k V := ExteriorAlgebra.ιMulti k n w with hω
  -- the coaction of `ω` modulo `J` is `ω ⊗ ρ`
  obtain ⟨ρ, hρ⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) ω
    (h _ (Submodule.mem_span_singleton_self _))
  -- `ρ` is a unit, with inverse the reduction of `S(⟨χ, ω₍₀₎⟩ ω₍₁₎)`
  set η : ExteriorAlgebra k V →ₗ[k] H :=
    (antipode k : H →ₗ[k] H) ∘ₗ coeffMap (H := H) χ with hη
  have hunit : Ideal.Quotient.mk J (η ω) * ρ = 1 := by
    have h1 := mulContractQ_lTensor_mk (V' := ExteriorAlgebra k V) J η (coact (R := k) (C := H) ω)
    rw [hρ, mulContractQ_tmul, mulContract_antipode_coeffMap χ hχ, map_one] at h1
    exact h1
  -- each basis vector's coaction is killed by wedging with `ω`
  have hkey : ∀ i : Fin n,
      LinearMap.rTensor (H ⧸ J) (ExteriorAlgebra.wedgeRight k w)
        (LinearMap.lTensor V (Ideal.Quotient.mkₐ k J).toLinearMap
          (coact (R := k) (C := H) (w i))) = 0 := by
    intro i
    have hmul : extCoactQAlgHom k H V J (ExteriorAlgebra.ι k (w i))
        * extCoactQAlgHom k H V J ω = 0 := by
      rw [← map_mul, ExteriorAlgebra.ι_mul_ιMulti_self, map_zero]
    rw [extCoactQAlgHom_ι, extCoactQAlgHom_apply, hρ] at hmul
    -- cancel the unit `ρ`
    have hcancel := congr($hmul * ((1 : ExteriorAlgebra k V) ⊗ₜ[k] (Ideal.Quotient.mk J (η ω))))
    simp only [zero_mul] at hcancel
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm ρ, hunit] at hcancel
    rw [← extIotaQ_mul_omega J w]
    exact hcancel
  -- conclude that the coaction of each `wᵢ` lands in `W ⊗ H/J`
  have hmem : ∀ i : Fin n,
      LinearMap.lTensor V (Ideal.Quotient.mkₐ k J).toLinearMap (coact (R := k) (C := H) (w i))
        ∈ LinearMap.range (LinearMap.rTensor (H ⧸ J)
            (Submodule.span k (Set.range w)).subtype) := by
    intro i
    have := mem_range_rTensor_ker_of_rTensor_eq_zero
      (ExteriorAlgebra.wedgeRight k w) (hkey i)
    rwa [ExteriorAlgebra.ker_wedgeRight hw] at this
  intro u hu
  refine Submodule.span_induction (p := fun u _ =>
    LinearMap.lTensor V (Ideal.Quotient.mkₐ k J).toLinearMap (coact (R := k) (C := H) u)
      ∈ LinearMap.range (LinearMap.rTensor (H ⧸ J)
        (Submodule.span k (Set.range w)).subtype)) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨i, rfl⟩
    exact hmem i
  · simp
  · intro a b _ _ ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ ha

/-- **Takeuchi's Lemma 4.10(i), the inclusion `N(V, W) ≤ N(⋀ V, ⋀ⁿ W)`** for a subspace `W` with
basis `w₀, …, w_{n-1}` and `ω = w₀ ∧ ⋯ ∧ w_{n-1}`. -/
theorem nIdeal_le_nIdeal_exterior_line {n : ℕ} {w : Fin n → V} (hw : LinearIndependent k w) :
    NIdeal H (Submodule.span k (Set.range w))
      ≤ NIdeal H (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V)) := by
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one k
    (ExteriorAlgebra.ιMulti_ne_zero_of_linearIndependent hw)
  refine (nIdeal_le_iff (fun x hx => antipode_mem_NIdeal _ hx) _).2 ?_
  exact isSubcomoduleMod_of_line_exterior _ hw χ hχ (isSubcomoduleMod_NIdeal _)

end Exterior

end HopfAlgebra.Commutative
end
