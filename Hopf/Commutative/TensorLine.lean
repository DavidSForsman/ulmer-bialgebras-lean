module

public import Hopf.Commutative.LineIdeal
public import Hopf.Basic.ComoduleTensor
public import Hopf.Basic.AntipodeInvolutive
public import Hopf.Commutative.RelInvTwist

/-!
# Takeuchi's Lemma 4.10(ii) for lines

Let `H` be a commutative Hopf algebra over a field `k` and let `V`, `V'` be right `H`-comodules.
Takeuchi's Lemma 4.10(ii) (*A correspondence between Hopf ideals and sub-Hopf algebras*,
manuscripta math. **7** (1972)) states that for one-dimensional subspaces `W ≤ V` and `W' ≤ V'`

```
N(V ⊗ V', W ⊗ W') = N(V, W) + N(V', W').
```

The inclusion `⊇` is immediate from the minimality of `N(V ⊗ V', W ⊗ W')`.  The inclusion `⊆`
rests on the fact that the line `W ⊗ W'` can only be a subcomodule of `V ⊗ V'` modulo an ideal
`J` if each of `W` and `W'` is already a subcomodule modulo `J`; this is Takeuchi's Lemma 4.11(ii)
in his argument, and is proved here by the *multiplicative contraction* of the coaction against
the antipode of a matrix coefficient, which shows that the coefficients of a unimodular vector
generate the unit ideal.

## Main results

* `HopfAlgebra.Commutative.mulContract_antipode_coeffMap`: for `⟨χ, w⟩ = 1`, the contraction
  `∑ S(⟨χ, w₍₀₎₍₀₎⟩ w₍₀₎₍₁₎) w₍₁₎` of the coaction of `w` equals `1`;
* `HopfAlgebra.Commutative.isSubcomoduleMod_left_of_tmul` and
  `HopfAlgebra.Commutative.isSubcomoduleMod_right_of_tmul`: if the line `k (w ⊗ w')` is a
  subcomodule of `V ⊗ V'` modulo `J`, then `k w` and `k w'` are subcomodules of `V` and `V'` modulo
  `J`;
* `HopfAlgebra.Commutative.isSubcomoduleMod_tmul`: the converse, which is straightforward;
* `HopfAlgebra.Commutative.nIdeal_tmul_line`: **Takeuchi's Lemma 4.10(ii) for lines**.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 4.10(ii), 4.11(ii) and 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V V' : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

/-! ### The multiplicative contraction of a coaction -/

/-- The contraction `v ⊗ h ↦ (η v) * h` of `V ⊗ H` against a map `η : V → H`. -/
noncomputable def mulContract (η : V →ₗ[k] H) : V ⊗[k] H →ₗ[k] H :=
  LinearMap.mul' k H ∘ₗ TensorProduct.map η LinearMap.id

/-- `mulContract η (v ⊗ h) = η v * h`. -/
@[simp] lemma mulContract_tmul (η : V →ₗ[k] H) (v : V) (h : H) :
    mulContract η (v ⊗ₜ[k] h) = η v * h := rfl

/-- The auxiliary map `x ⊗ y ↦ S(x) * y` on `H ⊗ H`. -/
noncomputable def antipodeMul : H ⊗[k] H →ₗ[k] H :=
  LinearMap.mul' k H ∘ₗ LinearMap.rTensor H (antipode k)
/-- `antipodeMul (x ⊗ y) = S(x) * y`. -/
@[simp] lemma antipodeMul_tmul (x y : H) :
    antipodeMul (k := k) (H := H) (x ⊗ₜ[k] y) = antipode k x * y := rfl

/-- The antipode axiom in the form `antipodeMul ∘ Δ = η ∘ ε`, i.e. `∑ S(x₍₁₎) x₍₂₎ = ε(x) 1`. -/
lemma antipodeMul_comp_comul :
    (antipodeMul (k := k) (H := H)) ∘ₗ (comul (R := k) (A := H))
      = Algebra.linearMap k H ∘ₗ (counit (R := k) (A := H)) := by
  rw [antipodeMul, LinearMap.comp_assoc]
  exact HopfAlgebra.mul_antipode_rTensor_comul

/-- The three-leg contraction `u ⊗ (x ⊗ y) ↦ ⟨χ, u⟩ S(x) y`, in two forms. -/
lemma antipodeMul_rTensor_contractFst (χ : V →ₗ[k] k) (z : V ⊗[k] (H ⊗[k] H)) :
    (LinearMap.mul' k H) (LinearMap.rTensor H (antipode k)
        (LinearMap.rTensor H (contractFst χ) ((TensorProduct.assoc k V H H).symm z)))
      = contractFst χ (LinearMap.lTensor V (antipodeMul (k := k) (H := H)) z) := by
  induction z with
  | tmul u y =>
      induction y with
      | tmul x y =>
          simp only [TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, contractFst_tmul,
            LinearMap.lTensor_tmul, antipodeMul_tmul, LinearMap.mul'_apply, map_smul,
            smul_mul_assoc]
      | add p q hp hq =>
          rw [TensorProduct.tmul_add]
          simp only [map_add, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

section Coeff

variable [RightComodule k H V]

/-- The matrix coefficient map `v ↦ ∑ ⟨χ, v₍₀₎⟩ v₍₁₎` as a linear map. -/
noncomputable def coeffMap (χ : V →ₗ[k] k) : V →ₗ[k] H :=
  contractFst χ ∘ₗ (coact (R := k) (C := H) : V →ₗ[k] V ⊗[k] H)

/-- Contracting the counital coaction: `∑ ⟨χ, v₍₀₎⟩ ε(v₍₁₎) 1 = ⟨χ, v⟩ 1`. -/
lemma contractFst_lTensor_counit (χ : V →ₗ[k] k) (v : V) :
    contractFst χ (LinearMap.lTensor V (Algebra.linearMap k H ∘ₗ (counit (R := k) (A := H)))
        (coact (R := k) (C := H) v)) = algebraMap k H (χ v) := by
  have key : ∀ z : V ⊗[k] H,
      contractFst χ (LinearMap.lTensor V (Algebra.linearMap k H ∘ₗ (counit (R := k) (A := H))) z)
        = algebraMap k H (χ ((TensorProduct.rid k V)
            (LinearMap.lTensor V (counit (R := k) (A := H)) z))) := by
    intro z
    induction z with
    | tmul u h =>
        simp [Algebra.algebraMap_eq_smul_one, smul_smul]
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, map_add, hp, hq, ← map_add]
  rw [key]
  have hc := congr($(Coalgebra.RightComodule.counit_coact (R := k) (C := H) (M := V)) v)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq,
    LinearEquiv.coe_coe] at hc
  rw [hc]

/-- **The coefficients of a unimodular vector generate the unit ideal**: if `⟨χ, w⟩ = 1`, the
multiplicative contraction of the coaction of `w` against the antipode of the coefficient map is
`1`, i.e. `∑ S(∑ ⟨χ, w₍₀₎₍₀₎⟩ w₍₀₎₍₁₎) w₍₁₎ = 1`. -/
theorem mulContract_antipode_coeffMap (χ : V →ₗ[k] k) {w : V} (hχ : χ w = 1) :
    mulContract ((antipode k : H →ₗ[k] H) ∘ₗ coeffMap (H := H) χ)
      (coact (R := k) (C := H) w) = 1 := by
  have hstep : mulContract ((antipode k : H →ₗ[k] H) ∘ₗ coeffMap (H := H) χ)
      (coact (R := k) (C := H) w)
      = (LinearMap.mul' k H) (LinearMap.rTensor H (antipode k)
          (LinearMap.rTensor H (contractFst χ)
            (LinearMap.rTensor H (coact (R := k) (C := H)) (coact (R := k) (C := H) w)))) := by
    rw [mulContract]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 1
    rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
    rfl
  have hcoassoc : LinearMap.rTensor H (coact (R := k) (C := H)) (coact (R := k) (C := H) w)
      = (TensorProduct.assoc k V H H).symm
          (LinearMap.lTensor V (comul (R := k) (A := H)) (coact (R := k) (C := H) w)) := by
    have := congr($(Coalgebra.RightComodule.coassoc (R := k) (C := H) (M := V)) w)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at this
    rw [← this]
    simp
  rw [hstep, hcoassoc, antipodeMul_rTensor_contractFst, ← LinearMap.lTensor_comp_apply,
    antipodeMul_comp_comul, contractFst_lTensor_counit, hχ, map_one]

end Coeff

/-! ### Lines in a tensor product of comodules -/

section TensorLine

variable {V₂ V₂' : Type u} [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₂'] [Module k V₂']

variable (J : Ideal H)

/-- The contraction `v ⊗ r ↦ mk(η v) * r` of `V' ⊗ H/J` against a map `η : V' → H`. -/
noncomputable def mulContractQ (η : V' →ₗ[k] H) : V' ⊗[k] (H ⧸ J) →ₗ[k] (H ⧸ J) :=
  LinearMap.mul' k (H ⧸ J) ∘ₗ
    TensorProduct.map ((Ideal.Quotient.mkₐ k J).toLinearMap ∘ₗ η) LinearMap.id

/-- `mulContractQ J η (v ⊗ r) = [η v] r`. -/
@[simp] lemma mulContractQ_tmul (η : V' →ₗ[k] H) (v : V') (r : H ⧸ J) :
    mulContractQ J η (v ⊗ₜ[k] r) = Ideal.Quotient.mk J (η v) * r := rfl

variable (V₂) in
/-- Right multiplication of the `H/J`-component: `(x ⊗ r) ⊗ s ↦ x ⊗ (r s)`. -/
noncomputable def rmulQ : ((V₂ ⊗[k] (H ⧸ J)) ⊗[k] (H ⧸ J)) →ₗ[k] V₂ ⊗[k] (H ⧸ J) :=
  LinearMap.lTensor V₂ (LinearMap.mul' k (H ⧸ J)) ∘ₗ
    (TensorProduct.assoc k V₂ (H ⧸ J) (H ⧸ J)).toLinearMap

/-- `rmulQ ((x ⊗ r) ⊗ s) = x ⊗ (r s)`. -/
@[simp] lemma rmulQ_tmul (x : V₂) (r s : H ⧸ J) :
    rmulQ V₂ J ((x ⊗ₜ[k] r) ⊗ₜ[k] s) = x ⊗ₜ[k] (r * s) := rfl

/-- `rmulQ (x ⊗ 1) = x`. -/
lemma rmulQ_one (x : V₂ ⊗[k] (H ⧸ J)) : rmulQ V₂ J (x ⊗ₜ[k] (1 : H ⧸ J)) = x := by
  induction x with
  | tmul v r => rw [rmulQ_tmul, mul_one]
  | add p q hp hq => rw [TensorProduct.add_tmul, map_add, hp, hq]

/-- The contraction of `(V ⊗ V') ⊗ H/J` which projects the first factor along `f` and contracts
the second factor multiplicatively against `η`. -/
noncomputable def contractLeftQ (f : V →ₗ[k] V₂) (η : V' →ₗ[k] H) :
    ((V ⊗[k] V') ⊗[k] (H ⧸ J)) →ₗ[k] V₂ ⊗[k] (H ⧸ J) :=
  LinearMap.lTensor V₂ (mulContractQ J η) ∘ₗ
    (TensorProduct.assoc k V₂ V' (H ⧸ J)).toLinearMap ∘ₗ
    LinearMap.rTensor (H ⧸ J) (LinearMap.rTensor V' f)

/-- `contractLeftQ J f η ((v ⊗ v') ⊗ r) = f v ⊗ [η v'] r`. -/
@[simp] lemma contractLeftQ_tmul (f : V →ₗ[k] V₂) (η : V' →ₗ[k] H) (v : V) (v' : V') (r : H ⧸ J) :
    contractLeftQ J f η ((v ⊗ₜ[k] v') ⊗ₜ[k] r) = f v ⊗ₜ[k] (Ideal.Quotient.mk J (η v') * r) := rfl

/-- The contraction of the second factor of `V' ⊗ V` against `η`, projecting the second factor
along `f`. -/
noncomputable def contractRightQ (f : V' →ₗ[k] V₂') (η : V →ₗ[k] H) :
    ((V ⊗[k] V') ⊗[k] (H ⧸ J)) →ₗ[k] V₂' ⊗[k] (H ⧸ J) :=
  LinearMap.lTensor V₂' (mulContractQ J η) ∘ₗ
    (TensorProduct.assoc k V₂' V (H ⧸ J)).toLinearMap ∘ₗ
    LinearMap.rTensor (H ⧸ J) ((TensorProduct.comm k V V₂').toLinearMap) ∘ₗ
    LinearMap.rTensor (H ⧸ J) (LinearMap.lTensor V f)

/-- `contractRightQ J f η ((v ⊗ v') ⊗ r) = f v' ⊗ [η v] r`. -/
@[simp] lemma contractRightQ_tmul (f : V' →ₗ[k] V₂') (η : V →ₗ[k] H) (v : V) (v' : V')
    (r : H ⧸ J) :
    contractRightQ J f η ((v ⊗ₜ[k] v') ⊗ₜ[k] r)
      = f v' ⊗ₜ[k] (Ideal.Quotient.mk J (η v) * r) := rfl

/-- The left contraction of a shuffle splits as a product. -/
lemma contractLeftQ_shuffleQuot (f : V →ₗ[k] V₂) (η : V' →ₗ[k] H)
    (x : V ⊗[k] (H ⧸ J)) (y : V' ⊗[k] (H ⧸ J)) :
    contractLeftQ J f η (shuffleQuot k H V V' J (x ⊗ₜ[k] y))
      = rmulQ V₂ J ((LinearMap.rTensor (H ⧸ J) f x) ⊗ₜ[k] (mulContractQ J η y)) := by
  induction x with
  | tmul v r =>
      induction y with
      | tmul v' s =>
          rw [shuffleQuot_tmul, contractLeftQ_tmul, LinearMap.rTensor_tmul, mulContractQ_tmul,
            rmulQ_tmul]
          ring_nf
      | add p q hp hq =>
          rw [TensorProduct.tmul_add, map_add, map_add, hp, hq, map_add, TensorProduct.tmul_add,
            map_add]
  | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, map_add, TensorProduct.add_tmul,
        map_add]

/-- The right contraction of a shuffle splits as a product. -/
lemma contractRightQ_shuffleQuot (f : V' →ₗ[k] V₂') (η : V →ₗ[k] H)
    (x : V ⊗[k] (H ⧸ J)) (y : V' ⊗[k] (H ⧸ J)) :
    contractRightQ J f η (shuffleQuot k H V V' J (x ⊗ₜ[k] y))
      = rmulQ V₂' J ((LinearMap.rTensor (H ⧸ J) f y) ⊗ₜ[k] (mulContractQ J η x)) := by
  induction x with
  | tmul v r =>
      induction y with
      | tmul v' s =>
          rw [shuffleQuot_tmul, contractRightQ_tmul, LinearMap.rTensor_tmul, mulContractQ_tmul,
            rmulQ_tmul]
          ring_nf
      | add p q hp hq =>
          rw [TensorProduct.tmul_add, map_add, map_add, hp, hq, map_add, TensorProduct.add_tmul,
            map_add]
  | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, hp, hq, map_add, TensorProduct.tmul_add,
        map_add]

/-- Reducing modulo `J` commutes with the multiplicative contraction. -/
lemma mulContractQ_lTensor_mk (η : V' →ₗ[k] H) (z : V' ⊗[k] H) :
    mulContractQ J η (LinearMap.lTensor V' (Ideal.Quotient.mkₐ k J).toLinearMap z)
      = Ideal.Quotient.mk J (mulContract η z) := by
  induction z with
  | tmul v h => rw [LinearMap.lTensor_tmul, mulContractQ_tmul, mulContract_tmul, map_mul]; rfl
  | add p q hp hq => simp only [map_add, hp, hq]

/-- An element of `(k v) ⊗ M` is a pure tensor `v ⊗ r`. -/
lemma exists_tmul_of_mem_range_span_singleton {M : Type u} [AddCommGroup M] [Module k M]
    (v : V) {y : V ⊗[k] M}
    (hy : y ∈ LinearMap.range (LinearMap.rTensor M (k ∙ v : Submodule k V).subtype)) :
    ∃ r : M, y = v ⊗ₜ[k] r := by
  obtain ⟨z, rfl⟩ := hy
  induction z with
  | tmul u r =>
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 u.2
      refine ⟨a • r, ?_⟩
      rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, ← ha, TensorProduct.smul_tmul]
  | add p q hp hq =>
      obtain ⟨r, hr⟩ := hp
      obtain ⟨s, hs⟩ := hq
      exact ⟨r + s, by rw [map_add, hr, hs, TensorProduct.tmul_add]⟩

/-- An ideal generated by two antipode-stable ideals is antipode-stable. -/
theorem antipode_mem_sup {I₁ I₂ : Ideal H} (h₁ : ∀ x ∈ I₁, antipode k x ∈ I₁)
    (h₂ : ∀ x ∈ I₂, antipode k x ∈ I₂) {x : H} (hx : x ∈ I₁ ⊔ I₂) : antipode k x ∈ I₁ ⊔ I₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  exact map_add (antipode k : H →ₗ[k] H) a b ▸
    Submodule.mem_sup.2 ⟨antipode k a, h₁ a ha, antipode k b, h₂ b hb, rfl⟩

variable [RightComodule k H V] [RightComodule k H V']

/-- `k v` is a subcomodule modulo `J` as soon as the coaction of `v` lands in `(k v) ⊗ H/J`. -/
lemma isSubcomoduleMod_span_singleton_iff (v : V) :
    IsSubcomoduleMod J (k ∙ v : Submodule k V) ↔
      LinearMap.lTensor V (Ideal.Quotient.mkₐ k J).toLinearMap (coact (R := k) (C := H) v)
        ∈ LinearMap.range (LinearMap.rTensor (H ⧸ J) (k ∙ v : Submodule k V).subtype) := by
  refine ⟨fun h => h v (Submodule.mem_span_singleton_self v), fun h u hu => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
  obtain ⟨z, hz⟩ := h
  refine ⟨a • z, ?_⟩
  rw [map_smul, hz, ← map_smul, ← map_smul]

/-- **The line `k w` is a subcomodule modulo `J` as soon as `k (w ⊗ w')` is.**  This is the
content of Takeuchi's Lemma 4.11(ii) in his proof of Lemma 4.10(ii); the hypothesis on `w'` says
that it spans a free rank-one direct summand of `V'`. -/
theorem isSubcomoduleMod_left_of_tmul {w : V} {w' : V'} (χ' : V' →ₗ[k] k) (hχ' : χ' w' = 1)
    (h : IsSubcomoduleMod J (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V'))) :
    IsSubcomoduleMod J (k ∙ w : Submodule k V) := by
  classical
  set η : V' →ₗ[k] H := (antipode k : H →ₗ[k] H) ∘ₗ coeffMap (H := H) χ' with hη
  obtain ⟨ρ, hρ⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) (w ⊗ₜ[k] w')
    (h _ (Submodule.mem_span_singleton_self _))
  have hcontract := congrArg (contractLeftQ J (k ∙ w : Submodule k V).mkQ η) hρ
  rw [lTensor_mk_coact_tmul, contractLeftQ_shuffleQuot, contractLeftQ_tmul,
    mulContractQ_lTensor_mk, mulContract_antipode_coeffMap χ' hχ', map_one, rmulQ_one] at hcontract
  have hzero : (k ∙ w : Submodule k V).mkQ w = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self w)
  rw [hzero, TensorProduct.zero_tmul] at hcontract
  rw [isSubcomoduleMod_span_singleton_iff, TensorProduct.range_rTensor_subtype_eq_ker]
  exact hcontract

/-- **The line `k w'` is a subcomodule modulo `J` as soon as `k (w ⊗ w')` is.** -/
theorem isSubcomoduleMod_right_of_tmul {w : V} {w' : V'} (χ : V →ₗ[k] k) (hχ : χ w = 1)
    (h : IsSubcomoduleMod J (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V'))) :
    IsSubcomoduleMod J (k ∙ w' : Submodule k V') := by
  classical
  set η : V →ₗ[k] H := (antipode k : H →ₗ[k] H) ∘ₗ coeffMap (H := H) χ with hη
  obtain ⟨ρ, hρ⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) (w ⊗ₜ[k] w')
    (h _ (Submodule.mem_span_singleton_self _))
  have hcontract := congrArg (contractRightQ J (k ∙ w' : Submodule k V').mkQ η) hρ
  rw [lTensor_mk_coact_tmul, contractRightQ_shuffleQuot, contractRightQ_tmul,
    mulContractQ_lTensor_mk, mulContract_antipode_coeffMap χ hχ, map_one, rmulQ_one] at hcontract
  have hzero : (k ∙ w' : Submodule k V').mkQ w' = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self w')
  rw [hzero, TensorProduct.zero_tmul] at hcontract
  rw [isSubcomoduleMod_span_singleton_iff, TensorProduct.range_rTensor_subtype_eq_ker]
  exact hcontract

/-! ### Takeuchi's Lemma 4.10(ii) for lines -/

/-- Takeuchi's ideal `N(V, W)` is stable under the antipode. -/
theorem antipode_mem_NIdeal (W : Submodule k V) {x : H} (hx : x ∈ NIdeal H W) :
    antipode k x ∈ NIdeal H W := by
  refine Submodule.span_induction (p := fun y _ => antipode k y ∈ NIdeal H W) ?_ ?_ ?_ ?_ hx
  · rintro c (hc | ⟨d, hd, rfl⟩)
    · exact Ideal.subset_span (Or.inr ⟨c, hc, rfl⟩)
    · rw [HopfAlgebra.antipode_antipode]
      exact Ideal.subset_span (Or.inl hd)
  · simp
  · intro a b _ _ ha hb
    rw [map_add]
    exact Ideal.add_mem _ ha hb
  · intro a b _ hb
    rw [smul_eq_mul, HopfAlgebra.antipode_mul_distrib]
    exact Ideal.mul_mem_left _ _ hb

/-- Being a subcomodule modulo `J` is inherited by larger ideals. -/
theorem IsSubcomoduleMod.mono {J J' : Ideal H} (hJ : J ≤ J') {W : Submodule k V}
    (h : IsSubcomoduleMod J W) : IsSubcomoduleMod J' W :=
  (isSubcomoduleMod_iff_coeffSet_subset J' W).2
    (fun _ hc => hJ ((isSubcomoduleMod_iff_coeffSet_subset J W).1 h hc))

/-- **The easy half of Takeuchi's Lemma 4.10(ii)**: a tensor product of lines which are
subcomodules modulo `J` is a subcomodule modulo `J`. -/
theorem isSubcomoduleMod_tmul {w : V} {w' : V'}
    (h : IsSubcomoduleMod J (k ∙ w : Submodule k V))
    (h' : IsSubcomoduleMod J (k ∙ w' : Submodule k V')) :
    IsSubcomoduleMod J (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V')) := by
  obtain ⟨r, hr⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) w
    ((isSubcomoduleMod_span_singleton_iff J w).1 h)
  obtain ⟨r', hr'⟩ := exists_tmul_of_mem_range_span_singleton (M := H ⧸ J) w'
    ((isSubcomoduleMod_span_singleton_iff J w').1 h')
  rw [isSubcomoduleMod_span_singleton_iff, lTensor_mk_coact_tmul, hr, hr', shuffleQuot_tmul]
  exact ⟨(⟨w ⊗ₜ[k] w', Submodule.mem_span_singleton_self _⟩ : (k ∙ (w ⊗ₜ[k] w') :
    Submodule k (V ⊗[k] V'))) ⊗ₜ[k] (r * r'), rfl⟩

/-- **Takeuchi's Lemma 4.10(ii) for lines** [Takeuchi1972]: for lines spanned by unimodular vectors,

```
N(V ⊗ V', k (w ⊗ w')) = N(V, k w) + N(V', k w').
```
-/
theorem nIdeal_tmul_line {w : V} {w' : V'} (χ : V →ₗ[k] k) (χ' : V' →ₗ[k] k)
    (hχ : χ w = 1) (hχ' : χ' w' = 1) :
    NIdeal H (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V'))
      = NIdeal H (k ∙ w : Submodule k V) ⊔ NIdeal H (k ∙ w' : Submodule k V') := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · refine (nIdeal_le_iff (fun _ hy => antipode_mem_sup
      (fun _ hz => antipode_mem_NIdeal (k ∙ w : Submodule k V) hz)
      (fun _ hz => antipode_mem_NIdeal (k ∙ w' : Submodule k V') hz) hy) _).2 ?_
    exact isSubcomoduleMod_tmul _
      ((isSubcomoduleMod_NIdeal (k ∙ w : Submodule k V)).mono le_sup_left)
      ((isSubcomoduleMod_NIdeal (k ∙ w' : Submodule k V')).mono le_sup_right)
  · exact (nIdeal_le_iff (fun _ hy => antipode_mem_NIdeal _ hy) _).2
      (isSubcomoduleMod_left_of_tmul _ χ' hχ'
        (isSubcomoduleMod_NIdeal (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V'))))
  · exact (nIdeal_le_iff (fun _ hy => antipode_mem_NIdeal _ hy) _).2
      (isSubcomoduleMod_right_of_tmul _ χ hχ
        (isSubcomoduleMod_NIdeal (k ∙ (w ⊗ₜ[k] w') : Submodule k (V ⊗[k] V'))))

/-- **The twisting step of Takeuchi's Lemma 4.15, in terms of `N(V, W)`.**  If a normal Hopf
ideal `I` is contained in `N(V, k v)` for a unimodular vector `v`, and if `v ⊗ u` is coinvariant
modulo `I` for a unimodular vector `u` of another comodule, then `I = K(I)⁺H`. -/
theorem eq_augIdeal_coinv_of_NIdeal_tmul {I : Ideal H} (hI : IsNormalHopfIdeal k I)
    {v : V} {u : V'} (χ : V →ₗ[k] k) (χ' : V' →ₗ[k] k) (hχ : χ v = 1) (hχ' : χ' u = 1)
    (hIv : I ≤ NIdeal H (k ∙ v : Submodule k V))
    (hcoinv : IsCoinvMod k I (v ⊗ₜ[k] u)) :
    I = augIdeal (coinvOfIdeal (k := k) I) := by
  refine eq_augIdeal_coinv_of_NIdeal_le hI hcoinv ?_
  rw [nIdeal_tmul_line χ χ' hχ hχ']
  exact hIv.trans le_sup_left

end TensorLine

end HopfAlgebra.Commutative
end
