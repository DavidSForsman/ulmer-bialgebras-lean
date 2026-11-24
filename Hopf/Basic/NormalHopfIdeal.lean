module

public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.HopfAdjointCoaction
public import Foundations.RingTheory.TensorSubmodule
public import Foundations.RingTheory.HopfAlgebra.Ideal
public import Hopf.Basic.IsSubHopfAlgebra

/-!
# Normal Hopf ideals and the sub-Hopf algebra they determine

This file formalises the syntactic part of §4 of M. Takeuchi, *A correspondence between Hopf ideals
and sub-Hopf algebras*, manuscripta math. **7** (1972), 251–270, for a commutative Hopf algebra `H`
over a commutative von Neumann regular ring `k` (for instance a field).

All the Sweedler calculus is carried out through the convolution identities established in
`Hopf/Basic/HopfAdjointCoaction.lean`.

## Main results

* `HopfAlgebra.IsHopfIdeal`: `I` is a Hopf ideal, i.e. `ε I = 0`, `Δ I ⊆ I ⊗ H + H ⊗ I` and
  `S I ⊆ I`;
* `HopfAlgebra.IsNormalHopfIdeal` (Takeuchi, Definition 4.1): a Hopf ideal `I` is *normal*
  if `∑ x₍₁₎ S(x₍₃₎) ⊗ x₍₂₎ ∈ H ⊗ I` for all `x ∈ I`;
* `HopfAlgebra.coinvLeft I` and `HopfAlgebra.coinvRight I` (Takeuchi, Lemma 4.4):
  the sets `Kₐ = {x | Δ x - x ⊗ 1 ∈ H ⊗ I}` and `K_b = {x | Δ x - 1 ⊗ x ∈ I ⊗ H}`, as
  subalgebras of `H`;
* `HopfAlgebra.coinvLeft_eq_coinvRight`: for a normal Hopf ideal the two coincide
  (Lemma 4.4); the common value `K(I)` is `HopfAlgebra.coinvOfIdeal I`;
* `HopfAlgebra.isSubHopfAlgebra_coinv`: `K(I)` is a sub-Hopf algebra of `H` (Lemma 4.4);
* `HopfAlgebra.coinv_augmentation_le` (first half of Lemma 4.7): `K(I)⁺ ⊆ I`.  (The second
  half, that `K(I)` is the greatest sub-Hopf algebra `K` of `H` with `K⁺ ⊆ I`, is not formalized
  here.)

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Section 4
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv LinearMap

section
open HopfAlgebra
namespace HopfAlgebra

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-! ### The quotient maps `id ⊗ π` and `π ⊗ id` -/

/-- `id ⊗ π : H ⊗ H → H ⊗ H/I`. -/
noncomputable def lTensorQuot (I : Ideal H) : H ⊗[k] H →ₐ[k] H ⊗[k] (H ⧸ I) :=
  Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)

/-- `π ⊗ id : H ⊗ H → H/I ⊗ H`. -/
noncomputable def rTensorQuot (I : Ideal H) : H ⊗[k] H →ₐ[k] (H ⧸ I) ⊗[k] H :=
  Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (AlgHom.id k H)

variable (I : Ideal H)

/-- `(id ⊗ π) (x ⊗ y) = x ⊗ [y]`. -/
@[simp] lemma lTensorQuot_tmul (x y : H) :
    lTensorQuot I (x ⊗ₜ[k] y) = x ⊗ₜ[k] (Ideal.Quotient.mk I y) := rfl

/-- `(π ⊗ id) (x ⊗ y) = [x] ⊗ y`. -/
@[simp] lemma rTensorQuot_tmul (x y : H) :
    rTensorQuot I (x ⊗ₜ[k] y) = (Ideal.Quotient.mk I x) ⊗ₜ[k] y := rfl

/-- The kernel of the quotient map `H → H/I` is `I` (as a `k`-submodule). -/
lemma ker_quotMkₐ : LinearMap.ker (Ideal.Quotient.mkₐ k I).toLinearMap = I.restrictScalars k := by
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]

/-- The underlying linear map of `lTensorQuot I` is `id ⊗ π`. -/
lemma lTensorQuot_toLinearMap :
    (lTensorQuot (k := k) I).toLinearMap
      = LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap := by
  ext x y; simp

/-- The underlying linear map of `rTensorQuot I` is `π ⊗ id`. -/
lemma rTensorQuot_toLinearMap :
    (rTensorQuot (k := k) I).toLinearMap
      = LinearMap.rTensor H (Ideal.Quotient.mkₐ k I).toLinearMap := by
  ext x y; simp

/-- If `(id ⊗ π)(t) = 0` then `t ∈ H ⊗ I`. -/
lemma mem_range_lTensor_ideal [IsAbsFlat k] {t : H ⊗[k] H} (h : lTensorQuot I t = 0) :
    t ∈ LinearMap.range (LinearMap.lTensor H (I.restrictScalars k).subtype) := by
  have := TensorProduct.mem_range_lTensor_ker (M := H) (Ideal.Quotient.mkₐ k I).toLinearMap
    (t := t) (by rw [← lTensorQuot_toLinearMap]; exact h)
  rwa [ker_quotMkₐ] at this

/-- If `(π ⊗ id)(t) = 0` then `t ∈ I ⊗ H`. -/
lemma mem_range_rTensor_ideal [IsAbsFlat k] {t : H ⊗[k] H} (h : rTensorQuot I t = 0) :
    t ∈ LinearMap.range (LinearMap.rTensor H (I.restrictScalars k).subtype) := by
  have := TensorProduct.mem_range_rTensor_ker (M := H) (Ideal.Quotient.mkₐ k I).toLinearMap
    (t := t) (by rw [← rTensorQuot_toLinearMap]; exact h)
  rwa [ker_quotMkₐ] at this

/-- `(id ⊗ π) ∘ τ = τ ∘ (π ⊗ id)`, where `τ` is the flip. -/
lemma lTensorQuot_comm (z : H ⊗[k] H) :
    lTensorQuot I ((TensorProduct.comm k H H) z)
      = (TensorProduct.comm k (H ⧸ I) H) (rTensorQuot I z) := by
  induction z with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- `(π ⊗ id) ∘ τ = τ ∘ (id ⊗ π)`, where `τ` is the flip. -/
lemma rTensorQuot_comm (z : H ⊗[k] H) :
    rTensorQuot I ((TensorProduct.comm k H H) z)
      = (TensorProduct.comm k H (H ⧸ I)) (lTensorQuot I z) := by
  induction z with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-! ### Hopf ideals and normal Hopf ideals -/

variable (k)

/-- A Hopf ideal, using Mathlib's coideal and antipode-stability definition. -/
abbrev IsHopfIdeal (I : Ideal H) : Prop := Ideal.IsHopfIdeal k I

namespace IsHopfIdeal

/-- Construct a Hopf ideal from its counit, comultiplication and antipode conditions. -/
theorem mk (I : Ideal H)
    (hc : ∀ x ∈ I, Coalgebra.counit (R := k) x = 0)
    (hd : ∀ x ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
      (Ideal.Quotient.mkₐ k I) (comul (R := k) x) = 0)
    (hs : ∀ x ∈ I, antipode k x ∈ I) : IsHopfIdeal k I := by
  exact (Ideal.isHopfIdeal_iff_quotient_conditions I).2 ⟨hc, hd, hs⟩

/-- The counit vanishes on a Hopf ideal. -/
theorem counit_eq_zero {I : Ideal H} (h : IsHopfIdeal k I) (x : H) (hx : x ∈ I) :
    Coalgebra.counit (R := k) x = 0 := by
  have := h
  exact Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hx

/-- The comultiplication of an element of a Hopf ideal vanishes after both quotient maps. -/
theorem comul_mem {I : Ideal H} (h : IsHopfIdeal k I) (x : H) (hx : x ∈ I) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
      (comul (R := k) x) = 0 := by
  have := h
  exact Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars k) hx

/-- The antipode preserves a Hopf ideal. -/
theorem antipode_mem {I : Ideal H} (h : IsHopfIdeal k I) (x : H) (hx : x ∈ I) :
    antipode k x ∈ I := by
  have := h
  exact Ideal.IsHopfIdeal.antipode_mem hx

end IsHopfIdeal

/-- **Takeuchi's Definition 4.1**: a Hopf ideal `I` of a commutative Hopf algebra is *normal* if
`∑ x₍₁₎ S(x₍₃₎) ⊗ x₍₂₎ ∈ H ⊗ I` for every `x ∈ I`; geometrically, the corresponding closed
subgroup scheme of `Spec H` is normal. -/
structure IsNormalHopfIdeal (I : Ideal H) : Prop extends IsHopfIdeal k I where
  ad_mem : ∀ x ∈ I, lTensorQuot I (adAlgHom k H x) = 0

variable {k}

/-! ### The subalgebras `Kₐ` and `K_b` -/

/-- `Kₐ = {x ∈ H | Δ x - x ⊗ 1 ∈ H ⊗ I}`, a subalgebra of `H`. -/
noncomputable def coinvLeft : Subalgebra k H where
  carrier := {x | lTensorQuot I (comul (R := k) x) = x ⊗ₜ[k] 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Bialgebra.comul_mul, map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Bialgebra.comul_one, map_one]
    rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, map_add, ha, hb, TensorProduct.add_tmul]
  zero_mem' := by simp
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one, map_smul,
      Bialgebra.comul_one, map_one]
    rfl

/-- `K_b = {x ∈ H | Δ x - 1 ⊗ x ∈ I ⊗ H}`, a subalgebra of `H`. -/
noncomputable def coinvRight : Subalgebra k H where
  carrier := {x | rTensorQuot I (comul (R := k) x) = 1 ⊗ₜ[k] x}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [Bialgebra.comul_mul, map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Bialgebra.comul_one, map_one]
    rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, map_add, ha, hb, TensorProduct.tmul_add]
  zero_mem' := by simp
  algebraMap_mem' := by
    intro c
    simp only [Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one, map_smul,
      Bialgebra.comul_one, map_one, TensorProduct.tmul_smul]
    rfl

/-- `x ∈ Kₐ` iff `(id ⊗ π) (Δ x) = x ⊗ 1`. -/
@[simp] lemma mem_coinvLeft {x : H} :
    x ∈ (coinvLeft I : Subalgebra k H) ↔ lTensorQuot I (comul (R := k) x) = x ⊗ₜ[k] 1 := Iff.rfl

/-- `x ∈ K_b` iff `(π ⊗ id) (Δ x) = 1 ⊗ x`. -/
@[simp] lemma mem_coinvRight {x : H} :
    x ∈ (coinvRight I : Subalgebra k H) ↔ rTensorQuot I (comul (R := k) x) = 1 ⊗ₜ[k] x := Iff.rfl

/-! ### The two auxiliary maps used in Lemma 4.4 -/

variable (k H)

/-- `a ⊗ b ↦ (a ⊗ 1) · ad*(b)`, where `ad* = (S ⊗ id) ∘ ad`. -/
noncomputable def GstarMap : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  TensorProduct.lift ((LinearMap.mul k (H ⊗[k] H)).compl₁₂
    ((TensorProduct.mk k H H).flip 1) (adStarAlgHom k H).toLinearMap)

/-- `a ⊗ b ↦ (τ ∘ ad)(a) · (1 ⊗ b)`. -/
noncomputable def GbarMap : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  TensorProduct.lift ((LinearMap.mul k (H ⊗[k] H)).compl₁₂
    (adBarAlgHom k H).toLinearMap (TensorProduct.mk k H H 1))

variable {k H}

/-- `GstarMap (a ⊗ b) = (a ⊗ 1) · ad*(b)`. -/
@[simp] lemma gstarMap_tmul (a b : H) :
    GstarMap k H (a ⊗ₜ[k] b) = (a ⊗ₜ[k] (1 : H)) * adStarAlgHom k H b := rfl

/-- `GbarMap (a ⊗ b) = (τ ∘ ad)(a) · (1 ⊗ b)`. -/
@[simp] lemma gbarMap_tmul (a b : H) :
    GbarMap k H (a ⊗ₜ[k] b) = (adBarAlgHom k H a) * ((1 : H) ⊗ₜ[k] b) := rfl

/-- `GstarMap (Δ x) = τ (Δ x)`, where `τ` is the flip. -/
lemma gstarMap_comul (x : H) :
    GstarMap k H (comul (R := k) x) = (TensorProduct.comm k H H) (comul (R := k) x) := by
  have h := congrArg (fun t : WithConv (H →ₗ[k] H ⊗[k] H) => t.ofConv x)
    (convL_convMul_adStar (k := k) (H := H))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
  rw [← h, conv_apply _ _ x (ℛ k x), ← (ℛ k x).eq, map_sum]
  simp

/-- `GbarMap (Δ x) = τ (Δ x)`, where `τ` is the flip. -/
lemma gbarMap_comul (x : H) :
    GbarMap k H (comul (R := k) x) = (TensorProduct.comm k H H) (comul (R := k) x) := by
  have h := congrArg (fun t : WithConv (H →ₗ[k] H ⊗[k] H) => t.ofConv x)
    (adBar_convMul_convR (k := k) (H := H))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h
  rw [← h, conv_apply _ _ x (ℛ k x), ← (ℛ k x).eq, map_sum]
  simp

/-- `ad*` maps `I` into `H ⊗ I` when `I` is normal. -/
lemma lTensorQuot_adStar (hI : IsNormalHopfIdeal k I) {u : H} (hu : u ∈ I) :
    lTensorQuot I (adStarAlgHom k H u) = 0 := by
  have h := hI.ad_mem u hu
  have : lTensorQuot I (adStarAlgHom k H u)
      = Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H)
          (AlgHom.id k (H ⧸ I)) (lTensorQuot I (adAlgHom k H u)) := by
    set z := adAlgHom k H u
    change lTensorQuot I (Algebra.TensorProduct.map _ _ z) = _
    induction z with
    | tmul a b => simp
    | add p q hp hq => simp only [map_add, hp, hq]
  rw [this, h, map_zero]

/-- `τ ∘ ad` maps `I` into `I ⊗ H` when `I` is normal. -/
lemma rTensorQuot_adBar (hI : IsNormalHopfIdeal k I) {u : H} (hu : u ∈ I) :
    rTensorQuot I (adBarAlgHom k H u) = 0 := by
  have h := hI.ad_mem u hu
  rw [adBarAlgHom_apply, show (Algebra.TensorProduct.comm k H H) (adAlgHom k H u)
      = (TensorProduct.comm k H H) (adAlgHom k H u) from rfl, rTensorQuot_comm, h, map_zero]

/-- Applying `Gstar` to an element of `H ⊗ I` lands again in `H ⊗ I`. -/
lemma lTensorQuot_GstarMap (hI : IsNormalHopfIdeal k I)
    (s : H ⊗[k] (I.restrictScalars k)) :
    lTensorQuot I (GstarMap k H (LinearMap.lTensor H (I.restrictScalars k).subtype s)) = 0 := by
  induction s with
  | tmul a u =>
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, gstarMap_tmul, map_mul]
    rw [lTensorQuot_adStar I hI u.2, mul_zero]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]

/-- Applying `Gbar` to an element of `I ⊗ H` lands again in `I ⊗ H`. -/
lemma rTensorQuot_GbarMap (hI : IsNormalHopfIdeal k I)
    (s : (I.restrictScalars k) ⊗[k] H) :
    rTensorQuot I (GbarMap k H (LinearMap.rTensor H (I.restrictScalars k).subtype s)) = 0 := by
  induction s with
  | tmul u a =>
    simp only [LinearMap.rTensor_tmul, Submodule.subtype_apply, gbarMap_tmul, map_mul]
    rw [rTensorQuot_adBar I hI u.2, zero_mul]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]

/-! ### Lemma 4.4: `Kₐ = K_b` -/

/-- **Takeuchi, Lemma 4.4** (first half): for a normal Hopf ideal, `Kₐ ⊆ K_b`. -/
theorem coinvLeft_le_coinvRight [IsAbsFlat k] (hI : IsNormalHopfIdeal k I) :
    coinvLeft I ≤ (coinvRight I : Subalgebra k H) := by
  intro x hx
  rw [mem_coinvLeft] at hx
  have h1 : lTensorQuot I (comul (R := k) x - x ⊗ₜ[k] 1) = 0 := by
    rw [map_sub, hx, lTensorQuot_tmul, map_one, sub_self]
  obtain ⟨s, hs⟩ := mem_range_lTensor_ideal I h1
  have h2 : lTensorQuot I (GstarMap k H (comul (R := k) x - x ⊗ₜ[k] 1)) = 0 := by
    rw [← hs]; exact lTensorQuot_GstarMap I hI s
  rw [map_sub, gstarMap_comul, gstarMap_tmul, map_one, mul_one, map_sub, sub_eq_zero,
    lTensorQuot_comm] at h2
  have h3 : (TensorProduct.comm k (H ⧸ I) H) (rTensorQuot I (comul (R := k) x))
      = (TensorProduct.comm k (H ⧸ I) H) (1 ⊗ₜ[k] x) := by
    rw [h2]; simp
  rw [mem_coinvRight]
  exact (TensorProduct.comm k (H ⧸ I) H).injective h3

/-- **Takeuchi, Lemma 4.4** (second half): for a normal Hopf ideal, `K_b ⊆ Kₐ`. -/
theorem coinvRight_le_coinvLeft [IsAbsFlat k] (hI : IsNormalHopfIdeal k I) :
    coinvRight I ≤ (coinvLeft I : Subalgebra k H) := by
  intro x hx
  rw [mem_coinvRight] at hx
  have h1 : rTensorQuot I (comul (R := k) x - 1 ⊗ₜ[k] x) = 0 := by
    rw [map_sub, hx, rTensorQuot_tmul, map_one, sub_self]
  obtain ⟨s, hs⟩ := mem_range_rTensor_ideal I h1
  have h2 : rTensorQuot I (GbarMap k H (comul (R := k) x - 1 ⊗ₜ[k] x)) = 0 := by
    rw [← hs]; exact rTensorQuot_GbarMap I hI s
  rw [map_sub, gbarMap_comul, gbarMap_tmul, map_one, one_mul, map_sub, sub_eq_zero,
    rTensorQuot_comm] at h2
  have h3 : (TensorProduct.comm k H (H ⧸ I)) (lTensorQuot I (comul (R := k) x))
      = (TensorProduct.comm k H (H ⧸ I)) (x ⊗ₜ[k] 1) := by
    rw [h2]; simp
  rw [mem_coinvLeft]
  exact (TensorProduct.comm k H (H ⧸ I)).injective h3

/-- **Takeuchi, Lemma 4.4**: for a normal Hopf ideal `I` the two subalgebras coincide. -/
theorem coinvLeft_eq_coinvRight [IsAbsFlat k] (hI : IsNormalHopfIdeal k I) :
    (coinvLeft I : Subalgebra k H) = coinvRight I :=
  le_antisymm (coinvLeft_le_coinvRight I hI) (coinvRight_le_coinvLeft I hI)

/-- **Takeuchi, Definition 4.5**: the sub-Hopf algebra `K(I)` attached to a normal Hopf ideal. -/
noncomputable def coinvOfIdeal : Subalgebra k H := coinvLeft I

/-! ### `K(I)` is a sub-Hopf algebra (Lemma 4.4, continued) -/

/-- `a ⊗ q ↦ ∑ a₍₁₎ ⊗ (a₍₂₎ ⊗ q)`. -/
noncomputable def PsiMapL : H ⊗[k] (H ⧸ I) →ₗ[k] H ⊗[k] (H ⊗[k] (H ⧸ I)) :=
  (TensorProduct.assoc k H H (H ⧸ I)).toLinearMap ∘ₗ
    (LinearMap.rTensor (H ⧸ I) (comul (R := k) (A := H)))

/-- `q ⊗ a ↦ ∑ (q ⊗ a₍₁₎) ⊗ a₍₂₎`. -/
noncomputable def PsiMapR : (H ⧸ I) ⊗[k] H →ₗ[k] ((H ⧸ I) ⊗[k] H) ⊗[k] H :=
  (TensorProduct.assoc k (H ⧸ I) H H).symm.toLinearMap ∘ₗ
    (LinearMap.lTensor (H ⧸ I) (comul (R := k) (A := H)))

/-- On a Sweedler representation of `a`: `PsiMapL (a ⊗ q) = ∑ a₍₁₎ ⊗ (a₍₂₎ ⊗ q)`. -/
lemma psiMapL_tmul {ι : Type*} (a : H) (q : H ⧸ I) (r : Coalgebra.Repr k a ι) :
    PsiMapL I (a ⊗ₜ[k] q) = ∑ i ∈ r.index, r.left i ⊗ₜ[k] (r.right i ⊗ₜ[k] q) := by
  simp [PsiMapL, ← r.eq, TensorProduct.sum_tmul, map_sum]

/-- On a Sweedler representation of `a`: `PsiMapR (q ⊗ a) = ∑ (q ⊗ a₍₁₎) ⊗ a₍₂₎`. -/
lemma psiMapR_tmul {ι : Type*} (a : H) (q : H ⧸ I) (r : Coalgebra.Repr k a ι) :
    PsiMapR I (q ⊗ₜ[k] a) = ∑ i ∈ r.index, (q ⊗ₜ[k] r.left i) ⊗ₜ[k] r.right i := by
  simp [PsiMapR, ← r.eq, TensorProduct.tmul_sum, map_sum]

/-- **Takeuchi, Lemma 4.4**: `Δ(Kₐ) ⊆ H ⊗ Kₐ`. -/
theorem comul_mem_lTensor_coinvLeft [IsAbsFlat k] {x : H}
    (hx : x ∈ (coinvLeft I : Subalgebra k H)) :
    comul (R := k) x ∈ LinearMap.range
      (LinearMap.lTensor H (coinvLeft I : Subalgebra k H).toSubmodule.subtype) := by
  classical
  rw [mem_coinvLeft] at hx
  set r := ℛ k x with hr
  set a₁ : (i : H × H) → Coalgebra.Repr k (r.left i) (H × H) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : H × H) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i) with ha2
  set θ : H →ₗ[k] H ⊗[k] (H ⧸ I) :=
    (lTensorQuot (k := k) I).toLinearMap ∘ₗ (comul (R := k) (A := H)) -
      ((TensorProduct.mk k H (H ⧸ I)).flip 1) with hθ
  have hker : LinearMap.ker θ = (coinvLeft I : Subalgebra k H).toSubmodule := by
    ext y
    simp only [LinearMap.mem_ker, hθ, LinearMap.sub_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply, sub_eq_zero]
    exact (mem_coinvLeft I).symm
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  apply_fun (LinearMap.lTensor H (LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap)) at key
  simp only [map_sum, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply,
    Ideal.Quotient.mkₐ_eq_mk] at key
  have hA : LinearMap.lTensor H θ (comul (R := k) x) = 0 := by
    have e1 : LinearMap.lTensor H θ (comul (R := k) x)
        = ∑ i ∈ r.index, r.left i ⊗ₜ[k] θ (r.right i) := by
      rw [← r.eq, map_sum]; simp
    have e2 : ∀ i ∈ r.index, θ (r.right i)
        = (∑ j ∈ (a₂ i).index, (a₂ i).left j ⊗ₜ[k] (Ideal.Quotient.mk I ((a₂ i).right j)))
          - r.right i ⊗ₜ[k] 1 := by
      intro i _
      simp only [hθ, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearMap.flip_apply, TensorProduct.mk_apply]
      congr 1
      rw [← (a₂ i).eq, map_sum]
      simp
    rw [e1, Finset.sum_congr rfl (fun i hi => by rw [e2 i hi])]
    simp only [TensorProduct.tmul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have hL : ∑ i ∈ r.index, r.left i ⊗ₜ[k]
        (∑ j ∈ (a₂ i).index, (a₂ i).left j ⊗ₜ[k] (Ideal.Quotient.mk I ((a₂ i).right j)))
        = PsiMapL I (lTensorQuot (k := k) I (comul (R := k) x)) := by
      rw [← r.eq, map_sum]
      simp only [lTensorQuot_tmul, map_sum, TensorProduct.tmul_sum]
      rw [← key]
      exact Finset.sum_congr rfl fun i _ => (psiMapL_tmul I _ _ (a₁ i)).symm
    have hR : ∑ i ∈ r.index, r.left i ⊗ₜ[k] (r.right i ⊗ₜ[k] (1 : H ⧸ I))
        = PsiMapL I (x ⊗ₜ[k] 1) := (psiMapL_tmul I x 1 r).symm
    rw [hL, hR, hx]
  have := TensorProduct.mem_range_lTensor_ker θ hA
  rwa [hker] at this

/-- **Takeuchi, Lemma 4.4**: `Δ(K_b) ⊆ K_b ⊗ H`. -/
theorem comul_mem_rTensor_coinvRight [IsAbsFlat k] {x : H}
    (hx : x ∈ (coinvRight I : Subalgebra k H)) :
    comul (R := k) x ∈ LinearMap.range
      (LinearMap.rTensor H (coinvRight I : Subalgebra k H).toSubmodule.subtype) := by
  classical
  rw [mem_coinvRight] at hx
  set r := ℛ k x with hr
  set a₁ : (i : H × H) → Coalgebra.Repr k (r.left i) (H × H) := fun i => ℛ k (r.left i) with ha1
  set a₂ : (i : H × H) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i) with ha2
  set θ : H →ₗ[k] (H ⧸ I) ⊗[k] H :=
    (rTensorQuot (k := k) I).toLinearMap ∘ₗ (comul (R := k) (A := H)) -
      (TensorProduct.mk k (H ⧸ I) H) 1 with hθ
  have hker : LinearMap.ker θ = (coinvRight I : Subalgebra k H).toSubmodule := by
    ext y
    simp only [LinearMap.mem_ker, hθ, LinearMap.sub_apply, LinearMap.coe_comp,
      Function.comp_apply, TensorProduct.mk_apply, sub_eq_zero]
    exact (mem_coinvRight I).symm
  have key := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  apply_fun ((LinearMap.rTensor H (LinearMap.rTensor H (Ideal.Quotient.mkₐ k I).toLinearMap)) ∘ₗ
    (TensorProduct.assoc k H H H).symm.toLinearMap) at key
  simp only [LinearMap.coe_comp, Function.comp_apply, map_sum, LinearEquiv.coe_coe,
    TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
    Ideal.Quotient.mkₐ_eq_mk] at key
  have hA : LinearMap.rTensor H θ (comul (R := k) x) = 0 := by
    have e1 : LinearMap.rTensor H θ (comul (R := k) x)
        = ∑ i ∈ r.index, θ (r.left i) ⊗ₜ[k] r.right i := by
      rw [← r.eq, map_sum]; simp
    have e2 : ∀ i ∈ r.index, θ (r.left i)
        = (∑ j ∈ (a₁ i).index, (Ideal.Quotient.mk I ((a₁ i).left j)) ⊗ₜ[k] (a₁ i).right j)
          - 1 ⊗ₜ[k] r.left i := by
      intro i _
      simp only [hθ, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
        TensorProduct.mk_apply]
      congr 1
      rw [← (a₁ i).eq, map_sum]
      simp
    rw [e1, Finset.sum_congr rfl (fun i hi => by rw [e2 i hi])]
    simp only [TensorProduct.sub_tmul]
    refine Eq.trans (Finset.sum_sub_distrib (G := ((H ⧸ I) ⊗[k] H) ⊗[k] H) _ _) ?_
    rw [sub_eq_zero]
    have hL : ∑ i ∈ r.index,
        (∑ j ∈ (a₁ i).index, (Ideal.Quotient.mk I ((a₁ i).left j)) ⊗ₜ[k] (a₁ i).right j)
          ⊗ₜ[k] r.right i
        = PsiMapR I (rTensorQuot (k := k) I (comul (R := k) x)) := by
      rw [← r.eq, map_sum]
      simp only [rTensorQuot_tmul, map_sum, TensorProduct.sum_tmul]
      rw [key]
      exact Finset.sum_congr rfl fun i _ => (psiMapR_tmul I _ _ (a₂ i)).symm
    have hR : ∑ i ∈ r.index, ((1 : H ⧸ I) ⊗ₜ[k] r.left i) ⊗ₜ[k] r.right i
        = PsiMapR I (1 ⊗ₜ[k] x) := (psiMapR_tmul I x 1 r).symm
    rw [hL, hR, hx]
  have := TensorProduct.mem_range_rTensor_ker θ hA
  rwa [hker] at this

/-- **Takeuchi, Lemma 4.4**: for a normal Hopf ideal, `K(I)` is stable under the antipode. -/
theorem antipode_mem_coinvLeft [IsAbsFlat k] (hI : IsNormalHopfIdeal k I) {x : H}
    (hx : x ∈ (coinvLeft I : Subalgebra k H)) : antipode k x ∈ (coinvLeft I : Subalgebra k H) := by
  rw [mem_coinvLeft] at hx
  -- `Δ x - x ⊗ 1` lies in `H ⊗ I`, the kernel of `id ⊗ π`
  have hker : lTensorQuot (k := k) I (comul (R := k) x - x ⊗ₜ[k] 1) = 0 := by
    rw [map_sub, hx, lTensorQuot_tmul, map_one, sub_self]
  obtain ⟨s, hs⟩ := mem_range_lTensor_ideal I hker
  -- `S ⊗ S` maps `H ⊗ I` into the kernel of `id ⊗ π`, since `S(I) ⊆ I`
  set SS : H ⊗[k] H →ₐ[k] H ⊗[k] H :=
    Algebra.TensorProduct.map (HopfAlgebra.antipodeAlgHom k H)
      (HopfAlgebra.antipodeAlgHom k H) with hSS
  have hkey : ∀ t : H ⊗[k] (I.restrictScalars k),
      lTensorQuot (k := k) I
        (SS (LinearMap.lTensor H (I.restrictScalars k).subtype t)) = 0 := by
    intro t
    induction t with
    | tmul a u =>
      have : antipode k (u : H) ∈ I := IsHopfIdeal.antipode_mem k hI.toIsHopfIdeal _ u.2
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply, hSS,
        Algebra.TensorProduct.map_tmul, HopfAlgebra.antipodeAlgHom_apply, lTensorQuot_tmul]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this, TensorProduct.tmul_zero]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  -- so `(id ⊗ π) ((S ⊗ S) (Δ x)) = S x ⊗ 1`
  have hSS_ker : lTensorQuot (k := k) I (SS (comul (R := k) x - x ⊗ₜ[k] 1)) = 0 := by
    rw [← hs]; exact hkey s
  have hSS_comul : lTensorQuot (k := k) I (SS (comul (R := k) x)) = antipode k x ⊗ₜ[k] 1 := by
    rw [map_sub, map_sub, sub_eq_zero] at hSS_ker
    rw [hSS_ker]
    simp [hSS]
  -- `Δ (S x)` is the flip of `(S ⊗ S) (Δ x)`, so `(π ⊗ id) (Δ (S x)) = 1 ⊗ S x`
  have hcomul_S :
      comul (R := k) (antipode k x) = (TensorProduct.comm k H H) (SS (comul (R := k) x)) := by
    rw [comul_antipode_apply x (ℛ k x)]
    rw [← (ℛ k x).eq]
    simp [hSS]
  have hright : rTensorQuot (k := k) I (comul (R := k) (antipode k x)) = 1 ⊗ₜ[k] antipode k x := by
    rw [hcomul_S, rTensorQuot_comm, hSS_comul]
    simp
  -- the right coinvariants of a normal Hopf ideal are left coinvariants
  exact (coinvRight_le_coinvLeft I hI) ((mem_coinvRight I).2 hright)

/-- **Takeuchi, Lemma 4.4**: for a normal Hopf ideal `I`, `K(I)` is a sub-Hopf algebra of `H`. -/
theorem isSubHopfAlgebra_coinv [IsAbsFlat k] (hI : IsNormalHopfIdeal k I) :
    IsSubHopfAlgebra k (coinvOfIdeal I : Subalgebra k H) where
  comul_mem x hx := by
    have h1 : comul (R := k) x ∈ LinearMap.range
        (LinearMap.lTensor H (coinvOfIdeal I : Subalgebra k H).toSubmodule.subtype) :=
      comul_mem_lTensor_coinvLeft I hx
    have hx' : x ∈ (coinvRight I : Subalgebra k H) := by
      rw [← coinvLeft_eq_coinvRight I hI]; exact hx
    have h2 : comul (R := k) x ∈ LinearMap.range
        (LinearMap.rTensor H (coinvOfIdeal I : Subalgebra k H).toSubmodule.subtype) := by
      have := comul_mem_rTensor_coinvRight I hx'
      rwa [coinvOfIdeal, coinvLeft_eq_coinvRight I hI]
    have := (TensorProduct.inf_range_rTensor_lTensor (M := H) (N := H)
      (coinvOfIdeal I : Subalgebra k H).toSubmodule (coinvOfIdeal I : Subalgebra k H).toSubmodule)
    rw [← this]
    exact ⟨h2, h1⟩
  antipode_mem x hx := antipode_mem_coinvLeft I hI hx

/-! ### Lemma 4.7: `K(I)` is the largest sub-Hopf algebra with `K⁺ ⊆ I` -/

/-- **Takeuchi, Lemma 4.7** (first half): if `x ∈ K(I)` and `ε x = 0`, then `x ∈ I`;
that is, `K(I)⁺ ⊆ I`. -/
theorem coinv_augmentation_le {x : H} (hx : x ∈ (coinvLeft I : Subalgebra k H))
    (hcx : Coalgebra.counit (R := k) x = 0) : x ∈ I := by
  rw [mem_coinvLeft] at hx
  have key : ∀ z : H ⊗[k] H,
      (TensorProduct.lid k (H ⧸ I))
          (LinearMap.rTensor (H ⧸ I) (Coalgebra.counit (R := k) (A := H)) (lTensorQuot I z))
        = (Ideal.Quotient.mkₐ k I)
            ((TensorProduct.lid k H) (LinearMap.rTensor H
              (Coalgebra.counit (R := k) (A := H)) z)) := by
    intro z
    induction z with
    | tmul a b => simp
    | add p q hp hq => simp only [map_add, hp, hq]
  have h := key (comul (R := k) x)
  rw [hx] at h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hcx, zero_smul,
    Coalgebra.rTensor_counit_comul, one_smul, Ideal.Quotient.mkₐ_eq_mk] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm

end HopfAlgebra
end
