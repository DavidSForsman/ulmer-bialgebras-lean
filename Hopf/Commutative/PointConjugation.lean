module

public import Hopf.Basic.ComoduleTransl
public import Hopf.Basic.NormalHopfIdeal
public import Hopf.Commutative.RelInvGroupLike

/-!
# Translation by a point, and conjugation of a character

Let `H` be a commutative Hopf algebra over a field `k` and let `u : H →ₐ[k] k` be a *point* of
`H` (a `k`-point of the affine group scheme `Spec H`).  Translation by `u`,

`T_u (x) = ∑ x₍₁₎ u (x₍₂₎)`,

is the operator `Coalgebra.Comodule.transl u` of `Hopf/Basic/ComoduleTransl.lean` applied
to the regular comodule `H`; geometrically it is right translation of functions, `(T_u f)(y) =
f (y u)`.  Conjugation by `u`,

`C_u (x) = ∑ u (S x₍₁₎) x₍₂₎ u (x₍₃₎)`,

corresponds to `(C_u f)(y) = f (u y u⁻¹)`.

The two are related by the identity

`Δ ∘ T_u = (T_u ⊗ C_u) ∘ Δ`,

which is the algebraic form of `f (y n u) = f ((y u) (u⁻¹ n u))`.  Together with the normality of
a Hopf ideal `I` — which is exactly the statement that `C_u` preserves `I` — it shows that the
translate by a point of a vector which is relatively invariant modulo `I` is again relatively
invariant, with the conjugated character.  This is the step of Takeuchi's Lemma 4.15 which
produces the weight decomposition of the space of translates of a group-like element.

All the identities are proved in the convolution algebra of linear maps from `H` to an algebra:
writing `w` for the composite of `u` with the unit, `T_u = id ⋆ w`, `C_u = (w ∘ S) ⋆ id ⋆ w`,
and the key identity reads
`Δ ⋆ w = (F ⋆ w) ⋆ ((w ∘ S) ⋆ G ⋆ w)` for the two inclusions `F, G : H → H ⊗ H`, which follows
from `F ⋆ G = Δ` and `w ⋆ (w ∘ S) = 1`.

## Main definitions and results

* `HopfAlgebra.Commutative.translPoint`, `HopfAlgebra.Commutative.conjPoint`: the operators `T_u`
  and `C_u`;
* `HopfAlgebra.Commutative.comul_comp_translPoint`: the identity `Δ ∘ T_u = (T_u ⊗ C_u) ∘ Δ`;
* `HopfAlgebra.Commutative.conjPoint_mem`: a normal Hopf ideal is stable under `C_u`;
* `HopfAlgebra.Commutative.isRelInvMod_translPoint`: `T_u v` is relatively invariant modulo a normal
  Hopf ideal `I` with character `C_u g` as soon as `v` is with character `g`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.15
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra WithConv

section
open Coalgebra.Comodule HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- The translation operator `T_u (x) = ∑ x₍₁₎ u (x₍₂₎)` by a point `u` of `H`. -/
noncomputable def translPoint (u : H →ₐ[k] k) : H →ₗ[k] H :=
  Coalgebra.Comodule.transl (R := k) (C := H) (M := H) u.toLinearMap

/-- Conjugation by a point, `C_u (x) = ∑ u (S x₍₁₎) x₍₂₎ u (x₍₃₎)`, obtained by contracting the
first leg of the adjoint coaction `x ↦ ∑ S(x₍₁₎) x₍₃₎ ⊗ x₍₂₎` against `u`. -/
noncomputable def conjPoint (u : H →ₐ[k] k) : H →ₗ[k] H :=
  (TensorProduct.lid k H).toLinearMap ∘ₗ LinearMap.rTensor H u.toLinearMap ∘ₗ
    (adStarAlgHom k H).toLinearMap

section Conv

/-- A point of `H`, viewed as a linear map into an algebra `A`: `x ↦ u x • 1`. -/
noncomputable def charLin (u : H →ₐ[k] k) (A : Type u) [Semiring A] [Algebra k A] : H →ₗ[k] A :=
  ((Algebra.ofId k A).comp u).toLinearMap
/-- `charLin u A x = algebraMap k A (u x)`. -/
@[simp] lemma charLin_apply (u : H →ₐ[k] k) (A : Type u) [Semiring A] [Algebra k A] (x : H) :
    charLin u A x = algebraMap k A (u x) := rfl

/-- Post-composing `charLin` with an algebra map does not change it. -/
lemma comp_charLin {A B : Type u} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
    (h : A →ₐ[k] B) (u : H →ₐ[k] k) :
    h.toLinearMap ∘ₗ charLin u A = charLin u B := by
  ext x
  simp [charLin]

/-- Post-composing the convolution unit with an algebra map gives the convolution unit. -/
lemma comp_convOne {A B : Type u} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
    (h : A →ₐ[k] B) :
    h.toLinearMap ∘ₗ (1 : WithConv (H →ₗ[k] A)).ofConv
      = (1 : WithConv (H →ₗ[k] B)).ofConv := by
  rw [LinearMap.convOne_def, LinearMap.convOne_def]
  ext x
  simp

/-- Post-composition with an algebra map distributes over the convolution product. -/
lemma toConv_algHom_comp' {A B : Type u} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]
    (F : A →ₐ[k] B) (f g : WithConv (H →ₗ[k] A)) :
    toConv (F.toLinearMap ∘ₗ (f * g).ofConv)
      = toConv (F.toLinearMap ∘ₗ f.ofConv) * toConv (F.toLinearMap ∘ₗ g.ofConv) := by
  rw [LinearMap.algHom_comp_convMul_distrib F f g, toConv_ofConv]

/-- `w ⋆ (w ∘ S) = 1`: a point is convolution invertible, with inverse `u ∘ S`. -/
lemma charLin_convMul_charLin_antipode (u : H →ₐ[k] k) (A : Type u) [Semiring A] [Algebra k A] :
    toConv (charLin u A) * toConv (charLin u A ∘ₗ (antipode k : H →ₗ[k] H)) = 1 := by
  have key := LinearMap.algHom_comp_convMul_distrib ((Algebra.ofId k A).comp u)
    (toConv (LinearMap.id : H →ₗ[k] H)) (toConv (antipode k : H →ₗ[k] H))
  rw [LinearMap.id_mul_antipode (R := k) (C := H), comp_convOne ((Algebra.ofId k A).comp u)] at key
  simp only [LinearMap.comp_id] at key
  exact (ofConv_injective key).symm

/-- The linear map underlying `includeLeft : H → H ⊗ H` is `convL k H`. -/
lemma includeLeft_toLinearMap :
    (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H).toLinearMap
      = (convL k H).ofConv := rfl

/-- The linear map underlying `includeRight : H → H ⊗ H` is `convR k H`. -/
lemma includeRight_toLinearMap :
    (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toLinearMap
      = (convR k H).ofConv := rfl

/-- Multiplication in `H ⊗ H` after `includeLeft ⊗ includeRight` is the identity of `H ⊗ H`. -/
lemma mul_comp_map_incl :
    LinearMap.mul' k (H ⊗[k] H) ∘ₗ TensorProduct.map
        (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H).toLinearMap
        (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toLinearMap
      = LinearMap.id := by
  ext a b
  simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- Convolution of maps landing in the two legs computes the tensor product of the maps. -/
lemma toConv_map_comp_comul (p q : H →ₗ[k] H) :
    toConv (TensorProduct.map p q ∘ₗ (comul (R := k) (A := H)))
      = toConv ((Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H).toLinearMap ∘ₗ p)
        * toConv ((Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toLinearMap ∘ₗ q) := by
  rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv]
  congr 1
  rw [TensorProduct.map_comp]
  simp only [← LinearMap.comp_assoc]
  rw [mul_comp_map_incl, LinearMap.id_comp]

/-- Translation by a point is the convolution `id ⋆ w`. -/
lemma translPoint_eq_conv (u : H →ₐ[k] k) :
    toConv (translPoint u)
      = toConv (LinearMap.id : H →ₗ[k] H) * toConv (charLin u H) := by
  rw [LinearMap.convMul_def, ofConv_toConv, ofConv_toConv]
  congr 1
  rw [translPoint, Coalgebra.Comodule.transl, Coalgebra.Comodule.coact_self]
  simp only [← LinearMap.comp_assoc]
  congr 1
  ext a b
  simp [Algebra.smul_def, mul_comm]

/-- The map `a ⊗ b ↦ u a • b`, as an algebra homomorphism. -/
noncomputable def evalFstAlg (u : H →ₐ[k] k) : H ⊗[k] H →ₐ[k] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId k H).comp u) (AlgHom.id k H)
    (fun _ _ => Commute.all _ _)

/-- `evalFstAlg u (a ⊗ b) = u a • b`. -/
@[simp] lemma evalFstAlg_tmul (u : H →ₐ[k] k) (a b : H) :
    evalFstAlg u (a ⊗ₜ[k] b) = u a • b := by
  simp [evalFstAlg, Algebra.smul_def]

/-- `conjPoint u` is `evalFstAlg u` composed with the adjoint coaction `adStarAlgHom k H`. -/
lemma conjPoint_eq_evalFstAlg (u : H →ₐ[k] k) :
    conjPoint u = (evalFstAlg u).toLinearMap ∘ₗ (adStarAlgHom k H).toLinearMap := by
  rw [conjPoint, ← LinearMap.comp_assoc]
  congr 1
  ext a b
  simp

/-- Conjugation by a point is the convolution `(w ∘ S) ⋆ id ⋆ w`. -/
lemma conjPoint_eq_conv (u : H →ₐ[k] k) :
    toConv (conjPoint u)
      = toConv (charLin u H ∘ₗ (antipode k : H →ₗ[k] H)) * toConv (LinearMap.id : H →ₗ[k] H)
          * toConv (charLin u H) := by
  set E : H ⊗[k] H →ₐ[k] H := evalFstAlg u with hE
  have h1 : toConv (E.toLinearMap ∘ₗ (convSL k H).ofConv)
      = toConv (charLin u H ∘ₗ (antipode k : H →ₗ[k] H)) := by
    congr 1
    ext x
    simp [hE, Algebra.smul_def]
  have h2 : toConv (E.toLinearMap ∘ₗ (convR k H).ofConv)
      = toConv (LinearMap.id : H →ₗ[k] H) := by
    congr 1
    ext x
    simp [hE]
  have h3 : toConv (E.toLinearMap ∘ₗ (convL k H).ofConv) = toConv (charLin u H) := by
    congr 1
    ext x
    simp [hE, Algebra.smul_def]
  rw [conjPoint_eq_evalFstAlg, show (adStarAlgHom k H).toLinearMap
      = (convSL k H * convR k H * convL k H).ofConv from
    congr(WithConv.ofConv $adStarAlgHom_eq_conv), toConv_algHom_comp', toConv_algHom_comp',
    h1, h2, h3]

/-- **The translation identity** `Δ ∘ T_u = (T_u ⊗ C_u) ∘ Δ`, the algebraic form of
`f (y n u) = f ((y u) (u⁻¹ n u))`. -/
theorem comul_comp_translPoint (u : H →ₐ[k] k) :
    (comul (R := k) (A := H)) ∘ₗ translPoint u
      = TensorProduct.map (translPoint u) (conjPoint u) ∘ₗ (comul (R := k) (A := H)) := by
  set W : WithConv (H →ₗ[k] H ⊗[k] H) := toConv (charLin u (H ⊗[k] H)) with hW
  set WS : WithConv (H →ₗ[k] H ⊗[k] H) :=
    toConv (charLin u (H ⊗[k] H) ∘ₗ (antipode k : H →ₗ[k] H)) with hWS
  -- the left-hand side is `Δ ⋆ w`
  have hlhs : toConv ((comul (R := k) (A := H)) ∘ₗ translPoint u)
      = toConv (comul (R := k) (A := H)) * W := by
    have hd : (comul (R := k) (A := H)) = (Bialgebra.comulAlgHom k H).toLinearMap := rfl
    rw [hd, show translPoint u = (toConv (LinearMap.id : H →ₗ[k] H)
        * toConv (charLin u H)).ofConv from congr(WithConv.ofConv $(translPoint_eq_conv u)),
      toConv_algHom_comp', ofConv_toConv, ofConv_toConv, LinearMap.comp_id, comp_charLin, hW]
  -- the right-hand side is `(F ⋆ w) ⋆ ((w ∘ S) ⋆ G ⋆ w)`
  have hFT : toConv ((Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] H).toLinearMap
        ∘ₗ translPoint u) = convL k H * W := by
    rw [show translPoint u = (toConv (LinearMap.id : H →ₗ[k] H)
        * toConv (charLin u H)).ofConv from congr(WithConv.ofConv $(translPoint_eq_conv u)),
      toConv_algHom_comp', ofConv_toConv, ofConv_toConv, LinearMap.comp_id, comp_charLin, hW,
      includeLeft_toLinearMap, toConv_ofConv]
  have hGC : toConv ((Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toLinearMap
        ∘ₗ conjPoint u) = WS * convR k H * W := by
    have h1 : (Algebra.TensorProduct.includeRight : H →ₐ[k] H ⊗[k] H).toLinearMap
        ∘ₗ (charLin u H ∘ₗ (antipode k : H →ₗ[k] H))
        = charLin u (H ⊗[k] H) ∘ₗ (antipode k : H →ₗ[k] H) := by
      rw [← LinearMap.comp_assoc, comp_charLin]
    rw [show conjPoint u = (toConv (charLin u H ∘ₗ (antipode k : H →ₗ[k] H))
          * toConv (LinearMap.id : H →ₗ[k] H) * toConv (charLin u H)).ofConv from
        congr(WithConv.ofConv $(conjPoint_eq_conv u)),
      toConv_algHom_comp', toConv_algHom_comp', ofConv_toConv, ofConv_toConv, ofConv_toConv,
      h1, LinearMap.comp_id, comp_charLin, hW, hWS, includeRight_toLinearMap, toConv_ofConv]
  have hrhs : toConv (TensorProduct.map (translPoint u) (conjPoint u)
        ∘ₗ (comul (R := k) (A := H))) = toConv (comul (R := k) (A := H)) * W := by
    rw [toConv_map_comp_comul, hFT, hGC, ← convL_convMul_convR]
    calc convL k H * W * (WS * convR k H * W)
        = convL k H * (W * WS) * (convR k H * W) := by simp only [mul_assoc]
      _ = convL k H * (convR k H * W) := by
          rw [hW, hWS, charLin_convMul_charLin_antipode, mul_one]
      _ = convL k H * convR k H * W := by rw [mul_assoc]
  exact toConv_injective (hlhs.trans hrhs.symm)

end Conv

/-- **A normal Hopf ideal is stable under conjugation by a point.** -/
theorem conjPoint_mem {I : Ideal H} (hI : IsNormalHopfIdeal k I) (u : H →ₐ[k] k)
    {x : H} (hx : x ∈ I) : conjPoint u x ∈ I := by
  -- reduce the first leg of `ad* x` against `u`; normality says the second leg dies modulo `I`
  have h0 : lTensorQuot I (adStarAlgHom k H x) = 0 := lTensorQuot_adStar I hI hx
  set F : H ⊗[k] (H ⧸ I) →ₗ[k] H ⧸ I :=
    (TensorProduct.lid k (H ⧸ I)).toLinearMap ∘ₗ LinearMap.rTensor (H ⧸ I) u.toLinearMap with hF
  have hcomm : ∀ z : H ⊗[k] H,
      Ideal.Quotient.mk I ((TensorProduct.lid k H) (LinearMap.rTensor H u.toLinearMap z))
        = F (lTensorQuot I z) := by
    intro z
    induction z with
    | tmul a b =>
        simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, lTensorQuot_tmul, hF,
          LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply]
        exact map_smul (Ideal.Quotient.mkₐ k I).toLinearMap (u a) b
    | add p q hp hq => simp only [map_add, hp, hq]
  have : Ideal.Quotient.mk I (conjPoint u x) = 0 := by
    rw [conjPoint]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      AlgHom.toLinearMap_apply]
    rw [show (TensorProduct.lid k H) (LinearMap.rTensor H u.toLinearMap (adStarAlgHom k H x))
        = (TensorProduct.lid k H) (LinearMap.rTensor H u.toLinearMap
          ((adStarAlgHom k H).toLinearMap x)) from rfl]
    rw [hcomm, show (adStarAlgHom k H).toLinearMap x = adStarAlgHom k H x from rfl, h0, map_zero]
  exact (Submodule.Quotient.mk_eq_zero I).1 this

/-- **The translate by a point of a relatively invariant vector is relatively invariant**, with
the conjugated character. -/
theorem isRelInvMod_translPoint {I : Ideal H} (hI : IsNormalHopfIdeal k I) (u : H →ₐ[k] k)
    {v g : H} (hv : IsRelInvMod k I v g) :
    IsRelInvMod k I (translPoint u v) (conjPoint u g) := by
  classical
  -- write `Δ v = v ⊗ g + t` with `t ∈ H ⊗ I`
  have h0 : LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap
      (coact (R := k) (C := H) v - v ⊗ₜ[k] g) = 0 := by
    rw [map_sub, hv]
    simp
  have ht : coact (R := k) (C := H) v - v ⊗ₜ[k] g
      ∈ LinearMap.range (LinearMap.lTensor H (I.restrictScalars k).subtype) := by
    have := TensorProduct.mem_range_lTensor_ker (M := H) (Ideal.Quotient.mkₐ k I).toLinearMap h0
    rwa [ker_quotMkₐ] at this
  obtain ⟨s, hs⟩ := ht
  have hsplit : comul (R := k) (A := H) v
      = v ⊗ₜ[k] g + LinearMap.lTensor H (I.restrictScalars k).subtype s := by
    rw [← Coalgebra.Comodule.coact_self k H, hs]; abel
  -- the image of `H ⊗ I` under `T_u ⊗ C_u` still dies modulo `I`
  have hker : ∀ z : H ⊗[k] ↥(I.restrictScalars k),
      LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap
        (TensorProduct.map (translPoint u) (conjPoint u)
          (LinearMap.lTensor H (I.restrictScalars k).subtype z)) = 0 := by
    intro z
    induction z with
    | tmul a b =>
        have hb : conjPoint u (b : H) ∈ I := conjPoint_mem hI u b.2
        simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, Submodule.subtype_apply,
          AlgHom.toLinearMap_apply]
        rw [show (Ideal.Quotient.mkₐ k I) (conjPoint u (b : H)) = 0 from
          (Submodule.Quotient.mk_eq_zero I).2 hb, TensorProduct.tmul_zero]
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, add_zero]
  have hmain := congr(LinearMap.lTensor H (Ideal.Quotient.mkₐ k I).toLinearMap
    (TensorProduct.map (translPoint u) (conjPoint u) $hsplit))
  simp only [map_add, hker] at hmain
  rw [IsRelInvMod, Coalgebra.Comodule.coact_self]
  rw [show comul (R := k) (A := H) (translPoint u v)
      = ((comul (R := k) (A := H)) ∘ₗ translPoint u) v from rfl, comul_comp_translPoint]
  simpa using hmain

end HopfAlgebra.Commutative
end
