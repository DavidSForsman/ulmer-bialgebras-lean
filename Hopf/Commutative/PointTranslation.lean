module

public import Hopf.Basic.Comodule
public import Hopf.Basic.ComoduleTransl
public import Hopf.Basic.RelativeHopfModule
public import Hopf.Basic.RelativeHopfFlat

/-!
# Translation of a comodule by a point

Let `C` be a coalgebra over `R` and `M` a right `C`-comodule with coaction
`ρ m = ∑ m₍₀₎ ⊗ m₍₁₎`.  Every functional `u : C →ₗ[R] R` acts on `M` by

`u ⇀ m = ∑ u (m₍₁₎) • m₍₀₎`.

This is Takeuchi's action of `C*` on comodules, used in §3 of *A correspondence between Hopf
ideals and sub-Hopf algebras* (manuscripta math. **7** (1972)); when `C = H` is a Hopf algebra and
`u : H →ₐ[k] k` is a point of the affine group scheme `Spec H`, the operator `u ⇀ -` is
invertible, with inverse `(u ∘ S) ⇀ -`, and it is *semilinear*: on a relative `(H,K)`-Hopf module
`M` one has `u ⇀ (x • m) = (u ⇀ x) • (u ⇀ m)`, where `u ⇀ x` is the translate of `x ∈ K` by the
point, an algebra automorphism of `K`.

## Main definitions

* `Coalgebra.Comodule.transl u`: the operator `u ⇀ -` on a comodule;
* `Coalgebra.Comodule.convFun v u`: the convolution product of two functionals;
* `HopfAlgebra.Commutative.translAlgHom w`: the translation of a bialgebra by an algebra map
  `w : K →ₐ[k] k`, as an algebra endomorphism of `K`;
* `HopfAlgebra.Commutative.translAlgEquiv`: the same, as an algebra automorphism, for `K` a Hopf
  algebra.

## Main results

* `Coalgebra.Comodule.transl_transl`: `v ⇀ (u ⇀ m) = (v ⋆ u) ⇀ m`;
* `Coalgebra.Comodule.transl_counit`: `ε ⇀ m = m`;
* `HopfAlgebra.Commutative.convFun_comp_antipode_left`,
  `HopfAlgebra.Commutative.convFun_comp_antipode_right`: for an algebra map `u` on a Hopf algebra,
  `u ∘ S` is a two-sided convolution inverse of `u`;
* `HopfAlgebra.Commutative.transl_smul`: semilinearity of `u ⇀ -` on a relative Hopf module.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Section 3
-/

@[expose] public section

section
open Coalgebra Coalgebra.Comodule HopfAlgebra

open TensorProduct _root_.Coalgebra

namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

section AlgHom

variable {k K : Type*} [CommRing k] [CommRing K] [Bialgebra k K]

/-- The translation of a bialgebra by an algebra map `w : K →ₐ[k] k`, as an algebra
endomorphism `x ↦ ∑ w (x₍₂₎) x₍₁₎` of `K`. -/
noncomputable def translAlgHom (w : K →ₐ[k] k) : K →ₐ[k] K :=
  (Algebra.TensorProduct.rid k k K).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id k K) w).comp (Bialgebra.comulAlgHom k K))

/-- Comparison of the algebra and module versions of `K ⊗ K → K`, `x ⊗ y ↦ w y • x`. -/
lemma rid_map_eq (w : K →ₐ[k] k) (t : K ⊗[k] K) :
    (Algebra.TensorProduct.rid k k K) ((Algebra.TensorProduct.map (AlgHom.id k K) w) t)
      = (TensorProduct.rid k K) (LinearMap.lTensor K w.toLinearMap t) := by
  induction t with
  | add a b ha hb => simp [ha, hb]
  | tmul a b => simp

/-- The underlying linear map of `translAlgHom w` is the translation `transl w`. -/
lemma translAlgHom_toLinearMap (w : K →ₐ[k] k) :
    (translAlgHom w).toLinearMap = (transl w.toLinearMap : K →ₗ[k] K) := by
  ext x
  exact rid_map_eq w (comul x)

/-- `translAlgHom w` agrees with the translation `transl w` pointwise. -/
lemma translAlgHom_apply (w : K →ₐ[k] k) (x : K) :
    translAlgHom w x = transl w.toLinearMap x :=
  congr($(translAlgHom_toLinearMap w) x)

end AlgHom

section Antipode

variable {k H : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]

/-- For an algebra map `u` on a Hopf algebra, `u ∘ S` is a left convolution inverse of `u`. -/
lemma convFun_comp_antipode_left (u : H →ₐ[k] k) :
    convFun (u.toLinearMap ∘ₗ HopfAlgebra.antipode k) u.toLinearMap
      = (counit : H →ₗ[k] k) := by
  ext x
  set r := Coalgebra.Repr.arbitrary k x with hr
  rw [convFun_apply _ _ r]
  have hsum : ∑ i ∈ r.index, HopfAlgebra.antipode k (r.left i) * r.right i
      = algebraMap k H (counit x) :=
    HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit r
  have := congr(u $hsum)
  rw [map_sum] at this
  simpa [Algebra.algebraMap_eq_smul_one] using this

/-- For an algebra map `u` on a Hopf algebra, `u ∘ S` is a right convolution inverse of `u`. -/
lemma convFun_comp_antipode_right (u : H →ₐ[k] k) :
    convFun u.toLinearMap (u.toLinearMap ∘ₗ HopfAlgebra.antipode k)
      = (counit : H →ₗ[k] k) := by
  ext x
  set r := Coalgebra.Repr.arbitrary k x with hr
  rw [convFun_apply _ _ r]
  have hsum : ∑ i ∈ r.index, r.left i * HopfAlgebra.antipode k (r.right i)
      = algebraMap k H (counit x) :=
    HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit r
  have := congr(u $hsum)
  rw [map_sum] at this
  simpa [Algebra.algebraMap_eq_smul_one] using this

end Antipode

section AlgEquiv

variable {k K : Type*} [CommRing k] [CommRing K] [HopfAlgebra k K]

/-- The translation of a Hopf algebra by an algebra map `w : K →ₐ[k] k` is an algebra
automorphism, with inverse the translation by `w ∘ S`. -/
noncomputable def translAlgEquiv (w : K →ₐ[k] k) : K ≃ₐ[k] K :=
  AlgEquiv.ofBijective (translAlgHom w) (by
    have hbij := Coalgebra.Comodule.transl_bijective (M := K) (convFun_comp_antipode_left w)
      (convFun_comp_antipode_right w)
    have heq : ⇑(translAlgHom w) = ⇑(Coalgebra.Comodule.transl w.toLinearMap : K →ₗ[k] K) :=
      funext (translAlgHom_apply w)
    rw [heq]
    exact hbij)

/-- `translAlgEquiv w` agrees with the translation `Coalgebra.Comodule.transl w` pointwise. -/
@[simp] lemma translAlgEquiv_apply (w : K →ₐ[k] k) (x : K) :
    translAlgEquiv w x = Coalgebra.Comodule.transl w.toLinearMap x :=
  translAlgHom_apply w x

end AlgEquiv

section Semilinear

variable {k K H M : Type*} [Field k] [CommRing K] [CommRing H]
  [Bialgebra k K] [Bialgebra k H] [AddCommGroup M] [Module k M] [Module K M]
  [IsScalarTower k K M] [RightComodule k H M] {φ : K →ₐc[k] H}

/-- The coaction of a product `x • m` in a relative Hopf module, in Sweedler form. -/
lemma coact_smul_sum (hM : IsRelativeHopfModule k K H M φ) (x : K) (m : M)
    {ι : Type*} (rx : Coalgebra.Repr k x ι) (rm : Coalgebra.Comodule.Repr k H m) :
    Coalgebra.Comodule.coact (R := k) (C := H) (x • m)
      = ∑ i ∈ rx.index, ∑ j ∈ rm.index,
          (rx.left i • rm.left j) ⊗ₜ[k] (φ (rx.right i) * rm.right j) := by
  rw [hM x m, ← rx.eq, ← rm.eq]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, relCompat_tmul]
  exact Finset.sum_comm

/-- A representation of the coaction of `x • m` in a relative Hopf module. -/
noncomputable def reprSmulProd (hM : IsRelativeHopfModule k K H M φ) {x : K} {m : M}
    {ι : Type*} (rx : Coalgebra.Repr k x ι) (rm : Coalgebra.Comodule.Repr k H m) :
    Coalgebra.Comodule.Repr k H (x • m) where
  ι := ι × rm.ι
  index := rx.index ×ˢ rm.index
  left := fun p => rx.left p.1 • rm.left p.2
  right := fun p => φ (rx.right p.1) * rm.right p.2
  eq := by
    rw [coact_smul_sum hM x m rx rm, Finset.sum_product]

/-- **Semilinearity of translation.**  On a relative `(H,K)`-Hopf module, translation by a point
`u` of `H` satisfies `u ⇀ (x • m) = (u ⇀ x) • (u ⇀ m)`, where `u ⇀ x` is the translation of
`K` by the algebra map `u ∘ φ`. -/
theorem transl_smul (hM : IsRelativeHopfModule k K H M φ) (u : H →ₐ[k] k) (x : K) (m : M) :
    Coalgebra.Comodule.transl u.toLinearMap (x • m)
      = (translAlgHom (u.comp (φ : K →ₐ[k] H)) x) • (Coalgebra.Comodule.transl u.toLinearMap m)
          := by
  classical
  set rx := Coalgebra.Repr.arbitrary k x with hrx
  set rm := Coalgebra.Comodule.Repr.arbitrary k H m with hrm
  rw [Coalgebra.Comodule.transl_apply _ (reprSmulProd hM rx rm)]
  change ∑ p ∈ rx.index ×ˢ rm.index,
      u.toLinearMap (φ (rx.right p.1) * rm.right p.2) • (rx.left p.1 • rm.left p.2) = _
  rw [Finset.sum_product]
  rw [translAlgHom_apply, Coalgebra.Comodule.transl_apply _ rx.toComodule,
    Coalgebra.Comodule.transl_apply _ rm, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
    map_mul, mul_smul, smul_assoc, smul_comm (u (rm.right j)) (rx.left i) (rm.left j)]
  rfl

end Semilinear

end HopfAlgebra.Commutative

end
