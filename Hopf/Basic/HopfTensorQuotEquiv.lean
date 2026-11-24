module

public import Mathlib.RingTheory.TensorProduct.Free
public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Basic.HopfGaloisMap
public import Hopf.Basic.HopfQuotientAug
public import Hopf.Basic.CoalgebraReprMul
public import Hopf.Basic.AntipodeBialgHom

/-!
# `B ⊗[A] B ≅ B ⊗[k] C` for a Hopf subalgebra `A ⊆ B`

Let `f : A →ₐc[k] B` be a morphism of commutative Hopf algebras over a commutative von Neumann
regular ring `k` (for instance a field) making `B` an `A`-algebra, and let `C = B / A⁺B`.
Waterhouse's proof of Takeuchi's theorem (*Introduction to Affine Group Schemes*, §14.2) uses the
isomorphism
```
B ⊗[A] B ≅ B ⊗[k] C
```
of left `B`-modules, coming from the group-scheme isomorphism `F ×_G F ≅ F × N` (`N` the kernel of
`F → G`), `(f, f') ↦ (f, f⁻¹f')`.  On Hopf algebras it is induced by the Galois map
`β : b ⊗ c ↦ ∑ b c₍₁₎ ⊗ c₍₂₎` of `Hopf/Basic/HopfGaloisMap.lean`.

Note that neither the injectivity of `f` nor any nilpotence is needed here.

## Main results

* `HopfAlgebra.galoisTensorEquiv`: the Galois map induces an isomorphism
  `B ⊗[A] B ≃ₗ[B] B ⊗[k] C` of left `B`-modules, where `C = B / A⁺B`.
* `HopfAlgebra.free_tensorProduct`: if `C` is a free `k`-module, then `B ⊗[A] B` is a free
  `B`-module.
* `HopfAlgebra.projective_tensorProduct`: if `C` is a free `k`-module, then `B ⊗[A] B` is a
  projective `B`-module.

## References

* [W. C. Waterhouse, *Introduction to Affine Group Schemes*]
  [waterhouseIntroductionAffineGroup1979], Section 14.2
* [S. U. Chase, M. E. Sweedler, *Hopf Algebras and Galois Theory*][chaseHopfAlgebrasGalois1969]
-/

@[expose] public section

section
open HopfAlgebra HopfAlgebra.Commutative
namespace HopfAlgebra

open TensorProduct Coalgebra

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B] [HopfAlgebra k A]
    [HopfAlgebra k B] [Algebra A B]

variable (k A B) in
/-- The `k`-linear map `B ⊗[k] B → B ⊗[k] C` given by `β` followed by the quotient map on the
second factor: `b ⊗ c ↦ ∑ b c₍₁₎ ⊗ [c₍₂₎]`. -/
noncomputable def galoisQuot : B ⊗[k] B →ₗ[k] B ⊗[k] QuotAug k A B :=
  (LinearMap.lTensor B (mkAug k A B).toLinearMap) ∘ₗ galoisMap k B

/-- On a Sweedler representation of `c`: `b ⊗ c ↦ ∑ b c₍₁₎ ⊗ [c₍₂₎]`. -/
lemma galoisQuot_tmul (b c : B) {ι : Type*} (r : Coalgebra.Repr k c ι) :
    galoisQuot k A B (b ⊗ₜ[k] c)
      = ∑ i ∈ r.index, (b * r.left i) ⊗ₜ[k] mkAug k A B (r.right i) := by
  rw [galoisQuot, LinearMap.comp_apply, galoisMap_tmul b c r, map_sum]
  rfl

/-- `galoisQuot ((b' * b) ⊗ c) = b' • galoisQuot (b ⊗ c)`. -/
lemma galoisQuot_mul_tmul (b' b c : B) :
    galoisQuot k A B ((b' * b) ⊗ₜ[k] c) = b' • galoisQuot k A B (b ⊗ₜ[k] c) := by
  classical
  rw [galoisQuot_tmul (b' * b) c (ℛ k c), galoisQuot_tmul b c (ℛ k c), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_assoc]

variable (k A B) in
/-- The projection `B ⊗[k] B → B ⊗[k] C` on the second factor. -/
noncomputable def quotRight : B ⊗[k] B →ₗ[k] B ⊗[k] QuotAug k A B :=
  LinearMap.lTensor B (mkAug k A B).toLinearMap

/-- The projection `B ⊗[k] B → B ⊗[k] C` is surjective. -/
lemma quotRight_surjective : Function.Surjective (quotRight k A B) :=
  LinearMap.lTensor_surjective B mkAug_surjective

/-- `galoisQuot` is `β` followed by the projection `B ⊗[k] B → B ⊗[k] C`. -/
lemma galoisQuot_eq_quotRight (z : B ⊗[k] B) :
    galoisQuot k A B z = quotRight k A B (galoisMap k B z) := rfl

variable [IsScalarTower k A B]

section Basic

variable (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)

include halg

/-- Multiplying by an element coming from `A` acts on `C = B / A⁺B` through the counit. -/
lemma mkAug_f_mul (a : A) (b : B) :
    mkAug k A B (f a * b) = (Coalgebra.counit (R := k) a) • mkAug k A B b := by
  rw [← halg a, map_mul, mkAug_algebraMap a, Algebra.smul_def]

end Basic

section Key

variable (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)

include halg

/-- **The key computation.**  The map `b ⊗ c ↦ ∑ b c₍₁₎ ⊗ [c₍₂₎]` is `A`-balanced: moving a factor
from `A` across the tensor sign does not change it, because `A` acts on `C` through its counit. -/
lemma galoisQuot_tmul_smul (a : A) (b c : B) :
    galoisQuot k A B (b ⊗ₜ[k] (f a * c)) = (f a) • galoisQuot k A B (b ⊗ₜ[k] c) := by
  classical
  set ra : Coalgebra.Repr k (f a) (A × A) := (ℛ k a).induced f with hra
  set rc : Coalgebra.Repr k c (B × B) := ℛ k c with hrc
  rw [galoisQuot_tmul b (f a * c) (ra.mul rc), galoisQuot_tmul b c rc]
  rw [Finset.smul_sum]
  -- both sides are sums over `ra.index ×ˢ rc.index` resp. `rc.index`
  have hprod : ∀ g : (A × A) × (B × B) → B ⊗[k] QuotAug k A B,
      ∑ x ∈ ra.index ×ˢ rc.index, g x = ∑ i ∈ ra.index, ∑ j ∈ rc.index, g (i, j) :=
    fun g => Finset.sum_product _ _ _
  refine Eq.trans (hprod (fun x => (b * (ra.left x.1 * rc.left x.2)) ⊗ₜ[k]
    mkAug k A B (ra.right x.1 * rc.right x.2))) ?_
  have step : ∀ i ∈ ra.index, ∀ j ∈ rc.index,
      (b * (ra.left i * rc.left j)) ⊗ₜ[k] mkAug k A B (ra.right i * rc.right j)
        = ((Coalgebra.counit (R := k) (ra.right i)) • (b * ra.left i * rc.left j)) ⊗ₜ[k]
            mkAug k A B (rc.right j) := by
    intro i _ j _
    have h1 : mkAug k A B (ra.right i * rc.right j)
        = (Coalgebra.counit (R := k) (ra.right i)) • mkAug k A B (rc.right j) := by
      have : ra.right i = f ((ℛ k a).right i) := rfl
      rw [this, mkAug_f_mul f halg, ← CoalgHomClass.counit_comp_apply (R := k) f]
    rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', mul_assoc]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => step i hi j hj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.sum_tmul, TensorProduct.smul_tmul', smul_eq_mul]
  congr 1
  have : ∑ i ∈ ra.index, (Coalgebra.counit (R := k) (ra.right i)) • (b * ra.left i * rc.left j)
      = b * (∑ i ∈ ra.index, (Coalgebra.counit (R := k) (ra.right i)) • ra.left i) * rc.left j := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by
      simp
  rw [this, Coalgebra.sum_smul_counit ra]
  ring

end Key

section Phi

/-- The map `b ⊗ c ↦ ∑ b c₍₁₎ ⊗ [c₍₂₎]`, as an `A`-bilinear map: it is `A`-linear in the first
variable because it is `B`-linear there, and `A`-linear in the second variable by
`galoisQuot_tmul_smul`. -/
noncomputable def galoisQuotBil (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    B →ₗ[A] B →ₗ[A] B ⊗[k] QuotAug k A B where
  toFun b :=
    { toFun := fun c => galoisQuot k A B (b ⊗ₜ[k] c)
      map_add' := fun c c' => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun a c => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, halg a, galoisQuot_tmul_smul f halg, ← halg a, algebraMap_smul] }
  map_add' := fun b b' => by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
    rw [TensorProduct.add_tmul, map_add]
  map_smul' := fun a b => by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
    rw [Algebra.smul_def, halg a, galoisQuot_mul_tmul, ← halg a, algebraMap_smul]

/-- **The Galois map on the relative tensor product**: the `A`-linear map
`Φ : B ⊗[A] B → B ⊗[k] C`, `b ⊗ c ↦ ∑ b c₍₁₎ ⊗ [c₍₂₎]`. -/
noncomputable def galoisTensor (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    B ⊗[A] B →ₗ[A] B ⊗[k] QuotAug k A B :=
  TensorProduct.lift (galoisQuotBil f halg)

/-- `Φ (b ⊗ c)` is `galoisQuot (b ⊗ c)`. -/
@[simp] lemma galoisTensor_tmul (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) (b c : B) :
    galoisTensor f halg (b ⊗ₜ[A] c) = galoisQuot k A B (b ⊗ₜ[k] c) := rfl

end Phi

variable (k A B) in
/-- The canonical surjection `B ⊗[k] B → B ⊗[A] B`. -/
noncomputable def tensorProj : B ⊗[k] B →ₗ[k] B ⊗[A] B :=
  TensorProduct.lift
    { toFun := fun b =>
        { toFun := fun c => b ⊗ₜ[A] c
          map_add' := fun c c' => TensorProduct.tmul_add b c c'
          map_smul' := fun r c => by
            simp only [RingHom.id_apply]
            rw [← TensorProduct.tmul_smul] }
      map_add' := fun b b' => by
        refine LinearMap.ext fun c => ?_
        simpa using TensorProduct.add_tmul b b' c
      map_smul' := fun r b => by
        refine LinearMap.ext fun c => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
        rw [← TensorProduct.smul_tmul'] }

/-- The projection `B ⊗[k] B → B ⊗[A] B` is surjective. -/
lemma tensorProj_surjective : Function.Surjective (tensorProj k A B) := by
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul b c => exact ⟨b ⊗ₜ[k] c, rfl⟩
  | add u v hu hv =>
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    exact ⟨u' + v', by rw [map_add]⟩

variable (k A B) in
/-- The `k`-linear map `Ψ₀ : B ⊗[k] B → B ⊗[A] B`, `b ⊗ c ↦ ∑ b S(c₍₁₎) ⊗ c₍₂₎`, obtained from the
inverse Galois map by projecting to the relative tensor product. -/
noncomputable def galoisInvProj : B ⊗[k] B →ₗ[k] B ⊗[A] B :=
  tensorProj k A B ∘ₗ galoisInvMap k B

/-- On a Sweedler representation of `c`: `Ψ₀ (b ⊗ c) = ∑ b S(c₍₁₎) ⊗ c₍₂₎`. -/
lemma galoisInvProj_tmul (b c : B) {ι : Type*} (r : Coalgebra.Repr k c ι) :
    galoisInvProj k A B (b ⊗ₜ[k] c)
      = ∑ i ∈ r.index, (b * antipode k (r.left i)) ⊗ₜ[A] r.right i := by
  rw [galoisInvProj, LinearMap.comp_apply, galoisInvMap_tmul b c r, map_sum]
  rfl

/-- **The key vanishing computation.**  If `a` lies in the augmentation ideal of `A`, then
`Ψ₀` kills `b ⊗ f(a) y`: after moving `a₍₂₎` across the tensor sign one is left with
`∑ S(a₍₁₎) a₍₂₎ = ε(a) = 0`. -/
lemma galoisInvProj_tmul_augmentation (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (a : A) (ha : Coalgebra.counit (R := k) a = 0) (b y : B) :
    galoisInvProj k A B (b ⊗ₜ[k] (f a * y)) = 0 := by
  classical
  set ra : Coalgebra.Repr k (f a) (A × A) := (ℛ k a).induced f with hra
  set ry : Coalgebra.Repr k y (B × B) := ℛ k y with hry
  rw [galoisInvProj_tmul b (f a * y) (ra.mul ry)]
  refine Eq.trans (Finset.sum_product ra.index ry.index
    (fun p => (b * antipode k (ra.left p.1 * ry.left p.2)) ⊗ₜ[A]
      (ra.right p.1 * ry.right p.2))) ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  have step : ∀ i ∈ ra.index,
      (b * antipode k (ra.left i * ry.left j)) ⊗ₜ[A] (ra.right i * ry.right j)
        = (antipode k (ra.left i) * ra.right i * (b * antipode k (ry.left j)))
            ⊗ₜ[A] ry.right j := by
    intro i _
    have hri : ra.right i = algebraMap A B ((ℛ k a).right i) := (halg _).symm
    have hsm : ra.right i * ry.right j = (ℛ k a).right i • ry.right j := by
      rw [Algebra.smul_def, hri]
    rw [hsm, ← TensorProduct.smul_tmul, Algebra.smul_def, ← hri, HopfAlgebra.antipode_mul_distrib]
    congr 1
    ring
  rw [Finset.sum_congr rfl step, ← TensorProduct.sum_tmul, ← Finset.sum_mul,
    HopfAlgebra.sum_antipode_mul_eq_smul ra]
  have hc : Coalgebra.counit (R := k) (f a) = 0 := by
    rw [CoalgHomClass.counit_comp_apply (R := k) f, ha]
  rw [hc]
  simp

/-- `Ψ₀` kills `b ⊗ j` for every `j` in the ideal `A⁺B`. -/
lemma galoisInvProj_tmul_mem (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (b : B) {j : B} (hj : j ∈ augIdealB k A B) :
    galoisInvProj k A B (b ⊗ₜ[k] j) = 0 := by
  classical
  rw [augIdealB, Ideal.map, Ideal.span, Submodule.mem_span_set'] at hj
  obtain ⟨n, cc, gg, hsum⟩ := hj
  rw [← hsum, TensorProduct.tmul_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨a, ha, hga⟩ := (gg i).2
  have hcc : cc i • ((gg i : B)) = f a * cc i := by
    rw [← hga, halg a, smul_eq_mul, mul_comm]
  rw [hcc]
  exact galoisInvProj_tmul_augmentation f halg a ha b (cc i)

/-- `Ψ₀` factors through `B ⊗[k] C`. -/
lemma ker_quotRight_le (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    LinearMap.ker (quotRight k A B) ≤ LinearMap.ker (galoisInvProj k A B) := by
  classical
  set J : Submodule k B := (augIdealB k A B).restrictScalars k with hJ
  have hex : Function.Exact (J.subtype) ((mkAug k A B).toLinearMap) := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      simpa [hJ, mkAug, Ideal.Quotient.eq_zero_iff_mem] using hx
    · rintro ⟨y, rfl⟩
      simp only [mkAug, AlgHom.toLinearMap_apply, Submodule.subtype_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact y.2
  have hex2 := lTensor_exact (f := J.subtype) (g := (mkAug k A B).toLinearMap) B hex
    mkAug_surjective
  have key : ∀ w : B ⊗[k] J, galoisInvProj k A B (LinearMap.lTensor B J.subtype w) = 0 := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul b j =>
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      exact galoisInvProj_tmul_mem f halg b j.2
    | add u v hu hv => rw [map_add, map_add, hu, hv, add_zero]
  intro z hz
  obtain ⟨w, hw⟩ := (hex2 z).mp hz
  rw [LinearMap.mem_ker, ← hw]
  exact key w

/-- **The inverse of the Galois map**, `Ψ : B ⊗[k] C → B ⊗[A] B`. -/
noncomputable def galoisInvTensor (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    B ⊗[k] QuotAug k A B →ₗ[k] B ⊗[A] B :=
  (Submodule.liftQ (LinearMap.ker (quotRight k A B)) (galoisInvProj k A B)
      (ker_quotRight_le f halg)) ∘ₗ
    ((quotRight k A B).quotKerEquivOfSurjective quotRight_surjective).symm.toLinearMap

/-- `Ψ` composed with the projection `B ⊗[k] B → B ⊗[k] C` is `Ψ₀`. -/
@[simp] lemma galoisInvTensor_quotRight (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)
    (z : B ⊗[k] B) :
    galoisInvTensor f halg (quotRight k A B z) = galoisInvProj k A B z := by
  have h : ((quotRight k A B).quotKerEquivOfSurjective quotRight_surjective).symm
      (quotRight k A B z) = Submodule.Quotient.mk z :=
    (LinearEquiv.symm_apply_eq _).mpr rfl
  rw [galoisInvTensor, LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]

section Iso

variable (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a)

/-- `Φ` composed with the projection `B ⊗[k] B → B ⊗[A] B` is `galoisQuot`. -/
lemma galoisTensor_tensorProj (z : B ⊗[k] B) :
    galoisTensor f halg (tensorProj k A B z) = galoisQuot k A B z := by
  induction z using TensorProduct.inductionOn with
  | tmul b c => rfl
  | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]

/-- `Ψ (Φ x) = x` for `x : B ⊗[A] B`. -/
lemma galoisInvTensor_galoisTensor (x : B ⊗[A] B) :
    galoisInvTensor f halg (galoisTensor f halg x) = x := by
  obtain ⟨z, rfl⟩ := tensorProj_surjective (k := k) x
  rw [galoisTensor_tensorProj, galoisQuot_eq_quotRight, galoisInvTensor_quotRight,
    galoisInvProj, LinearMap.comp_apply]
  congr 1
  exact congr($(galoisInvMap_comp_galoisMap (k := k) (B := B)) z)

/-- `Φ (Ψ y) = y` for `y : B ⊗[k] C`. -/
lemma galoisTensor_galoisInvTensor (y : B ⊗[k] QuotAug k A B) :
    galoisTensor f halg (galoisInvTensor f halg y) = y := by
  obtain ⟨z, rfl⟩ := quotRight_surjective y
  rw [galoisInvTensor_quotRight, galoisInvProj, LinearMap.comp_apply, galoisTensor_tensorProj,
    galoisQuot_eq_quotRight]
  congr 1
  exact congr($(galoisMap_comp_galoisInvMap (k := k) (B := B)) z)

/-- The Galois map `Φ : B ⊗[A] B → B ⊗[k] C` is linear for the *left* `B`-module structures. -/
noncomputable def galoisTensorB : B ⊗[A] B →ₗ[B] B ⊗[k] QuotAug k A B where
  toFun := galoisTensor f halg
  map_add' := map_add _
  map_smul' := by
    intro b' x
    simp only [RingHom.id_apply]
    induction x using TensorProduct.inductionOn with
    | tmul b c =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, galoisTensor_tmul, galoisTensor_tmul,
        galoisQuot_mul_tmul]
    | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add]

/-- **Waterhouse's isomorphism** (*Introduction to Affine Group Schemes*, §14.2):
for a Hopf subalgebra `A ⊆ B` with quotient `C = B/A⁺B`, the Galois map is an isomorphism
`B ⊗[A] B ≅ B ⊗[k] C` of left `B`-modules.  Geometrically it is the isomorphism
`F ×_G F ≅ F × N` of the kernel `N` of `F → G`, `(g, h) ↦ (g, g⁻¹h)`. -/
noncomputable def galoisTensorEquiv : (B ⊗[A] B) ≃ₗ[B] B ⊗[k] QuotAug k A B :=
  LinearEquiv.ofBijective (galoisTensorB f halg)
    ⟨Function.LeftInverse.injective (galoisInvTensor_galoisTensor f halg),
      Function.RightInverse.surjective (galoisTensor_galoisInvTensor f halg)⟩

/-- Consequently `B ⊗[A] B` is a **free** `B`-module (for the left action), as soon as `C` is
free over the base (automatic over a field), since then `B ⊗[k] C` is free over `B`. -/
theorem free_tensorProduct [Module.Free k (QuotAug k A B)]
    (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    Module.Free B (B ⊗[A] B) :=
  Module.Free.of_equiv (galoisTensorEquiv f halg).symm

/-- In particular `B ⊗[A] B` is a projective `B`-module; this is the input needed by the
freeness criterion of `Foundations/RingTheory/NilpotentFreeCriterion.lean`. -/
theorem projective_tensorProduct [Module.Free k (QuotAug k A B)]
    (f : A →ₐc[k] B) (halg : ∀ a, algebraMap A B a = f a) :
    Module.Projective B (B ⊗[A] B) :=
  letI := free_tensorProduct f halg
  inferInstance

end Iso

end HopfAlgebra
end
