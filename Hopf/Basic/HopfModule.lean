module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Hopf.Basic.Comodule
public import Hopf.Basic.HopfAdjointCoaction

/-!
# Hopf modules and Sweedler's fundamental theorem

Let `H` be a commutative Hopf algebra over a commutative ring `k`.  A **Hopf module** over `H`
is an `H`-module `M` which is at the same time a right `H`-comodule, the coaction being a map of
`H`-modules in the sense that

```
ρ (h • m) = ∑ (h₍₁₎ • m₍₀₎) ⊗ h₍₂₎ m₍₁₎ .
```

(Takeuchi's `(H,H)`-Hopf modules; see *A correspondence between Hopf ideals and sub-Hopf
algebras*, manuscripta math. **7** (1972), §2, and the Notes at the end of that paper.)

The main result is **Sweedler's fundamental theorem of Hopf modules**: multiplication induces an
isomorphism `M^{co H} ⊗[k] H ≅ M`, where `M^{co H} = {m | ρ m = m ⊗ 1}` is the module of
coinvariants.  In particular, over a field `k`, every Hopf module is a *free* `H`-module.

## Main definitions

* `HopfAlgebra.actMap`: the action `H ⊗[k] M →ₗ[k] M`;
* `HopfAlgebra.IsHopfModule`: the compatibility axiom above;
* `HopfAlgebra.coinv`: the coinvariants `M^{co H}`;
* `HopfAlgebra.proj`: the projection `m ↦ ∑ S(m₍₁₎) • m₍₀₎` onto the coinvariants.

## Main results

* `HopfAlgebra.hopfModuleEquiv`: `M^{co H} ⊗[k] H ≃ₗ[k] M`, `n ⊗ h ↦ h • n`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 4.1.1
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Section
  2
-/

@[expose] public section

section
open Coalgebra Coalgebra.Comodule
namespace HopfAlgebra

open TensorProduct Coalgebra Coalgebra.Comodule

section Defs

variable (k H M : Type*) [CommRing k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M]

/-- The action of `H` on `M`, as a `k`-linear map `H ⊗[k] M →ₗ[k] M`. -/
noncomputable def actMap : H ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift (Algebra.lsmul k k M : H →ₐ[k] Module.End k M).toLinearMap
/-- `actMap` on pure tensors: `h ⊗ m ↦ h • m`. -/
@[simp] lemma actMap_tmul (h : H) (m : M) : actMap k H M (h ⊗ₜ[k] m) = h • m := rfl


/-- The `k`-linear map `(H ⊗ H) ⊗ (M ⊗ H) → M ⊗ H`, `(a ⊗ b) ⊗ (m ⊗ c) ↦ (a • m) ⊗ (b * c)`,
used to state the compatibility axiom of a Hopf module. -/
noncomputable def hopfCompat : (H ⊗[k] H) ⊗[k] (M ⊗[k] H) →ₗ[k] M ⊗[k] H :=
  (TensorProduct.map (actMap k H M) (LinearMap.mul' k H)) ∘ₗ
    (TensorProduct.tensorTensorTensorComm k H H M H).toLinearMap

/-- `hopfCompat` on pure tensors: `(a ⊗ b) ⊗ (m ⊗ c) ↦ (a • m) ⊗ (b * c)`. -/
@[simp] lemma hopfCompat_tmul (a b : H) (m : M) (c : H) :
    hopfCompat k H M ((a ⊗ₜ[k] b) ⊗ₜ[k] (m ⊗ₜ[k] c)) = (a • m) ⊗ₜ[k] (b * c) := rfl

variable [RightComodule k H M]

/-- `M` is a **Hopf module** over `H`: an `H`-module and right `H`-comodule such that
`ρ (h • m) = ∑ (h₍₁₎ • m₍₀₎) ⊗ h₍₂₎ m₍₁₎`. -/
class IsHopfModule : Prop where
  /-- The coaction is compatible with the action. -/
  coact_smul (h : H) (m : M) :
    coact (R := k) (C := H) (h • m) = hopfCompat k H M (comul (R := k) h ⊗ₜ[k] coact (R := k) m)

end Defs

section FourLegs

variable (k H M : Type*) [CommRing k] [CommRing H] [HopfAlgebra k H] [AddCommGroup M]
  [Module k M]

/-- Splitting the third leg: `x ⊗ (y ⊗ z) ↦ x ⊗ (y ⊗ Δ z)`. -/
noncomputable def splitThird : M ⊗[k] (H ⊗[k] H) →ₗ[k] M ⊗[k] (H ⊗[k] (H ⊗[k] H)) :=
  LinearMap.lTensor M (LinearMap.lTensor H (comul (R := k) (A := H)))

/-- Splitting the second leg: `x ⊗ (y ⊗ z) ↦ x ⊗ (y₍₁₎ ⊗ (y₍₂₎ ⊗ z))`. -/
noncomputable def splitSecond : M ⊗[k] (H ⊗[k] H) →ₗ[k] M ⊗[k] (H ⊗[k] (H ⊗[k] H)) :=
  LinearMap.lTensor M ((TensorProduct.assoc k H H H).toLinearMap ∘ₗ
    LinearMap.rTensor H (comul (R := k) (A := H)))

/-- The map `H ⊗ H → H`, `u ⊗ y ↦ S(u) * y`. -/
noncomputable def mulAnti : H ⊗[k] H →ₗ[k] H :=
  (LinearMap.mul' k H) ∘ₗ (LinearMap.rTensor H (antipode k (A := H)))

variable {k H M}

/-- `mulAnti` on pure tensors: `u ⊗ y ↦ S(u) * y`. -/
@[simp] lemma mulAnti_tmul (u y : H) : mulAnti k H (u ⊗ₜ[k] y) = antipode k u * y := rfl

/-- `splitThird` on pure tensors: `x ⊗ (y ⊗ z) ↦ x ⊗ (y ⊗ Δ z)`. -/
@[simp] lemma splitThird_tmul (x : M) (y z : H) :
    splitThird k H M (x ⊗ₜ[k] (y ⊗ₜ[k] z))
      = x ⊗ₜ[k] (y ⊗ₜ[k] comul (R := k) z) := rfl

/-- `splitSecond` on pure tensors: `x ⊗ (y ⊗ z) ↦ x ⊗ assoc (Δ y ⊗ z)`. -/
@[simp] lemma splitSecond_tmul (x : M) (y z : H) :
    splitSecond k H M (x ⊗ₜ[k] (y ⊗ₜ[k] z))
      = x ⊗ₜ[k] ((TensorProduct.assoc k H H H) ((comul (R := k) y) ⊗ₜ[k] z)) := rfl

/-- `splitThird` and `splitSecond` agree on the three-leg coaction: this is coassociativity of
the comultiplication. -/
lemma splitThird_eq_splitSecond (x : M) (c : H) :
    splitThird k H M (x ⊗ₜ[k] comul (R := k) c) = splitSecond k H M (x ⊗ₜ[k] comul (R := k) c) := by
  have h := congr($(Coalgebra.coassoc (R := k) (A := H)) c)
  simp only [LinearMap.coe_comp, Function.comp_apply] at h
  simp only [splitThird, splitSecond, LinearMap.lTensor_tmul, LinearMap.coe_comp,
    Function.comp_apply]
  rw [← h]

variable [Module H M] [IsScalarTower k H M]

variable (k H M) in
/-- The map `M ⊗ H → M`, `x ⊗ v ↦ S(v) • x`. -/
noncomputable def actAnti : M ⊗[k] H →ₗ[k] M :=
  (actMap k H M) ∘ₗ (TensorProduct.comm k M H).toLinearMap ∘ₗ
    (LinearMap.lTensor M (antipode k (A := H)))

variable (k H M) in
/-- The four-leg map `x ⊗ (y ⊗ (u ⊗ v)) ↦ (S(v) • x) ⊗ (S(u) * y)`. -/
noncomputable def fourLegMap : M ⊗[k] (H ⊗[k] (H ⊗[k] H)) →ₗ[k] M ⊗[k] H :=
  (TensorProduct.map (actAnti k H M) (mulAnti k H)) ∘ₗ
    (TensorProduct.assoc k M H (H ⊗[k] H)).symm.toLinearMap ∘ₗ
    (LinearMap.lTensor M (TensorProduct.assoc k H H H).toLinearMap) ∘ₗ
    (LinearMap.lTensor M (LinearMap.rTensor H (TensorProduct.comm k H H).toLinearMap)) ∘ₗ
    (LinearMap.lTensor M (TensorProduct.comm k H (H ⊗[k] H)).toLinearMap)

/-- `actAnti` on pure tensors: `x ⊗ v ↦ S(v) • x`. -/
@[simp] lemma actAnti_tmul (x : M) (v : H) : actAnti k H M (x ⊗ₜ[k] v) = antipode k v • x := rfl

/-- `fourLegMap` on pure tensors: `x ⊗ (y ⊗ (u ⊗ v)) ↦ (S(v) • x) ⊗ (S(u) * y)`. -/
@[simp] lemma fourLegMap_tmul (x : M) (y u v : H) :
    fourLegMap k H M (x ⊗ₜ[k] (y ⊗ₜ[k] (u ⊗ₜ[k] v)))
      = (antipode k v • x) ⊗ₜ[k] (antipode k u * y) := rfl

/-- `fourLegMap ∘ splitSecond` on a pure tensor `x ⊗ (c ⊗ d)` is `(ε(c) • S(d) • x) ⊗ 1`. -/
lemma fourLegMap_splitSecond_tmul (x : M) (c d : H) :
    fourLegMap k H M (splitSecond k H M (x ⊗ₜ[k] (c ⊗ₜ[k] d)))
      = (counit (R := k) c • (antipode k d • x)) ⊗ₜ[k] (1 : H) := by
  set rc := ℛ k c with hrc
  rw [splitSecond_tmul, ← rc.eq]
  simp only [TensorProduct.sum_tmul, TensorProduct.assoc_tmul, TensorProduct.tmul_sum,
    map_sum, fourLegMap_tmul]
  rw [← TensorProduct.tmul_sum]
  have : ∑ p ∈ rc.index, antipode k (rc.right p) * rc.left p
      = counit (R := k) c • (1 : H) := by
    rw [Finset.sum_congr rfl (fun p _ => mul_comm (antipode k (rc.right p)) (rc.left p))]
    exact HopfAlgebra.sum_mul_antipode_eq_smul rc
  rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- The map `M ⊗ (H ⊗ H) → M`, `x ⊗ (y ⊗ z) ↦ (S(y) * z) • x`. -/
noncomputable def collapse : M ⊗[k] (H ⊗[k] H) →ₗ[k] M :=
  (actMap k H M) ∘ₗ (TensorProduct.comm k M H).toLinearMap ∘ₗ
    (LinearMap.lTensor M (mulAnti k H))

/-- `collapse` on pure tensors: `x ⊗ (y ⊗ z) ↦ (S(y) * z) • x`. -/
@[simp] lemma collapse_tmul (x : M) (y z : H) :
    collapse (k := k) (H := H) (M := M) (x ⊗ₜ[k] (y ⊗ₜ[k] z)) = (antipode k y * z) • x := rfl

end FourLegs

section Basic

variable {k H M : Type*} [CommRing k] [CommRing H] [HopfAlgebra k H]
  [AddCommGroup M] [Module k M] [Module H M] [IsScalarTower k H M] [RightComodule k H M]

/-- The compatibility axiom in Sweedler form. -/
lemma coact_smul_repr [IsHopfModule k H M] {ι : Type*} (h : H) (m : M)
    (rh : Coalgebra.Repr k h ι) (rm : Coalgebra.Comodule.Repr k H m) :
    coact (R := k) (C := H) (h • m)
      = ∑ i ∈ rm.index, ∑ j ∈ rh.index,
          (rh.left j • rm.left i) ⊗ₜ[k] (rh.right j * rm.right i) := by
  rw [IsHopfModule.coact_smul (k := k) h m, ← rh.eq, ← rm.eq]
  rw [TensorProduct.sum_tmul]
  simp only [map_sum, TensorProduct.tmul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    exact hopfCompat_tmul k H M _ _ _ _

variable (k H M)

/-- The coinvariants `M^{co H} = {m | ρ m = m ⊗ 1}` of a right `H`-comodule. -/
def coinv : Submodule k M where
  carrier := {m | coact (R := k) (C := H) m = m ⊗ₜ[k] 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [map_add, ha, hb, TensorProduct.add_tmul]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [map_smul, hx, TensorProduct.smul_tmul']

variable {k H M}

omit [Module H M] [IsScalarTower k H M] in
/-- `m` is coinvariant iff `ρ m = m ⊗ 1`. -/
lemma mem_coinv_iff {m : M} :
    m ∈ coinv k H M ↔ coact (R := k) (C := H) m = m ⊗ₜ[k] 1 := Iff.rfl

variable (k H M)

/-- The projection `P : M → M`, `m ↦ ∑ S(m₍₁₎) • m₍₀₎`, onto the coinvariants. -/
noncomputable def proj : M →ₗ[k] M :=
  (actMap k H M) ∘ₗ (TensorProduct.comm k M H).toLinearMap ∘ₗ
    (LinearMap.lTensor M (antipode k (A := H))) ∘ₗ (coact (R := k) (C := H))

variable {k H M}

/-- On a Sweedler representation of `m`: `P m = ∑ S(m₍₁₎) • m₍₀₎`. -/
lemma proj_apply (m : M) (r : Coalgebra.Comodule.Repr k H m) :
    proj k H M m = ∑ i ∈ r.index, antipode k (r.right i) • r.left i := by
  simp [proj, ← r.eq, map_sum]

/-- On a coinvariant element the projection acts through the counit: `P (h • n) = ε(h) • n`. -/
lemma proj_smul_of_mem_coinv [IsHopfModule k H M] (h : H) {n : M} (hn : n ∈ coinv k H M) :
    proj k H M (h • n) = (counit (R := k) h) • n := by
  classical
  set rh := ℛ k h with hrh
  -- the coaction of `h • n` is `∑ (h₍₁₎ • n) ⊗ h₍₂₎`
  have hcoact : coact (R := k) (C := H) (h • n)
      = ∑ j ∈ rh.index, (rh.left j • n) ⊗ₜ[k] rh.right j := by
    rw [IsHopfModule.coact_smul (k := k) h n, mem_coinv_iff.1 hn, ← rh.eq,
      TensorProduct.sum_tmul]
    simp
  let rr : Coalgebra.Comodule.Repr k H (h • n) :=
    { ι := H × H, index := rh.index, left := fun j => rh.left j • n, right := rh.right,
      eq := hcoact.symm }
  rw [proj_apply (h • n) rr]
  change ∑ j ∈ rh.index, antipode k (rh.right j) • (rh.left j • n) = _
  have hj : ∀ j ∈ rh.index, antipode k (rh.right j) • (rh.left j • n)
      = (rh.left j * antipode k (rh.right j)) • n := by
    intro j _
    rw [← mul_smul, mul_comm]
  rw [Finset.sum_congr rfl hj, ← Finset.sum_smul, HopfAlgebra.sum_mul_antipode_eq_smul rh,
    smul_assoc, one_smul]

/-- **The projection is `H`-linear through the counit**: `P (h • m) = ε(h) • P m`. -/
lemma proj_smul [IsHopfModule k H M] (h : H) (m : M) :
    proj k H M (h • m) = (counit (R := k) h) • proj k H M m := by
  classical
  set rh := ℛ k h with hrh
  set rm := Coalgebra.Comodule.Repr.arbitrary k H m with hrm
  let r : Coalgebra.Comodule.Repr k H (h • m) :=
    { ι := rm.ι × (H × H), index := rm.index ×ˢ rh.index,
      left := fun p => rh.left p.2 • rm.left p.1,
      right := fun p => rh.right p.2 * rm.right p.1,
      eq := by
        refine Eq.trans (Finset.sum_product (s := rm.index) (t := rh.index)
          (f := fun p => (rh.left p.2 • rm.left p.1) ⊗ₜ[k] (rh.right p.2 * rm.right p.1))) ?_
        exact (coact_smul_repr h m rh rm).symm }
  rw [proj_apply (h • m) r, proj_apply m rm]
  refine Eq.trans (Finset.sum_product (s := rm.index) (t := rh.index)
    (f := fun p => antipode k (rh.right p.2 * rm.right p.1) • (rh.left p.2 • rm.left p.1))) ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ∀ j ∈ rh.index,
      antipode k (rh.right j * rm.right i) • (rh.left j • rm.left i)
        = (antipode k (rm.right i)) • ((rh.left j * antipode k (rh.right j)) • rm.left i) := by
    intro j _
    rw [HopfAlgebra.antipode_mul_distrib, ← mul_smul, ← mul_smul]
    congr 1
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.sum_smul,
    HopfAlgebra.sum_mul_antipode_eq_smul rh, smul_assoc, one_smul, smul_comm]

/-- The projection lands in the coinvariants. -/
lemma proj_mem_coinv [IsHopfModule k H M] (m : M) : proj k H M m ∈ coinv k H M := by
  classical
  rw [mem_coinv_iff]
  set r := Coalgebra.Comodule.Repr.arbitrary k H m with hr
  let a : (i : r.ι) → Coalgebra.Comodule.Repr k H (r.left i) :=
    fun i => Coalgebra.Comodule.Repr.arbitrary k H (r.left i)
  let b : (i : r.ι) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i)
  set X : M ⊗[k] (H ⊗[k] H) :=
    ∑ i ∈ r.index, ∑ l ∈ (a i).index, (a i).left l ⊗ₜ[k] ((a i).right l ⊗ₜ[k] r.right i) with hX
  set Y : M ⊗[k] (H ⊗[k] H) :=
    ∑ i ∈ r.index, ∑ j ∈ (b i).index, r.left i ⊗ₜ[k] ((b i).left j ⊗ₜ[k] (b i).right j) with hY
  have hXY : X = Y := Coalgebra.Comodule.sum_tmul_tmul_eq r a b
  -- `Y` in closed form
  have hY' : Y = ∑ i ∈ r.index, r.left i ⊗ₜ[k] comul (R := k) (r.right i) := by
    rw [hY]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← TensorProduct.tmul_sum, (b i).eq]
  -- Step 1: the coaction of `P m` is `fourLegMap (splitThird X)`
  have hstep1 : coact (R := k) (C := H) (proj k H M m)
      = fourLegMap k H M (splitThird k H M X) := by
    rw [proj_apply m r, map_sum]
    let hSb : ∀ i, Coalgebra.Repr k (antipode k (r.right i)) (H × H) := fun i =>
      { index := (b i).index,
        left := fun j => antipode k ((b i).right j),
        right := fun j => antipode k ((b i).left j),
        eq := (HopfAlgebra.comul_antipode_apply (r.right i) (b i)).symm }
    have hleft : ∀ i ∈ r.index, coact (R := k) (C := H) (antipode k (r.right i) • r.left i)
        = ∑ l ∈ (a i).index, ∑ j ∈ (b i).index,
            (antipode k ((b i).right j) • (a i).left l) ⊗ₜ[k]
              (antipode k ((b i).left j) * (a i).right l) := by
      intro i _
      exact coact_smul_repr _ _ (hSb i) (a i)
    rw [Finset.sum_congr rfl hleft, hX]
    simp only [map_sum, splitThird_tmul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← (b i).eq]
    simp only [TensorProduct.tmul_sum, map_sum, fourLegMap_tmul]
  -- Step 2: `splitThird X = splitSecond X`
  have hstep2 : splitThird k H M X = splitSecond k H M X := by
    rw [hXY, hY', map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => splitThird_eq_splitSecond _ _
  -- Step 3: `fourLegMap (splitSecond X) = P m ⊗ 1`
  have hstep3 : fourLegMap k H M (splitSecond k H M X) = proj k H M m ⊗ₜ[k] (1 : H) := by
    rw [hX]
    simp only [map_sum]
    have hterm : ∀ i ∈ r.index, ∀ l ∈ (a i).index,
        fourLegMap k H M (splitSecond k H M
            ((a i).left l ⊗ₜ[k] ((a i).right l ⊗ₜ[k] r.right i)))
          = (counit (R := k) ((a i).right l) •
              (antipode k (r.right i) • (a i).left l)) ⊗ₜ[k] (1 : H) :=
      fun i _ l _ => fourLegMap_splitSecond_tmul _ _ _
    rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (hterm i hi)]
    rw [proj_apply m r, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← TensorProduct.sum_tmul]
    congr 1
    have : ∀ l ∈ (a i).index, counit (R := k) ((a i).right l) •
        (antipode k (r.right i) • (a i).left l)
        = antipode k (r.right i) • (counit (R := k) ((a i).right l) • (a i).left l) := by
      intro l _
      rw [smul_comm]
    rw [Finset.sum_congr rfl this, ← Finset.smul_sum, Coalgebra.Comodule.sum_counit_smul (a i)]
  rw [hstep1, hstep2, hstep3]

/-- The `k`-linear map `M^{co H} ⊗[k] H → M`, `n ⊗ h ↦ h • n`. -/
noncomputable def hopfModuleMap : (coinv k H M) ⊗[k] H →ₗ[k] M :=
  (actMap k H M) ∘ₗ (TensorProduct.comm k M H).toLinearMap ∘ₗ
    (LinearMap.rTensor H ((coinv k H M).subtype))

/-- `hopfModuleMap` on pure tensors: `n ⊗ h ↦ h • n`. -/
@[simp] lemma hopfModuleMap_tmul (n : coinv k H M) (h : H) :
    hopfModuleMap (k := k) (H := H) (M := M) (n ⊗ₜ[k] h) = h • (n : M) := by
  simp [hopfModuleMap]

/-- The `k`-linear map `M → M^{co H} ⊗[k] H`, `m ↦ ∑ P(m₍₀₎) ⊗ m₍₁₎`, inverse to
`HopfAlgebra.hopfModuleMap`. -/
noncomputable def hopfModuleInvMap [IsHopfModule k H M] : M →ₗ[k] (coinv k H M) ⊗[k] H :=
  (LinearMap.rTensor H ((proj k H M).codRestrict (coinv k H M) (proj_mem_coinv))) ∘ₗ
    (coact (R := k) (C := H))

/-- For a Hopf module, `hopfModuleMap` is a left inverse of `hopfModuleInvMap`. -/
lemma hopfModuleMap_hopfModuleInvMap [IsHopfModule k H M] (m : M) :
    hopfModuleMap (hopfModuleInvMap (k := k) (H := H) (M := M) m) = m := by
  classical
  set r := Coalgebra.Comodule.Repr.arbitrary k H m with hr
  let a : (i : r.ι) → Coalgebra.Comodule.Repr k H (r.left i) :=
    fun i => Coalgebra.Comodule.Repr.arbitrary k H (r.left i)
  let b : (i : r.ι) → Coalgebra.Repr k (r.right i) (H × H) := fun i => ℛ k (r.right i)
  -- rewrite the left-hand side as `collapse X`
  have hlhs : hopfModuleMap (hopfModuleInvMap (k := k) (H := H) (M := M) m)
      = collapse (k := k) (H := H) (M := M)
        (∑ i ∈ r.index, ∑ l ∈ (a i).index,
          (a i).left l ⊗ₜ[k] ((a i).right l ⊗ₜ[k] r.right i)) := by
    rw [hopfModuleInvMap]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← r.eq]
    simp only [map_sum, LinearMap.rTensor_tmul, hopfModuleMap_tmul, LinearMap.codRestrict_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [proj_apply (r.left i) (a i)]
    simp only [collapse_tmul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [mul_comm, mul_smul]
  -- and the right-hand side as `collapse Y`
  have hrhs : collapse (k := k) (H := H) (M := M)
      (∑ i ∈ r.index, ∑ j ∈ (b i).index,
        r.left i ⊗ₜ[k] ((b i).left j ⊗ₜ[k] (b i).right j)) = m := by
    simp only [map_sum, collapse_tmul]
    have hi : ∀ i ∈ r.index, ∑ j ∈ (b i).index,
        (antipode k ((b i).left j) * (b i).right j) • r.left i
        = counit (R := k) (r.right i) • r.left i := by
      intro i _
      rw [← Finset.sum_smul, HopfAlgebra.sum_antipode_mul_eq_smul (b i), smul_assoc, one_smul]
    rw [Finset.sum_congr rfl hi, Coalgebra.Comodule.sum_counit_smul r]
  rw [hlhs, Coalgebra.Comodule.sum_tmul_tmul_eq r a b]
  exact hrhs

/-- For a Hopf module, `hopfModuleInvMap` is a left inverse of `hopfModuleMap`. -/
lemma hopfModuleInvMap_hopfModuleMap [IsHopfModule k H M] (t : (coinv k H M) ⊗[k] H) :
    hopfModuleInvMap (hopfModuleMap t) = t := by
  classical
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul n h =>
    set rh := ℛ k h with hrh
    have hcoact : coact (R := k) (C := H) (h • (n : M))
        = ∑ j ∈ rh.index, (rh.left j • (n : M)) ⊗ₜ[k] rh.right j := by
      rw [IsHopfModule.coact_smul (k := k) h (n : M), mem_coinv_iff.1 n.2, ← rh.eq,
        TensorProduct.sum_tmul]
      simp
    rw [hopfModuleMap_tmul, hopfModuleInvMap]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [hcoact]
    simp only [map_sum, LinearMap.rTensor_tmul]
    have hj : ∀ j ∈ rh.index,
        (LinearMap.codRestrict (coinv k H M) (proj k H M) proj_mem_coinv) (rh.left j • (n : M))
            ⊗ₜ[k] rh.right j
          = n ⊗ₜ[k] (counit (R := k) (rh.left j) • rh.right j) := by
      intro j _
      rw [show (LinearMap.codRestrict (coinv k H M) (proj k H M) proj_mem_coinv)
            (rh.left j • (n : M)) = counit (R := k) (rh.left j) • n from
          Subtype.ext (proj_smul_of_mem_coinv (rh.left j) n.2),
        TensorProduct.smul_tmul]
    rw [Finset.sum_congr rfl hj, ← TensorProduct.tmul_sum, Coalgebra.sum_counit_smul rh]

/-- **Sweedler's fundamental theorem of Hopf modules** ([Sweedler], 4.1.1): for a Hopf module `M`
over a commutative Hopf algebra `H`, multiplication induces an isomorphism `M^{co H} ⊗[k] H ≅ M`. -/
noncomputable def hopfModuleEquiv [IsHopfModule k H M] : (coinv k H M) ⊗[k] H ≃ₗ[k] M :=
  LinearEquiv.ofLinearMap hopfModuleMap hopfModuleInvMap
    (by ext m; exact hopfModuleMap_hopfModuleInvMap m)
    (by ext t; exact hopfModuleInvMap_hopfModuleMap _)

/-- Sweedler's isomorphism sends `n ⊗ h` to `h • n`. -/
@[simp] lemma hopfModuleEquiv_tmul [IsHopfModule k H M] (n : coinv k H M) (h : H) :
    hopfModuleEquiv (n ⊗ₜ[k] h) = h • (n : M) := rfl

end Basic

section Free

variable {k H M : Type*} [Field k] [CommRing H] [hopf : HopfAlgebra k H]
  [AddCommGroup M] [modk : Module k M] [Module H M] [tower : IsScalarTower k H M]
  [comod : RightComodule k H M] [hopfmod : IsHopfModule k H M]

end Free

end HopfAlgebra
end
