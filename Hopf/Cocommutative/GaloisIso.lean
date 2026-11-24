module

public import Hopf.Cocommutative.RelTensor
public import Hopf.Coradical.Wedge
public import Hopf.Cocommutative.AntipodeAntiMul

/-!
# Takeuchi's isomorphism `H ⊗_K M ≅ (H ⧸ H K⁺) ⊗ M`

Let `K` be a sub-Hopf algebra of a Hopf algebra `H` over a field `k`, let `N = H K⁺ = τ K` and
`C = H ⧸ N`.  For every `k`-module `M` carrying an action `A` of `H` the two mutually inverse
maps

```
β : H ⊗_K M → C ⊗ M,   x ⊗ m ↦ x₁ ⊗ x₂ • m
γ : C ⊗ M → H ⊗_K M,   x ⊗ m ↦ x₁ ⊗ S x₂ • m
```

identify the relative tensor product with an ordinary one.  This is Takeuchi's Lemma 1.6, the
form in which Masuoka uses it (*On Hopf algebras with cocommutative coradicals*, Lemma 2.4(3));
no flatness hypothesis is needed.

## Main definitions and results

* `HopfAlgebra.Cocommutative.bet`, `HopfAlgebra.Cocommutative.gam` — the two maps;
* `HopfAlgebra.Cocommutative.bet_gam`, `HopfAlgebra.Cocommutative.gam_bet` — they are mutually
  inverse;
* `HopfAlgebra.Cocommutative.relTEquiv` — the resulting linear equivalence.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 1.6
* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991], Lemma 2.4(3)
* [S. U. Chase, M. E. Sweedler, *Hopf Algebras and Galois Theory*][chaseHopfAlgebrasGalois1969]
-/

@[expose] public section


open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

universe u

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### Two Hopf-algebraic identities -/

variable (k H) in
/-- The map `y ⊗ z ↦ y₁ ⊗ y₂ z`. -/
noncomputable def mulR : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  LinearMap.lTensor H (LinearMap.mul' k H) ∘ₗ (TensorProduct.assoc k H H H).toLinearMap ∘ₗ
    LinearMap.rTensor H (comul (R := k) (A := H))

variable (k H) in
/-- The map `x ↦ x₁ ⊗ S x₂`. -/
noncomputable def sAnti : H →ₗ[k] H ⊗[k] H :=
  LinearMap.lTensor H (antipode k) ∘ₗ comul

variable (k H) in
/-- The map `y ⊗ z ↦ y₁ ⊗ S(y₂) z`. -/
noncomputable def mulL : H ⊗[k] H →ₗ[k] H ⊗[k] H :=
  LinearMap.lTensor H (LinearMap.mul' k H) ∘ₗ (TensorProduct.assoc k H H H).toLinearMap ∘ₗ
    LinearMap.rTensor H (sAnti k H)

/-- `mulR` is `(id ⊗ μ) ∘ assoc ∘ (Δ ⊗ id)`. -/
lemma mulR_apply (w : H ⊗[k] H) :
    mulR k H w = LinearMap.lTensor H (LinearMap.mul' k H)
      ((TensorProduct.assoc k H H H) (LinearMap.rTensor H (comul (R := k) (A := H)) w)) := rfl

/-- `mulL` is `(id ⊗ μ) ∘ assoc ∘ (sAnti ⊗ id)`. -/
lemma mulL_apply (w : H ⊗[k] H) :
    mulL k H w = LinearMap.lTensor H (LinearMap.mul' k H)
      ((TensorProduct.assoc k H H H) (LinearMap.rTensor H (sAnti k H) w)) := rfl

/-- `mulR (y ⊗ z) = ∑ y₁ ⊗ y₂ z`, written as `(id ⊗ (· * z)) (Δ y)`. -/
@[simp] lemma mulR_tmul (y z : H) :
    mulR k H (y ⊗ₜ[k] z) = LinearMap.lTensor H ((LinearMap.mul k H).flip z) (comul (R := k) y) := by
  simp only [mulR, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  induction (comul (R := k) y) using TensorProduct.inductionOn with
  | tmul u v => simp
  | add s t hs ht =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, hs, ht]

/-- `sAnti x = (id ⊗ S) (Δ x) = ∑ x₁ ⊗ S x₂`. -/
@[simp] lemma sAnti_apply (x : H) :
    sAnti k H x = LinearMap.lTensor H (antipode k) (comul (R := k) x) := rfl

/-- Coassociativity applied to `x`: `assoc ((Δ ⊗ id) (Δ x)) = (id ⊗ Δ) (Δ x)`. -/
theorem coassoc_apply' (x : H) :
    (TensorProduct.assoc k H H H) (LinearMap.rTensor H (comul (R := k) (A := H)) (comul x))
      = LinearMap.lTensor H (comul (R := k) (A := H)) (comul x) := by
  have h := congr($(Coalgebra.coassoc (R := k) (A := H)) x)
  simp only [LinearMap.comp_apply] at h
  exact h

/-- The comultiplication of the first leg commutes with the antipode on the second. -/
theorem rTensor_comul_lTensor_antipode (w : H ⊗[k] H) :
    LinearMap.rTensor H (comul (R := k) (A := H)) (LinearMap.lTensor H (antipode k) w)
      = LinearMap.lTensor (H ⊗[k] H) (antipode k)
          (LinearMap.rTensor H (comul (R := k) (A := H)) w) := by
  have h : LinearMap.rTensor H (comul (R := k) (A := H)) ∘ₗ LinearMap.lTensor H (antipode k)
      = LinearMap.lTensor (H ⊗[k] H) (antipode k) ∘ₗ
        LinearMap.rTensor H (comul (R := k) (A := H)) := by
    rw [LinearMap.rTensor_comp_lTensor]
    rw [LinearMap.lTensor_def, LinearMap.rTensor_def, ← TensorProduct.map_comp]
    simp
  exact congr($h w)

/-- Associativity is natural in the antipode acting on the last leg. -/
theorem assoc_lTensor_antipode (w : (H ⊗[k] H) ⊗[k] H) :
    (TensorProduct.assoc k H H H) (LinearMap.lTensor (H ⊗[k] H) (antipode (R := k) (A := H)) w)
      = LinearMap.lTensor H (LinearMap.lTensor H (antipode k))
          ((TensorProduct.assoc k H H H) w) := by
  have h : (TensorProduct.assoc k H H H).toLinearMap ∘ₗ
      LinearMap.lTensor (H ⊗[k] H) (antipode (R := k) (A := H))
      = LinearMap.lTensor H (LinearMap.lTensor H (antipode k)) ∘ₗ
        (TensorProduct.assoc k H H H).toLinearMap := by
    ext x y z; simp
  exact congr($h w)

/-- **Coassociativity for `Ξ`**: `∑ (y₁)₁ ⊗ (y₁)₂ ⊗ S y₂ = ∑ y₁ ⊗ (y₂)₁ ⊗ S (y₂)₂`. -/
theorem assoc_rTensor_comul_sAnti (y : H) :
    (TensorProduct.assoc k H H H)
        (LinearMap.rTensor H (comul (R := k) (A := H)) (sAnti k H y))
      = LinearMap.lTensor H (sAnti k H) (comul (R := k) y) := by
  rw [sAnti_apply, rTensor_comul_lTensor_antipode, assoc_lTensor_antipode, coassoc_apply',
    ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  rfl

/-- `∑ x₁ ⊗ x₂ S x₃ = x ⊗ 1`. -/
theorem mulR_comp_sAnti : mulR k H ∘ₗ sAnti k H = (TensorProduct.mk k H H).flip 1 := by
  have step1 := rTensor_comul_lTensor_antipode (k := k) (H := H)
  have step2 := assoc_lTensor_antipode (k := k) (H := H)
  ext x
  rw [LinearMap.comp_apply, mulR_apply, sAnti_apply, step1, step2, coassoc_apply']
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.comp_apply,
    ← LinearMap.lTensor_comp, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_lTensor_comul]
  have h3 : LinearMap.lTensor H (Algebra.linearMap k H ∘ₗ (counit (R := k) (A := H))) ∘ₗ
      (comul (R := k) (A := H)) = (TensorProduct.mk k H H).flip 1 := by
    ext y; simp [LinearMap.lTensor_comp]
  exact congr($h3 x)

/-- `∑ x₁ ⊗ S(x₂) x₃ = x ⊗ 1`. -/
theorem mulL_comp_comul :
    mulL k H ∘ₗ (comul (R := k) (A := H)) = (TensorProduct.mk k H H).flip 1 := by
  have step1 : ∀ w : H ⊗[k] H,
      LinearMap.rTensor H (sAnti k H) w
        = LinearMap.rTensor H (LinearMap.lTensor H (antipode k))
            (LinearMap.rTensor H (comul (R := k) (A := H)) w) := by
    intro w
    have h : LinearMap.rTensor H (sAnti k H)
        = LinearMap.rTensor H (LinearMap.lTensor H (antipode k)) ∘ₗ
          LinearMap.rTensor H (comul (R := k) (A := H)) := by
      rw [← LinearMap.rTensor_comp, sAnti]
    exact congr($h w)
  have step2 : ∀ w : (H ⊗[k] H) ⊗[k] H,
      (TensorProduct.assoc k H H H)
          (LinearMap.rTensor H (LinearMap.lTensor H (antipode (R := k) (A := H))) w)
      = LinearMap.lTensor H (LinearMap.rTensor H (antipode k))
          ((TensorProduct.assoc k H H H) w) := by
    intro w
    have h : (TensorProduct.assoc k H H H).toLinearMap ∘ₗ
        LinearMap.rTensor H (LinearMap.lTensor H (antipode (R := k) (A := H)))
        = LinearMap.lTensor H (LinearMap.rTensor H (antipode k)) ∘ₗ
          (TensorProduct.assoc k H H H).toLinearMap := by
      ext x y z; simp
    exact congr($h w)
  ext x
  rw [LinearMap.comp_apply, mulL_apply, step1, step2, coassoc_apply']
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, ← LinearMap.comp_apply,
    ← LinearMap.lTensor_comp, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul]
  have h3 : LinearMap.lTensor H (Algebra.linearMap k H ∘ₗ (counit (R := k) (A := H))) ∘ₗ
      (comul (R := k) (A := H)) = (TensorProduct.mk k H H).flip 1 := by
    ext y; simp [LinearMap.lTensor_comp]
  exact congr($h3 x)

/-! ### The two maps -/

section Maps

variable {M : Type u} [AddCommGroup M] [Module k M]

/-- The action map `H ⊗ M → M`. -/
noncomputable def actLin (A : H →ₐ[k] Module.End k M) : H ⊗[k] M →ₗ[k] M :=
  TensorProduct.lift A.toLinearMap

/-- `actLin A (x ⊗ m) = A x m`. -/
@[simp] lemma actLin_tmul (A : H →ₐ[k] Module.End k M) (x : H) (m : M) :
    actLin A (x ⊗ₜ[k] m) = A x m := rfl

/-- The action of `H` on a fixed element `m`. -/
noncomputable def actOn (A : H →ₐ[k] Module.End k M) (m : M) : H →ₗ[k] M :=
  (LinearMap.applyₗ m) ∘ₗ A.toLinearMap

/-- `actOn A m x = A x m`, the action of `x` on `m`. -/
@[simp] lemma actOn_apply (A : H →ₐ[k] Module.End k M) (m : M) (x : H) :
    actOn A m x = A x m := rfl

variable (K : Subalgebra k H) (A : H →ₐ[k] Module.End k M)

/-- The underlying map of `β` on `H ⊗[k] M`. -/
noncomputable def betRaw :
    H ⊗[k] M →ₗ[k] (H ⧸ HopfAlgebra.Cocommutative.tau K.toSubmodule) ⊗[k] M :=
  TensorProduct.map (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ (actLin A) ∘ₗ
    (TensorProduct.assoc k H H M).toLinearMap ∘ₗ
    LinearMap.rTensor M (comul (R := k) (A := H))

/-- `betRaw (x ⊗ m) = ∑ [x₁] ⊗ x₂ • m`, written as `(mkQ ⊗ actOn A m) (Δ x)`. -/
lemma betRaw_tmul (x : H) (m : M) :
    betRaw K A (x ⊗ₜ[k] m)
      = TensorProduct.map (tau K.toSubmodule).mkQ (actOn A m) (comul (R := k) x) := by
  simp only [betRaw, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  induction (comul (R := k) x) using TensorProduct.inductionOn with
  | tmul u v => simp
  | add s t hs ht => rw [TensorProduct.add_tmul, map_add, map_add, map_add, hs, ht]

/-- The underlying map of `γ` on `H ⊗[k] M`. -/
noncomputable def gamRaw : H ⊗[k] M →ₗ[k] RelT K.toSubmodule A :=
  (balAct K.toSubmodule A).mkQ ∘ₗ TensorProduct.map LinearMap.id (actLin A) ∘ₗ
    (TensorProduct.assoc k H H M).toLinearMap ∘ₗ LinearMap.rTensor M (sAnti k H)

/-- The map `H ⊗ H → H ⊗_K M`, `y ⊗ z ↦ y ⊗ z • m`. -/
noncomputable def rmkOn (m : M) : H ⊗[k] H →ₗ[k] RelT K.toSubmodule A :=
  (balAct K.toSubmodule A).mkQ ∘ₗ TensorProduct.map LinearMap.id (actOn A m)

/-- `rmkOn K A m (y ⊗ z) = y ⊗ A z m` in `H ⊗_K M`. -/
@[simp] lemma rmkOn_tmul (m : M) (y z : H) :
    rmkOn K A m (y ⊗ₜ[k] z) = rmk K.toSubmodule A y (A z m) := rfl

/-- `gamRaw (x ⊗ m) = ∑ x₁ ⊗ S x₂ • m` in `H ⊗_K M`, written via `rmkOn` and `sAnti`. -/
lemma gamRaw_tmul (x : H) (m : M) :
    gamRaw K A (x ⊗ₜ[k] m) = rmkOn K A m (sAnti k H x) := by
  simp only [gamRaw, rmkOn, LinearMap.comp_apply, LinearMap.rTensor_tmul]
  induction (sAnti k H x) using TensorProduct.inductionOn with
  | tmul u v => simp
  | add s t hs ht =>
      rw [TensorProduct.add_tmul, map_add, map_add, map_add, map_add, hs, ht, ← map_add,
        ← map_add]

end Maps

/-! ### The isomorphism -/

section Iso

variable {M : Type u} [AddCommGroup M] [Module k M]
variable {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) (A : H →ₐ[k] Module.End k M)

/-- `x a ≡ ε a • x` modulo `τ K`, for `a ∈ K`. -/
theorem mkQ_mul_mem (x : H) {a : H} (ha : a ∈ K) :
    (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ (x * a)
      = (counit (R := k) a) • (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ x := by
  have hmem : x * a - counit (R := k) a • x ∈ HopfAlgebra.Cocommutative.tau K.toSubmodule := by
    have h1 : x * (a - (counit (R := k) a) • (1 : H)) ∈ tau K.toSubmodule :=
      mul_mem_tau x ⟨Submodule.sub_mem _ ha (Submodule.smul_mem _ _ K.one_mem), by
        simp [map_smul]⟩
    have h2 : x * (a - (counit (R := k) a) • (1 : H)) = x * a - counit (R := k) a • x := by
      rw [mul_sub, mul_smul_comm, mul_one]
    rwa [h2] at h1
  rw [← sub_eq_zero, ← map_smul, ← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).2 hmem

/-- Compatibility of `β` with the action: `β (y ⊗ z • m) = ∑ y₁ ⊗ (y₂ z) • m`. -/
lemma betRaw_map_actOn (m : M) (w : H ⊗[k] H) :
    betRaw K A (TensorProduct.map LinearMap.id (actOn A m) w)
      = TensorProduct.map (tau K.toSubmodule).mkQ (actOn A m) (mulR k H w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
      rw [TensorProduct.map_tmul, LinearMap.id_coe, id_eq, betRaw_tmul, mulR_tmul]
      induction (comul (R := k) y) using TensorProduct.inductionOn with
      | tmul u v => simp [map_mul, mul_apply_eq_comp]
      | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  | add s t hs ht => rw [map_add, map_add, map_add, map_add, hs, ht]

include hK

/-- A finite representation of `Δ a` with both legs in `K`, for `a ∈ K`. -/
theorem exists_comul_repr_mem {a : H} (ha : a ∈ K) :
    ∃ (ι : Type u) (t : Finset ι) (Y Z : ι → H), (∀ i, Y i ∈ K) ∧ (∀ i, Z i ∈ K) ∧
      comul (R := k) a = ∑ i ∈ t, Y i ⊗ₜ[k] Z i := by
  classical
  have hmem : comul (R := k) a ∈ Coalgebra.Coradical.tens K.toSubmodule K.toSubmodule :=
    Coalgebra.Coradical.comul_mem_tens (fun x hx => hK.comul_mem x hx) ha
  rw [Coalgebra.Coradical.mem_tens_iff_mem_range] at hmem
  obtain ⟨W, hW⟩ := hmem
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset W
  refine ⟨(↥K.toSubmodule) × (↥K.toSubmodule), s, fun i => (i.1 : H), fun i => (i.2 : H),
    fun i => i.1.2, fun i => i.2.2, ?_⟩
  rw [← hW, hs, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- `β` is `K`-balanced. -/
theorem betRaw_balanced (x : H) (m : M) {a : H} (ha : a ∈ K) :
    betRaw K A ((x * a) ⊗ₜ[k] m) = betRaw K A (x ⊗ₜ[k] (A a m)) := by
  classical
  obtain ⟨ι, t, Y, Z, hY, hZ, hcomula⟩ := exists_comul_repr_mem hK ha
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset (comul (R := k) x)
  have hcounit : ∑ i ∈ t, (counit (R := k) (Y i)) • Z i = a := by
    have h : (TensorProduct.lid k H)
        (LinearMap.rTensor H (counit (R := k) (A := H)) (comul (R := k) a)) = a := by
      have h0 := congr($(Coalgebra.rTensor_counit_comp_comul (R := k) (A := H)) a)
      simp only [LinearMap.comp_apply] at h0
      rw [h0]
      simp
    rw [hcomula] at h
    simpa using h
  rw [betRaw_tmul, betRaw_tmul, Bialgebra.comul_mul, hs, hcomula, Finset.sum_mul_sum,
    map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  have hterm : ∀ i ∈ t, TensorProduct.map (tau K.toSubmodule).mkQ (actOn A m)
      ((j.1 ⊗ₜ[k] j.2 : H ⊗[k] H) * (Y i ⊗ₜ[k] Z i))
      = (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ j.1 ⊗ₜ[k]
          ((counit (R := k) (Y i)) • (A (j.2 * Z i) m)) := by
    intro i _
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    simp only [TensorProduct.map_tmul, actOn_apply]
    rw [mkQ_mul_mem j.1 (hY i), TensorProduct.smul_tmul]
  rw [Finset.sum_congr rfl hterm, ← TensorProduct.tmul_sum]
  simp only [TensorProduct.map_tmul, actOn_apply]
  congr 1
  rw [← hcounit, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_mul,
    mul_apply_eq_comp]

/-- `γ` kills `N ⊗ M`, `N = τ K`. -/
theorem gamRaw_eq_zero_of_mem_tau {n : H} (hn : n ∈ tau K.toSubmodule) (m : M) :
    gamRaw K A (n ⊗ₜ[k] m) = 0 := by
  classical
  have hle : HopfAlgebra.Cocommutative.tau K.toSubmodule ≤
      LinearMap.ker (gamRaw K A ∘ₗ (TensorProduct.mk k H M).flip m) := by
    refine HopfAlgebra.Cocommutative.tau_le fun u a ha => ?_
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    obtain ⟨ι, t, Y, Z, hY, hZ, hcomula⟩ := exists_comul_repr_mem hK ha.1
    obtain ⟨s, hs⟩ := TensorProduct.exists_finset (comul (R := k) u)
    -- the antipode identity for `a`
    have hann : ∑ i ∈ t, Y i * antipode k (Z i) = 0 := by
      have h := HopfAlgebra.sum_mul_antipode_eq_smul
        (Coalgebra.Repr.mk (R := k) (a := a) t Y Z hcomula.symm)
      rw [ha.2, zero_smul] at h
      exact h
    -- expand
    rw [gamRaw_tmul, sAnti_apply, Bialgebra.comul_mul, hs, hcomula, Finset.sum_mul_sum]
    rw [map_sum, map_sum]
    have hterm : ∀ j ∈ s, (rmkOn K A m) (LinearMap.lTensor H (antipode k)
        (∑ i ∈ t, (j.1 ⊗ₜ[k] j.2 : H ⊗[k] H) * (Y i ⊗ₜ[k] Z i))) = 0 := by
      intro j _
      rw [map_sum, map_sum]
      have hsum : ∀ i ∈ t, (rmkOn K A m) (LinearMap.lTensor H (antipode k)
          ((j.1 ⊗ₜ[k] j.2 : H ⊗[k] H) * (Y i ⊗ₜ[k] Z i)))
          = rmkR K.toSubmodule A j.1
              (actOn A m (Y i * antipode k (Z i) * antipode k j.2)) := by
        intro i _
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp only [LinearMap.lTensor_tmul, rmkOn_tmul, rmkR_apply, actOn_apply]
        rw [HopfAlgebra.Cocommutative.antipode_mul, rmk_balanced K.toSubmodule A j.1 _ (hY i)]
        simp only [map_mul, mul_apply_eq_comp]
      rw [Finset.sum_congr rfl hsum, ← map_sum, ← map_sum, ← Finset.sum_mul, hann, zero_mul,
        map_zero, map_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const_zero]
  simpa using hle hn

/-- **Takeuchi's map** `β : H ⊗_K M → (H ⧸ H K⁺) ⊗ M`, `x ⊗ m ↦ x₁ ⊗ x₂ • m`. -/
noncomputable def bet : RelT K.toSubmodule A →ₗ[k] (H ⧸ tau K.toSubmodule) ⊗[k] M :=
  liftT K.toSubmodule A (betRaw K A) (fun x m _ ha => betRaw_balanced hK A x m ha)

/-- `β (x ⊗_K m) = betRaw (x ⊗ m)`. -/
@[simp] lemma bet_rmk (x : H) (m : M) :
    bet hK A (rmk K.toSubmodule A x m) = betRaw K A (x ⊗ₜ[k] m) := rfl

/-- **Takeuchi's inverse map** `γ : (H ⧸ H K⁺) ⊗ M → H ⊗_K M`, `x ⊗ m ↦ x₁ ⊗ S x₂ • m`. -/
noncomputable def gam : (H ⧸ tau K.toSubmodule) ⊗[k] M →ₗ[k] RelT K.toSubmodule A :=
  TensorProduct.lift (Submodule.liftQ _ (TensorProduct.curry (gamRaw K A))
    (by
      intro n hn
      refine LinearMap.ext fun m => ?_
      simpa using gamRaw_eq_zero_of_mem_tau hK A hn m))

/-- `γ ([x] ⊗ m) = gamRaw (x ⊗ m)`. -/
@[simp] lemma gam_tmul (x : H) (m : M) :
    gam hK A ((tau K.toSubmodule).mkQ x ⊗ₜ[k] m) = gamRaw K A (x ⊗ₜ[k] m) := rfl

/-- `β` on the class of `w ∈ H ⊗[k] M` is `betRaw w`. -/
@[simp] lemma bet_mkQ (w : H ⊗[k] M) :
    bet hK A ((balAct K.toSubmodule A).mkQ w) = betRaw K A w := rfl

/-- Compatibility of `γ` with the action: `γ (p y ⊗ z • m) = ∑ y₁ ⊗ (S y₂ z) • m`. -/
lemma gam_map_actOn (m : M) (w : H ⊗[k] H) :
    gam hK A (TensorProduct.map (HopfAlgebra.Cocommutative.tau K.toSubmodule).mkQ (actOn A m) w)
      = rmkOn K A m (mulL k H w) := by
  induction w using TensorProduct.inductionOn with
  | tmul y z =>
      rw [TensorProduct.map_tmul, actOn_apply, gam_tmul, gamRaw_tmul, mulL]
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul]
      induction (sAnti k H y) using TensorProduct.inductionOn with
      | tmul u v => simp [map_mul, mul_apply_eq_comp]
      | add s t hs ht =>
          rw [map_add, TensorProduct.add_tmul, map_add, map_add, map_add, hs, ht]
  | add s t hs ht => rw [map_add, map_add, hs, ht, ← map_add, ← map_add]

/-- `β ∘ γ = id` on `(H ⧸ H K⁺) ⊗ M`. -/
theorem bet_gam (z : (H ⧸ tau K.toSubmodule) ⊗[k] M) : bet hK A (gam hK A z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul c m =>
      induction c using Submodule.Quotient.induction_on with
      | H x =>
          rw [show (Submodule.Quotient.mk x : H ⧸ HopfAlgebra.Cocommutative.tau K.toSubmodule)
              = (tau K.toSubmodule).mkQ x from rfl, gam_tmul, gamRaw_tmul, rmkOn,
            LinearMap.comp_apply, bet_mkQ, betRaw_map_actOn,
            show mulR k H (sAnti k H x) = x ⊗ₜ[k] (1 : H) from congr($mulR_comp_sAnti x)]
          simp
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- `γ ∘ β = id` on `H ⊗_K M`. -/
theorem gam_bet (t : RelT K.toSubmodule A) : gam hK A (bet hK A t) = t := by
  induction t using RelT.induction_on with
  | rmk x m =>
      rw [bet_rmk, betRaw_tmul, gam_map_actOn,
        show mulL k H (comul (R := k) x) = x ⊗ₜ[k] (1 : H) from congr($mulL_comp_comul x)]
      simp
  | add u v hu hv => rw [map_add, map_add, hu, hv]

/-- **Takeuchi's isomorphism** `H ⊗_K M ≅ (H ⧸ H K⁺) ⊗ M`. -/
noncomputable def relTEquiv :
    RelT K.toSubmodule A ≃ₗ[k] (H ⧸ HopfAlgebra.Cocommutative.tau K.toSubmodule) ⊗[k] M :=
  LinearEquiv.ofLinearMap (bet hK A) (gam hK A)
    (LinearMap.ext fun z => bet_gam hK A z) (LinearMap.ext fun t => gam_bet hK A t)

/-- Takeuchi's map `β : H ⊗_K M → (H ⧸ H K⁺) ⊗ M` is injective. -/
theorem bet_injective : Function.Injective (bet hK A) :=
  (relTEquiv hK A).injective

end Iso

end HopfAlgebra.Cocommutative
