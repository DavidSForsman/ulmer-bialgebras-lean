module

public import Hopf.Cocommutative.HopfBiIdeal
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Relative tensor products `H ⊗_K M` over a subalgebra

Masuoka's proof of the surjectivity of Newman's correspondence (*On Hopf algebras with
cocommutative coradicals*, J. Algebra **144** (1991)) runs through the `H`-coring `H ⊗_K H`
attached to a sub-Hopf algebra `K ⊆ H`.  Since `K` is in general noncommutative, the tensor
product `H ⊗_K M` is not available in Mathlib; this file constructs it, for a `k`-module `M`
equipped with an action of `H`, as the quotient of `H ⊗[k] M` by the balanced relations
`x a ⊗ m - x ⊗ a • m`, `a ∈ K`.

Only the `k`-module structure of the quotient is needed, so an action of `H` on `M` is encoded
as an algebra map `A : H →ₐ[k] Module.End k M`; this avoids putting (diamond-prone) `Module H`
instances on quotient types.

## Main definitions

* `HopfAlgebra.Cocommutative.balAct K A` — the submodule of balanced relations in `H ⊗[k] M`;
* `HopfAlgebra.Cocommutative.RelT K A` — the relative tensor product `H ⊗_K M`;
* `HopfAlgebra.Cocommutative.rmk` — the canonical map `H → M → H ⊗_K M`;
* `HopfAlgebra.Cocommutative.actH`, `HopfAlgebra.Cocommutative.Q₂`,
  `HopfAlgebra.Cocommutative.act₂`, `HopfAlgebra.Cocommutative.Q₃` — the two corings `H ⊗_K H` and
  `H ⊗_K H ⊗_K H` used in the proof.

## References

* [A. Masuoka, *On Hopf algebras with cocommutative
  coradicals*][masuokaHopfAlgebrasCocommutative1991]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

universe u

variable {k H : Type u} [CommRing k] [Ring H] [Algebra k H]

section Def

variable {M : Type u} [AddCommGroup M] [Module k M]

/-- The `K`-balanced relations `x a ⊗ m - x ⊗ a • m` inside `H ⊗[k] M`. -/
def balAct (K : Submodule k H) (A : H →ₐ[k] Module.End k M) : Submodule k (H ⊗[k] M) :=
  Submodule.span k {t | ∃ (x : H) (m : M) (a : H), a ∈ K ∧ t = (x * a) ⊗ₜ[k] m - x ⊗ₜ[k] (A a m)}

/-- The relative tensor product `H ⊗_K M`. -/
abbrev RelT (K : Submodule k H) (A : H →ₐ[k] Module.End k M) := (H ⊗[k] M) ⧸ balAct K A

variable (K : Submodule k H) (A : H →ₐ[k] Module.End k M)

/-- The canonical map `H → M → H ⊗_K M`. -/
def rmk (x : H) (m : M) : RelT K A := Submodule.Quotient.mk (x ⊗ₜ[k] m)

/-- `rmk K A x m` is the class of `x ⊗ m` in `H ⊗_K M`. -/
lemma rmk_def (x : H) (m : M) : rmk K A x m = Submodule.Quotient.mk (x ⊗ₜ[k] m) := rfl

/-- For `a ∈ K`, `x a ⊗ m - x ⊗ a • m` lies in `balAct K A`. -/
lemma sub_mem_balAct (x : H) (m : M) {a : H} (ha : a ∈ K) :
    (x * a) ⊗ₜ[k] m - x ⊗ₜ[k] (A a m) ∈ balAct K A :=
  Submodule.subset_span ⟨x, m, a, ha, rfl⟩

/-- `balAct K A ≤ P` as soon as `P` contains every `x a ⊗ m - x ⊗ a • m` with `a ∈ K`. -/
lemma balAct_le {P : Submodule k (H ⊗[k] M)}
    (h : ∀ (x : H) (m : M), ∀ a ∈ K, (x * a) ⊗ₜ[k] m - x ⊗ₜ[k] (A a m) ∈ P) : balAct K A ≤ P := by
  refine Submodule.span_le.2 ?_
  rintro t ⟨x, m, a, ha, rfl⟩
  exact h x m a ha

/-- The defining relation of the relative tensor product. -/
lemma rmk_balanced (x : H) (m : M) {a : H} (ha : a ∈ K) :
    rmk K A (x * a) m = rmk K A x (A a m) := by
  rw [rmk_def, rmk_def, Submodule.Quotient.eq]
  exact sub_mem_balAct K A x m ha

/-- `0 ⊗ m = 0` in `H ⊗_K M`. -/
@[simp] lemma rmk_zero_left (m : M) : rmk K A 0 m = 0 := by
  rw [rmk_def, TensorProduct.zero_tmul, Submodule.Quotient.mk_zero]

/-- `(x + y) ⊗ m = x ⊗ m + y ⊗ m` in `H ⊗_K M`. -/
lemma rmk_add_left (x y : H) (m : M) : rmk K A (x + y) m = rmk K A x m + rmk K A y m := by
  rw [rmk_def, rmk_def, rmk_def, TensorProduct.add_tmul, Submodule.Quotient.mk_add]

/-- `(c • x) ⊗ m = c • (x ⊗ m)` in `H ⊗_K M`, for `c : k`. -/
lemma rmk_smul_left (c : k) (x : H) (m : M) : rmk K A (c • x) m = c • rmk K A x m := by
  have h : ((c • x) ⊗ₜ[k] m : H ⊗[k] M) = c • (x ⊗ₜ[k] m) := TensorProduct.smul_tmul' c x m
  rw [rmk_def, h]
  rfl

/-- `rmk` as a linear map in its second argument. -/
noncomputable def rmkR (x : H) : M →ₗ[k] RelT K A :=
  (balAct K A).mkQ ∘ₗ (TensorProduct.mk k H M x)

/-- `rmkR K A x m = rmk K A x m`. -/
@[simp] lemma rmkR_apply (x : H) (m : M) : rmkR K A x m = rmk K A x m := rfl

/-- Induction principle for the relative tensor product. -/
@[elab_as_elim]
theorem RelT.induction_on {motive : RelT K A → Prop} (t : RelT K A)
    (rmk : ∀ (x : H) (m : M), motive (HopfAlgebra.Cocommutative.rmk K A x m))
    (add : ∀ u v, motive u → motive v → motive (u + v)) : motive t := by
  induction t using Submodule.Quotient.induction_on with
  | H w =>
    induction w using TensorProduct.inductionOn with
    | tmul x m => exact rmk x m
    | add u v hu hv =>
        have h : (Submodule.Quotient.mk (u + v) : RelT K A) =
            Submodule.Quotient.mk u + Submodule.Quotient.mk v := rfl
        rw [h]; exact add _ _ hu hv

/-- A linear map out of the relative tensor product. -/
noncomputable def liftT {P : Type u} [AddCommGroup P] [Module k P] (f : H ⊗[k] M →ₗ[k] P)
    (hf : ∀ (x : H) (m : M), ∀ a ∈ K, f ((x * a) ⊗ₜ[k] m) = f (x ⊗ₜ[k] (A a m))) :
    RelT K A →ₗ[k] P :=
  Submodule.liftQ _ f (balAct_le K A fun x m a ha => by
    simp only [LinearMap.mem_ker, map_sub, hf x m a ha, sub_self])

/-- `liftT K A f hf (x ⊗ m) = f (x ⊗ m)`. -/
@[simp] lemma liftT_rmk {P : Type u} [AddCommGroup P] [Module k P] (f : H ⊗[k] M →ₗ[k] P)
    (hf : ∀ (x : H) (m : M), ∀ a ∈ K, f ((x * a) ⊗ₜ[k] m) = f (x ⊗ₜ[k] (A a m)))
    (x : H) (m : M) : liftT K A f hf (rmk K A x m) = f (x ⊗ₜ[k] m) := rfl

/-- Two linear maps out of the relative tensor product agreeing on `rmk` are equal. -/
theorem relT_ext {P : Type u} [AddCommGroup P] [Module k P] {f g : RelT K A →ₗ[k] P}
    (h : ∀ (x : H) (m : M), f (rmk K A x m) = g (rmk K A x m)) : f = g := by
  refine LinearMap.ext fun t => ?_
  induction t using RelT.induction_on with
  | rmk x m => exact h x m
  | add u v hu hv => rw [map_add, map_add, hu, hv]

end Def

/-! ### The two corings -/

section Corings

variable (K : Submodule k H)

/-- The action of `H` on itself by left multiplication. -/
noncomputable def actH : H →ₐ[k] Module.End k H := Algebra.lsmul k k H

/-- `actH x y = x * y`. -/
@[simp] lemma actH_apply (x y : H) : actH (k := k) x y = x * y := rfl

/-- The coring `H ⊗_K H`. -/
abbrev Q₂ := RelT K (actH (k := k) (H := H))

/-- Left multiplication by `x` on `H ⊗_K H`. -/
noncomputable def act₂Aux (x : H) : Q₂ (k := k) K →ₗ[k] Q₂ (k := k) K :=
  liftT K _ ((balAct K (actH (k := k) (H := H))).mkQ ∘ₗ
      LinearMap.rTensor H (LinearMap.mulLeft k x))
    (fun y m a ha => by
      have h1 : x * (y * a) = (x * y) * a := (mul_assoc x y a).symm
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply, h1]
      exact rmk_balanced K _ (x * y) m ha)

/-- `act₂Aux K x (y ⊗ m) = (x * y) ⊗ m` in `H ⊗_K H`. -/
@[simp] lemma act₂Aux_rmk (x y m : H) :
    act₂Aux K x (rmk K _ y m) = rmk K (actH (k := k) (H := H)) (x * y) m := rfl

/-- The action of `H` on the coring `H ⊗_K H` by left multiplication on the first factor. -/
noncomputable def act₂ : H →ₐ[k] Module.End k (Q₂ (k := k) K) where
  toFun := act₂Aux K
  map_one' := by
    refine relT_ext K _ fun x m => ?_
    simp [act₂Aux_rmk]
  map_mul' x y := by
    refine relT_ext K _ fun z m => ?_
    simp [act₂Aux_rmk, mul_assoc]
  map_zero' := by
    refine relT_ext K _ fun x m => ?_
    simp [act₂Aux_rmk]
  map_add' x y := by
    refine relT_ext K _ fun z m => ?_
    simp [act₂Aux_rmk, add_mul, rmk_add_left]
  commutes' c := by
    refine relT_ext K _ fun x m => ?_
    simp [act₂Aux_rmk, rmk_smul_left, Algebra.algebraMap_eq_smul_one]

/-- `act₂ K x (y ⊗_K m) = (x y) ⊗_K m`: `H` acts on `H ⊗_K H` by left multiplication on the first
factor. -/
@[simp] lemma act₂_apply_rmk (x y m : H) :
    act₂ K x (rmk K _ y m) = rmk K (actH (k := k) (H := H)) (x * y) m := rfl

/-- The coring `H ⊗_K H ⊗_K H`. -/
abbrev Q₃ := RelT K (act₂ (k := k) K)

end Corings

end HopfAlgebra.Cocommutative
