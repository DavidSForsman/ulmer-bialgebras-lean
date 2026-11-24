module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Subcoalgebras of a coalgebra over a field

Let `k` be a field and `C` a `k`-coalgebra.  A submodule `W ≤ C` is a **subcoalgebra** when the
comultiplication maps it into `W ⊗ W`, i.e. when `Δ x` lies in the image of `W ⊗ W → C ⊗ C` for
every `x ∈ W` (over a field that map is injective, so the image is a genuine copy of `W ⊗ W`).

This file develops the basic theory of subcoalgebras used by the coradical filtration
(`Hopf/Coradical/`):

* `UlmerBialgebras.Subcoalg.IsSubcoalgebra` — the predicate;
* `UlmerBialgebras.Subcoalg.subComul` — the induced comultiplication `W → W ⊗ W`, and
  `UlmerBialgebras.Subcoalg.subCoalgebra` — the induced coalgebra structure on `W`;
* `UlmerBialgebras.Subcoalg.isSubcoalgebra_sSup` — an arbitrary supremum of subcoalgebras is a
  subcoalgebra.

## Main results

* `UlmerBialgebras.Subcoalg.IsSubcoalgebra`: a submodule `W` is a subcoalgebra when the
  comultiplication maps it into the image of `W ⊗ W`.
* `UlmerBialgebras.Subcoalg.subCoalgebra`: the coalgebra structure on a subcoalgebra `W`, with
  comultiplication `UlmerBialgebras.Subcoalg.subComul`.
* `UlmerBialgebras.Subcoalg.isSubcoalgebra_sSup`: the supremum of a set of subcoalgebras is a
  subcoalgebra.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace UlmerBialgebras

namespace Subcoalg

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

/-- Over a field, `W ⊗ W → C ⊗ C` induced by the inclusion `W ⊆ C` is injective. -/
lemma injective_map_subtype (W : Submodule k C) :
    Function.Injective (TensorProduct.map W.subtype W.subtype) :=
  TensorProduct.map_injective_of_flat_flat _ _ W.subtype_injective W.subtype_injective

/-- Over a field, `W ⊗ (W ⊗ W) → C ⊗ (C ⊗ C)` induced by the inclusion `W ⊆ C` is injective. -/
lemma injective_map_subtype₃ (W : Submodule k C) :
    Function.Injective
      (TensorProduct.map W.subtype (TensorProduct.map W.subtype W.subtype)) :=
  TensorProduct.map_injective_of_flat_flat _ _ W.subtype_injective (injective_map_subtype W)

/-- Over a field, `id ⊗ ι : k ⊗ W → k ⊗ C` is injective, for `ι : W ⊆ C` the inclusion. -/
lemma injective_map_id_subtype (W : Submodule k C) :
    Function.Injective (TensorProduct.map (LinearMap.id (R := k) (M := k)) W.subtype) :=
  TensorProduct.map_injective_of_flat_flat _ _ Function.injective_id W.subtype_injective

/-- Over a field, `ι ⊗ id : W ⊗ k → C ⊗ k` is injective, for `ι : W ⊆ C` the inclusion. -/
lemma injective_map_subtype_id (W : Submodule k C) :
    Function.Injective (TensorProduct.map W.subtype (LinearMap.id (R := k) (M := k))) :=
  TensorProduct.map_injective_of_flat_flat _ _ W.subtype_injective Function.injective_id

variable [Coalgebra k C]

/-- A submodule of a coalgebra is a **subcoalgebra** if the comultiplication maps it into the
image of `W ⊗ W`. -/
def IsSubcoalgebra (W : Submodule k C) : Prop :=
  ∀ x ∈ W, comul (R := k) x ∈ LinearMap.range (TensorProduct.map W.subtype W.subtype)

section Comul

variable {W : Submodule k C} (hW : IsSubcoalgebra W)

/-- The comultiplication induced on a subcoalgebra. -/
noncomputable def subComul : W →ₗ[k] W ⊗[k] W :=
  (LinearEquiv.ofInjective (TensorProduct.map W.subtype W.subtype)
      (injective_map_subtype W)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (TensorProduct.map W.subtype W.subtype))
      (comul (R := k) ∘ₗ W.subtype) (fun x => hW x x.2)

/-- The defining property of the induced comultiplication. -/
theorem map_subtype_comp_subComul :
    TensorProduct.map W.subtype W.subtype ∘ₗ subComul hW = comul (R := k) ∘ₗ W.subtype := by
  ext x
  simp only [LinearMap.comp_apply, subComul]
  exact congrArg Subtype.val ((LinearEquiv.ofInjective _ _).apply_symm_apply
    (⟨comul (R := k) (x : C), hW x x.2⟩))

/-- The counit induced on a subcoalgebra. -/
noncomputable def subCounit (W : Submodule k C) : W →ₗ[k] k := counit (R := k) ∘ₗ W.subtype

private lemma rTensor_transfer :
    TensorProduct.map (TensorProduct.map W.subtype W.subtype) W.subtype ∘ₗ
        LinearMap.rTensor W (subComul hW)
      = LinearMap.rTensor C (comul (R := k)) ∘ₗ TensorProduct.map W.subtype W.subtype := by
  rw [LinearMap.rTensor, LinearMap.rTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    map_subtype_comp_subComul hW, LinearMap.comp_id, LinearMap.id_comp]

private lemma lTensor_transfer :
    TensorProduct.map W.subtype (TensorProduct.map W.subtype W.subtype) ∘ₗ
        LinearMap.lTensor W (subComul hW)
      = LinearMap.lTensor C (comul (R := k)) ∘ₗ TensorProduct.map W.subtype W.subtype := by
  rw [LinearMap.lTensor, LinearMap.lTensor, ← TensorProduct.map_comp, ← TensorProduct.map_comp,
    map_subtype_comp_subComul hW, LinearMap.comp_id, LinearMap.id_comp]

private lemma comp_assoc_transfer :
    TensorProduct.map W.subtype (TensorProduct.map W.subtype W.subtype) ∘ₗ
        ((TensorProduct.assoc k W W W : W ⊗[k] W ⊗[k] W →ₗ[k] W ⊗[k] (W ⊗[k] W)) ∘ₗ
          LinearMap.rTensor W (subComul hW) ∘ₗ subComul hW)
      = ((TensorProduct.assoc k C C C : C ⊗[k] C ⊗[k] C →ₗ[k] C ⊗[k] (C ⊗[k] C)) ∘ₗ
          LinearMap.rTensor C (comul (R := k)) ∘ₗ comul (R := k)) ∘ₗ W.subtype := by
  simp only [← LinearMap.comp_assoc, TensorProduct.map_map_comp_assoc_eq]
  simp only [LinearMap.comp_assoc]
  rw [← LinearMap.comp_assoc _ (LinearMap.rTensor W (subComul hW)), rTensor_transfer,
    LinearMap.comp_assoc, map_subtype_comp_subComul]

private lemma comp_lTensor_transfer :
    TensorProduct.map W.subtype (TensorProduct.map W.subtype W.subtype) ∘ₗ
        (LinearMap.lTensor W (subComul hW) ∘ₗ subComul hW)
      = (LinearMap.lTensor C (comul (R := k)) ∘ₗ comul (R := k)) ∘ₗ W.subtype := by
  rw [← LinearMap.comp_assoc, lTensor_transfer, LinearMap.comp_assoc, map_subtype_comp_subComul,
    LinearMap.comp_assoc]

/-- Coassociativity of the induced comultiplication. -/
theorem subComul_coassoc :
    (TensorProduct.assoc k W W W : W ⊗[k] W ⊗[k] W →ₗ[k] W ⊗[k] (W ⊗[k] W)) ∘ₗ
        LinearMap.rTensor W (subComul hW) ∘ₗ subComul hW
      = LinearMap.lTensor W (subComul hW) ∘ₗ subComul hW := by
  rw [← LinearMap.cancel_left (injective_map_subtype₃ W), comp_assoc_transfer, Coalgebra.coassoc,
    comp_lTensor_transfer]

private lemma rTensor_counit_transfer (W : Submodule k C) :
    TensorProduct.map (LinearMap.id (R := k) (M := k)) W.subtype ∘ₗ
        LinearMap.rTensor W (subCounit W)
      = LinearMap.rTensor C (counit (R := k)) ∘ₗ TensorProduct.map W.subtype W.subtype := by
  ext w₁ w₂
  simp [subCounit]

private lemma lTensor_counit_transfer (W : Submodule k C) :
    TensorProduct.map W.subtype (LinearMap.id (R := k) (M := k)) ∘ₗ
        LinearMap.lTensor W (subCounit W)
      = LinearMap.lTensor C (counit (R := k)) ∘ₗ TensorProduct.map W.subtype W.subtype := by
  ext w₁ w₂
  simp [subCounit]

/-- The left counit law for the induced structure. -/
theorem subComul_rTensor_counit :
    LinearMap.rTensor W (subCounit W) ∘ₗ subComul hW = TensorProduct.mk k k W 1 := by
  have hL : TensorProduct.map (LinearMap.id (R := k) (M := k)) W.subtype ∘ₗ
      (LinearMap.rTensor W (subCounit W) ∘ₗ subComul hW)
      = (LinearMap.rTensor C (counit (R := k)) ∘ₗ comul (R := k)) ∘ₗ W.subtype := by
    rw [← LinearMap.comp_assoc, rTensor_counit_transfer, LinearMap.comp_assoc,
      map_subtype_comp_subComul, LinearMap.comp_assoc]
  have hR : TensorProduct.map (LinearMap.id (R := k) (M := k)) W.subtype ∘ₗ
      (TensorProduct.mk k k W 1 : W →ₗ[k] k ⊗[k] W)
      = (TensorProduct.mk k k C 1 : C →ₗ[k] k ⊗[k] C) ∘ₗ W.subtype := by
    ext w; simp
  rw [← LinearMap.cancel_left (injective_map_id_subtype W), hL,
    Coalgebra.rTensor_counit_comp_comul, hR]

/-- The right counit law for the induced structure. -/
theorem subComul_lTensor_counit :
    LinearMap.lTensor W (subCounit W) ∘ₗ subComul hW = (TensorProduct.mk k W k).flip 1 := by
  have hL : TensorProduct.map W.subtype (LinearMap.id (R := k) (M := k)) ∘ₗ
      (LinearMap.lTensor W (subCounit W) ∘ₗ subComul hW)
      = (LinearMap.lTensor C (counit (R := k)) ∘ₗ comul (R := k)) ∘ₗ W.subtype := by
    rw [← LinearMap.comp_assoc, lTensor_counit_transfer, LinearMap.comp_assoc,
      map_subtype_comp_subComul, LinearMap.comp_assoc]
  have hR : TensorProduct.map W.subtype (LinearMap.id (R := k) (M := k)) ∘ₗ
      ((TensorProduct.mk k W k).flip 1 : W →ₗ[k] W ⊗[k] k)
      = ((TensorProduct.mk k C k).flip 1 : C →ₗ[k] C ⊗[k] k) ∘ₗ W.subtype := by
    ext w; simp
  rw [← LinearMap.cancel_left (injective_map_subtype_id W), hL,
    Coalgebra.lTensor_counit_comp_comul, hR]

/-- The coalgebra structure carried by a subcoalgebra. -/
@[instance_reducible]
noncomputable def subCoalgebra : Coalgebra k W where
  comul := subComul hW
  counit := subCounit W
  coassoc := subComul_coassoc hW
  rTensor_counit_comp_comul := subComul_rTensor_counit hW
  lTensor_counit_comp_comul := subComul_lTensor_counit hW

/-- A subcoalgebra of a cocommutative coalgebra is cocommutative. -/
theorem subComul_comm [Coalgebra.IsCocomm k C] :
    (TensorProduct.comm k W W : W ⊗[k] W →ₗ[k] W ⊗[k] W) ∘ₗ subComul hW = subComul hW := by
  have hcomm : TensorProduct.map W.subtype W.subtype ∘ₗ
      (TensorProduct.comm k W W : W ⊗[k] W →ₗ[k] W ⊗[k] W)
      = (TensorProduct.comm k C C : C ⊗[k] C →ₗ[k] C ⊗[k] C) ∘ₗ
          TensorProduct.map W.subtype W.subtype := by
    ext a b; simp
  have hL : TensorProduct.map W.subtype W.subtype ∘ₗ
      ((TensorProduct.comm k W W : W ⊗[k] W →ₗ[k] W ⊗[k] W) ∘ₗ subComul hW)
      = ((TensorProduct.comm k C C : C ⊗[k] C →ₗ[k] C ⊗[k] C) ∘ₗ comul (R := k)) ∘ₗ
          W.subtype := by
    rw [← LinearMap.comp_assoc, hcomm, LinearMap.comp_assoc, map_subtype_comp_subComul,
      LinearMap.comp_assoc]
  rw [← LinearMap.cancel_left (injective_map_subtype W), hL, Coalgebra.comm_comp_comul,
    map_subtype_comp_subComul]

end Comul

/-! ### Stability properties -/

/-- An arbitrary supremum of subcoalgebras is a subcoalgebra. -/
theorem isSubcoalgebra_sSup {S : Set (Submodule k C)} (hS : ∀ W ∈ S, IsSubcoalgebra W) :
    IsSubcoalgebra (sSup S) := by
  intro x hx
  -- the set of elements whose comultiplication lands in `sSup S ⊗ sSup S` is a submodule
  set E : Submodule k C := sSup S with hE
  have hsub : ∀ W ∈ S, W ≤ Submodule.comap (comul (R := k))
      (LinearMap.range (TensorProduct.map E.subtype E.subtype)) := by
    intro W hW y hy
    obtain ⟨t, ht⟩ := hS W hW y hy
    have hWE : W ≤ E := le_sSup hW
    refine ⟨TensorProduct.map (Submodule.inclusion hWE) (Submodule.inclusion hWE) t, ?_⟩
    rw [← ht, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    rfl
  have : E ≤ Submodule.comap (comul (R := k))
      (LinearMap.range (TensorProduct.map E.subtype E.subtype)) := sSup_le hsub
  exact this hx

end Subcoalg

end UlmerBialgebras
