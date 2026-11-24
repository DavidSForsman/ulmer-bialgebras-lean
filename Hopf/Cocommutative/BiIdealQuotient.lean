module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Hopf.Cocommutative.HopfBiIdeal

/-!
# Left bi-ideals are the same thing as quotient module coalgebras

Let `H` be a Hopf algebra over a field `k`.  Newman's correspondence
(`Hopf/Cocommutative/HopfBiIdeal.lean`) relates sub-Hopf algebras of `H` to *left bi-ideals*
of `H`, i.e. left ideals which are two-sided coideals.  In Newman's formulation the second side
of the correspondence is described as a *quotient*: a left bi-ideal `I` is exactly the kernel of
a surjection `π : H ↠ M` onto a left `H`-module coalgebra, the surjection being simultaneously
a map of coalgebras and a map of left `H`-modules.  This file proves the linear-algebra half of
that dictionary: the kernels of tensor products of surjections, and the coalgebra structure on the
quotient by a left bi-ideal.

## Main results

* `HopfAlgebra.Cocommutative.ker_map_of_surjective`,
  `HopfAlgebra.Cocommutative.ker_lTensor_of_surjective`: for a surjective `k`-linear `π : H → M`,
  the kernel of `π ⊗ π` is `I ⊗ H + H ⊗ I` and the kernel of `1 ⊗ π` is `H ⊗ I`, where `I = ker π`
  (here the ground ring being a field is used, through flatness);
* `HopfAlgebra.Cocommutative.mem_coinv_iff_lTensor_mkQ`: Newman's `μ I` is the space of coinvariants
  `{h | (1 ⊗ π) (Δ h) = h ⊗ π 1}` of the quotient `π : H ↠ H/I`;
* `HopfAlgebra.Cocommutative.quotComul`, `HopfAlgebra.Cocommutative.quotCounit`,
  `HopfAlgebra.Cocommutative.quotCoalgebra`: for a left bi-ideal `I`, the quotient `H ⧸ I` carries a
  coalgebra structure for which the projection is a morphism of coalgebras
  (`HopfAlgebra.Cocommutative.quotComul_mk`, `HopfAlgebra.Cocommutative.quotCounit_mk`).

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

/-! ### Kernels of tensor products of surjections -/

section Kernels

variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The image of `H ⊗ I → H ⊗ H` (induced by the inclusion `I ⊆ H`) is `rightTensor I`, the span of
the `h ⊗ x` with `x ∈ I`. -/
lemma range_lTensor_subtype (I : Submodule k H) :
    LinearMap.range (LinearMap.lTensor H I.subtype) = rightTensor I := by
  refine le_antisymm ?_ (rightTensor_le fun a x hx => ⟨a ⊗ₜ[k] ⟨x, hx⟩, by simp⟩)
  rintro _ ⟨s, rfl⟩
  induction s using TensorProduct.inductionOn with
  | tmul a y => exact tmul_mem_rightTensor a y.2
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

/-- The image of `I ⊗ H → H ⊗ H` (induced by the inclusion `I ⊆ H`) is `leftTensor I`, the span of
the `x ⊗ h` with `x ∈ I`. -/
lemma range_rTensor_subtype (I : Submodule k H) :
    LinearMap.range (LinearMap.rTensor H I.subtype) = leftTensor I := by
  refine le_antisymm ?_ (leftTensor_le fun x hx a => ⟨⟨x, hx⟩ ⊗ₜ[k] a, by simp⟩)
  rintro _ ⟨s, rfl⟩
  induction s using TensorProduct.inductionOn with
  | tmul y a => exact tmul_mem_leftTensor y.2 a
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

/-- `leftTensor ⊥ = ⊥`: the submodule `0 ⊗ H` of `H ⊗ H` is zero. -/
lemma leftTensor_bot : leftTensor (⊥ : Submodule k H) = ⊥ :=
  le_antisymm (leftTensor_le fun x hx a => by simp [(Submodule.mem_bot k).1 hx]) bot_le

/-- For a surjective linear map `π : H → M` with kernel `I`, the kernel of `π ⊗ π` is
`I ⊗ H + H ⊗ I`.  (Flatness of `H` and `M` over the field `k` is what makes this true.) -/
theorem ker_map_of_surjective (π : H →ₗ[k] M) (hπ : Function.Surjective π) :
    LinearMap.ker (TensorProduct.map π π)
      = leftTensor (LinearMap.ker π) ⊔ rightTensor (LinearMap.ker π) := by
  rw [TensorProduct.map_ker (LinearMap.exact_subtype_ker_map π) hπ
      (LinearMap.exact_subtype_ker_map π) hπ,
    range_lTensor_subtype, range_rTensor_subtype, sup_comm]

/-- For a surjective linear map `π : H → M` with kernel `I`, the kernel of `1 ⊗ π` is `H ⊗ I`. -/
theorem ker_lTensor_of_surjective (π : H →ₗ[k] M) (hπ : Function.Surjective π) :
    LinearMap.ker (LinearMap.lTensor H π) = rightTensor (LinearMap.ker π) := by
  have h : LinearMap.lTensor H π = TensorProduct.map (LinearMap.id (R := k) (M := H)) π := rfl
  rw [h, TensorProduct.map_ker (LinearMap.exact_subtype_ker_map (LinearMap.id (R := k) (M := H)))
      Function.surjective_id (LinearMap.exact_subtype_ker_map π) hπ,
    range_lTensor_subtype, range_rTensor_subtype, LinearMap.ker_id, leftTensor_bot, sup_bot_eq]

end Kernels

/-! ### Newman's `μ` as a space of coinvariants -/

/-- Newman's `λ`-kernel `μ I` is the space of coinvariants of the quotient `H ↠ H/I`: the
elements `h` with `(1 ⊗ π) (Δ h) = h ⊗ π 1`. -/
theorem mem_coinv_iff_lTensor_mkQ (I : Submodule k H) (h : H) :
    h ∈ coinv I ↔
      LinearMap.lTensor H I.mkQ (comul (R := k) h) = h ⊗ₜ[k] I.mkQ (1 : H) := by
  have hker : LinearMap.ker (LinearMap.lTensor H I.mkQ) = rightTensor I := by
    rw [ker_lTensor_of_surjective I.mkQ I.mkQ_surjective, Submodule.ker_mkQ]
  rw [mem_coinv, ← hker, LinearMap.mem_ker, map_sub, sub_eq_zero]
  simp

/-! ### The coalgebra structure on `H ⧸ I` -/

/-- The comultiplication induced on `H ⧸ I` by a left bi-ideal `I`. -/
noncomputable def quotComul {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    (H ⧸ I) →ₗ[k] (H ⧸ I) ⊗[k] (H ⧸ I) :=
  I.liftQ ((TensorProduct.map I.mkQ I.mkQ) ∘ₗ (comul (R := k) (A := H))) (by
    intro x hx
    have hmem := hI.comul_mem x hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
    have hle : leftTensor I ⊔ rightTensor I ≤
        LinearMap.ker (TensorProduct.map I.mkQ I.mkQ) := by
      refine sup_le ?_ ?_
      · refine leftTensor_le fun y hy a => ?_
        simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 hy]
      · refine rightTensor_le fun a y hy => ?_
        simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 hy]
    exact hle hmem)

/-- The counit induced on `H ⧸ I` by a left bi-ideal `I`. -/
noncomputable def quotCounit {I : Submodule k H} (hI : IsLeftBiIdeal I) : (H ⧸ I) →ₗ[k] k :=
  I.liftQ (counit (R := k) (A := H)) (fun x hx => hI.counit_eq_zero x hx)

/-- The comultiplication of `H ⧸ I` on a class: `Δ [x] = (π ⊗ π) (Δ x)`. -/
@[simp] lemma quotComul_mk {I : Submodule k H} (hI : IsLeftBiIdeal I) (x : H) :
    quotComul hI (Submodule.Quotient.mk x : H ⧸ I)
      = TensorProduct.map I.mkQ I.mkQ (comul (R := k) x) := rfl

/-- The counit of `H ⧸ I` on a class: `ε [x] = ε x`. -/
@[simp] lemma quotCounit_mk {I : Submodule k H} (hI : IsLeftBiIdeal I) (x : H) :
    quotCounit hI (Submodule.Quotient.mk x : H ⧸ I) = counit (R := k) x := rfl

/-- `Δ_{H/I} ∘ π = (π ⊗ π) ∘ Δ`, where `π : H → H ⧸ I` is the quotient map. -/
lemma quotComul_comp_mkQ {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    quotComul hI ∘ₗ I.mkQ = TensorProduct.map I.mkQ I.mkQ ∘ₗ comul (R := k) (A := H) := rfl

/-- For a left bi-ideal `I`, the comultiplication `quotComul` of `H ⧸ I` is coassociative. -/
theorem quotComul_coassoc {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    (TensorProduct.assoc k (H ⧸ I) (H ⧸ I) (H ⧸ I)).toLinearMap
        ∘ₗ LinearMap.rTensor (H ⧸ I) (quotComul hI) ∘ₗ quotComul hI
      = LinearMap.lTensor (H ⧸ I) (quotComul hI) ∘ₗ quotComul hI := by
  -- `rTensor Δ̄`, `lTensor Δ̄` and the associator commute with the quotient maps (`hA`, `hB`,
  -- `hC`), so on a class `[x]` coassociativity of `H ⧸ I` is the image of that of `H`.
  have hA : ∀ t : H ⊗[k] H,
      LinearMap.rTensor (H ⧸ I) (quotComul hI) (TensorProduct.map I.mkQ I.mkQ t)
        = TensorProduct.map (TensorProduct.map I.mkQ I.mkQ) I.mkQ
            (LinearMap.rTensor H (comul (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  have hB : ∀ t : H ⊗[k] H,
      LinearMap.lTensor (H ⧸ I) (quotComul hI) (TensorProduct.map I.mkQ I.mkQ t)
        = TensorProduct.map I.mkQ (TensorProduct.map I.mkQ I.mkQ)
            (LinearMap.lTensor H (comul (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  have hC : ∀ u : (H ⊗[k] H) ⊗[k] H,
      TensorProduct.assoc k (H ⧸ I) (H ⧸ I) (H ⧸ I)
          (TensorProduct.map (TensorProduct.map I.mkQ I.mkQ) I.mkQ u)
        = TensorProduct.map I.mkQ (TensorProduct.map I.mkQ I.mkQ)
            (TensorProduct.assoc k H H H u) := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul s c =>
      induction s using TensorProduct.inductionOn with
      | tmul a b => simp
      | add s1 s2 h1 h2 => simp only [add_tmul, map_add, h1, h2]
    | add u v hu hv => simp only [map_add, hu, hv]
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    have hco := congr($(Coalgebra.coassoc (R := k) (A := H)) x)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hco
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, quotComul_mk,
      hA, hB, hC, hco]

/-- Left counit law on `H ⧸ I`: `(ε ⊗ id) ∘ Δ = (x ↦ 1 ⊗ x)`. -/
theorem quot_rTensor_counit_comp_comul {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    LinearMap.rTensor (H ⧸ I) (quotCounit hI) ∘ₗ quotComul hI
      = (TensorProduct.mk k k (H ⧸ I)) 1 := by
  have hA : ∀ t : H ⊗[k] H,
      LinearMap.rTensor (H ⧸ I) (quotCounit hI) (TensorProduct.map I.mkQ I.mkQ t)
        = LinearMap.lTensor k I.mkQ (LinearMap.rTensor H (counit (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    have hco := congr($(Coalgebra.rTensor_counit_comp_comul (R := k) (A := H)) x)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hco
    simp only [LinearMap.coe_comp, Function.comp_apply, quotComul_mk, hA, hco,
      TensorProduct.mk_apply, LinearMap.lTensor_tmul, Submodule.mkQ_apply]

/-- Right counit law on `H ⧸ I`: `(id ⊗ ε) ∘ Δ = (x ↦ x ⊗ 1)`. -/
theorem quot_lTensor_counit_comp_comul {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    LinearMap.lTensor (H ⧸ I) (quotCounit hI) ∘ₗ quotComul hI
      = (TensorProduct.mk k (H ⧸ I) k).flip 1 := by
  have hA : ∀ t : H ⊗[k] H,
      LinearMap.lTensor (H ⧸ I) (quotCounit hI) (TensorProduct.map I.mkQ I.mkQ t)
        = LinearMap.rTensor k I.mkQ (LinearMap.lTensor H (counit (R := k) (A := H)) t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    have hco := congr($(Coalgebra.lTensor_counit_comp_comul (R := k) (A := H)) x)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hco
    simp only [LinearMap.coe_comp, Function.comp_apply, quotComul_mk, hA, hco,
      LinearMap.flip_apply, TensorProduct.mk_apply, LinearMap.rTensor_tmul, Submodule.mkQ_apply]

/-- The coalgebra structure on the quotient of `H` by a left bi-ideal. -/
@[instance_reducible]
noncomputable def quotCoalgebraStruct {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    CoalgebraStruct k (H ⧸ I) where
  comul := quotComul hI
  counit := quotCounit hI

/-- **The quotient of `H` by a left bi-ideal is a coalgebra**, and the projection is a morphism
of coalgebras (`quotComul_comp_mkQ`, `quotCounit_mk`). -/
@[instance_reducible]
noncomputable def quotCoalgebra {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    letI := quotCoalgebraStruct hI
    Coalgebra k (H ⧸ I) :=
  letI := quotCoalgebraStruct hI
  { coassoc := quotComul_coassoc hI
    rTensor_counit_comp_comul := quot_rTensor_counit_comp_comul hI
    lTensor_counit_comp_comul := quot_lTensor_counit_comp_comul hI }

/-! ### The `H`-module structure on `H ⧸ I` -/



/-! ### The kernel of a quotient module coalgebra is a left bi-ideal -/

/-! ### A quotient module coalgebra is determined by its bi-ideal -/

end HopfAlgebra.Cocommutative
