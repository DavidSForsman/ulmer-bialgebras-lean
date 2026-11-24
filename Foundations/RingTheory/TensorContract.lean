module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Contractions of a tensor product of vector spaces

For vector spaces `M`, `N` over a field `k` we consider the two *contraction* operators on
`M ⊗[k] N`:

* `TensorProduct.contractLeft θ : M ⊗[k] N →ₗ[k] N` for a functional `θ : M →ₗ[k] k`;
* `TensorProduct.contractRight θ : M ⊗[k] N →ₗ[k] M` for a functional `θ : N →ₗ[k] k`.

The main results say that a tensor is detected by its contractions.

These are the linear-algebra input to the fundamental theorem of coalgebras
(`Hopf/Basic/CoalgebraLocallyFinite.lean`).

## Main results

* `TensorProduct.mem_range_lTensor_of_forall_contractLeft_of_projective`: over a commutative ring,
  for `M` projective, if all left contractions of `z : M ⊗[k] N` lie in a submodule `E ≤ N`, then
  `z` lies in `M ⊗ E`;
* `TensorProduct.mem_range_lTensor_of_forall_contractLeft`: if all left contractions of
  `z : M ⊗[k] N` lie in a subspace `E ≤ N`, then `z` lies in `M ⊗ E`;
* `TensorProduct.mem_range_rTensor_of_forall_contractRight`: the mirror statement;
* `TensorProduct.mem_range_map_of_forall_contract`: if all contractions of `z : C ⊗[k] C` lie in a
  subspace `E ≤ C`, then `z` lies in `E ⊗ E`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

namespace TensorProduct

open TensorProduct

section CommRing

variable {k M N : Type*} [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Contraction of the left leg of a tensor product by a functional. -/
noncomputable def contractLeft (θ : M →ₗ[k] k) : M ⊗[k] N →ₗ[k] N :=
  (TensorProduct.lid k N).toLinearMap ∘ₗ LinearMap.rTensor N θ

/-- Contraction of the right leg of a tensor product by a functional. -/
noncomputable def contractRight (θ : N →ₗ[k] k) : M ⊗[k] N →ₗ[k] M :=
  (TensorProduct.rid k M).toLinearMap ∘ₗ LinearMap.lTensor M θ

/-- `contractLeft θ (m ⊗ₜ n) = θ m • n`. -/
@[simp] lemma contractLeft_tmul (θ : M →ₗ[k] k) (m : M) (n : N) :
    contractLeft (N := N) θ (m ⊗ₜ[k] n) = θ m • n := by
  simp [contractLeft]

/-- `contractRight θ (m ⊗ₜ n) = θ n • m`. -/
@[simp] lemma contractRight_tmul (θ : N →ₗ[k] k) (m : M) (n : N) :
    contractRight (M := M) θ (m ⊗ₜ[k] n) = θ n • m := by
  simp [contractRight]

/-! ### Compatibilities -/

/-- Contracting the left leg after swapping the factors is contracting the right leg:
`contractLeft θ (comm z) = contractRight θ z`. -/
lemma contractLeft_comm (θ : N →ₗ[k] k) (z : M ⊗[k] N) :
    contractLeft θ ((TensorProduct.comm k M N) z) = contractRight θ z := by
  induction z using TensorProduct.inductionOn with
  | tmul m n => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- For a subspace `E ≤ M`, swapping the factors commutes with the inclusions
`E ⊗ N → M ⊗ N` and `N ⊗ E → N ⊗ M`. -/
lemma comm_rTensor_subtype (E : Submodule k M) (w : (↥E) ⊗[k] N) :
    (TensorProduct.comm k M N) (LinearMap.rTensor N E.subtype w)
      = LinearMap.lTensor N E.subtype ((TensorProduct.comm k (↥E) N) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul e n => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- For a subspace `E ≤ N`, contracting the image of `z : M ⊗ E` in `M ⊗ N` by `Θ` is
contracting `z` by `Θ ∘ₗ E.subtype`. -/
lemma contractRight_lTensor_subtype (E : Submodule k N) (Θ : N →ₗ[k] k) (z : M ⊗[k] (↥E)) :
    contractRight Θ (LinearMap.lTensor M E.subtype z) = contractRight (Θ ∘ₗ E.subtype) z := by
  induction z using TensorProduct.inductionOn with
  | tmul m e => simp
  | add u v hu hv => simp only [map_add, hu, hv]

/-- **A dual basis detects a tensor by its contractions.** If `M` is projective and every left
contraction of `z : M ⊗[k] N` lies in a submodule `E` of `N`, then `z` lies in `M ⊗ E`. -/
theorem mem_range_lTensor_of_forall_contractLeft_of_projective [Module.Projective k M]
    (E : Submodule k N) (z : M ⊗[k] N) (h : ∀ θ : M →ₗ[k] k, contractLeft θ z ∈ E) :
    z ∈ LinearMap.range (LinearMap.lTensor M E.subtype) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.1 ‹Module.Projective k M›
  set f := finsuppScalarLeft k N M (LinearMap.rTensor N s z) with hf
  have hz : z = LinearMap.rTensor N (Finsupp.linearCombination k id)
      ((finsuppScalarLeft k N M).symm f) := by
    rw [hf, LinearEquiv.symm_apply_apply, ← LinearMap.rTensor_comp_apply, hs,
      LinearMap.rTensor_id, LinearMap.id_apply]
  have hmem : ∀ i, f i ∈ E := fun i => by
    rw [hf, finsuppScalarLeft_apply, ← LinearMap.rTensor_comp_apply]
    exact h _
  rw [hz, ← Finsupp.sum_single f, Finsupp.sum, map_sum, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [finsuppScalarLeft_symm_apply_single, LinearMap.rTensor_tmul,
    Finsupp.linearCombination_single, one_smul, id_eq]
  exact ⟨i ⊗ₜ[k] ⟨f i, hmem i⟩, rfl⟩

end CommRing

section Field

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The left contractions of a fixed tensor all lie in the span of a fixed finite set. -/
theorem exists_finset_forall_contractLeft (z : M ⊗[k] N) :
    ∃ S : Finset N, ∀ θ : M →ₗ[k] k, contractLeft θ z ∈ Submodule.span k (S : Set N) := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul m n =>
    refine ⟨{n}, fun θ => ?_⟩
    rw [contractLeft_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  | add u v hu hv =>
    obtain ⟨S, hS⟩ := hu
    obtain ⟨T, hT⟩ := hv
    refine ⟨S ∪ T, fun θ => ?_⟩
    rw [map_add]
    refine Submodule.add_mem _ (Submodule.span_mono ?_ (hS θ)) (Submodule.span_mono ?_ (hT θ))
    · intro y hy; simp only [Finset.coe_union, Set.mem_union]; exact Or.inl hy
    · intro y hy; simp only [Finset.coe_union, Set.mem_union]; exact Or.inr hy

/-! ### Detecting a tensor by its contractions -/

/-- If every left contraction of `z : M ⊗[k] N` lies in a subspace `E` of `N`, then `z` lies in
`M ⊗ E`. -/
theorem mem_range_lTensor_of_forall_contractLeft (E : Submodule k N) (z : M ⊗[k] N)
    (h : ∀ θ : M →ₗ[k] k, contractLeft θ z ∈ E) :
    z ∈ LinearMap.range (LinearMap.lTensor M E.subtype) := by
  classical
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := k) (M := M)
  set ψ : M ⊗[k] N ≃ₗ[k] (ι →₀ N) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl k N)).trans
      (TensorProduct.finsuppScalarLeft k N ι) with hψ
  have hψ_tmul : ∀ (m : M) (n : N) (i : ι), ψ (m ⊗ₜ[k] n) i = (b.repr m i) • n := by
    intro m n i
    simp [hψ, TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  have hψ_symm : ∀ (i : ι) (n : N), ψ.symm (Finsupp.single i n) = b i ⊗ₜ[k] n := by
    intro i n
    apply ψ.injective
    rw [LinearEquiv.apply_symm_apply]
    ext j
    rw [hψ_tmul]
    by_cases hij : i = j <;> simp [hij, eq_comm]
  have hdecomp : ∀ t : M ⊗[k] N, t = ∑ i ∈ (ψ t).support, b i ⊗ₜ[k] (ψ t i) := by
    intro t
    have h1 : ψ.symm (∑ i ∈ (ψ t).support, Finsupp.single i (ψ t i))
        = ∑ i ∈ (ψ t).support, b i ⊗ₜ[k] (ψ t i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => hψ_symm i _
    have h2 : ∑ i ∈ (ψ t).support, Finsupp.single i (ψ t i) = ψ t := by
      simpa [Finsupp.sum] using Finsupp.sum_single (ψ t)
    rw [← h1, h2, ψ.symm_apply_apply]
  -- the coordinates of a tensor are its contractions by the dual basis
  have hcoord : ∀ (t : M ⊗[k] N) (i : ι), ψ t i = contractLeft (b.coord i) t := by
    intro t i
    induction t using TensorProduct.inductionOn with
    | tmul m n => rw [hψ_tmul, contractLeft_tmul]; simp
    | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
  rw [hdecomp z]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact ⟨b i ⊗ₜ[k] (⟨ψ z i, by rw [hcoord z i]; exact h _⟩ : E), by simp⟩

/-- If every right contraction of `z : M ⊗[k] N` lies in a subspace `E` of `M`, then `z` lies in
`E ⊗ N`. -/
theorem mem_range_rTensor_of_forall_contractRight (E : Submodule k M) (z : M ⊗[k] N)
    (h : ∀ θ : N →ₗ[k] k, contractRight θ z ∈ E) :
    z ∈ LinearMap.range (LinearMap.rTensor N E.subtype) := by
  obtain ⟨w, hw⟩ := mem_range_lTensor_of_forall_contractLeft (M := N) E
    (TensorProduct.comm k M N z) (fun θ => by rw [contractLeft_comm θ z]; exact h θ)
  refine ⟨TensorProduct.comm k N (↥E) w, ?_⟩
  apply (TensorProduct.comm k M N).injective
  rw [comm_rTensor_subtype E ((TensorProduct.comm k N (↥E)) w), ← TensorProduct.comm_symm,
    LinearEquiv.symm_apply_apply, hw]

/-- If every contraction of `z : C ⊗[k] C` — on either side — lies in a subspace `E` of `C`, then
`z` lies in `E ⊗ E`. -/
theorem mem_range_map_of_forall_contract {C : Type*} [AddCommGroup C] [Module k C]
    (E : Submodule k C) (z : C ⊗[k] C)
    (hl : ∀ θ : C →ₗ[k] k, contractLeft θ z ∈ E)
    (hr : ∀ θ : C →ₗ[k] k, contractRight θ z ∈ E) :
    z ∈ LinearMap.range (TensorProduct.map E.subtype E.subtype) := by
  obtain ⟨z', hz'⟩ := mem_range_lTensor_of_forall_contractLeft E z hl
  -- contract the left leg of `z'` by functionals on `E`, extended to `C`
  have hz'r : ∀ θ : (↥E) →ₗ[k] k, contractRight (M := C) θ z' ∈ E := by
    intro θ
    obtain ⟨Θ, hΘ⟩ := LinearMap.exists_extend (p := E) (V' := k) θ
    have hcomm : contractRight (M := C) (N := C) Θ z = contractRight (M := C) (N := ↥E) θ z' := by
      rw [← hz', contractRight_lTensor_subtype E Θ z', hΘ]
    rw [← hcomm]
    exact hr Θ
  obtain ⟨z'', hz''⟩ := mem_range_rTensor_of_forall_contractRight (N := ↥E) E z' hz'r
  refine ⟨z'', ?_⟩
  rw [← hz', ← hz'']
  exact (DFunLike.congr_fun (LinearMap.lTensor_comp_rTensor (↥E) E.subtype E.subtype) z'').symm

end Field

end TensorProduct
