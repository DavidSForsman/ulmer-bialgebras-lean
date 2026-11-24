module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Submodules of a tensor product over a field

This file collects the elementary facts about the submodules `X ⊗ Y ⊆ M ⊗ N` that are needed for
the theory of wedge products and coradical filtrations of coalgebras.  Everything here is
ordinary (flat) linear algebra over a field.

## Main results

* `Coalgebra.Coradical.tens` — the submodule `X ⊗ Y` of `M ⊗ N`, `Coalgebra.Coradical.tens_le_iff`
  its universal property, `Coalgebra.Coradical.tens_mono` monotonicity;
* `Coalgebra.Coradical.ker_lTensor` / `Coalgebra.Coradical.ker_rTensor` — `ker (1 ⊗ f) = M ⊗ ker f`
  and `ker (f ⊗ 1) = ker f ⊗ N`;
* `Coalgebra.Coradical.ker_map` — `ker (f ⊗ g) = ker f ⊗ N + M ⊗ ker g` for surjective `f`, `g`;
* `Coalgebra.Coradical.tens_top_inf_top_tens` — `(X ⊗ N) ⊓ (M ⊗ Y) = X ⊗ Y`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
-/

@[expose] public section

open TensorProduct

namespace Coalgebra.Coradical

variable {k M N P Q : Type*} [Field k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup P] [Module k P] [AddCommGroup Q] [Module k Q]

/-- The submodule `X ⊗ Y` of `M ⊗ N`, for submodules `X ≤ M` and `Y ≤ N`. -/
noncomputable def tens (X : Submodule k M) (Y : Submodule k N) : Submodule k (M ⊗[k] N) :=
  Submodule.map₂ (TensorProduct.mk k M N) X Y

/-- `tens X Y ≤ Z` iff `x ⊗ y ∈ Z` for all `x ∈ X` and `y ∈ Y`. -/
theorem tens_le_iff {X : Submodule k M} {Y : Submodule k N} {Z : Submodule k (M ⊗[k] N)} :
    tens X Y ≤ Z ↔ ∀ x ∈ X, ∀ y ∈ Y, x ⊗ₜ[k] y ∈ Z :=
  Submodule.map₂_le

/-- `x ⊗ y ∈ X ⊗ Y` for `x ∈ X`, `y ∈ Y`. -/
theorem tmul_mem_tens {X : Submodule k M} {Y : Submodule k N} {x : M} {y : N}
    (hx : x ∈ X) (hy : y ∈ Y) : x ⊗ₜ[k] y ∈ tens X Y :=
  Submodule.apply_mem_map₂ _ hx hy

/-- `X ⊗ Y` is monotone in `X` and `Y`. -/
theorem tens_mono {X X' : Submodule k M} {Y Y' : Submodule k N} (hX : X ≤ X') (hY : Y ≤ Y') :
    tens X Y ≤ tens X' Y' :=
  Submodule.map₂_le_map₂ hX hY

/-- `X ⊗ Y` is the range of `X ⊗ Y → M ⊗ N`. -/
theorem tens_eq_range (X : Submodule k M) (Y : Submodule k N) :
    tens X Y = LinearMap.range (map X.subtype Y.subtype) := by
  rw [tens, ← TensorProduct.range_mapIncl]

/-- Membership in `X ⊗ Y` is membership in the range of `X ⊗ Y → M ⊗ N`. -/
theorem mem_tens_iff_mem_range {X : Submodule k M} {Y : Submodule k N} {t : M ⊗[k] N} :
    t ∈ tens X Y ↔ t ∈ LinearMap.range (map X.subtype Y.subtype) := by
  rw [tens_eq_range]

/-- The range of `M ⊗ Y → M ⊗ N` is `M ⊗ Y`. -/
theorem range_lTensor_subtype (Y : Submodule k N) :
    LinearMap.range (LinearMap.lTensor M Y.subtype) = tens (⊤ : Submodule k M) Y := by
  refine le_antisymm ?_ (tens_le_iff.2 fun x _ y hy => ⟨x ⊗ₜ[k] ⟨y, hy⟩, by simp⟩)
  rintro _ ⟨s, rfl⟩
  induction s using TensorProduct.inductionOn with
  | tmul x y => exact tmul_mem_tens Submodule.mem_top y.2
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

/-- The range of `X ⊗ N → M ⊗ N` is `X ⊗ N`. -/
theorem range_rTensor_subtype (X : Submodule k M) :
    LinearMap.range (LinearMap.rTensor N X.subtype) = tens X (⊤ : Submodule k N) := by
  refine le_antisymm ?_ (tens_le_iff.2 fun x hx y _ => ⟨⟨x, hx⟩ ⊗ₜ[k] y, by simp⟩)
  rintro _ ⟨s, rfl⟩
  induction s using TensorProduct.inductionOn with
  | tmul x y => exact tmul_mem_tens x.2 Submodule.mem_top
  | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv

/-- `ker (1 ⊗ f) = M ⊗ ker f`. -/
theorem ker_lTensor (f : N →ₗ[k] P) :
    LinearMap.ker (LinearMap.lTensor M f) = tens (⊤ : Submodule k M) (LinearMap.ker f) := by
  rw [← range_lTensor_subtype]
  exact (Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)).linearMap_ker_eq

/-- `ker (f ⊗ 1) = ker f ⊗ N`. -/
theorem ker_rTensor (f : M →ₗ[k] P) :
    LinearMap.ker (LinearMap.rTensor N f) = tens (LinearMap.ker f) (⊤ : Submodule k N) := by
  rw [← range_rTensor_subtype]
  exact (Module.Flat.rTensor_exact N (LinearMap.exact_subtype_ker_map f)).linearMap_ker_eq

/-- `ker (f ⊗ g) = ker f ⊗ N + M ⊗ ker g`, for surjective `f` and `g`. -/
theorem ker_map (f : M →ₗ[k] P) (hf : Function.Surjective f) (g : N →ₗ[k] Q)
    (hg : Function.Surjective g) :
    LinearMap.ker (map f g)
      = tens (LinearMap.ker f) (⊤ : Submodule k N)
        ⊔ tens (⊤ : Submodule k M) (LinearMap.ker g) := by
  rw [← range_rTensor_subtype, ← range_lTensor_subtype,
    TensorProduct.map_ker (LinearMap.exact_subtype_ker_map f) hf
      (LinearMap.exact_subtype_ker_map g) hg, sup_comm]

/-- Over a field, `(X ⊗ N) ⊓ (M ⊗ Y) = X ⊗ Y`. -/
theorem tens_top_inf_top_tens (X : Submodule k M) (Y : Submodule k N) :
    tens X (⊤ : Submodule k N) ⊓ tens (⊤ : Submodule k M) Y = tens X Y := by
  refine le_antisymm ?_ (le_inf (tens_mono le_rfl le_top) (tens_mono le_top le_rfl))
  obtain ⟨W, hW⟩ := X.exists_isCompl
  set p : M →ₗ[k] M := X.subtype ∘ₗ X.projectionOnto W hW with hp
  have hpX : ∀ x ∈ X, p x = x := fun x hx =>
    Subtype.ext_iff.1 (X.projectionOnto_apply_left hW ⟨x, hx⟩)
  have hpmem : ∀ x : M, p x ∈ X := fun x => (X.projectionOnto W hW x).2
  have hsplit : ∀ t : M ⊗[k] N,
      LinearMap.rTensor N p t + LinearMap.rTensor N (LinearMap.id - p) t = t := by
    intro t
    rw [← LinearMap.add_apply, ← LinearMap.rTensor_add, add_sub_cancel, LinearMap.rTensor_id,
      LinearMap.id_apply]
  -- `t = p t + (1 - p) t`, where `(1 - p) t = 0` as `t ∈ X ⊗ N`, and `p t ∈ X ⊗ Y` as `t ∈ M ⊗ Y`.
  rintro t ⟨htX, htY⟩
  have hzero : LinearMap.rTensor N (LinearMap.id - p) t = 0 := by
    have hle : tens X (⊤ : Submodule k N)
        ≤ LinearMap.ker (LinearMap.rTensor N (LinearMap.id (R := k) (M := M) - p)) :=
      tens_le_iff.2 fun x hx y _ => by simp [LinearMap.mem_ker, hpX x hx]
    exact hle htX
  have hmem : LinearMap.rTensor N p t ∈ tens X Y := by
    have hle : tens (⊤ : Submodule k M) Y
        ≤ Submodule.comap (LinearMap.rTensor N p) (tens X Y) :=
      tens_le_iff.2 fun x _ y hy => by
        simp only [Submodule.mem_comap, LinearMap.rTensor_tmul]
        exact tmul_mem_tens (hpmem x) hy
    exact hle htY
  have hts := hsplit t
  rw [hzero, add_zero] at hts
  rwa [hts] at hmem

/-- `0 ⊗ Y = 0`. -/
theorem tens_bot_left (Y : Submodule k N) : tens (⊥ : Submodule k M) Y = ⊥ :=
  le_antisymm (tens_le_iff.2 fun x hx y _ => by simp [(Submodule.mem_bot k).1 hx]) bot_le

/-- `X ⊗ 0 = 0`. -/
theorem tens_bot_right (X : Submodule k M) : tens X (⊥ : Submodule k N) = ⊥ :=
  le_antisymm (tens_le_iff.2 fun x _ y hy => by simp [(Submodule.mem_bot k).1 hy]) bot_le

/-- `M ⊗ N` (as a submodule) is everything. -/
theorem tens_top_top : tens (⊤ : Submodule k M) (⊤ : Submodule k N) = ⊤ := by
  refine le_antisymm le_top ?_
  have h : ∀ t : M ⊗[k] N, t ∈ tens (⊤ : Submodule k M) (⊤ : Submodule k N) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x y => exact tmul_mem_tens Submodule.mem_top Submodule.mem_top
    | add u v hu hv => exact Submodule.add_mem _ hu hv
  exact fun t _ => h t


/-! ### Intersections -/

section Inter

variable (N) in
/-- The canonical injection `(P × Q) ⊗ N → (P ⊗ N) × (Q ⊗ N)`. -/
noncomputable def prodTensorMap (P Q : Type*) [AddCommGroup P] [Module k P]
    [AddCommGroup Q] [Module k Q] : (P × Q) ⊗[k] N →ₗ[k] (P ⊗[k] N) × (Q ⊗[k] N) :=
  LinearMap.prod (LinearMap.rTensor N (LinearMap.fst k P Q))
      (LinearMap.rTensor N (LinearMap.snd k P Q))

/-- The map `(P × Q) ⊗ N → (P ⊗ N) × (Q ⊗ N)` is injective. -/
theorem injective_prodTensorMap (P Q : Type*) [AddCommGroup P] [Module k P]
    [AddCommGroup Q] [Module k Q] : Function.Injective (prodTensorMap (k := k) N P Q) := by
  have h : (LinearMap.coprod (LinearMap.rTensor N (LinearMap.inl k P Q))
      (LinearMap.rTensor N (LinearMap.inr k P Q))) ∘ₗ prodTensorMap (k := k) N P Q
      = LinearMap.id := by
    ext p n
    · simp [prodTensorMap]
    · simp [prodTensorMap]
  exact Function.LeftInverse.injective (g := LinearMap.coprod
    (LinearMap.rTensor N (LinearMap.inl k P Q)) (LinearMap.rTensor N (LinearMap.inr k P Q)))
    (LinearMap.ext_iff.1 h :)

/-- Intersecting in the left variable: `(X ⊗ N) ⊓ (X' ⊗ N) = (X ⊓ X') ⊗ N`. -/
theorem tens_inf_tens_left (X X' : Submodule k M) :
    tens X (⊤ : Submodule k N) ⊓ tens X' (⊤ : Submodule k N)
      = tens (X ⊓ X') (⊤ : Submodule k N) := by
  have hX : tens X (⊤ : Submodule k N) = LinearMap.ker (LinearMap.rTensor N X.mkQ) := by
    rw [ker_rTensor, Submodule.ker_mkQ]
  have hX' : tens X' (⊤ : Submodule k N) = LinearMap.ker (LinearMap.rTensor N X'.mkQ) := by
    rw [ker_rTensor, Submodule.ker_mkQ]
  have hI : tens (X ⊓ X') (⊤ : Submodule k N)
      = LinearMap.ker (LinearMap.rTensor N (X.mkQ.prod X'.mkQ)) := by
    rw [ker_rTensor, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hcomp : prodTensorMap (k := k) N (M ⧸ X) (M ⧸ X') ∘ₗ
      LinearMap.rTensor N (X.mkQ.prod X'.mkQ)
      = LinearMap.prod (LinearMap.rTensor N X.mkQ) (LinearMap.rTensor N X'.mkQ) := by
    ext x n
    · simp [prodTensorMap]
    · simp [prodTensorMap]
  have hker : LinearMap.ker (prodTensorMap (k := k) N (M ⧸ X) (M ⧸ X') ∘ₗ
      LinearMap.rTensor N (X.mkQ.prod X'.mkQ))
      = LinearMap.ker (LinearMap.rTensor N (X.mkQ.prod X'.mkQ)) :=
    LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 (injective_prodTensorMap (N := N) (M ⧸ X) (M ⧸ X')))
  rw [hX, hX', hI, ← LinearMap.ker_prod, ← hcomp, hker]

end Inter

/-- Intersecting in the right variable: `(M ⊗ Y) ⊓ (M ⊗ Y') = M ⊗ (Y ⊓ Y')`. -/
theorem tens_inf_tens_right (Y Y' : Submodule k N) :
    tens (⊤ : Submodule k M) Y ⊓ tens (⊤ : Submodule k M) Y'
      = tens (⊤ : Submodule k M) (Y ⊓ Y') := by
  have hY : tens (⊤ : Submodule k M) Y = LinearMap.ker (LinearMap.lTensor M Y.mkQ) := by
    rw [ker_lTensor, Submodule.ker_mkQ]
  have hY' : tens (⊤ : Submodule k M) Y' = LinearMap.ker (LinearMap.lTensor M Y'.mkQ) := by
    rw [ker_lTensor, Submodule.ker_mkQ]
  have hI : tens (⊤ : Submodule k M) (Y ⊓ Y')
      = LinearMap.ker (LinearMap.lTensor M (Y.mkQ.prod Y'.mkQ)) := by
    rw [ker_lTensor, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  have hcomp : (TensorProduct.prodRight k k M (N ⧸ Y) (N ⧸ Y')).toLinearMap ∘ₗ
      LinearMap.lTensor M (Y.mkQ.prod Y'.mkQ)
      = LinearMap.prod (LinearMap.lTensor M Y.mkQ) (LinearMap.lTensor M Y'.mkQ) := by
    ext x n
    · simp
    · simp
  have hker : LinearMap.ker ((TensorProduct.prodRight k k M (N ⧸ Y) (N ⧸ Y')).toLinearMap ∘ₗ
      LinearMap.lTensor M (Y.mkQ.prod Y'.mkQ))
      = LinearMap.ker (LinearMap.lTensor M (Y.mkQ.prod Y'.mkQ)) :=
    LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot.2 (TensorProduct.prodRight k k M (N ⧸ Y) (N ⧸ Y')).injective)
  rw [hY, hY', hI, ← LinearMap.ker_prod, ← hcomp, hker]

/-- Intersections of tensor submodules: `(X ⊗ Y) ⊓ (X' ⊗ Y') = (X ⊓ X') ⊗ (Y ⊓ Y')`. -/
theorem tens_inf_tens (X X' : Submodule k M) (Y Y' : Submodule k N) :
    tens X Y ⊓ tens X' Y' = tens (X ⊓ X') (Y ⊓ Y') := by
  rw [← tens_top_inf_top_tens X Y, ← tens_top_inf_top_tens X' Y',
    ← tens_top_inf_top_tens (X ⊓ X') (Y ⊓ Y'), ← tens_inf_tens_left, ← tens_inf_tens_right]
  ac_rfl

/-- The image of `X ⊗ Y` under `f ⊗ g` is `f X ⊗ g Y`. -/
theorem map_tens (f : M →ₗ[k] P) (g : N →ₗ[k] Q) (X : Submodule k M) (Y : Submodule k N) :
    Submodule.map (map f g) (tens X Y) = tens (X.map f) (Y.map g) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    exact tens_le_iff.2 fun x hx y hy => by
      simp only [Submodule.mem_comap, TensorProduct.map_tmul]
      exact tmul_mem_tens ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
  · refine tens_le_iff.2 ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact ⟨x ⊗ₜ[k] y, tmul_mem_tens hx hy, by simp⟩

end Coalgebra.Coradical
