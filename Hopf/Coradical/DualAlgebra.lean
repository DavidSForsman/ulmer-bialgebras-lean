module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Hopf.Coradical.Simple
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The dual algebra of a coalgebra, and the annihilator correspondence

For a `k`-coalgebra `C` the linear dual `C* = C →ₗ[k] k` carries the convolution product
`(f * g) c = ∑ f c₍₁₎ g c₍₂₎`, which Mathlib provides on the type synonym
`WithConv (C →ₗ[k] k)`.  We write `DualAlg k C` for that algebra.

Annihilators set up an order-reversing correspondence between subspaces of `C` and subspaces of
`DualAlg k C`, which is a bijection when `C` is finite-dimensional.  Under it (see
`Hopf/Coradical/IdealCorrespondence.lean`):

* subcoalgebras correspond to two-sided ideals (`Coalgebra.Coradical.isTwoSided_ann`,
  `Coalgebra.Coradical.isSubcoalgebra_of_isTwoSided_ann`);
* the wedge product corresponds to the product of ideals (`Coalgebra.Coradical.ann_wedge`).

## Main definitions

* `Coalgebra.Coradical.DualAlg` — the convolution algebra `C*`;
* `Coalgebra.Coradical.ann`, `Coalgebra.Coradical.coann` — the two annihilator operations, with
  `Coalgebra.Coradical.ann_coann`, `Coalgebra.Coradical.coann_ann` and
  `Coalgebra.Coradical.ann_injective`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.2
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

variable (k C) in
/-- The convolution (dual) algebra `C*` of a coalgebra `C`. -/
protected abbrev DualAlg : Type u := WithConv (C →ₗ[k] k)

namespace DualAlg

/-- `μ ((r • f) ⊗ g) t = r * μ (f ⊗ g) t` for functionals `f g` and `t : C ⊗ C`. -/
theorem mul'_map_smul_left (r : k) (f g : C →ₗ[k] k) (t : C ⊗[k] C) :
    LinearMap.mul' k k (map (r • f) g t)
      = r * LinearMap.mul' k k (map f g t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [mul_assoc]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv, mul_add]

/-- `μ (f ⊗ (r • g)) t = r * μ (f ⊗ g) t` for functionals `f g` and `t : C ⊗ C`. -/
theorem mul'_map_smul_right (r : k) (f g : C →ₗ[k] k) (t : C ⊗[k] C) :
    LinearMap.mul' k k (map f (r • g) t)
      = r * LinearMap.mul' k k (map f g t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp; ring
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv, mul_add]

variable [Coalgebra k C]

/-- The `k`-algebra structure on the convolution algebra. -/
noncomputable instance instAlgebra : Algebra k (Coalgebra.Coradical.DualAlg k C) :=
  Algebra.ofModule
    (fun r f g => by
      apply WithConv.ofConv_injective
      ext c
      exact mul'_map_smul_left r f.ofConv g.ofConv (comul (R := k) c))
    (fun r f g => by
      apply WithConv.ofConv_injective
      ext c
      exact mul'_map_smul_right r f.ofConv g.ofConv (comul (R := k) c))

end DualAlg

/-- The annihilator in `C*` of a subspace of `C`. -/
noncomputable def ann (W : Submodule k C) : Submodule k (Coalgebra.Coradical.DualAlg k C) :=
  Submodule.comap (WithConv.linearEquiv k (C →ₗ[k] k)).toLinearMap W.dualAnnihilator

/-- The annihilator in `C` of a subspace of `C*`. -/
noncomputable def coann (I : Submodule k (Coalgebra.Coradical.DualAlg k C)) : Submodule k C :=
  Submodule.dualCoannihilator
    (Submodule.map (WithConv.linearEquiv k (C →ₗ[k] k)).toLinearMap I)

/-- `f ∈ ann W` iff `f` vanishes on `W`. -/
theorem mem_ann {W : Submodule k C} {f : Coalgebra.Coradical.DualAlg k C} :
    f ∈ ann W ↔ ∀ c ∈ W, f.ofConv c = 0 := by
  simp [ann, Submodule.mem_dualAnnihilator]

/-- `c ∈ coann I` iff every `f ∈ I` vanishes at `c`. -/
theorem mem_coann {I : Submodule k (Coalgebra.Coradical.DualAlg k C)} {c : C} :
    c ∈ coann I ↔ ∀ f ∈ I, f.ofConv c = 0 := by
  rw [coann, Submodule.mem_dualCoannihilator]
  constructor
  · intro hc f hf
    exact hc _ ⟨f, hf, rfl⟩
  · rintro h _ ⟨f, hf, rfl⟩
    exact h f hf

/-- `ann` is antitone. -/
theorem ann_antitone {W W' : Submodule k C} (h : W ≤ W') : ann W' ≤ ann W :=
  fun _ hf => mem_ann.2 fun c hc => mem_ann.1 hf c (h hc)

/-- `coann` is antitone. -/
theorem coann_antitone {I J : Submodule k (Coalgebra.Coradical.DualAlg k C)} (h : I ≤ J) :
    coann J ≤ coann I :=
  fun _ hc => mem_coann.2 fun f hf => mem_coann.1 hc f (h hf)

/-- Over a field, a subspace is recovered from its annihilator. -/
theorem coann_ann (W : Submodule k C) : coann (ann W) = W := by
  have hmap : Submodule.map (WithConv.linearEquiv k (C →ₗ[k] k)).toLinearMap (ann W)
      = W.dualAnnihilator := by
    rw [ann, Submodule.map_comap_eq_of_surjective
      (WithConv.linearEquiv k (C →ₗ[k] k)).surjective]
  rw [coann, hmap, Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- For a finite-dimensional coalgebra, a subspace of the dual is recovered from its
annihilator. -/
theorem ann_coann [FiniteDimensional k C] (I : Submodule k (Coalgebra.Coradical.DualAlg k C)) :
    ann (coann I) = I := by
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (K := k) (V := C)
    (W := Submodule.map (WithConv.linearEquiv k (C →ₗ[k] k)).toLinearMap I)
  rw [ann, coann, h]
  exact Submodule.comap_map_eq_of_injective
    (WithConv.linearEquiv k (C →ₗ[k] k)).injective I

/-- Over a field, `ann` is injective on subspaces of `C`. -/
theorem ann_injective : Function.Injective (ann (k := k) (C := C)) :=
  fun W W' h => by rw [← coann_ann W, ← coann_ann W', h]

/-- `ann C = 0`. -/
theorem ann_top : ann (⊤ : Submodule k C) = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  have : f.ofConv = 0 := by
    ext c
    exact mem_ann.1 hf c Submodule.mem_top
  exact (Submodule.mem_bot k).2 (WithConv.ofConv_injective (by simpa using this))

/-- `ann 0 = C*`. -/
theorem ann_bot : ann (⊥ : Submodule k C) = ⊤ :=
  eq_top_iff.2 fun f _ => mem_ann.2 fun c hc => by
    simp [(Submodule.mem_bot k).1 hc]

/-- For finite-dimensional `C`, `coann C* = 0`. -/
theorem coann_top [FiniteDimensional k C] :
    coann (⊤ : Submodule k (Coalgebra.Coradical.DualAlg k C)) = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  have h : ∀ f : C →ₗ[k] k, f c = 0 := fun f =>
    mem_coann.1 hc (WithConv.toConv f) Submodule.mem_top
  have hc0 : c = 0 := (Module.forall_dual_apply_eq_zero_iff k c).1 h
  simp [hc0]

end Coalgebra.Coradical
