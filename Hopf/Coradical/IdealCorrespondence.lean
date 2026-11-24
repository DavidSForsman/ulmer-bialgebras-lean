module

public import Hopf.Coradical.FiniteDual

/-!
# Subcoalgebras versus two-sided ideals of the dual algebra

For a finite-dimensional coalgebra `C`, annihilation is an order-reversing bijection between the
subspaces of `C` and the subspaces of the convolution algebra `C*`, and under it

* subcoalgebras correspond to two-sided ideals (`Coalgebra.Coradical.isTwoSided_ann`,
  `Coalgebra.Coradical.isSubcoalgebra_of_isTwoSided_ann`);
* the wedge product corresponds to the product of ideals (`Coalgebra.Coradical.ann_wedge`).

## Main results

* `Coalgebra.Coradical.IsTwoSided`: a `k`-submodule of `C*` is a two-sided ideal.
* `Coalgebra.Coradical.isTwoSided_ann`: the annihilator of a subcoalgebra is a two-sided ideal of
  `C*`.
* `Coalgebra.Coradical.isSubcoalgebra_of_isTwoSided_ann`: for finite-dimensional `C`, a subspace
  whose annihilator is a two-sided ideal is a subcoalgebra.
* `Coalgebra.Coradical.ann_wedge`: for finite-dimensional `C`, `ann (wedge X Y) = ann X * ann Y`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapters 1 and 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Sections 1.2 and 5.2
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A `k`-submodule of the dual algebra is a two-sided ideal. -/
def IsTwoSided (I : Submodule k (Coalgebra.Coradical.DualAlg k C)) : Prop :=
  ∀ a : Coalgebra.Coradical.DualAlg k C, ∀ f ∈ I, a * f ∈ I ∧ f * a ∈ I
/-- The convolution product in `C*`: `(f * g) c = μ ((f ⊗ g) (Δ c))`. -/
theorem mul_ofConv_apply (f g : Coalgebra.Coradical.DualAlg k C) (c : C) :
    (f * g).ofConv c = LinearMap.mul' k k
      (map f.ofConv g.ofConv (comul (R := k) c)) := rfl


/-- The annihilator of a subcoalgebra is a two-sided ideal of the dual algebra. -/
theorem isTwoSided_ann {W : Submodule k C} (hW : IsSubcoalgebra W) : IsTwoSided (ann W) := by
  intro a f hf
  constructor
  · refine mem_ann.2 fun c hc => ?_
    have hle : tens (⊤ : Submodule k C) W
        ≤ LinearMap.ker (LinearMap.mul' k k ∘ₗ map a.ofConv f.ofConv) :=
      tens_le_iff.2 fun x _ y hy => by simp [LinearMap.mem_ker, mem_ann.1 hf y hy]
    have := hle (tens_mono le_top le_rfl (comul_mem_tens hW hc))
    simpa [mul_ofConv_apply] using this
  · refine mem_ann.2 fun c hc => ?_
    have hle : tens W (⊤ : Submodule k C)
        ≤ LinearMap.ker (LinearMap.mul' k k ∘ₗ map f.ofConv a.ofConv) :=
      tens_le_iff.2 fun x hx y _ => by simp [LinearMap.mem_ker, mem_ann.1 hf x hx]
    have := hle (tens_mono le_rfl le_top (comul_mem_tens hW hc))
    simpa [mul_ofConv_apply] using this

/-- Conversely, over a finite-dimensional coalgebra a subspace whose annihilator is a two-sided
ideal is a subcoalgebra. -/
theorem isSubcoalgebra_of_isTwoSided_ann [FiniteDimensional k C] {W : Submodule k C}
    (hW : IsTwoSided (ann W)) : IsSubcoalgebra W := by
  rw [isSubcoalgebra_iff]
  intro c hc
  rw [← tens_top_inf_top_tens]
  constructor
  · have hmem : comul (R := k) c ∈ tens W (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) ⊥ := by
      refine (mem_sup_tens_iff W ⊥ _).2 fun f hf g _ => ?_
      have hfg : f * g ∈ ann W := (hW g f hf).2
      simpa [mul_ofConv_apply] using mem_ann.1 hfg c hc
    simpa [tens_bot_right] using hmem
  · have hmem : comul (R := k) c ∈ tens (⊥ : Submodule k C) (⊤ : Submodule k C)
        ⊔ tens (⊤ : Submodule k C) W := by
      refine (mem_sup_tens_iff ⊥ W _).2 fun f _ g hg => ?_
      have hfg : f * g ∈ ann W := (hW f g hg).1
      simpa [mul_ofConv_apply] using mem_ann.1 hfg c hc
    simpa [tens_bot_left] using hmem

/-- The annihilator of a wedge product contains the product of the annihilators. -/
theorem ann_mul_le_ann_wedge (X Y : Submodule k C) : ann X * ann Y ≤ ann (wedge X Y) := by
  refine Submodule.mul_le.2 fun f hf g hg => mem_ann.2 fun c hc => ?_
  have hle : tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y
      ≤ LinearMap.ker (LinearMap.mul' k k ∘ₗ map f.ofConv g.ofConv) := by
    refine sup_le (tens_le_iff.2 fun x hx y _ => ?_) (tens_le_iff.2 fun x _ y hy => ?_)
    · simp [LinearMap.mem_ker, mem_ann.1 hf x hx]
    · simp [LinearMap.mem_ker, mem_ann.1 hg y hy]
  have := hle (mem_wedge_iff.1 hc)
  simpa [mul_ofConv_apply] using this

/-- **The wedge product is dual to the product of ideals.** -/
theorem ann_wedge [FiniteDimensional k C] (X Y : Submodule k C) :
    ann (wedge X Y) = ann X * ann Y := by
  refine le_antisymm ?_ (ann_mul_le_ann_wedge X Y)
  rw [← ann_coann (ann X * ann Y)]
  refine ann_antitone ?_
  intro c hc
  rw [mem_wedge_iff]
  refine (mem_sup_tens_iff X Y _).2 fun f hf g hg => ?_
  have hfg : f * g ∈ ann X * ann Y := Submodule.mul_mem_mul hf hg
  simpa [mul_ofConv_apply] using mem_coann.1 hc _ hfg

end Coalgebra.Coradical
