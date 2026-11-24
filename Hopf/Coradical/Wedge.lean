module

public import Hopf.Coradical.TensorSub
public import Hopf.Cocommutative.Subcoalgebra

/-!
# The wedge product of subspaces of a coalgebra

Let `k` be a field and `C` a `k`-coalgebra.  For submodules `X, Y ≤ C` the **wedge product** is

```
X ∧ Y = Δ⁻¹ (X ⊗ C + C ⊗ Y) = ker ((π_X ⊗ π_Y) ∘ Δ)
```

where `π_X : C ↠ C/X` is the canonical projection.  It is the basic operation out of which the
coradical filtration of a coalgebra is built: `Cₙ = C₀ ∧ Cₙ₋₁` for `C₀` the coradical.

## Main results

* `Coalgebra.Coradical.wedge` and `Coalgebra.Coradical.mem_wedge_iff` — the definition and its
  `Δ x ∈ X ⊗ C + C ⊗ Y` description;
* `Coalgebra.Coradical.wedge_mono` — monotonicity in both arguments;
* `Coalgebra.Coradical.left_le_wedge` — a subcoalgebra is contained in each of its wedges on the
  left;
* `Coalgebra.Coradical.isSubcoalgebra_wedge` — the wedge of two subcoalgebras is a subcoalgebra;
* `Coalgebra.Coradical.wedge_assoc` (in `Hopf/Coradical/WedgeAssoc.lean`) — the wedge product is
  associative.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

open TensorProduct Coalgebra

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The **wedge product** `X ∧ Y = Δ⁻¹ (X ⊗ C + C ⊗ Y)` of two subspaces of a coalgebra. -/
noncomputable def wedge (X Y : Submodule k C) : Submodule k C :=
  LinearMap.ker (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))

omit [Coalgebra k C] in
/-- The kernel of `C ⊗ C → C/X ⊗ C/Y` is `X ⊗ C + C ⊗ Y`. -/
theorem ker_map_mkQ (X Y : Submodule k C) :
    LinearMap.ker (map X.mkQ Y.mkQ)
      = tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y := by
  rw [ker_map _ X.mkQ_surjective _ Y.mkQ_surjective, Submodule.ker_mkQ, Submodule.ker_mkQ]

/-- `x ∈ X ∧ Y` iff `Δ x ∈ X ⊗ C + C ⊗ Y`. -/
theorem mem_wedge_iff {X Y : Submodule k C} {x : C} :
    x ∈ wedge X Y ↔ comul (R := k) x ∈ tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y := by
  rw [wedge, LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ker_map_mkQ]

/-- The wedge product is monotone in both arguments. -/
theorem wedge_mono {X X' Y Y' : Submodule k C} (hX : X ≤ X') (hY : Y ≤ Y') :
    wedge X Y ≤ wedge X' Y' := by
  intro x hx
  rw [mem_wedge_iff] at hx ⊢
  exact (sup_le_sup (tens_mono hX le_rfl) (tens_mono le_rfl hY)) hx

/-- The comultiplication of an element of a subcoalgebra lands in `W ⊗ W`. -/
theorem comul_mem_tens {W : Submodule k C} (hW : UlmerBialgebras.Subcoalg.IsSubcoalgebra W) {x : C}
    (hx : x ∈ W) : comul (R := k) x ∈ tens W W := by
  rw [mem_tens_iff_mem_range]
  exact hW x hx

/-- `W` is a subcoalgebra iff `Δ W ⊆ W ⊗ W`. -/
theorem isSubcoalgebra_iff (W : Submodule k C) :
    UlmerBialgebras.Subcoalg.IsSubcoalgebra W ↔ ∀ x ∈ W, comul (R := k) x ∈ tens W W := by
  constructor
  · intro hW x hx; exact comul_mem_tens hW hx
  · intro h x hx; rw [← mem_tens_iff_mem_range]; exact h x hx

/-- A subcoalgebra is contained in each of its wedges on the left. -/
theorem left_le_wedge {X : Submodule k C} (hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra X)
    (Y : Submodule k C) : X ≤ wedge X Y := by
  intro x hx
  rw [mem_wedge_iff]
  exact Submodule.mem_sup_left (tens_mono le_rfl le_top (comul_mem_tens hX hx))

section SubcoalgebraWedge

variable (X Y : Submodule k C)

/-- Coassociativity, in the form needed to see that `Δ (X ∧ Y) ⊆ C ⊗ (X ∧ Y)`. -/
theorem lTensor_wedgeMap_comp_comul :
    LinearMap.lTensor C (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) ∘ₗ
      comul
      = (TensorProduct.assoc k C (C ⧸ X) (C ⧸ Y)).toLinearMap ∘ₗ
          map (LinearMap.lTensor C X.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) Y.mkQ
            ∘ₗ comul := by
  have hnat : (TensorProduct.assoc k C (C ⧸ X) (C ⧸ Y)).toLinearMap ∘ₗ
      map (LinearMap.lTensor C X.mkQ) Y.mkQ
      = LinearMap.lTensor C (map X.mkQ Y.mkQ) ∘ₗ
        (TensorProduct.assoc k C C C).toLinearMap := by
    ext a b c
    simp
  have h1 : map (LinearMap.lTensor C X.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) Y.mkQ
      = map (LinearMap.lTensor C X.mkQ) Y.mkQ ∘ₗ
          LinearMap.rTensor C comul := by
    ext a b
    simp
  have h2 : LinearMap.lTensor C (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
      = LinearMap.lTensor C (map X.mkQ Y.mkQ) ∘ₗ
          LinearMap.lTensor C comul := by
    ext a b
    simp
  rw [h1, h2]
  simp only [← LinearMap.comp_assoc]
  rw [hnat]
  simp only [LinearMap.comp_assoc]
  rw [Coalgebra.coassoc]

/-- Coassociativity, in the form needed to see that `Δ (X ∧ Y) ⊆ (X ∧ Y) ⊗ C`. -/
theorem rTensor_wedgeMap_comp_comul :
    LinearMap.rTensor C (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) ∘ₗ
      comul
      = (TensorProduct.assoc k (C ⧸ X) (C ⧸ Y) C).symm.toLinearMap ∘ₗ
          map X.mkQ (LinearMap.rTensor C Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
            ∘ₗ comul := by
  have hnat : (TensorProduct.assoc k (C ⧸ X) (C ⧸ Y) C).symm.toLinearMap ∘ₗ
      map X.mkQ (LinearMap.rTensor C Y.mkQ)
      = LinearMap.rTensor C (map X.mkQ Y.mkQ) ∘ₗ
        (TensorProduct.assoc k C C C).symm.toLinearMap := by
    ext a b c
    simp
  have h1 : map X.mkQ (LinearMap.rTensor C Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
      = map X.mkQ (LinearMap.rTensor C Y.mkQ) ∘ₗ
          LinearMap.lTensor C comul := by
    ext a b
    simp
  have h2 : LinearMap.rTensor C (map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))
      = LinearMap.rTensor C (map X.mkQ Y.mkQ) ∘ₗ
          LinearMap.rTensor C comul := by
    ext a b
    simp
  rw [h1, h2]
  simp only [← LinearMap.comp_assoc]
  rw [hnat]
  simp only [LinearMap.comp_assoc]
  rw [Coalgebra.coassoc_symm]

variable {X Y}

/-- `Δ (X ∧ Y) ⊆ C ⊗ (X ∧ Y)` when `X` is a subcoalgebra. -/
theorem comul_wedge_mem_top_tens (hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra X) {w : C}
    (hw : w ∈ wedge X Y) : comul (R := k) w ∈ tens (⊤ : Submodule k C) (wedge X Y) := by
  set f : C →ₗ[k] (C ⧸ X) ⊗[k] (C ⧸ Y) :=
    map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C) with hf
  have hker : tens (⊤ : Submodule k C) (wedge X Y) = LinearMap.ker (LinearMap.lTensor C f) := by
    rw [ker_lTensor]; rfl
  rw [hker, LinearMap.mem_ker, ← LinearMap.comp_apply, hf, lTensor_wedgeMap_comp_comul]
  have hzero :
      map (LinearMap.lTensor C X.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) Y.mkQ
      (comul (R := k) w) = 0 := by
    have hle : tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y
        ≤ LinearMap.ker (map
            (LinearMap.lTensor C X.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) Y.mkQ) := by
      refine sup_le (tens_le_iff.2 fun x hx c _ => ?_) (tens_le_iff.2 fun c _ y hy => ?_)
      · have : LinearMap.lTensor C X.mkQ (comul (R := k) x) = 0 := by
          have hmem : comul (R := k) x ∈ tens (⊤ : Submodule k C) X :=
            tens_mono le_top le_rfl (comul_mem_tens hX hx)
          have : comul (R := k) x ∈ LinearMap.ker (LinearMap.lTensor C X.mkQ) := by
            rw [ker_lTensor, Submodule.ker_mkQ]; exact hmem
          simpa using this
        simp [LinearMap.mem_ker, this]
      · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero Y).2 hy]
    exact hle (mem_wedge_iff.1 hw)
  simp [hzero]

/-- `Δ (X ∧ Y) ⊆ (X ∧ Y) ⊗ C` when `Y` is a subcoalgebra. -/
theorem comul_wedge_mem_tens_top (hY : UlmerBialgebras.Subcoalg.IsSubcoalgebra Y) {w : C}
    (hw : w ∈ wedge X Y) : comul (R := k) w ∈ tens (wedge X Y) (⊤ : Submodule k C) := by
  set f : C →ₗ[k] (C ⧸ X) ⊗[k] (C ⧸ Y) :=
    map X.mkQ Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C) with hf
  have hker : tens (wedge X Y) (⊤ : Submodule k C) = LinearMap.ker (LinearMap.rTensor C f) := by
    rw [ker_rTensor]; rfl
  rw [hker, LinearMap.mem_ker, ← LinearMap.comp_apply, hf, rTensor_wedgeMap_comp_comul]
  have hzero : map X.mkQ
      (LinearMap.rTensor C Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C)) (comul (R := k) w) = 0 := by
    have hle : tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y
        ≤ LinearMap.ker (map X.mkQ
            (LinearMap.rTensor C Y.mkQ ∘ₗ (comul : C →ₗ[k] C ⊗[k] C))) := by
      refine sup_le (tens_le_iff.2 fun x hx c _ => ?_) (tens_le_iff.2 fun c _ y hy => ?_)
      · simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero X).2 hx]
      · have : LinearMap.rTensor C Y.mkQ (comul (R := k) y) = 0 := by
          have hmem : comul (R := k) y ∈ tens Y (⊤ : Submodule k C) :=
            tens_mono le_rfl le_top (comul_mem_tens hY hy)
          have : comul (R := k) y ∈ LinearMap.ker (LinearMap.rTensor C Y.mkQ) := by
            rw [ker_rTensor, Submodule.ker_mkQ]; exact hmem
          simpa using this
        simp [LinearMap.mem_ker, this]
    exact hle (mem_wedge_iff.1 hw)
  simp [hzero]

/-- **The wedge of two subcoalgebras is a subcoalgebra.** -/
theorem isSubcoalgebra_wedge (hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra X)
    (hY : UlmerBialgebras.Subcoalg.IsSubcoalgebra Y) :
    UlmerBialgebras.Subcoalg.IsSubcoalgebra (wedge X Y) := by
  rw [isSubcoalgebra_iff]
  intro w hw
  rw [← tens_top_inf_top_tens]
  exact ⟨comul_wedge_mem_tens_top hY hw, comul_wedge_mem_top_tens hX hw⟩

end SubcoalgebraWedge

end Coalgebra.Coradical
