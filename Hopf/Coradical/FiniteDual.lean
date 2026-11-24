module

public import Hopf.Coradical.DualAlgebra
public import Mathlib.LinearAlgebra.Contraction

/-!
# Finite-dimensional duality for coalgebras

For a finite-dimensional coalgebra `C` the annihilator maps `ann` and `coann` are mutually
inverse bijections between the subspaces of `C` and the subspaces of the convolution algebra
`C*`.  This file proves the linear-algebra fact that makes that bijection interact with the
coalgebra structure; it is the only place where finite-dimensionality is used, through the fact
that the functionals `f ⊗ g` span the dual of `C ⊗ C`. The consequences (subcoalgebras versus
two-sided ideals, `Coalgebra.Coradical.ann_wedge`) are in `Hopf/Coradical/IdealCorrespondence.lean`.

## Main results

* `Coalgebra.Coradical.mem_sup_tens_iff`: for finite-dimensional `C`, a tensor `t ∈ C ⊗ C` lies in
  `X ⊗ C + C ⊗ Y` if and only if it is annihilated by all the functionals `f ⊗ g` with
  `f ∈ X^⊥` and `g ∈ Y^⊥`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 1
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 1.2
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

/-! ### Separating tensors by product functionals -/

/-- `dualDistrib (a ⊗ b) t = μ ((a ⊗ b) t)`, with `μ : k ⊗ k → k` the multiplication. -/
theorem dualDistrib_apply_eq (a b : C →ₗ[k] k) (t : C ⊗[k] C) :
    TensorProduct.dualDistrib k C C (a ⊗ₜ[k] b) t
      = LinearMap.mul' k k (map a b t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-- Over a finite-dimensional space, a tensor annihilated by all product functionals is zero. -/
theorem eq_zero_of_forall_pairing [FiniteDimensional k C] {t : C ⊗[k] C}
    (h : ∀ a b : C →ₗ[k] k, LinearMap.mul' k k (map a b t) = 0) : t = 0 := by
  have key : ∀ s : Module.Dual k C ⊗[k] Module.Dual k C,
      TensorProduct.dualDistrib k C C s t = 0 := by
    intro s
    induction s using TensorProduct.inductionOn with
    | tmul a b => rw [dualDistrib_apply_eq]; exact h a b
    | add u v hu hv => rw [map_add]; simp [hu, hv]
  refine (Module.forall_dual_apply_eq_zero_iff k t).1 fun φ => ?_
  obtain ⟨s, rfl⟩ := (TensorProduct.dualDistribEquiv k C C).surjective φ
  rw [← LinearEquiv.coe_coe, TensorProduct.toLinearMap_dualDistribEquiv]
  exact key s

/-- Splitting a tensor along two linear endomorphisms `p` and `q` as `p ⊗ id + (id - p) ⊗ q +
(id - p) ⊗ (id - q)`. -/
private lemma tensor_map_split_proj (p q : C →ₗ[k] C) (s : C ⊗[k] C) :
    map p LinearMap.id s
      + map (LinearMap.id - p) q s
      + map (LinearMap.id - p) (LinearMap.id - q) s = s := by
  induction s using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [map_tmul, LinearMap.id_coe, id_eq, LinearMap.sub_apply]
    rw [add_assoc, ← TensorProduct.tmul_add, show q y + (y - q y) = y by abel,
      ← TensorProduct.add_tmul, show p x + (x - p x) = x by abel]
  | add v w hv hw =>
    simp only [map_add]
    calc _ = (map p LinearMap.id v
              + map (LinearMap.id - p) q v
              + map (LinearMap.id - p) (LinearMap.id - q) v)
            + (map p LinearMap.id w
              + map (LinearMap.id - p) q w
              + map (LinearMap.id - p) (LinearMap.id - q) w) := by abel
      _ = v + w := by rw [hv, hw]

/-- A tensor map `p ⊗ q` lands in `X ⊗ C` whenever `p` has range in `X`. -/
private lemma tensor_map_mem_tens_left {X : Submodule k C} {p q : C →ₗ[k] C}
    (hp : ∀ x : C, p x ∈ X) (t : C ⊗[k] C) :
    map p q t ∈ tens X (⊤ : Submodule k C) := by
  have hle : (⊤ : Submodule k (C ⊗[k] C)) ≤
      Submodule.comap (map p q) (tens X (⊤ : Submodule k C)) := by
    rw [← tens_top_top (k := k) (M := C) (N := C)]
    exact tens_le_iff.2 fun x _ y _ =>
      by simpa using tmul_mem_tens (hp x) Submodule.mem_top
  exact hle Submodule.mem_top

/-- A tensor map `p ⊗ q` lands in `C ⊗ Y` whenever `q` has range in `Y`. -/
private lemma tensor_map_mem_tens_right {Y : Submodule k C} {p q : C →ₗ[k] C}
    (hq : ∀ y : C, q y ∈ Y) (t : C ⊗[k] C) :
    map p q t ∈ tens (⊤ : Submodule k C) Y := by
  have hle : (⊤ : Submodule k (C ⊗[k] C)) ≤
      Submodule.comap (map p q) (tens (⊤ : Submodule k C) Y) := by
    rw [← tens_top_top (k := k) (M := C) (N := C)]
    exact tens_le_iff.2 fun x _ y _ =>
      by simpa using tmul_mem_tens Submodule.mem_top (hq y)
  exact hle Submodule.mem_top

/-- **Duality for the sum `X ⊗ C + C ⊗ Y`.**  A tensor lies in `X ⊗ C + C ⊗ Y` exactly when it is
annihilated by every product functional `f ⊗ g` with `f` vanishing on `X` and `g` vanishing on
`Y`. -/
theorem mem_sup_tens_iff [FiniteDimensional k C] (X Y : Submodule k C) (t : C ⊗[k] C) :
    t ∈ tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y ↔
      ∀ f ∈ ann X, ∀ g ∈ ann Y,
        LinearMap.mul' k k (map f.ofConv g.ofConv t) = 0 := by
  constructor
  · -- `f ⊗ g` kills `X ⊗ C` and `C ⊗ Y`
    intro ht f hf g hg
    have hle : tens X (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) Y
        ≤ LinearMap.ker (LinearMap.mul' k k ∘ₗ map f.ofConv g.ofConv) := by
      refine sup_le (tens_le_iff.2 fun x hx c _ => ?_) (tens_le_iff.2 fun c _ y hy => ?_)
      · simp [LinearMap.mem_ker, mem_ann.1 hf x hx]
      · simp [LinearMap.mem_ker, mem_ann.1 hg y hy]
    simpa using hle ht
  · -- conversely, split `t` along projections `p` onto `X` and `q` onto `Y`:
    -- `t = (p ⊗ 1) t + ((1 - p) ⊗ q) t + ((1 - p) ⊗ (1 - q)) t`, and the last term `u` vanishes
    -- because every functional `a ⊗ b` kills it
    intro h
    obtain ⟨X', hX'⟩ := X.exists_isCompl
    obtain ⟨Y', hY'⟩ := Y.exists_isCompl
    set p : C →ₗ[k] C := X.subtype ∘ₗ X.projectionOnto X' hX'
    set q : C →ₗ[k] C := Y.subtype ∘ₗ Y.projectionOnto Y' hY'
    have hpX : ∀ x ∈ X, p x = x := fun x hx =>
      Subtype.ext_iff.1 (X.projectionOnto_apply_left hX' ⟨x, hx⟩)
    have hqY : ∀ y ∈ Y, q y = y := fun y hy =>
      Subtype.ext_iff.1 (Y.projectionOnto_apply_left hY' ⟨y, hy⟩)
    set u : C ⊗[k] C := map (LinearMap.id - p) (LinearMap.id - q) t
    have hu0 : u = 0 := by
      refine eq_zero_of_forall_pairing fun a b => ?_
      have ha : WithConv.toConv (a ∘ₗ (LinearMap.id - p)) ∈ ann X :=
        mem_ann.2 fun x hx => by simp [hpX x hx]
      have hb : WithConv.toConv (b ∘ₗ (LinearMap.id - q)) ∈ ann Y :=
        mem_ann.2 fun y hy => by simp [hqY y hy]
      have hcomp : map a b u
          = map (a ∘ₗ (LinearMap.id - p)) (b ∘ₗ (LinearMap.id - q)) t := by
        rw [TensorProduct.map_comp]
        rfl
      rw [hcomp]
      exact h _ ha _ hb
    -- the first two terms lie in `X ⊗ C` and `C ⊗ Y`
    have h1 := tensor_map_mem_tens_left (X := X) (p := p) (q := LinearMap.id)
      (fun x => (X.projectionOnto X' hX' x).2) t
    have h2 := tensor_map_mem_tens_right (Y := Y) (p := LinearMap.id - p) (q := q)
      (fun y => (Y.projectionOnto Y' hY' y).2) t
    have hts := tensor_map_split_proj p q t
    rw [show map (LinearMap.id - p) (LinearMap.id - q) t = 0 from hu0,
      add_zero] at hts
    rw [← hts]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

end Coalgebra.Coradical
