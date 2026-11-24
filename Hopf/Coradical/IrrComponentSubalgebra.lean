module

public import Hopf.Coradical.WedgeMul
public import Hopf.Coradical.PointedComponents

/-!
# The irreducible component of `1` is a sub-Hopf algebra

Let `H` be a Hopf algebra over a field `k` and let `H₁ = glComponent 1` be the irreducible
component of the unit group-like element, i.e. the union of the wedge powers of the line `k · 1`.

## Main results

* `Coalgebra.Coradical.one_mem_glComponent_one`, `Coalgebra.Coradical.mul_glComponent_one_le`: `H₁`
  is a subalgebra of `H`; it is packaged as `Coalgebra.Coradical.irrSubalgebra k H`.
* `Coalgebra.Coradical.map_mulRight_glComponent`: right multiplication by a group-like element `d`
  carries the component of `g` onto the component of `g * d` (the right-handed companion of
  `Coalgebra.Coradical.map_mulLeft_glComponent`).
* `Coalgebra.Coradical.glComponent_eq_map_mulRight`: `H_g = H₁ · g`.
* `Coalgebra.Coradical.mem_glComponent_iff_exists_right`,
  `Coalgebra.Coradical.mem_glComponent_iff_exists_left`: `H_g = H₁ · g = g · H₁` elementwise.
* `Coalgebra.Coradical.mul_glComponent_le`: the `G(H)`-grading is multiplicative,
  `H_g · H_h ⊆ H_{g h}`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapters 8–9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Chapter 5
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### Right multiplication by a group-like element -/

/-- Right multiplication by a group-like element is a morphism of coalgebras. -/
theorem mulRight_comul (d : GroupLike k H) :
    map (LinearMap.mulRight k (d : H)) (LinearMap.mulRight k (d : H))
        ∘ₗ (comul : H →ₗ[k] H ⊗[k] H)
      = comul ∘ₗ (LinearMap.mulRight k (d : H)) := by
  have key : ∀ t : H ⊗[k] H,
      map (LinearMap.mulRight k (d : H)) (LinearMap.mulRight k (d : H)) t
        = t * ((d : H) ⊗ₜ[k] (d : H)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add u v hu hv => rw [map_add, hu, hv, add_mul]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
  rw [key, Bialgebra.comul_mul, d.2.comul_eq_tmul_self]

/-- Right multiplication by a group-like element commutes with taking irreducible components. -/
theorem map_mulRight_irrComponent (d : GroupLike k H) (X : Submodule k H) :
    Submodule.map (LinearMap.mulRight k (d : H)) (irrComponent X)
      = irrComponent (Submodule.map (LinearMap.mulRight k (d : H)) X) := by
  have hcancel : ∀ (a b : GroupLike k H) (Y : Submodule k H),
      Submodule.map (LinearMap.mulRight k (a : H))
        (Submodule.map (LinearMap.mulRight k (b : H)) Y)
      = Submodule.map (LinearMap.mulRight k ((b * a : GroupLike k H) : H)) Y := by
    intro a b Y
    rw [← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun y => by simp [mul_assoc]
  have hid : ∀ Y : Submodule k H,
      Submodule.map (LinearMap.mulRight k ((1 : GroupLike k H) : H)) Y = Y := by
    intro Y
    have h1 : LinearMap.mulRight k ((1 : GroupLike k H) : H) = LinearMap.id :=
      LinearMap.ext fun y => by simp
    rw [h1, Submodule.map_id]
  refine le_antisymm (map_irrComponent_le (mulRight_comul d) X) ?_
  have h1 := map_irrComponent_le (mulRight_comul d⁻¹)
    (Submodule.map (LinearMap.mulRight k (d : H)) X)
  rw [hcancel, mul_inv_cancel, hid] at h1
  have h2 := Submodule.map_mono (f := LinearMap.mulRight k (d : H)) h1
  rwa [hcancel, inv_mul_cancel, hid] at h2

/-- Right multiplication by a group-like element `d` carries the component of `g` onto the
component of `g * d`. -/
theorem map_mulRight_glComponent (d g : GroupLike k H) :
    Submodule.map (LinearMap.mulRight k (d : H)) (glComponent g) = glComponent (g * d) := by
  rw [glComponent, map_mulRight_irrComponent]
  congr 1
  rw [Submodule.map_span]
  simp

/-- The component of a group-like element `g` is `H₁ · g`. -/
theorem glComponent_eq_map_mulRight (g : GroupLike k H) :
    glComponent g
      = Submodule.map (LinearMap.mulRight k (g : H)) (glComponent (1 : GroupLike k H)) := by
  rw [map_mulRight_glComponent, one_mul]

/-! ### `H₁` is a subalgebra -/

/-- `1` lies in the irreducible component of the group-like element `1`. -/
theorem one_mem_glComponent_one : (1 : H) ∈ glComponent (1 : GroupLike k H) :=
  le_irrComponent (Submodule.span k {((1 : GroupLike k H) : H)})
    (by simp [Submodule.mem_span_singleton_self])

/-- The irreducible component of `1` is closed under multiplication. -/
theorem mul_glComponent_one_le :
    glComponent (1 : GroupLike k H) * glComponent (1 : GroupLike k H)
      ≤ glComponent (1 : GroupLike k H) := by
  refine mul_irrComponent_le (isSubcoalgebra_span_groupLike (1 : GroupLike k H).2) ?_
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine Submodule.mem_span_singleton.2 ⟨a * b, ?_⟩
  simp [smul_smul, mul_comm]

variable (k H) in
/-- **The irreducible component of `1`, as a subalgebra of `H`.** -/
noncomputable def irrSubalgebra : Subalgebra k H where
  __ := glComponent (1 : GroupLike k H)
  mul_mem' := by
    intro a b ha hb
    exact mul_glComponent_one_le (Submodule.mul_mem_mul ha hb)
  algebraMap_mem' := by
    intro c
    have : algebraMap k H c = c • (1 : H) := by simp [Algebra.algebraMap_eq_smul_one]
    rw [this]
    exact Submodule.smul_mem _ _ one_mem_glComponent_one

/-- Membership in `irrSubalgebra k H` is membership in the irreducible component of `1`. -/
@[simp] theorem mem_irrSubalgebra {x : H} :
    x ∈ irrSubalgebra k H ↔ x ∈ glComponent (1 : GroupLike k H) := Iff.rfl

/-! ### The components of the group-like elements multiply -/

/-- Every element of `H_g` is of the form `a · g` with `a ∈ H₁`. -/
theorem mem_glComponent_iff_exists_right {g : GroupLike k H} {x : H} :
    x ∈ glComponent g ↔ ∃ a ∈ glComponent (1 : GroupLike k H), x = a * (g : H) := by
  rw [glComponent_eq_map_mulRight g]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-- Every element of `H_g` is of the form `g · a` with `a ∈ H₁`. -/
theorem mem_glComponent_iff_exists_left {g : GroupLike k H} {x : H} :
    x ∈ glComponent g ↔ ∃ a ∈ glComponent (1 : GroupLike k H), x = (g : H) * a := by
  have h : glComponent g
      = Submodule.map (LinearMap.mulLeft k (g : H)) (glComponent (1 : GroupLike k H)) := by
    rw [map_mulLeft_glComponent, mul_one]
  rw [h]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩

/-- For a group-like `g`, `g v` lies in the component `H_g` whenever `v` lies in `H₁`. -/
theorem mul_mem_glComponent (g : GroupLike k H) {v : H}
    (hv : v ∈ glComponent (1 : GroupLike k H)) : (g : H) * v ∈ glComponent g :=
  mem_glComponent_iff_exists_left.2 ⟨v, hv, rfl⟩

/-- **The `G(H)`-grading is multiplicative**: `H_g · H_h ⊆ H_{g h}`. -/
theorem mul_glComponent_le (g h : GroupLike k H) :
    glComponent g * glComponent h ≤ glComponent (g * h) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, ha, rfl⟩ := mem_glComponent_iff_exists_left.1 hx
  obtain ⟨b, hb, rfl⟩ := mem_glComponent_iff_exists_right.1 hy
  have hab : a * b ∈ glComponent (1 : GroupLike k H) :=
    mul_glComponent_one_le (Submodule.mul_mem_mul ha hb)
  have hga : (g : H) * (a * b) ∈ glComponent g := mem_glComponent_iff_exists_left.2
      ⟨a * b, hab, rfl⟩
  obtain ⟨c, hc, hceq⟩ := mem_glComponent_iff_exists_right.1 hga
  have hxy : (g : H) * a * (b * (h : H)) = c * ((g * h : GroupLike k H) : H) := by
    have : (g : H) * a * (b * (h : H)) = ((g : H) * (a * b)) * (h : H) := by
      simp [mul_assoc]
    rw [this, hceq]
    simp [mul_assoc]
  rw [hxy]
  exact mem_glComponent_iff_exists_right.2 ⟨c, hc, rfl⟩

end Coalgebra.Coradical
