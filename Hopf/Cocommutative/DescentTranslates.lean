module

public import Hopf.Cocommutative.DescentSubgroupComponent

/-!
# Translated components and retractions

For a subgroup of group-like elements and a conjugation-stable subalgebra of the
irreducible component, define the sum of its translated components. A retraction onto the
subalgebra induces a projection onto that sum, compatible with right multiplication.
These constructions are inputs to the correspondence layers.

## Main results

* `HopfAlgebra.Cocommutative.transComponent`: the submodule `⨆_{d ∈ Δ} d · A` of translates of `A`.
* `HopfAlgebra.Cocommutative.ConjStable`: `d A d⁻¹ ⊆ A` for every `d ∈ Δ`.
* `HopfAlgebra.Cocommutative.transProj`: the map `H → H` which on `H_g` is `x ↦ pA (x g⁻¹) g` for
  `g ∈ Δ` and `0` otherwise.
* `HopfAlgebra.Cocommutative.transProj_mem`, `HopfAlgebra.Cocommutative.transProj_id`,
  `HopfAlgebra.Cocommutative.transProj_mul`: under the stated hypotheses on `A` and `pA`,
  `transProj` takes values in `transComponent Δ A`, is the identity on it, and satisfies
  `transProj (x * a) = transProj x * a` for `a ∈ transComponent Δ A`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra Coalgebra.Coradical

universe u

namespace HopfAlgebra.Cocommutative

section RingIdentities

variable {H : Type u} [Ring H]

/-- A ring identity used in `transProj_mul`: with `Gi * G = 1`,
`y (D w) (Di Gi) = (y Gi) (G D w Di Gi)`. -/
lemma conj_arg_eq {G Gi : H} (h : Gi * G = 1) (y D w Di : H) :
    y * (D * w) * (Di * Gi) = (y * Gi) * (G * D * w * (Di * Gi)) := by
  have e : (y * Gi) * (G * D * w * (Di * Gi)) = y * ((Gi * G) * (D * (w * (Di * Gi)))) := by
    simp only [mul_assoc]
  rw [e, h, one_mul]
  simp only [mul_assoc]

/-- A ring identity used in `transProj_mul`: with `Gi * G = 1` and `Di * D = 1`,
`p (G D w Di Gi) (G D) = p G (D w)`. -/
lemma conj_final_eq {G Gi D Di : H} (hG : Gi * G = 1) (hD : Di * D = 1) (p w : H) :
    p * (G * D * w * (Di * Gi)) * (G * D) = p * G * (D * w) := by
  have e1 : p * (G * D * w * (Di * Gi)) * (G * D)
      = p * (G * (D * (w * (Di * ((Gi * G) * D))))) := by
    simp only [mul_assoc]
  have e2 : p * G * (D * w) = p * (G * (D * w)) := by
    simp only [mul_assoc]
  rw [e1, e2, hG, one_mul, hD, mul_one]

end RingIdentities

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### Group-like bookkeeping -/

/-- For a group-like `g`: `g g⁻¹ = 1` in `H`. -/
theorem gl_mul_inv (g : GroupLike k H) : (g : H) * ((g⁻¹ : GroupLike k H) : H) = 1 := by
  rw [← GroupLike.val_mul, mul_inv_cancel, GroupLike.val_one]

/-- For a group-like `g`: `g⁻¹ g = 1` in `H`. -/
theorem gl_inv_mul (g : GroupLike k H) : ((g⁻¹ : GroupLike k H) : H) * (g : H) = 1 := by
  rw [← GroupLike.val_mul, inv_mul_cancel, GroupLike.val_one]

/-- For group-likes `g d`: `(g d)⁻¹ = d⁻¹ g⁻¹` in `H`. -/
theorem gl_val_inv_mul (g d : GroupLike k H) :
    (((g * d)⁻¹ : GroupLike k H) : H)
      = ((d⁻¹ : GroupLike k H) : H) * ((g⁻¹ : GroupLike k H) : H) := by
  rw [mul_inv_rev, GroupLike.val_mul]

/-! ### The subalgebra of translates -/

section Translates

variable (Δ : Subgroup (GroupLike k H)) (A : Subalgebra k H)

/-- The submodule `⨆_{d ∈ Δ} d · A` of translates of `A` by the elements of `Δ`. -/
noncomputable def transComponent : Submodule k H :=
  ⨆ d : Δ, Submodule.map (LinearMap.mulLeft k ((d : GroupLike k H) : H))
    (Subalgebra.toSubmodule A)

variable {Δ A}

/-- For `d ∈ Δ` and `a ∈ A`, the translate `d a` lies in `⨆_{d ∈ Δ} d · A`. -/
theorem mem_transComponent_of_mem {d : GroupLike k H} (hd : d ∈ Δ) {a : H} (ha : a ∈ A) :
    (d : H) * a ∈ transComponent Δ A :=
  le_iSup (fun e : Δ => Submodule.map (LinearMap.mulLeft k ((e : GroupLike k H) : H))
    (Subalgebra.toSubmodule A)) ⟨d, hd⟩ ⟨a, ha, rfl⟩

variable (Δ A) in
/-- The conjugation-stability hypothesis on `A`: `d A d⁻¹ ⊆ A` for every `d ∈ Δ`. -/
def ConjStable : Prop :=
  ∀ d ∈ Δ, ∀ a ∈ A, (d : H) * a * ((d⁻¹ : GroupLike k H) : H) ∈ A

/-- If `A` is `ConjStable` under `Δ`, then `d⁻¹ a d ∈ A` for `d ∈ Δ` and `a ∈ A`. -/
theorem conj_mem_of_conjStable (hconj : ConjStable Δ A) {d : GroupLike k H} (hd : d ∈ Δ)
    {a : H} (ha : a ∈ A) : ((d⁻¹ : GroupLike k H) : H) * a * (d : H) ∈ A := by
  have := hconj d⁻¹ (Δ.inv_mem hd) a ha
  rwa [inv_inv] at this

/-- If `A` is `ConjStable` under `Δ`, then `a d ∈ transComponent Δ A` for `d ∈ Δ` and
`a ∈ A`. -/
theorem mem_transComponent_mul_right (hconj : ConjStable Δ A) {d : GroupLike k H} (hd : d ∈ Δ)
    {a : H} (ha : a ∈ A) : a * (d : H) ∈ transComponent Δ A := by
  have hu : ((d⁻¹ : GroupLike k H) : H) * a * (d : H) ∈ A := conj_mem_of_conjStable hconj hd ha
  have heq : (d : H) * (((d⁻¹ : GroupLike k H) : H) * a * (d : H)) = a * (d : H) := by
    have step : (d : H) * (((d⁻¹ : GroupLike k H) : H) * a * (d : H))
        = ((d : H) * ((d⁻¹ : GroupLike k H) : H)) * (a * (d : H)) := by
      simp only [mul_assoc]
    rw [step, gl_mul_inv, one_mul]
  exact heq ▸ mem_transComponent_of_mem hd hu

end Translates

/-! ### The retraction -/

section Proj

variable {Δ : Subgroup (GroupLike k H)} {A : Subalgebra k H}
variable [DecidableEq (GroupLike k H)] [Coalgebra.IsCocomm k H]

open Classical in
/-- **The retraction `H ↠ ⨆_{d ∈ Δ} d · A`** built from a right `A`-linear retraction
`pA : H₁ ↠ A`: on the Kostant component `H_g = H₁ · g` it is `x ↦ pA (x g⁻¹) g` when `g ∈ Δ`, and
`0` otherwise. -/
noncomputable def transProj (Δ : Subgroup (GroupLike k H)) (pA : H →ₗ[k] H)
    (hpt : IsPointed k H) : H →ₗ[k] H :=
  (DirectSum.toModule k (GroupLike k H) H
      (fun g => if g ∈ Δ then
        (LinearMap.mulRight k ((g : GroupLike k H) : H)) ∘ₗ pA ∘ₗ
          (LinearMap.mulRight k ((g⁻¹ : GroupLike k H) : H)) ∘ₗ (glComponent g).subtype
        else 0))
    ∘ₗ (glEquiv hpt).symm.toLinearMap

open Classical in
/-- On `x ∈ glComponent g`, `transProj Δ pA hpt x` is `pA (x g⁻¹) g` if `g ∈ Δ` and `0`
otherwise. -/
theorem transProj_apply_of_mem (Δ : Subgroup (GroupLike k H)) (pA : H →ₗ[k] H)
    (hpt : IsPointed k H) {g : GroupLike k H} {x : H} (hx : x ∈ glComponent g) :
    transProj Δ pA hpt x =
      if g ∈ Δ then pA (x * ((g⁻¹ : GroupLike k H) : H)) * (g : H) else 0 := by
  have hsymm : (glEquiv (k := k) (H := H) hpt).symm x
      = DirectSum.lof k (GroupLike k H) (fun g => ↥(glComponent g)) g ⟨x, hx⟩ := by
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    change x = DirectSum.coeLinearMap (glComponent (k := k) (H := H)) _
    simp [DirectSum.lof_eq_of, DirectSum.coeLinearMap_of]
  rw [transProj, LinearMap.comp_apply, LinearEquiv.coe_coe, hsymm, DirectSum.toModule_lof]
  by_cases hg : g ∈ Δ <;> simp [hg]

/-- If `pA` takes values in `A` and `A` is conjugation-stable, then `transProj` takes values in
`⨆_{d ∈ Δ} d · A`. -/
theorem transProj_mem (hconj : ConjStable Δ A) {pA : H →ₗ[k] H} (hpAmem : ∀ x : H, pA x ∈ A)
    (hpt : IsPointed k H) (x : H) : transProj Δ pA hpt x ∈ transComponent Δ A := by
  classical
  have hx : x ∈ ⨆ g : GroupLike k H, glComponent g := by
    rw [iSup_glComponent_eq_top hpt]; trivial
  refine Submodule.iSup_induction
    (motive := fun z => transProj Δ pA hpt z ∈ transComponent Δ A) _ hx ?_ (by simp) ?_
  · intro g y hy
    rw [transProj_apply_of_mem Δ pA hpt hy]
    by_cases hg : g ∈ Δ
    · rw [ite_eq_left hg]
      exact mem_transComponent_mul_right hconj hg (hpAmem _)
    · simp [hg]
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

/-- If `A ⊆ H₁` is conjugation-stable and `pA` is the identity on `A`, then `transProj` is the
identity on `⨆_{d ∈ Δ} d · A`. -/
theorem transProj_id (hconj : ConjStable Δ A)
    (hA : Subalgebra.toSubmodule A ≤ glComponent (1 : GroupLike k H))
    {pA : H →ₗ[k] H} (hpAid : ∀ a ∈ A, pA a = a) (hpt : IsPointed k H)
    {a : H} (ha : a ∈ transComponent Δ A) : transProj Δ pA hpt a = a := by
  classical
  refine Submodule.iSup_induction
    (motive := fun z => transProj Δ pA hpt z = z) _ ha ?_ (by simp) ?_
  · rintro d _ ⟨w, hw, rfl⟩
    simp only [LinearMap.mulLeft_apply]
    have hmem : ((d : GroupLike k H) : H) * w ∈ glComponent (d : GroupLike k H) :=
      mul_mem_glComponent (d : GroupLike k H) (hA hw)
    have hu : ((d : GroupLike k H) : H) * w * (((d : GroupLike k H)⁻¹ : GroupLike k H) : H) ∈ A :=
      hconj _ d.2 w hw
    rw [transProj_apply_of_mem Δ pA hpt hmem, ite_eq_left d.2, hpAid _ hu]
    have step : ((d : GroupLike k H) : H) * w * (((d : GroupLike k H)⁻¹ : GroupLike k H) : H)
        * ((d : GroupLike k H) : H)
        = ((d : GroupLike k H) : H) * (w *
            ((((d : GroupLike k H)⁻¹ : GroupLike k H) : H) * ((d : GroupLike k H) : H))) := by
      simp only [mul_assoc]
    rw [step, gl_inv_mul, mul_one]
  · intro y z hy hz
    rw [map_add, hy, hz]

/-- If `A ⊆ H₁` is conjugation-stable and `pA` is right `A`-linear, then `transProj` is right linear
over `⨆_{d ∈ Δ} d · A`: `transProj (x a) = transProj x · a`. -/
theorem transProj_mul (hconj : ConjStable Δ A)
    (hA : Subalgebra.toSubmodule A ≤ glComponent (1 : GroupLike k H))
    {pA : H →ₗ[k] H} (hpAmul : ∀ (x : H), ∀ u ∈ A, pA (x * u) = pA x * u)
    (hpt : IsPointed k H) (x : H) {a : H} (ha : a ∈ transComponent Δ A) :
    transProj Δ pA hpt (x * a) = transProj Δ pA hpt x * a := by
  classical
  -- the core computation, for `x` in a single component and `a = d · w`
  have hcore : ∀ (g d : GroupLike k H), d ∈ Δ → ∀ y ∈ glComponent g, ∀ w ∈ A,
      transProj Δ pA hpt (y * ((d : H) * w)) = transProj Δ pA hpt y * ((d : H) * w) := by
    intro g d hd y hy w hw
    have hdw : (d : H) * w ∈ glComponent d := mul_mem_glComponent d (hA hw)
    have hprod : y * ((d : H) * w) ∈ glComponent (g * d) :=
      mul_glComponent_le g d (Submodule.mul_mem_mul hy hdw)
    have hiff : g * d ∈ Δ ↔ g ∈ Δ :=
      ⟨fun h => by simpa using Δ.mul_mem h (Δ.inv_mem hd), fun h => Δ.mul_mem h hd⟩
    rw [transProj_apply_of_mem Δ pA hpt hprod, transProj_apply_of_mem Δ pA hpt hy]
    by_cases hg : g ∈ Δ
    · rw [ite_eq_left (hiff.2 hg), ite_eq_left hg]
      set G : H := (g : H)
      set D : H := (d : H)
      set Gi : H := ((g⁻¹ : GroupLike k H) : H)
      set Di : H := ((d⁻¹ : GroupLike k H) : H)
      have hu : G * D * w * (Di * Gi) ∈ A := by
        have := hconj (g * d) (Δ.mul_mem hg hd) w hw
        rwa [GroupLike.val_mul, gl_val_inv_mul] at this
      -- rewrite the argument of `pA`
      have harg : y * (D * w) * (((g * d)⁻¹ : GroupLike k H) : H)
          = (y * Gi) * (G * D * w * (Di * Gi)) := by
        rw [gl_val_inv_mul]
        exact conj_arg_eq (gl_inv_mul g) y D w Di
      rw [harg, hpAmul _ _ hu, GroupLike.val_mul]
      -- and simplify the resulting product
      exact conj_final_eq (gl_inv_mul g) (gl_inv_mul d) (pA (y * Gi)) w
    · rw [ite_eq_right (fun h => hg (hiff.1 h)), ite_eq_right hg, zero_mul]
  -- vary `x`, then `a`
  have hstep : ∀ (d : GroupLike k H), d ∈ Δ → ∀ w ∈ A, ∀ z : H,
      transProj Δ pA hpt (z * ((d : H) * w)) = transProj Δ pA hpt z * ((d : H) * w) := by
    intro d hd w hw z
    have hz : z ∈ ⨆ g : GroupLike k H, glComponent g := by
      rw [iSup_glComponent_eq_top hpt]; trivial
    refine Submodule.iSup_induction
      (motive := fun v => transProj Δ pA hpt (v * ((d : H) * w))
        = transProj Δ pA hpt v * ((d : H) * w)) _ hz ?_ (by simp) ?_
    · intro g y hy
      exact hcore g d hd y hy w hw
    · intro y v hy hv
      rw [add_mul, map_add, map_add, hy, hv, add_mul]
  refine Submodule.iSup_induction
    (motive := fun c => transProj Δ pA hpt (x * c) = transProj Δ pA hpt x * c) _ ha ?_
    (by simp) ?_
  · rintro d _ ⟨w, hw, rfl⟩
    simpa only [LinearMap.mulLeft_apply] using hstep (d : GroupLike k H) d.2 w hw x
  · intro b c hb hc
    rw [mul_add, map_add, hb, hc, mul_add]

end Proj

end HopfAlgebra.Cocommutative
