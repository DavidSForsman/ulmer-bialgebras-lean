module

public import Hopf.Cocommutative.DescentTranslates

/-!
# Sub-Hopf algebras in Kostant's decomposition

In a pointed cocommutative Hopf algebra, a sub-Hopf algebra is the sum of the translates
of its irreducible part by its group-like elements. Its irreducible part is stable under
conjugation by those elements. These structural identities are inputs to the correspondence
layers.

## Main results

* `Coalgebra.Coradical.subcoalgebra_le_iSup_inf_glComponent`: a subcoalgebra `E` of a pointed
  cocommutative Hopf algebra lies in the sum of the `E ⊓ H_g` over the group-like elements `g ∈ E`.
* `Coalgebra.Coradical.glSubgroup`: the subgroup of `G(H)` formed by the group-like elements of a
  sub-Hopf algebra `K`.
* `Coalgebra.Coradical.toSubmodule_eq_transComponent`: in a pointed cocommutative Hopf algebra, a
  sub-Hopf algebra is `K = ⨆_{d ∈ G(K)} d · (K ∩ H₁)`.
* `Coalgebra.Coradical.conjStable_glSubgroup`: `K ∩ H₁` is stable under conjugation by the
  group-like elements of `K`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.6
* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### Subcoalgebras of a pointed cocommutative Hopf algebra -/

/-- A subcoalgebra `E` of a pointed cocommutative Hopf algebra is contained in the sum of its
traces on the Kostant components `H_g` of the group-like elements `g` that lie in `E`. -/
theorem subcoalgebra_le_iSup_inf_glComponent [Coalgebra.IsCocomm k H] (hpt : IsPointed k H)
    {E : Submodule k H} (hE : IsSubcoalgebra E) :
    E ≤ ⨆ g : GroupLike k H, ⨆ _ : (g : H) ∈ E, E ⊓ glComponent g := by
  let : Coalgebra k E := subCoalgebra hE
  have : Coalgebra.IsCocomm k E := ⟨subComul_comm hE⟩
  have hcomul : _root_.TensorProduct.map E.subtype E.subtype ∘ₗ (comul : E →ₗ[k] E ⊗[k] E)
      = comul ∘ₗ E.subtype := map_subtype_comp_subComul hE
  have hmap := congrArg (Submodule.map E.subtype) (iSup_irrComponent_eq_top' (k := k) (C := E))
  rw [Submodule.map_top, Submodule.range_subtype] at hmap
  conv_lhs => rw [← hmap]
  rw [Submodule.map_iSup]
  refine iSup_le fun S => ?_
  rw [Submodule.map_iSup]
  refine iSup_le fun hS => ?_
  rw [map_irrComponent_eq hE hS.1]
  obtain ⟨g, hg, hgS⟩ := hpt (Submodule.map E.subtype S)
    (isSimpleSubcoalgebra_map E.subtype_injective hcomul hS)
  have hgE : g ∈ E := by
    have hle : Submodule.map E.subtype S ≤ E := map_subtype_le_self S
    exact hle (by rw [hgS]; exact Submodule.mem_span_singleton_self _)
  have hcomp : irrComponent (Submodule.map E.subtype S) = glComponent ⟨g, hg⟩ := by
    rw [hgS]; rfl
  rw [hcomp, inf_comm]
  exact le_iSup_of_le ⟨g, hg⟩ (le_iSup_of_le hgE le_rfl)

/-! ### The group of group-like elements of a sub-Hopf algebra -/

/-- The group-like elements lying in a sub-Hopf algebra form a subgroup of `G(H)`. -/
def glSubgroup (K : Subalgebra k H) (hK : HopfAlgebra.IsSubHopfAlgebra k K) :
    Subgroup (GroupLike k H) where
  carrier := {d : GroupLike k H | (d : H) ∈ K}
  mul_mem' := by
    intro a b ha hb
    simpa only [Set.mem_ofPred_eq, GroupLike.val_mul] using K.mul_mem ha hb
  one_mem' := by
    simpa only [Set.mem_ofPred_eq, GroupLike.val_one] using K.one_mem
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, GroupLike.val_inv] using hK.antipode_mem _ ha

variable (k H) in
/-- The intersection of a subalgebra with the irreducible component of the unit. -/
noncomputable def irrPart (K : Subalgebra k H) : Subalgebra k H := K ⊓ irrSubalgebra k H

/-- The underlying submodule of `irrPart k H K` is `K ⊓ glComponent 1` (true by definition). -/
theorem toSubmodule_irrPart (K : Subalgebra k H) :
    Subalgebra.toSubmodule (irrPart k H K)
      = Subalgebra.toSubmodule K ⊓ glComponent (1 : GroupLike k H) := rfl

/-- The irreducible part `K ⊓ H₁` of a subalgebra `K` lies in the irreducible component `H₁` of the
unit. -/
theorem toSubmodule_irrPart_le (K : Subalgebra k H) :
    Subalgebra.toSubmodule (irrPart k H K) ≤ glComponent (1 : GroupLike k H) := by
  rw [toSubmodule_irrPart]
  exact inf_le_right

/-! ### The Kostant shape of a sub-Hopf algebra -/

/-- **The Kostant shape of a sub-Hopf algebra** of a pointed cocommutative Hopf algebra:
`K = ⨆_{d ∈ G(K)} d · (K ∩ H₁)`. -/
theorem toSubmodule_eq_transComponent [Coalgebra.IsCocomm k H] (hpt : IsPointed k H)
    {K : Subalgebra k H} (hK : HopfAlgebra.IsSubHopfAlgebra k K) :
    Subalgebra.toSubmodule K
      = HopfAlgebra.Cocommutative.transComponent (glSubgroup K hK) (irrPart k H K) := by
  refine le_antisymm ?_ ?_
  · -- `≤` : decompose `K` along the components of the group-like elements it contains
    have hEsub : IsSubcoalgebra (Subalgebra.toSubmodule K) := fun x hx => hK.comul_mem x hx
    refine le_trans (subcoalgebra_le_iSup_inf_glComponent hpt hEsub) ?_
    refine iSup_le fun d => iSup_le fun hd => ?_
    rintro x ⟨hxK, hxd⟩
    simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule] at hxK
    obtain ⟨a, ha, rfl⟩ := mem_glComponent_iff_exists_left.1 hxd
    have haK : a ∈ K := by
      have hinv : ((d⁻¹ : GroupLike k H) : H) ∈ K := by
        simpa only [GroupLike.val_inv] using hK.antipode_mem _ hd
      have : ((d⁻¹ : GroupLike k H) : H) * ((d : H) * a) = a := by
        rw [← mul_assoc, HopfAlgebra.Cocommutative.gl_inv_mul, one_mul]
      rw [← this]
      exact K.mul_mem hinv hxK
    exact HopfAlgebra.Cocommutative.mem_transComponent_of_mem (Δ := glSubgroup K hK) hd
      (A := irrPart k H K) ⟨haK, ha⟩
  · -- `≥` : each translate `d · (K ∩ H₁)` lies in `K`
    refine iSup_le fun d => ?_
    rintro _ ⟨a, ha, rfl⟩
    simp only [SetLike.mem_coe, Subalgebra.mem_toSubmodule] at ha
    exact K.mul_mem d.2 ha.1

/-- `K ∩ H₁` is stable under conjugation by the group-like elements of `K`. -/
theorem conjStable_glSubgroup {K : Subalgebra k H} (hK : HopfAlgebra.IsSubHopfAlgebra k K) :
    HopfAlgebra.Cocommutative.ConjStable (glSubgroup K hK) (irrPart k H K) := by
  intro d hd a ha
  obtain ⟨haK, ha1⟩ := ha
  have hinv : ((d⁻¹ : GroupLike k H) : H) ∈ K := by
    simpa only [GroupLike.val_inv] using hK.antipode_mem _ hd
  refine ⟨K.mul_mem (K.mul_mem hd haK) hinv, ?_⟩
  have h1 : (d : H) * a ∈ glComponent d := mul_mem_glComponent d ha1
  have h2 : ((d⁻¹ : GroupLike k H) : H) ∈ glComponent d⁻¹ :=
    le_irrComponent _ (Submodule.mem_span_singleton_self _)
  have h3 := mul_glComponent_le d d⁻¹ (Submodule.mul_mem_mul h1 h2)
  rwa [mul_inv_cancel] at h3

end Coalgebra.Coradical
