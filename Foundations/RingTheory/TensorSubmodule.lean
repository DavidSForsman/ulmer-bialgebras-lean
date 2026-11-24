module

public import Foundations.RingTheory.AbsFlatClass

/-!
# Submodules of a tensor product of modules

Elementary facts about tensor products of modules which are used to manipulate the
conditions "`Δ x - x ⊗ 1 ∈ H ⊗ I`" appearing in Takeuchi's description of normal Hopf ideals.
Only flatness of the modules involved is used, so everything is stated over an absolutely flat
base ring (`IsAbsFlat`): a field, or — as in Section 4 of the paper — a commutative von
Neumann regular ring.

## Main results

* `TensorProduct.mem_range_lTensor_ker` / `TensorProduct.mem_range_rTensor_ker`: if
  `(id ⊗ θ) t = 0`, then `t` lies in the image of `M ⊗ ker θ`;
* `TensorProduct.inf_range_rTensor_lTensor`: `(V ⊗ N) ⊓ (M ⊗ W) = V ⊗ W` inside `M ⊗ N`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Section 4
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes],
  Section 4
-/

@[expose] public section

open TensorProduct

namespace TensorProduct

variable {k M N P : Type*} [CommRing k] [AddCommGroup M] [Module k M] [AddCommGroup N]
  [Module k N] [AddCommGroup P] [Module k P]

/-- If `(id ⊗ θ) t = 0` then `t` comes from `M ⊗ ker θ`. -/
lemma mem_range_lTensor_ker [IsAbsFlat k] (θ : N →ₗ[k] P) {t : M ⊗[k] N}
    (h : LinearMap.lTensor M θ t = 0) :
    t ∈ LinearMap.range (LinearMap.lTensor M (LinearMap.ker θ).subtype) :=
  ((Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map θ)) t).mp h

/-- If `(θ ⊗ id) t = 0` then `t` comes from `ker θ ⊗ M`. -/
lemma mem_range_rTensor_ker [IsAbsFlat k] (θ : N →ₗ[k] P) {t : N ⊗[k] M}
    (h : LinearMap.rTensor M θ t = 0) :
    t ∈ LinearMap.range (LinearMap.rTensor M (LinearMap.ker θ).subtype) :=
  ((Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map θ)) t).mp h

/-- The image of `M ⊗ W` in `M ⊗ N` is the kernel of `id ⊗ (N → N/W)`. -/
lemma range_lTensor_subtype_eq_ker [Module.Flat k M] (W : Submodule k N) :
    LinearMap.range (LinearMap.lTensor M W.subtype) = LinearMap.ker (LinearMap.lTensor M W.mkQ) :=
  ((Module.Flat.lTensor_exact M (LinearMap.exact_subtype_mkQ W)).linearMap_ker_eq).symm

/-- The image of `V ⊗ N` in `M ⊗ N` is the kernel of `(M → M/V) ⊗ id`. -/
lemma range_rTensor_subtype_eq_ker [Module.Flat k N] (V : Submodule k M) :
    LinearMap.range (LinearMap.rTensor N V.subtype) = LinearMap.ker (LinearMap.rTensor N V.mkQ) :=
  ((Module.Flat.rTensor_exact N (LinearMap.exact_subtype_mkQ V)).linearMap_ker_eq).symm

variable (V : Submodule k M) (W : Submodule k N)

/-- The map `V ⊗ W → M ⊗ N` induced by the inclusions factors as `lTensor` followed by
`rTensor`. -/
lemma rTensor_comp_lTensor :
    (LinearMap.rTensor N V.subtype) ∘ₗ (LinearMap.lTensor V W.subtype)
      = TensorProduct.map V.subtype W.subtype := by
  ext v w; simp

/-- The map `V ⊗ W → M ⊗ N` induced by the inclusions factors as `rTensor` followed by
`lTensor`. -/
lemma lTensor_comp_rTensor :
    (LinearMap.lTensor M W.subtype) ∘ₗ (LinearMap.rTensor W V.subtype)
      = TensorProduct.map V.subtype W.subtype := by
  ext v w; simp

/-- The maps `V ⊗ N → M ⊗ N → M ⊗ (N ⧸ W)` and `V ⊗ N → V ⊗ (N ⧸ W) → M ⊗ (N ⧸ W)` agree. -/
lemma lTensor_mkQ_comp_rTensor_subtype :
    (LinearMap.lTensor M W.mkQ) ∘ₗ (LinearMap.rTensor N V.subtype)
      = (LinearMap.rTensor (N ⧸ W) V.subtype) ∘ₗ (LinearMap.lTensor V W.mkQ) := by
  ext v n; simp

variable [IsAbsFlat k]

/-- **`(V ⊗ N) ⊓ (M ⊗ W) = V ⊗ W`** inside `M ⊗ N`, for subspaces `V ≤ M` and `W ≤ N`. -/
theorem inf_range_rTensor_lTensor :
    LinearMap.range (LinearMap.rTensor N V.subtype) ⊓
        LinearMap.range (LinearMap.lTensor M W.subtype)
      = LinearMap.range (TensorProduct.map V.subtype W.subtype) := by
  apply le_antisymm
  · rintro t ⟨⟨s, rfl⟩, ht2⟩
    have h0 : LinearMap.lTensor M W.mkQ (LinearMap.rTensor N V.subtype s) = 0 := by
      rw [range_lTensor_subtype_eq_ker] at ht2
      exact ht2
    have h1 : LinearMap.rTensor (N ⧸ W) V.subtype (LinearMap.lTensor V W.mkQ s) = 0 := by
      rw [← LinearMap.comp_apply, ← lTensor_mkQ_comp_rTensor_subtype, LinearMap.comp_apply]
      exact h0
    have h2 : LinearMap.lTensor V W.mkQ s = 0 :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := N ⧸ W) V.subtype
        (Submodule.injective_subtype V) (by simpa using h1)
    have h3 : s ∈ LinearMap.range (LinearMap.lTensor V W.subtype) := by
      rw [range_lTensor_subtype_eq_ker]
      exact h2
    obtain ⟨s', hs'⟩ := h3
    exact ⟨s', by rw [← hs', ← LinearMap.comp_apply, rTensor_comp_lTensor]⟩
  · rintro t ⟨s, rfl⟩
    refine ⟨⟨LinearMap.lTensor V W.subtype s, ?_⟩, ⟨LinearMap.rTensor W V.subtype s, ?_⟩⟩
    · rw [← LinearMap.comp_apply, rTensor_comp_lTensor]
    · rw [← LinearMap.comp_apply, lTensor_comp_rTensor]

end TensorProduct
