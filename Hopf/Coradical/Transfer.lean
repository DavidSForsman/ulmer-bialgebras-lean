module

public import Hopf.Coradical.Simple

/-!
# Transfer of the coradical filtration along an injective coalgebra map

Let `f : D →ₗ[k] C` be an injective linear map between `k`-coalgebras which is compatible with
the comultiplications, i.e. a monomorphism of coalgebras.  The statements below let one transfer
information from the finite-dimensional subcoalgebras of `C` (which exist in abundance by the
fundamental theorem of coalgebras) to `C` itself.

## Main results

* `Coalgebra.Coradical.isSubcoalgebra_map`: for `f` compatible with the comultiplications, the image
  of a subcoalgebra is a subcoalgebra.
* `Coalgebra.Coradical.map_wedge_le`: for `f` compatible with the comultiplications,
  `f (X ∧ Y) ≤ f X ∧ f Y`.
* `Coalgebra.Coradical.isSubcoalgebra_comap`: for `f` injective and compatible with the
  comultiplications, the preimage of a subcoalgebra is a subcoalgebra.
* `Coalgebra.Coradical.isSimpleSubcoalgebra_map`: for `f` injective and compatible with the
  comultiplications, the image of a simple subcoalgebra is simple.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1 and Chapter 9
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C D : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup D] [Module k D] [Coalgebra k D]

section Map

variable {f : D →ₗ[k] C}
  (hcomul : map f f ∘ₗ (comul : D →ₗ[k] D ⊗[k] D) = comul ∘ₗ f)

include hcomul

/-- For `f` compatible with the comultiplications, `Δ (f x) = (f ⊗ f) (Δ x)`. -/
theorem comul_apply_map (x : D) :
    comul (R := k) (f x) = map f f (comul (R := k) x) :=
  (LinearMap.ext_iff.1 hcomul x).symm

/-- The image of a subcoalgebra under a coalgebra map is a subcoalgebra. -/
theorem isSubcoalgebra_map {X : Submodule k D} (hX : IsSubcoalgebra X) :
    IsSubcoalgebra (X.map f) := by
  rw [isSubcoalgebra_iff]
  rintro _ ⟨x, hx, rfl⟩
  rw [comul_apply_map hcomul, ← map_tens]
  exact Submodule.mem_map_of_mem (comul_mem_tens hX hx)

/-- The image of a wedge product is contained in the wedge product of the images. -/
theorem map_wedge_le (X Y : Submodule k D) :
    Submodule.map f (wedge X Y) ≤ wedge (X.map f) (Y.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_wedge_iff, comul_apply_map hcomul]
  have hx' := mem_wedge_iff.1 hx
  have : map f f (comul (R := k) x)
      ∈ Submodule.map (map f f)
        (tens X (⊤ : Submodule k D) ⊔ tens (⊤ : Submodule k D) Y) :=
    Submodule.mem_map_of_mem hx'
  rw [Submodule.map_sup, map_tens, map_tens] at this
  have hle : tens (X.map f) ((⊤ : Submodule k D).map f)
        ⊔ tens ((⊤ : Submodule k D).map f) (Y.map f)
      ≤ tens (X.map f) (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) (Y.map f) :=
    sup_le (le_sup_of_le_left (tens_mono le_rfl le_top))
      (le_sup_of_le_right (tens_mono le_top le_rfl))
  exact hle this

end Map

section Injective

variable {f : D →ₗ[k] C} (hf : Function.Injective f)
  (hcomul : map f f ∘ₗ (comul : D →ₗ[k] D ⊗[k] D) = comul ∘ₗ f)

include hf hcomul

/-- The preimage of a subcoalgebra under an injective coalgebra map is a subcoalgebra. -/
theorem isSubcoalgebra_comap {V : Submodule k C} (hV : IsSubcoalgebra V) :
    IsSubcoalgebra (V.comap f) := by
  set A : Submodule k D := V.comap f with hA
  have hAV : A ≤ Submodule.comap f V := le_rfl
  -- the induced map on quotients is injective
  set q : (D ⧸ A) →ₗ[k] (C ⧸ V) := Submodule.mapQ A V f hAV with hq
  have hqinj : Function.Injective q := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun y hy => ?_
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker, hq, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact (Submodule.Quotient.mk_eq_zero A).2 hy
  rw [isSubcoalgebra_iff]
  intro x hx
  have hVcomul : comul (R := k) (f x) ∈ tens V V := comul_mem_tens hV hx
  rw [← tens_top_inf_top_tens]
  constructor
  · -- `comul x ∈ tens A ⊤`
    have hker : LinearMap.ker (LinearMap.rTensor D A.mkQ) = tens A (⊤ : Submodule k D) := by
      rw [ker_rTensor, Submodule.ker_mkQ]
    rw [← hker]
    refine LinearMap.mem_ker.2 ?_
    have hinj : Function.Injective (map q f) :=
      TensorProduct.map_injective_of_flat_flat _ _ hqinj hf
    apply hinj
    have hcomp : map q f ∘ₗ LinearMap.rTensor D A.mkQ
        = LinearMap.rTensor C V.mkQ ∘ₗ map f f := by
      rw [LinearMap.rTensor, LinearMap.rTensor, ← TensorProduct.map_comp,
        ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
      congr 1
    rw [← LinearMap.comp_apply (map q f), hcomp, LinearMap.comp_apply,
      ← comul_apply_map hcomul, map_zero]
    have : comul (R := k) (f x) ∈ tens V (⊤ : Submodule k C) := tens_mono le_rfl le_top hVcomul
    rw [← Submodule.ker_mkQ V, ← ker_rTensor] at this
    exact this
  · -- `comul x ∈ tens ⊤ A`
    have hker : LinearMap.ker (LinearMap.lTensor D A.mkQ) = tens (⊤ : Submodule k D) A := by
      rw [ker_lTensor, Submodule.ker_mkQ]
    rw [← hker]
    refine LinearMap.mem_ker.2 ?_
    have hinj : Function.Injective (map f q) :=
      TensorProduct.map_injective_of_flat_flat _ _ hf hqinj
    apply hinj
    have hcomp : map f q ∘ₗ LinearMap.lTensor D A.mkQ
        = LinearMap.lTensor C V.mkQ ∘ₗ map f f := by
      rw [LinearMap.lTensor, LinearMap.lTensor, ← TensorProduct.map_comp,
        ← TensorProduct.map_comp, LinearMap.id_comp, LinearMap.comp_id]
      congr 1
    rw [← LinearMap.comp_apply (map f q), hcomp, LinearMap.comp_apply,
      ← comul_apply_map hcomul, map_zero]
    have : comul (R := k) (f x) ∈ tens (⊤ : Submodule k C) V := tens_mono le_top le_rfl hVcomul
    rw [← Submodule.ker_mkQ V, ← ker_lTensor] at this
    exact this

/-- The image of a simple subcoalgebra under an injective coalgebra map is simple. -/
theorem isSimpleSubcoalgebra_map {X : Submodule k D} (hX : IsSimpleSubcoalgebra X) :
    IsSimpleSubcoalgebra (X.map f) := by
  obtain ⟨hXsub, hX0, hXmin⟩ := hX
  refine ⟨isSubcoalgebra_map hcomul hXsub, ?_, ?_⟩
  · intro h
    apply hX0
    have : X ≤ Submodule.comap f (X.map f) := Submodule.le_comap_map _ _
    rw [h] at this
    simpa [Submodule.comap_bot, LinearMap.ker_eq_bot.2 hf] using this
  · intro V hVX hV
    have hVcomap : IsSubcoalgebra (V.comap f) := isSubcoalgebra_comap hf hcomul hV
    have hle : V.comap f ≤ X := by
      intro x hx
      have : f x ∈ X.map f := hVX hx
      obtain ⟨y, hy, hxy⟩ := this
      rwa [← hf hxy]
    rcases hXmin _ hle hVcomap with h | h
    · left
      refine le_antisymm (fun v hv => ?_) bot_le
      have hvrange : v ∈ Submodule.map f X := hVX hv
      obtain ⟨x, hx, rfl⟩ := hvrange
      have : x ∈ V.comap f := hv
      rw [h] at this
      simp [(Submodule.mem_bot k).1 this]
    · right
      refine le_antisymm hVX ?_
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ V.comap f := by rw [h]; exact hx
      exact this

end Injective

end Coalgebra.Coradical
