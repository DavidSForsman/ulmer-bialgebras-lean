module

public import Mathlib.RingTheory.Flat.TorsionFree
public import AffineGroupSchemes.HopfPushout

/-!
# Corestriction along an injective morphism of Hopf algebras

If `i : S →ₐc[k] X` is an injective morphism of commutative Hopf algebras over a commutative
ring and `t : T →ₐc[k] X` is a morphism whose image is contained in the image of `i`, then `t`
factors uniquely through `i` by a morphism of Hopf algebras `t' : T →ₐc[k] S`.

The point is that the factorization, which exists trivially as a map of algebras, is
automatically compatible with the comultiplications and the counits: for the counit this is
immediate, and for the comultiplication it follows from the injectivity of `i ⊗ i`, which holds
if its source and target are flat over the base ring.

## Main results

* `AffineGroupSchemes.exists_unique_corestriction`: if `i : S →ₐc[k] X` is injective between
  flat modules and every value of `t` lies in the image of `i`, there is a unique morphism `t'`
  with `i ∘ t' = t`.

## References

* [D. Forsman, *On the semi-abelianness of affine
  group schemes*][forsman2026semiabeliannessaffinegroupschemes], Theorem 3.12
-/

@[expose] public section

open TensorProduct Coalgebra Function

namespace AffineGroupSchemes


universe u

variable {k S X T : Type u} [CommRing k] [CommRing S] [CommRing X] [CommRing T]
  [HopfAlgebra k S] [HopfAlgebra k X] [HopfAlgebra k T]

/-- The tensor square of an injective morphism of `k`-algebras with flat source and target
is injective. -/
lemma injective_algTensorMap_of_injective {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Module.Flat k A] [Module.Flat k B]
    (p : A →ₐ[k] B) (hp : Injective p) :
    Injective (Algebra.TensorProduct.map p p) := by
  have h : Injective (TensorProduct.map (p.toLinearMap) (p.toLinearMap)) :=
    TensorProduct.map_injective_of_flat_flat _ _ hp hp
  intro x y hxy
  refine h ?_
  have hx : ∀ z : A ⊗[k] A, Algebra.TensorProduct.map p p z
      = TensorProduct.map p.toLinearMap p.toLinearMap z := by
    intro z
    induction z with
    | tmul a b => simp
    | add s t hs ht => simp [hs, ht]
  rw [← hx, ← hx]
  exact hxy

/-- **Corestriction.** A morphism of commutative Hopf algebras whose image is contained in the
image of an injective morphism of flat commutative Hopf algebras factors uniquely through it
by a morphism of Hopf algebras. -/
theorem exists_unique_corestriction [Module.Flat k S] [Module.Flat k X]
    (i : S →ₐc[k] X) (hi : Injective i) (t : T →ₐc[k] X)
    (hmem : ∀ τ : T, ∃ s : S, i s = t τ) :
    ∃! t' : T →ₐc[k] S, ∀ τ : T, i (t' τ) = t τ := by
  set i₀ : S →ₐ[k] X := (i : S →ₐ[k] X) with hi₀
  have hmem' : ∀ τ : T, (t : T →ₐ[k] X) τ ∈ i₀.range := fun τ => by
    obtain ⟨s, hs⟩ := hmem τ
    exact ⟨s, hs⟩
  set t₀ : T →ₐ[k] i₀.range := (t : T →ₐ[k] X).codRestrict i₀.range hmem' with ht₀
  set d : T →ₐ[k] S := ((AlgEquiv.ofInjective i₀ hi).symm.toAlgHom).comp t₀ with hd
  have hd_spec : ∀ τ : T, i (d τ) = t τ := by
    intro τ
    exact congr(Subtype.val $((AlgEquiv.ofInjective i₀ hi).apply_symm_apply (t₀ τ)))
  have hcounit : (Bialgebra.counitAlgHom k S).comp d = Bialgebra.counitAlgHom k T := by
    ext τ
    simpa using congr(counit (R := k) $(hd_spec τ))
  have hid : i₀.comp d = (t : T →ₐ[k] X) := by ext τ; exact hd_spec τ
  have hcomul : (Algebra.TensorProduct.map d d).comp (Bialgebra.comulAlgHom k T)
      = (Bialgebra.comulAlgHom k S).comp d := by
    ext τ
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
      Bialgebra.comulAlgHom_apply]
    refine injective_algTensorMap_of_injective i₀ hi ?_
    rw [algTensorMap_comp, hid, algTensorMap_comul t τ, ← hd_spec τ, ← algTensorMap_comul i (d τ)]
  refine ⟨BialgHom.ofAlgHom d hcounit hcomul, hd_spec, ?_⟩
  intro d' hd'
  refine DFunLike.ext _ _ fun τ => hi ?_
  rw [hd' τ]
  exact (hd_spec τ).symm

end AffineGroupSchemes
