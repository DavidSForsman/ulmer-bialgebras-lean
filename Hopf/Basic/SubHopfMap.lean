module

public import Hopf.Basic.SubHopfAlgebra
public import Hopf.Basic.HopfFaithfulFlatness

/-!
# Restricting a morphism of Hopf algebras to sub-Hopf algebras

Let `f : A →ₐc[k] B` be a morphism of commutative Hopf algebras over a field, let `A₀ ≤ A` and
`B₀ ≤ B` be sub-Hopf algebras with `f A₀ ⊆ B₀`.  Then `f` restricts to a morphism of Hopf
algebras `A₀ →ₐc[k] B₀` (`HopfAlgebra.subBialgHom`), which is injective if `f` is.

## Main definitions and results

* `HopfAlgebra.subBialgHom`: the restriction of `f`;
* `HopfAlgebra.subBialgHom_coe`, `HopfAlgebra.subBialgHom_injective`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open HopfAlgebra
namespace HopfAlgebra

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B]
  (f : A →ₐc[k] B) (A₀ : Subalgebra k A) (B₀ : Subalgebra k B)
  [IsSubHopfAlgebra k A₀] [IsSubHopfAlgebra k B₀] (hf : ∀ a ∈ A₀, f a ∈ B₀)

include hf

/-- The restriction of `f : A →ₐc[k] B` to sub-Hopf algebras, as an algebra map. -/
def subAlgHomRestrict : (↥A₀) →ₐ[k] (↥B₀) :=
  AlgHom.codRestrict ((f : A →ₐ[k] B).comp A₀.val) B₀ (fun a => hf (a : A) a.2)

omit [IsSubHopfAlgebra k A₀] [IsSubHopfAlgebra k B₀] in
/-- `subAlgHomRestrict f A₀ B₀ hf` acts as `f` on underlying elements. -/
@[simp] lemma subAlgHomRestrict_coe (a : ↥A₀) :
    ((subAlgHomRestrict f A₀ B₀ hf a : ↥B₀) : B) = f (a : A) := rfl

/-- The restriction of `f : A →ₐc[k] B` to sub-Hopf algebras, as a morphism of Hopf algebras. -/
noncomputable def subBialgHom : (↥A₀) →ₐc[k] (↥B₀) :=
  BialgHom.ofAlgHom (subAlgHomRestrict f A₀ B₀ hf)
    (by
      ext a
      simp [subAlgHomRestrict_coe])
    (by
      ext a
      apply mapVal2_injective (K := B₀)
      set φ := subAlgHomRestrict f A₀ B₀ hf with hφ
      have hmap : ∀ z : (↥A₀) ⊗[k] (↥A₀),
          mapVal2 (k := k) B₀ ((Algebra.TensorProduct.map φ φ) z)
            = TensorProduct.map f.toLinearMap f.toLinearMap (mapVal2 (k := k) A₀ z) := by
        intro z
        induction z using TensorProduct.inductionOn with
        | tmul a b => simp [mapVal2, hφ, subAlgHomRestrict]; rfl
        | add p q hp hq => simp only [map_add, hp, hq]
      have hcomulf : ∀ x : A, comul (R := k) (f x)
          = TensorProduct.map f.toLinearMap f.toLinearMap (comul (R := k) x) := by
        intro x
        exact (DFunLike.congr_fun f.map_comp_comul x).symm
      have hLHS : mapVal2 (k := k) B₀ ((Algebra.TensorProduct.map φ φ) (comul (R := k) a))
          = TensorProduct.map f.toLinearMap f.toLinearMap (comul (R := k) (a : A)) := by
        rw [hmap, mapVal2_comul]
      have hRHS : mapVal2 (k := k) B₀ (comul (R := k) (φ a))
          = TensorProduct.map f.toLinearMap f.toLinearMap (comul (R := k) (a : A)) := by
        rw [mapVal2_comul, hφ, subAlgHomRestrict_coe, hcomulf]
      exact hLHS.trans hRHS.symm)

/-- `subBialgHom f A₀ B₀ hf` acts as `f` on underlying elements. -/
@[simp] lemma subBialgHom_coe (a : ↥A₀) : ((subBialgHom f A₀ B₀ hf a : ↥B₀) : B) = f (a : A) := rfl

/-- If `f` is injective, so is its restriction `A₀ → B₀`. -/
lemma subBialgHom_injective (hinj : Function.Injective f) :
    Function.Injective (subBialgHom f A₀ B₀ hf) := by
  intro a b hab
  have h : f (a : A) = f (b : A) := by
    rw [← subBialgHom_coe f A₀ B₀ hf a, ← subBialgHom_coe f A₀ B₀ hf b, hab]
  exact Subtype.ext (hinj h)

end HopfAlgebra
end
