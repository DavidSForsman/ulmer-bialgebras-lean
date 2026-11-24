module

public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Examples.MonModel

/-!
# The tensor product with one argument fixed

The functor `MonEx.tensFunctor C : (Fin 2 → C) ⥤ C` of a monoidal category, with one of its two
arguments fixed (`UlmerBialgebras.updateFunctor`), is a tensoring functor. This identifies the
componentwise preservation hypotheses of the `Σ_Mon`-model of `C` (`PreservesColimitsComponentwise`)
with preservation by `X ⊗ -` and `- ⊗ X`.

## Main definitions

* `UlmerBialgebras.MonEx.updateTensZero`: fixing the second argument gives `- ⊗ x 1`.
* `UlmerBialgebras.MonEx.updateTensOne`: fixing the first argument gives `x 0 ⊗ -`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Examples
  3.20 (1), Lemma 4.16
-/

@[expose] public section

universe u v

namespace UlmerBialgebras.MonEx

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Fixing the second argument of the tensor product. -/
def updateTensZero (x : ∀ _ : Fin 2, C) :
    updateFunctor x 0 ⋙ MonEx.tensFunctor C ≅ tensorRight (x 1) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Fin.isValue, updateFunctor, MonEx.tensFunctor, Functor.comp_obj,
        Functor.flip_obj_obj, curriedTensor_obj_obj, Functor.comp_map, Functor.pi'_map,
        ↓dreduceDIte, Functor.id_map, Iso.refl_hom,
        Functor.flip_obj_map, curriedTensor_map_app]
    exact (Category.comp_id _).trans ((tensorHom_id _ _).trans (Category.id_comp _).symm))

/-- Fixing the first argument of the tensor product. -/
def updateTensOne (x : ∀ _ : Fin 2, C) :
    updateFunctor x 1 ⋙ MonEx.tensFunctor C ≅ tensorLeft (x 0) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by
    simp only [Fin.isValue, updateFunctor, MonEx.tensFunctor, Functor.comp_obj,
        curriedTensor_obj_obj, Functor.comp_map, Functor.pi'_map, ↓dreduceDIte,
        Functor.id_map, Iso.refl_hom, curriedTensor_obj_map]
    exact (Category.comp_id _).trans ((id_tensorHom _ _).trans (Category.id_comp _).symm))


end UlmerBialgebras.MonEx
