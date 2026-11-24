module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Isomorphisms of categories from a faithful functor with a strict section

A helper for Examples 3.20 (1), (2) and (4): if `F : A ⥤ B` is faithful and `G : B ⥤ A`
satisfies `G ⋙ F = 𝟭 B` and `G (F a) = a` for every object `a`, then also `F ⋙ G = 𝟭 A`, so `F`
and `G` are mutually inverse isomorphisms of categories.

In the examples, `F` is the comparison functor from `M^T` and `G` its inverse. The equation
`G ⋙ F = 𝟭` holds by `rfl` (structure eta), while `G (F a) = a` needs function extensionality over
the function symbols.

## Main results

* `UlmerBialgebras.Paper.comp_eq_id_of_faithful`: if `F` is faithful, `G ⋙ F = 𝟭 B` and
  `G (F a) = a` for every object `a`, then `F ⋙ G = 𝟭 A`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20
-/

@[expose] public section

namespace UlmerBialgebras.Paper

open CategoryTheory

/-- If `F` is faithful, `G ⋙ F = 𝟭` and `G (F a) = a` for every object `a`, then
`F ⋙ G = 𝟭`. -/
lemma comp_eq_id_of_faithful {A B : Type*} [Category A] [Category B] (F : A ⥤ B) (G : B ⥤ A)
    [F.Faithful] (hGF : G ⋙ F = 𝟭 B) (hobj : ∀ a, G.obj (F.obj a) = a) : F ⋙ G = 𝟭 A := by
  refine CategoryTheory.Functor.ext hobj (fun a a' f => F.map_injective ?_)
  have h := CategoryTheory.Functor.congr_hom hGF (F.map f)
  simp only [Functor.comp_map, Functor.id_map] at h
  simp [h, eqToHom_map]

end UlmerBialgebras.Paper
