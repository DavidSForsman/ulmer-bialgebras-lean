module

public import UlmerBialgebras.Proofs.Sec5.ExtrasAlgTheory
public import UlmerBialgebras.Proofs.Sec5.Sec5Proofs
public import UlmerBialgebras.Proofs.Sec5.ColimitsOfAlgebras
public import UlmerBialgebras.Kan.KanInverse

/-!
# Monadicity of categories of models of a theory of universal algebra

Corollary 5.9 of [forsman2026syntactic] speaks of "a single-sorted theory `T` of universal algebra
with a countable signature". `UlmerBialgebras.Paper.cartThy_monadic` states it for an algebraic
single-sorted `Σ_Cart`-theory. This file states it for an equational theory `T` over a language
`L : MSLanguage` (`MSLanguage.Theory.ModelCat`), and proves it from `cartThy_monadic` through the
translation `MSLanguage.Theory.toCartTheory`: the category of models of `T` is isomorphic to the
category of models of the translated theory, over `C^S`
(`UlmerBialgebras.Paper.modelCat_iso_cartThy_univ`).

## Main results

* `UlmerBialgebras.Paper.UniversalAlgebra.toCartTheory_isAlgebraic`: the translated theory is
  algebraic.
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_monadic`: Corollary 5.9 for `T.ModelCat C`: the
  category of models has countable colimits and its forgetful functor is monadic.
* `UlmerBialgebras.Paper.UniversalAlgebra.modelCat_strictlyCreates`: the rest of Corollary 5.9:
  the forgetful functor strictly creates countable sifted colimits. Strict creation passes along
  the isomorphism by `UlmerBialgebras.strictlyCreatesLeftKan_of_inv`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 5.9
-/

@[expose] public section

universe v w s

namespace UlmerBialgebras.Paper.UniversalAlgebra

open CategoryTheory Limits Cart MSLanguage

variable {L : MSLanguage.{s, s}}

/-- The `Σ_Cart`-theory of an equational theory is algebraic: the codomain of every function
symbol and of every equation is a sort. -/
theorem toCartTheory_isAlgebraic (T : L.Theory) : T.toCartTheory.IsAlgebraic :=
  ⟨fun _ => trivial, fun _ => trivial⟩

/-- The isomorphism of `modelCat_iso_cartThy_univ`, as an equivalence. -/
noncomputable def modelCatEquivCartThy (C : Type (max s v w)) [Category.{max s v} C]
    [CartesianMonoidalCategory C] (T : L.Theory) : T.ModelCat C ≌ Theory.cartThy.{v, w, s} C T :=
  let h := modelCat_iso_cartThy_univ.{v, w, s} C T
  CategoryTheory.Equivalence.mk h.choose h.choose_spec.choose
    (eqToIso h.choose_spec.choose_spec.1.symm) (eqToIso h.choose_spec.choose_spec.2.1)

/-- The equivalence `modelCatEquivCartThy` lies over `C^S`. -/
theorem modelCatEquivCartThy_forget (C : Type (max s v w)) [Category.{max s v} C]
    [CartesianMonoidalCategory C] (T : L.Theory) :
    (modelCatEquivCartThy.{v, w, s} C T).functor ⋙ Theory.cartThyForget.{v, w, s} C T =
      Theory.ModelCat.forget C T :=
  (modelCat_iso_cartThy_univ.{v, w, s} C T).choose_spec.choose_spec.2.2

attribute [local instance] catOfSizeHom in
/-- **Corollary 5.9 for a theory of universal algebra.** Let `C` be a cartesian closed category
with countable colimits, and `T` an equational theory over a single-sorted language `L` with
countably many function symbols. Then the category `T.ModelCat C` of models of `T` in `C` has
countable colimits, and its forgetful functor to `C^S` is monadic. -/
theorem modelCat_monadic {L : MSLanguage.{s, s}} (C : Type (max s v w))
    [Category.{max s v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{max s v} C) [Unique L.Sorts]
    (hsize : Cardinal.mk L.Functions ≤ Cardinal.aleph0) (T : L.Theory) :
    Nonempty (MonadicRightAdjoint (Theory.ModelCat.forget C T)) ∧
      HasColimitsOfSizeLE Cardinal.aleph0.{max s v} (T.ModelCat C) := by
  obtain ⟨⟨hmon⟩, hcolT, -⟩ := cartThy_monadic.{max s v w, max s v, s, s, s} hcol L.toCartSig
    T.toCartTheory
    (Cardinal.mk_eq_one L.Sorts) hsize (toCartTheory_isAlgebraic T)
  set e := modelCatEquivCartThy.{v, w, s} C T
  refine ⟨?_, fun J _ hJ => ?_⟩
  · rw [← modelCatEquivCartThy_forget]
    have : MonadicRightAdjoint (Theory.cartThyForget.{v, w, s} C T) := hmon
    exact ColimitsOfAlgebras.monadic_comp e _
  · have := hcolT J hJ
    exact Adjunction.hasColimitsOfShape_of_equivalence e.functor

attribute [local instance] catOfSizeHom in
/-- **Corollary 5.9 for a theory of universal algebra, strict creation.** Under the hypotheses of
`modelCat_monadic`, the forgetful functor `T.ModelCat C ⥤ C^S` strictly creates countable
sifted colimits. -/
theorem modelCat_strictlyCreates {L : MSLanguage.{s, s}} (C : Type (max s v w))
    [Category.{max s v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
    (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{max s v} C) [Unique L.Sorts]
    (hsize : Cardinal.mk L.Functions ≤ Cardinal.aleph0) (T : L.Theory)
    (I : Cat.{max s v, max s v w}) [IsSifted (I : Type (max s v w))]
    (hI : Cardinal.mk (I : Type (max s v w)) ≤ Cardinal.aleph0)
    (d : I ⟶ Cat.of (T.ModelCat C)) :
    StrictlyCreatesLeftKan (toOne I) d (Theory.ModelCat.forget C T).toCatHom := by
  obtain ⟨-, -, hcr⟩ := cartThy_monadic.{max s v w, max s v, s, s, s} hcol L.toCartSig
    T.toCartTheory (Cardinal.mk_eq_one L.Sorts) hsize (toCartTheory_isAlgebraic T)
  obtain ⟨F, G, hFG, hGF, hF⟩ := modelCat_iso_cartThy_univ.{v, w, s} C T
  rw [← hF]
  exact strictlyCreatesLeftKan_comp (toOne I) d F.toCatHom _ (hcr I hI (d ≫ F.toCatHom))
    (fun _ _ => strictlyCreatesLeftKan_of_inv (toOne I) d (g := G.toCatHom)
      (congrArg Functor.toCatHom hFG) (congrArg Functor.toCatHom hGF))

end UlmerBialgebras.Paper.UniversalAlgebra
