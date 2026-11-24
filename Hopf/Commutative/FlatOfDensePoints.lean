module

public import Hopf.Commutative.PointTranslation
public import Foundations.RingTheory.GenericFreenessReduced
public import Foundations.RingTheory.LocallyFreeFlat
public import Hopf.Commutative.RelativeHopfModuleQuot

/-!
# Takeuchi's Proposition 3.7, relative to the density of the points

Takeuchi's Proposition 3.7 (M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf
algebras*, manuscripta math. **7** (1972), 251–270) proves the faithful flatness theorem for a
*reduced* Hopf subalgebra `K` of a commutative Hopf algebra `H` over an algebraically closed
field.  Its proof has three ingredients:

1. **generic freeness** over the reduced noetherian ring `K`
   (`Module.Free.exists_free_localizedModule_of_isReduced`, Takeuchi's Lemma 3.4);
2. the **translation action** of the points `u : H →ₐ[k] k` on a relative `(H,K)`-Hopf module `M`,
   which is semilinear over the translation automorphisms of `K`
   (`HopfAlgebra.Commutative.transl_smul`);
3. the **density** of the points: the translates `u ⇀ g` of a nonzero `g ∈ K` generate the unit
   ideal of `K` (Takeuchi's Lemmas 3.5 and 3.6 together with Sweedler's theorem; this is where
   `k` algebraically closed and `K` reduced and finitely generated are used).

The first two are formalised; the third is carried here as an explicit named hypothesis
`HopfAlgebra.Commutative.DensePointTranslates` — never as an axiom or a `sorry`.  Relative to it,
this file proves Proposition 3.7:

* `HopfAlgebra.Commutative.flat_of_isReduced_of_densePointTranslates`: every relative `(H,K)`-Hopf
  module which is finitely generated over `K` is flat;
* `HopfAlgebra.Commutative.faithfullyFlat_of_isReduced_of_densePointTranslates`: consequently, by
  Takeuchi's Proposition 2.4, `H` is faithfully flat over `K`.

## Main results

* `HopfAlgebra.Commutative.DensePointTranslates`: the hypothesis that the translates of a nonzero
  element of `K` by the points of `H` generate the unit ideal of `K`.
* `HopfAlgebra.Commutative.flat_of_isReduced_of_densePointTranslates`: for a reduced noetherian `K`,
  given `DensePointTranslates`, a relative `(H,K)`-Hopf module finitely generated over `K` is flat
  over `K` (Takeuchi's Proposition 3.7).
* `HopfAlgebra.Commutative.faithfullyFlat_of_isReduced_of_densePointTranslates`: for such `K`, given
  `DensePointTranslates φ`, if the algebra map `K → H` is `φ` and is injective, then `H` is
  faithfully flat over `K`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 3.4–3.6 and Proposition 3.7
* [A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*][EGAIV2], Section 6.9
-/

@[expose] public section

section
open Coalgebra Coalgebra.Comodule HopfAlgebra HopfAlgebra.Commutative

namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

section

variable {k K H : Type u} [Field k] [CommRing K] [CommRing H] [HopfAlgebra k K] [HopfAlgebra k H]
  (φ : K →ₐc[k] H)

/-- The translation `x ↦ ∑ u (φ x₍₂₎) x₍₁₎` of `K` by a point `u : H →ₐ[k] k`, an algebra
automorphism of `K`. -/
noncomputable def pointAut (u : H →ₐ[k] k) : K ≃ₐ[k] K :=
  translAlgEquiv (u.comp (φ : K →ₐ[k] H))

/-- `pointAut φ u` agrees with `translAlgHom (u ∘ φ)` pointwise. -/
lemma pointAut_apply (u : H →ₐ[k] k) (x : K) :
    pointAut φ u x = translAlgHom (u.comp (φ : K →ₐ[k] H)) x :=
  translAlgHom_apply _ x

/-- **The density hypothesis** of Takeuchi's Proposition 3.7: the translates of a nonzero element
of `K` by the points of `H` generate the unit ideal of `K`.  Takeuchi derives this from the
Nullstellensatz (Lemma 3.6) and Sweedler's theorem, for `k` algebraically closed and `K` reduced
and finitely generated. -/
def DensePointTranslates : Prop :=
  ∀ g : K, g ≠ 0 → Ideal.span (Set.range fun u : H →ₐ[k] k => pointAut φ u g) = ⊤

variable [IsNoetherianRing K] [IsReduced K] [Nontrivial K]

/-- **Takeuchi's Proposition 3.7** [Takeuchi1972] (relative to the density of the points): a
relative `(H,K)`-Hopf module which is finitely generated over a reduced noetherian `K` is flat,
provided the translates of every nonzero element of `K` by the points of `H` generate the unit
ideal.

The proof is Takeuchi's: `M` becomes free after inverting one nonzero `g` (generic freeness), the
point `u` carries this to freeness after inverting the translate `u ⇀ g` (the translation of `M`
being semilinear over the translation automorphism of `K`), and a module which is free after
inverting each element of a family generating the unit ideal is flat. -/
theorem flat_of_isReduced_of_densePointTranslates (hdense : DensePointTranslates φ)
    {M : Type u} [AddCommGroup M] [Module k M] [Module K M] [IsScalarTower k K M]
    [RightComodule k H M] (hM : IsRelativeHopfModule k K H M φ) [Module.Finite K M] :
    Module.Flat K M := by
  obtain ⟨g, hg0, hfree⟩ := Module.Free.exists_free_localizedModule_of_isReduced K M
  have := hfree
  refine Module.Flat.flat_of_free_localization_of_semilinear_cover
    (fun u : H →ₐ[k] k => (pointAut φ u).toRingEquiv)
    (fun u : H →ₐ[k] k => Coalgebra.Comodule.translAddEquiv (M := M)
      (convFun_comp_antipode_left u) (convFun_comp_antipode_right u))
    ?_ g (hdense g hg0)
  intro u a x
  simpa [pointAut_apply] using transl_smul hM u a x

/-- **Takeuchi's Theorem 3.1 for reduced `K`** (relative to the density of the points): combining
Proposition 3.7 with Proposition 2.4, `H` is a faithfully flat `K`-module. -/
theorem faithfullyFlat_of_isReduced_of_densePointTranslates [Algebra K H] [IsScalarTower k K H]
    (hdense : DensePointTranslates φ) (hφ : ∀ x : K, φ x = algebraMap K H x)
    (hinj : Function.Injective (algebraMap K H)) :
    Module.FaithfullyFlat K H :=
  faithfullyFlat_of_relativeHopfModulesFlat
    (fun _M _ _ _ _ _ hM _ => flat_of_isReduced_of_densePointTranslates φ hdense hM) hφ hinj

end

end HopfAlgebra.Commutative

end
