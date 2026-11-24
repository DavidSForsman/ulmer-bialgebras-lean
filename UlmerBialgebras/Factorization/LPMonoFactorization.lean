module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Foundations.CategoryTheory.Factorization.ExtremalMono
public import UlmerBialgebras.Monadicity.AccCoWellPowered
public import Foundations.CategoryTheory.Presentable.LPComplete
public import Foundations.CategoryTheory.Factorization.OFS
public import Foundations.CategoryTheory.Factorization.StableRegularOFS

/-!
# Epimorphisms and orthogonality

In a category with equalizers, a morphism left orthogonal to all monomorphisms is a strong
epimorphism. It is an epimorphism by `UlmerBialgebras.OFS.epi_of_leftOrth_monomorphisms`; the
converse is `UlmerBialgebras.OFS.orthogonal_of_strongEpi_of_mono`.

## Main results

* `UlmerBialgebras.strongEpi_of_leftOrth_monomorphisms`: in a category with equalizers, a morphism
  left orthogonal to all monomorphisms is a strong epimorphism.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 6.4
* [J. Adámek, H. Herrlich, G. Strecker, *Abstract and Concrete Categories: The Joy of
  Cats*][AHS:Cats]
* [G. M. Kelly, *Monomorphisms, epimorphisms, and pull-backs*][Kelly1969MonomorphismsEA]
-/

@[expose] public section

universe w u

namespace UlmerBialgebras

open CategoryTheory Limits

section OFS

variable {D : Type u} [Category.{w} D]

/-- A morphism left orthogonal to all monomorphisms is a strong epimorphism; the converse is
`UlmerBialgebras.OFS.orthogonal_of_strongEpi_of_mono`. -/
lemma strongEpi_of_leftOrth_monomorphisms [HasEqualizers D] {X Y : D} {e : X ⟶ Y}
    (he : leftOrth (MorphismProperty.monomorphisms D) e) : StrongEpi e := by
  have := OFS.epi_of_leftOrth_monomorphisms he
  refine ⟨inferInstance, fun {P Q} m hm => ⟨fun {t b} sq => ?_⟩⟩
  have hlift := he m hm t b sq.w
  exact ⟨⟨hlift.choose, hlift.choose_spec.1.1, hlift.choose_spec.1.2⟩⟩

end OFS

end UlmerBialgebras
