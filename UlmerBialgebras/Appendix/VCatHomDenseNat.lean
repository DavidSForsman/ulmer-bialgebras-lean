module

public import UlmerBialgebras.Appendix.VCatHomDenseUnit

/-!
# Naturality of the comparison isomorphism

`VCatHomDenseUnit.lean` reduces naturality of `UlmerBialgebras.AHomFamily.homIso` in the 1-cell to
the unit probe, and proves it there.  Assembling the components gives naturality at an arbitrary
small probe:

* `UlmerBialgebras.AHomFamily.homIso_naturality`.

## Main results

* `UlmerBialgebras.AHomFamily.homIso_naturality`: for `V` with an absorbing initial object and a
  system of probes containing the arrow `V`-categories, the comparison isomorphism `homIso` is
  natural in the 1-cell `k`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]
variable {D C : VCat.{w, v, max u w} V}

namespace AHomFamily

variable {P : VCat.{w, v, max u w} V → Prop} [VProbeSystem.{w, v, u} P]
variable (Φ : AHomFamily P D C)

/-- **The comparison isomorphism is natural in the 1-cell.** -/
lemma homIso_naturality (Z : MonoidalInitial V)
    (harr : ∀ y : V, P (arrowVCat.{w, v, max u w} Z y)) {x : VCat.{w, v, max u w} V}
    [hx : IsVProbeIndex.{w, v, u} P x.carrier] {k k' : x ⟶ D} (β : k ⟶ k') :
    (β ▷ toVFunctor Φ) ≫ (homIso Φ k').hom
      = (homIso Φ k).hom ≫ (Φ.fn (IsVProbeIndex.mem_self P x)).map β := by
  refine VNatTrans.ext (funext fun a => ?_)
  exact (homIso_component_iff Φ β a).mpr (homIso_naturality_unit Φ Z harr _)

end AHomFamily

end UlmerBialgebras
