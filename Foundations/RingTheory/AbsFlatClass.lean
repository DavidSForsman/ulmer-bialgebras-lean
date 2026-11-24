module

public import Foundations.RingTheory.VonNeumannRegularFlat

/-!
# Absolutely flat (von Neumann regular) base rings, as a typeclass

Section 4 of

  D. Forsman, *On the Semi-Abelianness of Affine Group Schemes*,

extends the results of Section 3 from fields to commutative von Neumann regular (VNR) base rings.
The arguments of Section 3 use the base to be a field only through *flatness*, and over a von
Newman regular ring every module is flat.  To be able to state the generalizations in exactly
the same way as the field versions — so that the field case is literally an instance — this file
packages von Neumann regularity of the base as a typeclass.

This file contains only the class and its two basic instances, so that it can be imported early
in the development; Takeuchi's theorem over such a base is
`AffineGroupSchemes.faithfullyFlat_of_injective_of_isVonNeumannRegular_holds`.

## Main definitions and results

* `IsAbsFlat R`: the base ring `R` is von Neumann regular, equivalently (over a
  commutative ring) every `R`-module is flat;
* `IsAbsFlat.toFlat`: the resulting flatness instance;
* every field is an `IsAbsFlat` ring.

## References

* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27
* [D. Forsman, *On the semi-abelianness of affine group
  schemes*][forsman2026semiabeliannessaffinegroupschemes], Section 4
-/

@[expose] public section

section

universe u v

/-- A commutative ring over which every module is flat, i.e. a commutative von Neumann regular
ring.  (`abs` is for *absolutely flat*, the classical synonym.) -/
class IsAbsFlat (R : Type u) [CommRing R] : Prop where
  isVonNeumannRegular : IsVonNeumannRegular R

/-- Absolute flatness is the class wrapper for von Neumann regularity. -/
theorem IsAbsFlat.iff_isVonNeumannRegularRing (R : Type u) [CommRing R] :
    IsAbsFlat R ↔ IsVonNeumannRegular R :=
  ⟨fun h => h.isVonNeumannRegular, fun h => ⟨h⟩⟩

/-- Every field is absolutely flat (von Neumann regular). -/
instance (priority := 100) IsAbsFlat.of_field (k : Type u) [Field k] : IsAbsFlat k :=
  ⟨fun a => ⟨a⁻¹, by
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · field_simp⟩⟩

/-- **Every module over an absolutely flat base ring is flat.** -/
instance (priority := 100) IsAbsFlat.toFlat (R : Type u) [CommRing R] [IsAbsFlat R]
    (M : Type v) [AddCommGroup M] [Module R M] : Module.Flat R M :=
  IsVonNeumannRegular.flat (IsAbsFlat.isVonNeumannRegular (R := R)) M

end
