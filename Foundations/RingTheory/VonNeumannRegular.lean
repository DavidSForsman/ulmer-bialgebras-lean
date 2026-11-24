module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.LinearCombination.Lemmas
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Commutative von Neumann regular rings

This file introduces commutative von Neumann regular (VNR) rings and proves the basic fact
used in Section 4 of the paper: all localizations of a commutative von Neumann regular ring
at prime ideals are fields.

## Main results

* `IsVonNeumannRegular`: a commutative ring `R` is von Neumann regular if every `a : R`
  has some `b : R` with `a * b * a = a`.
* `IsVonNeumannRegular.isLocalization`: every localization of a commutative von Neumann
  regular ring is von Neumann regular.
* `IsVonNeumannRegular.isField_of_isLocalRing`: a von Neumann regular local ring is a
  field.
* `IsVonNeumannRegular.isField_localizationAtPrime`: the localization of a commutative von
  Neumann regular ring at a prime ideal is a field (the field part of the paper's Lemma 6.10).
* `IsVonNeumannRegular.iff_exists_pseudoInverse`: equivalently, every element has a
  pseudo-inverse `s` (`r * s * r = r` and `s * r * s = s`), the paper's definition.
* `IsVonNeumannRegular.iff_isReduced_and_krullDimLE_zero`: a commutative ring is von
  Neumann regular if and only if it is reduced and of Krull dimension at most zero.
* `IsVonNeumannRegular.isReduced`, `IsVonNeumannRegular.krullDimLE_zero` and
  `IsVonNeumannRegular.of_isReduced_of_krullDimLE_zero`: the two directions.

## References

* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 2, Exercise 27; Chapter 3, Exercises 10 and 11
* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 6.10
* [D. Forsman,
  *On the semi-abelianness of affine group schemes*][forsman2026semiabeliannessaffinegroupschemes],
  Section 4
-/

@[expose] public section

section

universe u

variable {R : Type*} [CommRing R]

/-- A commutative ring `R` is *von Neumann regular* if every element `a` admits a
"weak inverse" `b`, i.e. an element with `a * b * a = a`. -/
def IsVonNeumannRegular (R : Type*) [CommRing R] : Prop :=
  ∀ a : R, ∃ b : R, a * b * a = a

/-- Any localization of a commutative von Neumann regular ring is von Neumann regular. -/
theorem IsVonNeumannRegular.isLocalization (hR : IsVonNeumannRegular R) (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] :
    IsVonNeumannRegular S := by
  intro x
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (M := M) x
  obtain ⟨b, hb⟩ := hR a
  refine ⟨algebraMap R S b * algebraMap R S s, ?_⟩
  have hu : IsUnit (algebraMap R S (s : R)) := IsLocalization.map_units S s
  refine hu.mul_left_cancel ?_
  calc algebraMap R S (s : R) * (x * (algebraMap R S b * algebraMap R S s) * x)
      = (x * algebraMap R S (s : R)) * (x * algebraMap R S (s : R)) * algebraMap R S b := by
        ring
    _ = algebraMap R S a * algebraMap R S a * algebraMap R S b := by rw [hs]
    _ = algebraMap R S (a * b * a) := by rw [← hb]; push_cast [map_mul]; ring
    _ = algebraMap R S a := by rw [hb]
    _ = algebraMap R S (s : R) * x := by rw [← hs]; ring

/-- A von Neumann regular local ring is a field. -/
theorem IsVonNeumannRegular.isField_of_isLocalRing (S : Type*) [CommRing S] [IsLocalRing S]
    (hS : IsVonNeumannRegular S) : IsField S := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hS a
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (a * b) with h | h
  · -- `a * b` is a unit, hence so is `a`
    exact ⟨b * (h.unit⁻¹ : Sˣ), by rw [← mul_assoc]; exact h.mul_val_inv⟩
  · -- `1 - a * b` is a unit; but `a * (1 - a * b) = 0`, so `a = 0`, a contradiction
    exfalso
    apply ha
    have hz : a * (1 - a * b) = 0 := by linear_combination -hb
    exact h.mul_left_eq_zero.mp hz

/-- A localization of a commutative von Neumann regular ring that is a local ring is a field. -/
theorem IsVonNeumannRegular.isField_localization (hR : IsVonNeumannRegular R) (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S] [IsLocalRing S] :
    IsField S :=
  IsVonNeumannRegular.isField_of_isLocalRing S (hR.isLocalization M S)

/-- A localization of a commutative von Neumann regular ring that is a local ring is a field. -/
theorem IsVonNeumannRegular.isField_localizationAtPrime (hR : IsVonNeumannRegular R)
    (p : Ideal R) [p.IsPrime] : IsField (Localization.AtPrime p) :=
  hR.isField_localization p.primeCompl _

/-- A commutative von Neumann regular ring is reduced. -/
theorem IsVonNeumannRegular.isReduced (hR : IsVonNeumannRegular R) : IsReduced R := by
  refine ⟨fun a ⟨n, hn⟩ => ?_⟩
  obtain ⟨b, hb⟩ := hR a
  -- `e = a * b` is idempotent with `e * a = a`, and `e = e ^ n = a ^ n * b ^ n = 0`.
  have he : IsIdempotentElem (a * b) := by
    change a * b * (a * b) = a * b
    rw [← mul_assoc, hb]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simpa using congrArg (a * ·) hn
  have h0 : a * b = 0 := by rw [← he.pow_eq hpos.ne', mul_pow, hn, zero_mul]
  rw [← hb, h0, zero_mul]

/-- A commutative von Neumann regular ring has Krull dimension at most zero, i.e. every prime
ideal is maximal. -/
theorem IsVonNeumannRegular.krullDimLE_zero (hR : IsVonNeumannRegular R) :
    Ring.KrullDimLE 0 R := by
  refine .mk₀ fun I hI => Ideal.Quotient.maximal_of_isField I ?_
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := hR a
  refine ⟨Ideal.Quotient.mk I b, ?_⟩
  -- In the domain `R ⧸ I`, `x * (x * b - 1) = 0` with `x ≠ 0` forces `x * b = 1`.
  have hz : Ideal.Quotient.mk I a * (Ideal.Quotient.mk I a * Ideal.Quotient.mk I b - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, ← map_mul, ← mul_assoc, mul_right_comm, hb, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hx)

/-- A reduced commutative ring of Krull dimension at most zero is von Neumann regular. The
localizations at maximal ideals are reduced zero-dimensional local rings, hence fields, so
`a ∈ (a ^ 2)` holds locally and therefore globally. -/
theorem IsVonNeumannRegular.of_isReduced_of_krullDimLE_zero [IsReduced R]
    [Ring.KrullDimLE 0 R] : IsVonNeumannRegular R := by
  intro a
  suffices h : a ∈ Ideal.span {a * a} by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
    exact ⟨c, by linear_combination hc⟩
  refine Ideal.mem_of_localization_maximal fun P hP => ?_
  have : Ring.KrullDimLE 0 (Localization.AtPrime P) :=
    Ring.KrullDimLE.of_isLocalization P (Ideal.mem_minimalPrimes_of_krullDimLE_zero P) _
  have hF : IsField (Localization.AtPrime P) := Ring.KrullDimLE.isField_of_isReduced
  rw [Ideal.map_span, Set.image_singleton, map_mul]
  set x := algebraMap R (Localization.AtPrime P) a
  by_cases hx : x = 0
  · rw [hx]
    exact Ideal.zero_mem _
  obtain ⟨y, hy⟩ := hF.mul_inv_cancel hx
  exact Ideal.mem_span_singleton'.mpr ⟨y, by linear_combination x * hy⟩

/-- A commutative ring is von Neumann regular if and only if it is reduced and has Krull
dimension at most zero ([atiyah_introduction_1969], Chapter 3, Exercise 11). -/
theorem IsVonNeumannRegular.iff_isReduced_and_krullDimLE_zero :
    IsVonNeumannRegular R ↔ IsReduced R ∧ Ring.KrullDimLE 0 R :=
  ⟨fun h => ⟨h.isReduced, h.krullDimLE_zero⟩, fun ⟨_, _⟩ =>
    IsVonNeumannRegular.of_isReduced_of_krullDimLE_zero⟩

/-- A commutative ring is von Neumann regular if and only if every element `r` has a
*pseudo-inverse* `s`, with `r * s * r = r` and `s * r * s = s`. This is the definition of
[forsman2026syntactic] (before Lemma 6.10); the pseudo-inverse of a weak inverse `b` is
`b * r * b`. -/
theorem IsVonNeumannRegular.iff_exists_pseudoInverse :
    IsVonNeumannRegular R ↔ ∀ r : R, ∃ s : R, r * s * r = r ∧ s * r * s = s := by
  refine ⟨fun h r => ?_, fun h r => ?_⟩
  · obtain ⟨b, hb⟩ := h r
    exact ⟨b * r * b, by linear_combination (b * r + 1) * hb,
      by linear_combination (b ^ 3 * r + b ^ 2) * hb⟩
  · obtain ⟨s, hs, -⟩ := h r
    exact ⟨s, hs⟩

end
