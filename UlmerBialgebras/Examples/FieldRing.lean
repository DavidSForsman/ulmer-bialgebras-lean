module

public import Mathlib.Algebra.Field.MinimalAxioms
public import UlmerBialgebras.Examples.FieldCalc

/-!
# A `T_Field`-bialgebra in sets is a field

Continuation of Examples 3.20 (3) of *A Syntactic Approach to Ulmer's Bialgebras*.  For an
object `z` of `M^σ` satisfying the axioms of `T_Field` (`UlmerBialgebras.FieldEx.Axioms`, computed
in `FieldCalc.lean`), the set `Option (ob z) = S(ob z)` carries a field structure:

* the additive group is `(m₁, ν, ι)`;
* the multiplication is `m₂`, with unit `ηs ∘ u`;
* the inverse is `Option.map i`, the inverse of the group `(ob z, m, i, u)` extended by
  `0 ↦ 0`.

The one point that has to be proved rather than read off is that the zero `ι` of the ring is
the extra point `none`: otherwise the zero would be invertible (every element of the image of
`ηs` is, because `(ob z, m, i, u)` is a group), so the ring would be trivial, which it is not
because `none ≠ some u`.  Hence the nonzero elements of `Option (ob z)` are exactly the
elements of the image of `ηs`, and they are invertible.

## Main results

* `UlmerBialgebras.FieldEx.Carrier.commRing`: the commutative ring structure on `Option (ob z)`
  given by the axioms of `T_Field`.
* `UlmerBialgebras.FieldEx.Carrier.zero_eq_extra`: the zero of this ring is the extra point `none`.
* `UlmerBialgebras.FieldEx.Carrier.field`: the field structure on `Option (ob z)` (Examples 3.20
  (3)).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3)
-/

@[expose] public section

universe u

namespace UlmerBialgebras

namespace FieldEx

open CategoryTheory

/-- The carrier `S s = Option X` of the ring attached to an object of `M^σ`, as a type
synonym carrying the ring structure. -/
def Carrier (z : SigObj.{u}) : Type u := Option (ob z)

namespace Carrier

variable {z : SigObj.{u}}

/-- An element of `X`, as an element of the carrier. -/
def of (x : ob z) : Carrier z := (some x : Option (ob z))

/-- The extra point of the carrier. -/
def extra (z : SigObj.{u}) : Carrier z := (none : Option (ob z))

/-- `of` is injective: `of x = of y ↔ x = y`. -/
@[simp] lemma of_inj {x y : ob z} : (of x : Carrier z) = of y ↔ x = y :=
  Option.some_inj

/-- An element coming from `X` is not the extra point. -/
@[simp] lemma of_ne_extra (x : ob z) : (of x : Carrier z) ≠ extra z := by
  intro hcon
  exact Option.some_ne_none x (show (some x : Option (ob z)) = none from hcon)

/-- Every element of the carrier is either the extra point or comes from `X`. -/
lemma eq_extra_or_of (a : Carrier z) : a = extra z ∨ ∃ x, a = of x := by
  rcases a with _ | x
  · exact Or.inl rfl
  · exact Or.inr ⟨x, rfl⟩

/-- The addition on the carrier, given by the operation `add`. -/
instance : Add (Carrier z) := ⟨fun a b => FieldEx.add z a b⟩
/-- The multiplication on the carrier, given by the operation `rmul`. -/
instance : Mul (Carrier z) := ⟨fun a b => FieldEx.rmul z a b⟩
/-- The negation on the carrier, given by the operation `neg`. -/
instance : Neg (Carrier z) := ⟨fun a => FieldEx.neg z a⟩
/-- The zero of the carrier, given by the operation `zero`. -/
instance : Zero (Carrier z) := ⟨FieldEx.zero z⟩
/-- The one of the carrier: the unit `one` of `X`. -/
instance : _root_.One (Carrier z) := ⟨of (FieldEx.one z)⟩
/-- The inverse on the carrier: `inv` on `X`, fixing the extra point. -/
instance : Inv (Carrier z) := ⟨fun a => Option.map (FieldEx.inv z) a⟩

/-- The one of the carrier is `of (one z)`. -/
lemma one_def : (1 : Carrier z) = of (FieldEx.one z) := rfl

/-- The inverse of `of x` is `of (inv z x)`. -/
@[simp] lemma inv_of (x : ob z) : (of x : Carrier z)⁻¹ = of (FieldEx.inv z x) := rfl
/-- The inverse fixes the extra point. -/
@[simp] lemma inv_extra : (extra z)⁻¹ = extra z := rfl

/-- The commutative ring structure on `Option X` given by the axioms of `T_Field`. -/
@[instance_reducible]
noncomputable def commRing (h : Axioms z) : CommRing (Carrier z) :=
  CommRing.ofMinimalAxioms
    (fun a b c => h.addAssoc a b c)
    (fun a => h.addUnit a)
    (fun a => h.addInv a)
    (fun a b c => h.rmulAssoc a b c)
    (fun a b => h.rmulComm a b)
    (fun a => h.rmulUnit a)
    (fun a b c => h.distrib a b c)

/-- Every element of the image of `ηs` is invertible. -/
lemma of_mul_of_inv (h : Axioms z) (x : ob z) :
    (of x : Carrier z) * (of (FieldEx.inv z x)) = 1 := by
  change FieldEx.rmul z (some x) (some (FieldEx.inv z x)) = _
  rw [h.etaMul, h.mulComm, h.mulInv]
  rfl

/-- **The zero of the ring is the extra point.** -/
lemma zero_eq_extra (h : Axioms z) : (0 : Carrier z) = extra z := by
  let := commRing h
  by_contra hne
  obtain ⟨c, hc⟩ : ∃ x, (0 : Carrier z) = of x := by
    rcases eq_extra_or_of (0 : Carrier z) with h0 | h0
    · exact absurd h0 hne
    · exact h0
  have h1 : (1 : Carrier z) = 0 := by
    have hmul := of_mul_of_inv h c
    rw [← hc] at hmul
    exact ((zero_mul _).symm.trans hmul).symm
  have h2 : ∀ a : Carrier z, a = 0 := by
    intro a
    calc a = 1 * a := (one_mul a).symm
      _ = 0 * a := by rw [h1]
      _ = 0 := zero_mul a
  exact (of_ne_extra (FieldEx.one z)) ((h2 (of (FieldEx.one z))).trans (h2 (extra z)).symm)

/-- A nonzero element of the carrier lies in the image of `ηs`. -/
lemma exists_of_of_ne_zero (h : Axioms z) {a : Carrier z} (ha : a ≠ 0) : ∃ x, a = of x := by
  rcases eq_extra_or_of a with h0 | h0
  · exact absurd (h0.trans (zero_eq_extra h).symm) ha
  · exact h0

/-- **The field structure on `S s = Option X`** (Examples 3.20 (3)). -/
@[instance_reducible]
noncomputable def field (h : Axioms z) : Field (Carrier z) :=
  Field.ofMinimalAxioms (Carrier z)
    (fun a b c => h.addAssoc a b c)
    (fun a => h.addUnit a)
    (fun a => h.addInv a)
    (fun a b c => h.rmulAssoc a b c)
    (fun a b => h.rmulComm a b)
    (fun a => h.rmulUnit a)
    (fun a ha => by
      obtain ⟨x, rfl⟩ := exists_of_of_ne_zero h ha
      rw [inv_of]
      exact of_mul_of_inv h x)
    (by rw [zero_eq_extra h, inv_extra])
    (fun a b c => h.distrib a b c)
    ⟨extra z, of (FieldEx.one z), fun hcon => (of_ne_extra (FieldEx.one z)) hcon.symm⟩

end Carrier

end FieldEx

end UlmerBialgebras
