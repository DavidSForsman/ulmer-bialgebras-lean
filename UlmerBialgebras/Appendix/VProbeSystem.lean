module

public import UlmerBialgebras.Appendix.VCatProbe
public import UlmerBialgebras.Appendix.VCatUnit

/-!
# Which probes does the density argument actually use?

The proof that the small `V`-categories are dense in `CAT_V` (`VCatDense.lean`) evaluates a
pseudonatural family of functors on the representables at only a handful of probes:

* the **unit** `V`-category `1`;
* the **free `V`-category on an arrow** `2_x` (only for the naturality statements, and only
  when `V` has an absorbing initial object);
* the induced probes `vProbe ι` (`VCatProbe.lean`) on families indexed by
  - `PUnit` (the object map),
  - `ULift Bool` (the action on hom-objects and on morphisms),
  - `Option (ULift Bool)` (functoriality and compatibility with enriched composition), and
  - the object type of a probe already in the class (the comparison isomorphism at a 1-cell
    out of that probe).

This file isolates those closure properties, so that the reconstruction of a `V`-functor can
be carried out for **any** class of objects of `CAT_V` satisfying them, not just for the
small `V`-categories:

* `UlmerBialgebras.IsVProbeIndex P S` — every induced probe indexed by `S` belongs to `P`;
* `UlmerBialgebras.VProbeSystem P` — `P` contains the unit `V`-category and is closed under induced
  probes indexed by `PUnit`, by `ULift Bool`, by `Option (ULift Bool)` and by the object type
  of any of its own members.

`VCatTinyDense.lean` exhibits the minimal such class: the `V`-categories with at most three
objects.

## Main definitions

* `UlmerBialgebras.IsVProbeIndex`: every induced probe indexed by `S` belongs to the class `P`.
* `UlmerBialgebras.VProbeSystem`: a class containing the unit `V`-category and closed under
  two-point probes, three-point probes and probes indexed by the object type of a member.
* `UlmerBialgebras.vProbeSystem_isSmallVCat`: the small `V`-categories form a system of probes.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1,
  Theorem A.5
* [P. Hofstra, M. Karvonen, *Inner Autoequivalences in General and Those of Monoidal Categories in
  Particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The index type `S` is a **probe index** for the class `P`: every induced probe indexed by
`S` belongs to `P`. -/
class IsVProbeIndex (P : VCat.{w, v, max u w} V → Prop) (S : Type max u w) : Prop where
  /-- Every probe indexed by `S` is in the class. -/
  mem : ∀ {E : VCat.{w, v, max u w} V} (ι : S → E.carrier), P (vProbe ι)

/-- A **system of probes**: a class of objects of `CAT_V` containing the unit `V`-category and
closed under the induced probes used by the reconstruction of a `V`-functor from a
pseudonatural family. -/
class VProbeSystem (P : VCat.{w, v, max u w} V → Prop) : Prop where
  /-- The unit `V`-category is in the class. -/
  unit : P (unitVCat.{w, v, max u w} V)
  /-- Probes indexed by the object type of a member of the class are in the class. -/
  ofMem : ∀ ⦃x : VCat.{w, v, max u w} V⦄, P x →
    ∀ {E : VCat.{w, v, max u w} V} (ι : x.carrier → E.carrier), P (vProbe ι)
  /-- Two-point probes are in the class. -/
  bool : ∀ {E : VCat.{w, v, max u w} V} (ι : ULift.{max u w} Bool → E.carrier), P (vProbe ι)
  /-- Three-point probes are in the class. -/
  option : ∀ {E : VCat.{w, v, max u w} V} (ι : Option (ULift.{max u w} Bool) → E.carrier),
    P (vProbe ι)

/-- An object whose type of objects is a probe index for `P` belongs to `P`: it is the probe
on the identity family of its own objects. -/
lemma IsVProbeIndex.mem_self (P : VCat.{w, v, max u w} V → Prop) (x : VCat.{w, v, max u w} V)
    [IsVProbeIndex.{w, v, u} P x.carrier] : P x :=
  IsVProbeIndex.mem (P := P) (E := x) id

namespace VProbeSystem

variable {P : VCat.{w, v, max u w} V → Prop} [VProbeSystem.{w, v, u} P]

/-- `PUnit` is a probe index for any probe system (its probes are unit `V`-categories). -/
instance isVProbeIndex_punit : IsVProbeIndex.{w, v, u} P PUnit.{max u w + 1} :=
  ⟨fun ι => VProbeSystem.ofMem (VProbeSystem.unit (V := V)) ι⟩

/-- The object type of the unit `V`-category is a probe index for any probe system. -/
instance isVProbeIndex_unitVCat :
    IsVProbeIndex.{w, v, u} P (unitVCat.{w, v, max u w} V).carrier :=
  ⟨fun ι => VProbeSystem.ofMem (VProbeSystem.unit (V := V)) ι⟩

/-- The two-element type is a probe index for any probe system. -/
instance isVProbeIndex_bool : IsVProbeIndex.{w, v, u} P (ULift.{max u w} Bool) :=
  ⟨fun ι => VProbeSystem.bool ι⟩

/-- The three-element type `Option Bool` is a probe index for any probe system. -/
instance isVProbeIndex_option : IsVProbeIndex.{w, v, u} P (Option (ULift.{max u w} Bool)) :=
  ⟨fun ι => VProbeSystem.option ι⟩

/-- The object type of a member of the class is a probe index. -/
lemma isVProbeIndex_carrier {x : VCat.{w, v, max u w} V} (hx : P x) :
    IsVProbeIndex.{w, v, u} P x.carrier :=
  ⟨fun ι => VProbeSystem.ofMem hx ι⟩

end VProbeSystem

/-- The small `V`-categories form a system of probes. -/
instance vProbeSystem_isSmallVCat :
    VProbeSystem.{w, v, u} (IsSmallVCat.{w, v, u} V) where
  unit := inferInstanceAs (Small.{w} _)
  ofMem := fun _ hx _ _ => hx
  bool := fun _ => ⟨ULift.{w} Bool, ⟨Equiv.ulift.trans Equiv.ulift.symm⟩⟩
  option := fun _ => ⟨Option (ULift.{w} Bool),
    ⟨Equiv.optionCongr (Equiv.ulift.trans Equiv.ulift.symm)⟩⟩

end UlmerBialgebras
