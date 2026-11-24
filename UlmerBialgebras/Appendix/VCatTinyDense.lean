module

public import Mathlib.Data.ZMod.Defs
public import UlmerBialgebras.Appendix.VCatDense

/-!
# A minimal dense class in `CAT_V`: the `V`-categories with at most three objects

`VCatDense.lean` proves density of a class of objects of `CAT_V` from the axiomatic interface
of `VProbeSystem.lean`: all the reconstruction of a 1-cell out of a pseudonatural family on
the representables ever uses is

* the **point** object (the unit `V`-category) — it gives the object map;
* **two-point** probes — the action on morphisms and on hom-objects;
* **three-point** probes — functoriality and compatibility with the enriched composition
  (this is where associativity is seen, and two points do not suffice);
* probes on the object type of a member of the class — the comparison isomorphism at a
  1-cell out of such a member;
* the **arrow** objects `2_x`, and only for the 2-cell statements: this is the single place
  where an absorbing initial object of `V` is used, since `2_x` has a zero hom-object.

Consequently the dense class may be cut down from *all* small `V`-categories to the ones with
**at most three objects**:

* `UlmerBialgebras.IsTinyVCat` — the class of `V`-categories with at most three objects;
* `UlmerBialgebras.vProbeSystem_isTinyVCat` — it is a system of probes in the sense of
  `UlmerBialgebras.VProbeSystem`;
* `UlmerBialgebras.isTinyVCat_arrowVCat` — it contains the arrow `V`-categories, for `V` with an
  absorbing initial object;
* `UlmerBialgebras.isADense_isTinyVCat` — **the `V`-categories with at most three objects are dense
  in `CAT_V`**, for any monoidal base with an absorbing initial object.  This class contains the
  class `{1, 2_x, 3_{x,y}}` of Theorem A.5 of the paper.

Three is optimal for this argument: the compatibility of the reconstructed `V`-functor with
the enriched composition `(d₁ ⟶ d₂) ⊗ (d₂ ⟶ d₃) ⟶ (d₁ ⟶ d₃)` is read off a probe on three
objects.

## Main results

* `UlmerBialgebras.IsTinyVCat`: the class of `V`-categories with at most three objects.
* `UlmerBialgebras.vProbeSystem_isTinyVCat`: this class is a system of probes
  (`UlmerBialgebras.VProbeSystem`).
* `UlmerBialgebras.isTinyVCat_arrowVCat`: the arrow `V`-categories `2_x` belong to it.
* `UlmerBialgebras.isADense_isTinyVCat`: for `V` with an absorbing initial object, the
  `V`-categories with at most three objects are dense in `CAT_V`; this class contains the class of
  Theorem A.5.

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

/-- A `V`-category is **tiny** when it has at most three objects. -/
def IsTinyVCat (C : VCat.{w, v, max u w} V) : Prop :=
  ∃ f : C.carrier → Fin 3, Function.Injective f

/-- The unit `V`-category is tiny. -/
lemma isTinyVCat_unitVCat : IsTinyVCat.{w, v, u} (unitVCat.{w, v, max u w} V) :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

/-- The `V`-categories with at most three objects form a system of probes: the point, the
two-point and the three-point probes all have at most three objects, and a probe on the
objects of a tiny `V`-category has the same object type. -/
instance vProbeSystem_isTinyVCat : VProbeSystem.{w, v, u} (IsTinyVCat.{w, v, u} (V := V)) where
  unit := isTinyVCat_unitVCat
  ofMem := fun _ hx _ _ => hx
  bool := fun _ => ⟨fun b => if b.down then 1 else 0, by
    rintro ⟨(_ | _)⟩ ⟨(_ | _)⟩ h <;> simp_all <;> rfl⟩
  option := fun _ => ⟨fun o =>
      match o with
      | none => 0
      | some ⟨false⟩ => 1
      | some ⟨true⟩ => 2, by
    rintro (_ | ⟨(_ | _)⟩) (_ | ⟨(_ | _)⟩) h <;> simp_all <;> rfl⟩

/-- Numbering the two objects of the free `V`-category on an arrow. -/
def arrowIdx (Z : MonoidalInitial V) (x : V) : ArrowObj.{w, v, max u w} Z x → Fin 3
  | .src => 0
  | .tgt => 1

/-- The free `V`-category on an arrow is tiny: it has two objects. -/
lemma isTinyVCat_arrowVCat (Z : MonoidalInitial V) (x : V) :
    IsTinyVCat.{w, v, u} (arrowVCat.{w, v, max u w} Z x) := by
  refine ⟨fun a => arrowIdx Z x (ForgetEnrichment.to V a), ?_⟩
  intro a b h
  have hinj : Function.Injective (arrowIdx.{w, v, u} Z x) := by
    rintro (_ | _) (_ | _) h <;> first | rfl | simp [arrowIdx] at h
  have hto : ForgetEnrichment.to V a = ForgetEnrichment.to V b := hinj h
  exact hto

/-- **The `V`-categories with at most three objects are dense in `CAT_V`**, for any monoidal
base `V` with an absorbing initial object.  This is the minimal dense class the argument of
`VCatDense.lean` produces; it contains the class `{1, 2_x, 3_{x,y}}` of **Theorem A.5**
([forsman2026syntactic]). -/
theorem isADense_isTinyVCat (Z : MonoidalInitial V) :
    IsADense (Obj := VCat.{w, v, max u w} V) (IsTinyVCat.{w, v, u} (V := V)) :=
  isADense_of_vProbeSystem Z _ (fun y => isTinyVCat_arrowVCat.{w, v, u} Z y)

end UlmerBialgebras
