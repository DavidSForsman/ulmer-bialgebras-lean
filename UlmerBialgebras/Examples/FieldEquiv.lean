module

public import Mathlib.RingTheory.Henselian
public import UlmerBialgebras.Examples.FieldRing

/-!
# `M^T` is the category of fields

Completion of Examples 3.20 (3) of *A Syntactic Approach to Ulmer's Bialgebras*: for the
categorical `Σ`-model `M = (Set, ×, 1, (−) + 1)` and the theory `T_Field`, the category
`M^{T_Field}` of `T_Field`-bialgebras is equivalent to the category of fields and field
homomorphisms.

The comparison functor sends a bialgebra `z` to the field `S s = Option (ob z)` of
`FieldRing.lean` and a morphism to the induced map `Option.map`.  It is faithful because
`Option.map` is injective on functions, full because a homomorphism of fields is injective
and therefore restricts to the subsets of nonzero elements, and essentially surjective
because a field `K` arises from the multiplicative group `Kˣ = {x : K // x ≠ 0}` of its
nonzero elements together with the ring structure transported along `Option Kˣ ≃ K`.

## Main results

* `UlmerBialgebras.FieldEx.comparison`: the comparison functor from `T_Field`-bialgebras to fields.
* `UlmerBialgebras.FieldEx.fieldEquiv`: the category of `T_Field`-bialgebras of
  `M = (Set, ×, 1, (−) + 1)` is equivalent to the category of fields (Examples 3.20 (3)).
* `UlmerBialgebras.FieldEx.nonempty_thyObj_equiv_fieldCat`: the same statement as a proposition.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3)
-/

@[expose] public section

universe u

namespace UlmerBialgebras

namespace FieldEx

open CategoryTheory

/-! ## The category of fields -/

/-- The category of fields: a field, bundled with its carrier. -/
structure FieldCat : Type (u + 1) where
  /-- The underlying set of the field. -/
  carrier : Type u
  [str : Field carrier]

attribute [instance] FieldCat.str

/-- A field, as an object of `FieldCat`. -/
def FieldCat.of (K : Type u) [Field K] : FieldCat.{u} := ⟨K⟩

/-- The category of fields, with ring homomorphisms as morphisms. -/
instance : Category FieldCat.{u} where
  Hom X Y := X.carrier →+* Y.carrier
  id X := RingHom.id X.carrier
  comp f g := g.comp f

/-- A morphism of `FieldCat`, as a ring homomorphism. -/
def FieldCat.homFn {X Y : FieldCat.{u}} (f : X ⟶ Y) : X.carrier →+* Y.carrier := f

/-- A ring homomorphism, as a morphism of `FieldCat`. -/
def FieldCat.homOf {X Y : FieldCat.{u}} (f : X.carrier →+* Y.carrier) : X ⟶ Y := f

/-- `homFn` undoes `homOf`. -/
@[simp] lemma FieldCat.homFn_homOf {X Y : FieldCat.{u}} (f : X.carrier →+* Y.carrier) :
    homFn (homOf f) = f := rfl

/-- `homFn` of the identity morphism is the identity on elements. -/
@[simp] lemma FieldCat.homFn_id (X : FieldCat.{u}) (x : X.carrier) : homFn (𝟙 X) x = x := rfl

/-- `homFn` of a composite `f ≫ g` applies `homFn f`, then `homFn g`. -/
@[simp] lemma FieldCat.homFn_comp {X Y Z : FieldCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : X.carrier) : homFn (f ≫ g) x = homFn g (homFn f x) := rfl

/-- Morphisms of `FieldCat` agreeing on all elements are equal. -/
lemma FieldCat.hom_ext {X Y : FieldCat.{u}} {f g : X ⟶ Y}
    (h : ∀ x, homFn f x = homFn g x) : f = g :=
  RingHom.ext h

/-- An isomorphism of `FieldCat` from a ring isomorphism. -/
def FieldCat.isoOfRingEquiv {X Y : FieldCat.{u}} (e : X.carrier ≃+* Y.carrier) : X ≅ Y where
  hom := homOf (e : X.carrier →+* Y.carrier)
  inv := homOf (e.symm : Y.carrier →+* X.carrier)
  hom_inv_id := hom_ext fun x => e.symm_apply_apply x
  inv_hom_id := hom_ext fun x => e.apply_symm_apply x

/-! ## The category of `T_Field`-bialgebras -/

/-- The category `M^{T_Field}` of `T_Field`-bialgebras in sets. -/
abbrev ThyObj : Type (u + 1) := ((model.{u}).thyObj oneSig theory : Type (u + 1))

/-- The axioms of `T_Field` hold in a `T_Field`-bialgebra. -/
lemma axioms_of (t : ThyObj.{u}) : Axioms t.obj := (mem_thy_iff t.obj).1 t.property

/-- The field structure carried by `S s` for a `T_Field`-bialgebra. -/
noncomputable instance instFieldCarrier (t : ThyObj.{u}) : Field (Carrier t.obj) :=
  Carrier.field (axioms_of t)

/-- The field attached to a `T_Field`-bialgebra. -/
noncomputable def toFieldObj (t : ThyObj.{u}) : FieldCat.{u} := FieldCat.of (Carrier t.obj)

/-- The ring homomorphism of the carriers attached to a morphism of `T_Field`-bialgebras. -/
noncomputable def carrierHom {t t' : ThyObj.{u}} (f : t ⟶ t') :
    Carrier t.obj →+* Carrier t'.obj where
  toFun a := Option.map (bs f.hom) a
  map_one' := congr(some $(bs_one f.hom))
  map_mul' a b := bs_rmul f.hom a b
  map_zero' := bs_zero f.hom
  map_add' a b := bs_add f.hom a b

/-- `carrierHom` of the identity is the identity. -/
lemma carrierHom_id (t : ThyObj.{u}) (a : Carrier t.obj) : carrierHom (𝟙 t) a = a := by
  cases a <;> rfl

/-- `carrierHom` of a composite is the composite. -/
lemma carrierHom_comp {t t' t'' : ThyObj.{u}} (f : t ⟶ t') (g : t' ⟶ t'') (a : Carrier t.obj) :
    carrierHom (f ≫ g) a = carrierHom g (carrierHom f a) := by
  cases a <;> rfl

/-- The ring homomorphism attached to a morphism of `T_Field`-bialgebras. -/
noncomputable def toFieldHom {t t' : ThyObj.{u}} (f : t ⟶ t') :
    toFieldObj t ⟶ toFieldObj t' :=
  FieldCat.homOf (carrierHom f)

/-- **The comparison functor** from the category of `T_Field`-bialgebras to the category of
fields. -/
@[simps]
noncomputable def comparison : ThyObj.{u} ⥤ FieldCat.{u} where
  obj := toFieldObj
  map := toFieldHom
  map_id t := FieldCat.hom_ext (carrierHom_id t)
  map_comp f g := FieldCat.hom_ext (carrierHom_comp f g)

/-- The comparison functor sends a morphism `f` to the map `Option.map (bs f.hom)`. -/
@[simp] lemma homFn_comparison_map {t t' : ThyObj.{u}} (f : t ⟶ t') (a : Carrier t.obj) :
    FieldCat.homFn (comparison.map f) a = Option.map (bs f.hom) a := rfl


/-! ## The comparison functor is faithful and full -/

/-- The comparison functor from `T_Field`-bialgebras to fields is faithful. -/
instance : comparison.{u}.Faithful where
  map_injective {t t'} f g hfg := by
    apply ObjectProperty.hom_ext
    apply bs_injective
    funext x
    have := congr(FieldCat.homFn $hfg (Carrier.of x))
    simp only [homFn_comparison_map] at this
    exact Option.some_inj.1 this

section Full

variable {t t' : ThyObj.{u}} (φ : comparison.obj t ⟶ comparison.obj t')

private noncomputable abbrev phiFn : Carrier t.obj →+* Carrier t'.obj := FieldCat.homFn φ

private lemma phi_injective : Function.Injective (phiFn φ) := (phiFn φ).injective

private lemma exists_image (x : ob t.obj) : ∃ y, phiFn φ (Carrier.of x) = Carrier.of y := by
  refine Carrier.exists_of_of_ne_zero (axioms_of t') ?_
  intro hcon
  have h0 : (Carrier.of x : Carrier t.obj) = 0 := by
    apply phi_injective φ
    rw [hcon, map_zero]
  exact Carrier.of_ne_extra x (h0.trans (Carrier.zero_eq_extra (axioms_of t)))

/-- The map on the sets of nonzero elements underlying a homomorphism of the fields. -/
private noncomputable def fullFn (x : ob t.obj) : ob t'.obj := (exists_image φ x).choose

private lemma fullFn_spec (x : ob t.obj) :
    phiFn φ (Carrier.of x) = Carrier.of (fullFn φ x) := (exists_image φ x).choose_spec

private lemma phi_eq_map (a : Carrier t.obj) : phiFn φ a = Option.map (fullFn φ) a := by
  rcases Carrier.eq_extra_or_of a with rfl | ⟨x, rfl⟩
  · rw [show (Carrier.extra t.obj) = 0 from (Carrier.zero_eq_extra (axioms_of t)).symm,
      map_zero, Carrier.zero_eq_extra (axioms_of t'), Carrier.zero_eq_extra (axioms_of t)]
    rfl
  · exact fullFn_spec φ x

private lemma fullFn_add (x y : Carrier t.obj) :
    Option.map (fullFn φ) (FieldEx.add t.obj x y)
      = FieldEx.add t'.obj (Option.map (fullFn φ) x) (Option.map (fullFn φ) y) := by
  refine (phi_eq_map φ _).symm.trans ((map_add (phiFn φ) x y).trans ?_)
  exact congrArg₂ (FieldEx.add t'.obj) (phi_eq_map φ x) (phi_eq_map φ y)

private lemma fullFn_rmul (x y : Carrier t.obj) :
    Option.map (fullFn φ) (FieldEx.rmul t.obj x y)
      = FieldEx.rmul t'.obj (Option.map (fullFn φ) x) (Option.map (fullFn φ) y) := by
  refine (phi_eq_map φ _).symm.trans ((map_mul (phiFn φ) x y).trans ?_)
  exact congrArg₂ (FieldEx.rmul t'.obj) (phi_eq_map φ x) (phi_eq_map φ y)

private lemma fullFn_neg (x : Carrier t.obj) :
    Option.map (fullFn φ) (FieldEx.neg t.obj x) = FieldEx.neg t'.obj (Option.map (fullFn φ) x) := by
  refine (phi_eq_map φ _).symm.trans ((map_neg (phiFn φ) x).trans ?_)
  exact congr(FieldEx.neg t'.obj $(phi_eq_map φ x))

private lemma fullFn_zero :
    Option.map (fullFn φ) (FieldEx.zero t.obj) = FieldEx.zero t'.obj := by
  exact (phi_eq_map φ _).symm.trans (map_zero (phiFn φ))

private lemma of_mul_of (z : SigObj.{u}) (h : Axioms z) (x y : ob z) :
    (Carrier.of x : Carrier z) * Carrier.of y = Carrier.of (mul z x y) := h.etaMul x y

private lemma fullFn_mul (x y : ob t.obj) :
    fullFn φ (mul t.obj x y) = mul t'.obj (fullFn φ x) (fullFn φ y) := by
  rw [← Carrier.of_inj, ← fullFn_spec φ, ← of_mul_of t.obj (axioms_of t) x y, map_mul,
    fullFn_spec φ, fullFn_spec φ, of_mul_of t'.obj (axioms_of t')]

private lemma fullFn_inv (x : ob t.obj) : fullFn φ (inv t.obj x) = inv t'.obj (fullFn φ x) := by
  rw [← Carrier.of_inj, ← fullFn_spec φ, ← Carrier.inv_of, map_inv₀, fullFn_spec φ,
    Carrier.inv_of]

private lemma fullFn_one : fullFn φ (one t.obj) = one t'.obj := by
  rw [← Carrier.of_inj, ← fullFn_spec φ, ← Carrier.one_def, map_one, Carrier.one_def]

/-- The morphism of `T_Field`-bialgebras underlying a homomorphism of the fields. -/
private noncomputable def fullHom : t.obj ⟶ t'.obj :=
  homMk (fullFn φ) (fullFn_mul φ) (fullFn_inv φ) (fullFn_one φ) (fullFn_add φ) (fullFn_rmul φ)
    (fullFn_neg φ) (fullFn_zero φ)

end Full

/-- The comparison functor from `T_Field`-bialgebras to fields is full. -/
instance : comparison.{u}.Full where
  map_surjective {t t'} φ :=
    ⟨⟨fullHom φ⟩, FieldCat.hom_ext fun a => by
      exact (phi_eq_map φ a).symm⟩

/-! ## The comparison functor is essentially surjective -/

section EssSurj

variable (K : FieldCat.{u})

/-- The set of nonzero elements of a field. -/
def NZ : Type u := {x : K.carrier // x ≠ 0}

/-- `Option (NZ K) → K`, sending the extra point to `0`. -/
def valNZ : Option (NZ K) → K.carrier
  | none => 0
  | some x => x.1

open Classical in
/-- `K → Option (NZ K)`, sending `0` to the extra point. -/
noncomputable def optNZ (k : K.carrier) : Option (NZ K) :=
  if h : k = 0 then none else some ⟨k, h⟩

/-- `valNZ` is a left inverse of `optNZ`: `valNZ K (optNZ K k) = k`. -/
@[simp] lemma valNZ_optNZ (k : K.carrier) : valNZ K (optNZ K k) = k := by
  by_cases h : k = 0 <;> simp [optNZ, valNZ, h]

/-- `optNZ` is a left inverse of `valNZ`: `optNZ K (valNZ K a) = a`. -/
@[simp] lemma optNZ_valNZ (a : Option (NZ K)) : optNZ K (valNZ K a) = a := by
  rcases a with _ | x
  · simp [optNZ, valNZ]
  · have : x.1 ≠ 0 := x.2
    simp [optNZ, valNZ, this]
    rfl

/-- `optNZ` sends a nonzero `k` to `some ⟨k, h⟩`. -/
lemma optNZ_of_ne_zero {k : K.carrier} (h : k ≠ 0) : optNZ K k = some ⟨k, h⟩ := by
  simp [optNZ, h]

/-- `optNZ` sends `0` to the extra point `none`. -/
@[simp] lemma optNZ_zero : optNZ K 0 = none := by simp [optNZ]

/-- The multiplication of nonzero elements. -/
def mulNZ (x y : NZ K) : NZ K := ⟨x.1 * y.1, mul_ne_zero x.2 y.2⟩

/-- The inverse of a nonzero element. -/
noncomputable def invNZ (x : NZ K) : NZ K := ⟨x.1⁻¹, inv_ne_zero x.2⟩

/-- The unit of the multiplicative group of nonzero elements. -/
def oneNZ : NZ K := ⟨1, one_ne_zero⟩

/-- The addition, transported to `Option (NZ K)`. -/
noncomputable def addNZ (a b : Option (NZ K)) : Option (NZ K) :=
  optNZ K (valNZ K a + valNZ K b)

/-- The ring multiplication, transported to `Option (NZ K)`. -/
noncomputable def rmulNZ (a b : Option (NZ K)) : Option (NZ K) :=
  optNZ K (valNZ K a * valNZ K b)

/-- The negation, transported to `Option (NZ K)`. -/
noncomputable def negNZ (a : Option (NZ K)) : Option (NZ K) := optNZ K (-valNZ K a)

/-- `valNZ` turns `rmulNZ` into the multiplication of the field. -/
lemma valNZ_rmulNZ (a b : Option (NZ K)) : valNZ K (rmulNZ K a b) = valNZ K a * valNZ K b := by
  simp [rmulNZ]

/-- `valNZ` turns `addNZ` into the addition of the field. -/
lemma valNZ_addNZ (a b : Option (NZ K)) : valNZ K (addNZ K a b) = valNZ K a + valNZ K b := by
  simp [addNZ]

/-- The `Σ`-model object of operations attached to a field. -/
noncomputable def ofField : SigObj.{u} :=
  ofData (NZ K) (mulNZ K) (invNZ K) (oneNZ K) (addNZ K) (rmulNZ K) (negNZ K) (optNZ K 0)

/-- The axioms of `T_Field` hold in the `Σ`-model object `ofField K`. -/
lemma axioms_ofField : Axioms (ofField K) := by
  constructor <;> simp only [ofField, ob_ofData, mul_ofData, inv_ofData, one_ofData, add_ofData,
    rmul_ofData, neg_ofData, zero_ofData]
  · intro x y w; exact Subtype.ext (mul_assoc x.1 y.1 w.1)
  · intro x y; exact Subtype.ext (mul_comm x.1 y.1)
  · intro x; exact Subtype.ext (one_mul x.1)
  · intro x; exact Subtype.ext (inv_mul_cancel₀ x.2)
  · intro x y w; simp [addNZ, add_assoc]
  · intro x y; simp [addNZ, add_comm]
  · intro x; simpa [addNZ, valNZ] using optNZ_valNZ K x
  · intro x; simp [addNZ, negNZ]
  · intro x y w; simp [rmulNZ, mul_assoc]
  · intro x y; simp [rmulNZ, mul_comm]
  · intro x; simpa [rmulNZ, valNZ, oneNZ] using optNZ_valNZ K x
  · intro x y w; simp [rmulNZ, addNZ, mul_add]
  · intro x y
    have hne : x.1 * y.1 ≠ 0 := mul_ne_zero x.2 y.2
    simp [rmulNZ, valNZ, optNZ_of_ne_zero K hne, mulNZ]

/-- A field, as a `T_Field`-bialgebra. -/
noncomputable def ofFieldThy : ThyObj.{u} :=
  ⟨ofField K, (mem_thy_iff (ofField K)).2 (axioms_ofField K)⟩

/-- The comparison functor sends the bialgebra attached to a field back to that field. -/
noncomputable def ringEquivOfField :
    (comparison.obj (ofFieldThy K)).carrier ≃+* K.carrier where
  toFun := valNZ K
  invFun := optNZ K
  left_inv := optNZ_valNZ K
  right_inv := valNZ_optNZ K
  map_mul' := valNZ_rmulNZ K
  map_add' := valNZ_addNZ K

end EssSurj

/-- The comparison functor is essentially surjective: every field arises from a
`T_Field`-bialgebra. -/
instance : comparison.{u}.EssSurj where
  mem_essImage K := ⟨ofFieldThy K, ⟨FieldCat.isoOfRingEquiv (ringEquivOfField K)⟩⟩

/-- The comparison functor is an equivalence (Examples 3.20 (3) of [forsman2026syntactic]). -/
instance : comparison.{u}.IsEquivalence where

/-- **The category of `T_Field`-bialgebras of the model `M = (Set, ×, 1, (−) + 1)` is the
category of fields** (Examples 3.20 (3)). -/
noncomputable def fieldEquiv : ThyObj.{u} ≌ FieldCat.{u} := comparison.asEquivalence

/-- **Examples 3.20 (3)**, as a proposition: the category of `T_Field`-bialgebras of the model
`M = (Set, ×, 1, (−) + 1)` is equivalent to the category of fields. -/
theorem nonempty_thyObj_equiv_fieldCat : Nonempty (ThyObj.{u} ≌ FieldCat.{u}) := ⟨fieldEquiv⟩

end FieldEx

end UlmerBialgebras
