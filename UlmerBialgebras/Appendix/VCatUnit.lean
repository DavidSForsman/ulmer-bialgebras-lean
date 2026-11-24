module

public import UlmerBialgebras.Appendix.VCat

/-!
# The unit `V`-category

The one-object `V`-category `UlmerBialgebras.UnitVCat V`: its unique hom-object is the unit `𝟙_V` of
the monoidal structure, so that — in the convention of `VCat.lean`, where a `V`-category
carries an ordinary category whose hom-sets are represented by the hom-objects — its
underlying category has a single object and the monoid `V(𝟙_V, 𝟙_V)` of endomorphisms of the
unit as its hom-set.

The point of the construction is the **representability of the underlying category**: for
every `V`-category `C`,

* `UlmerBialgebras.unitVCatEval C : (unitVCat V ⟶ C) ⥤ C.carrier` is an equivalence,

i.e. the hom-category of `CAT_V` out of the unit `V`-category is the underlying ordinary
category of `C`.  A `V`-functor out of the unit `V`-category is exactly an object of `C`
(its action on hom-objects is forced to be `eId`), and a `V`-natural transformation between
two such is exactly a morphism of `C` (the `V`-naturality square is automatic).

## Main results

* `UlmerBialgebras.unitVCat`: the unit `V`-category `1`, as an object of `CAT_V`.
* `UlmerBialgebras.UnitVCat.const`: the `V`-functor out of the unit `V`-category at an object `c`.
* `UlmerBialgebras.unitVCatEval`: evaluation `(unitVCat V ⟶ C) ⥤ C.carrier` at the unique object,
  which carries an `IsEquivalence` instance.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition A.4
  (the `V`-category `1`), Theorem A.5
* [G. M. Kelly, *Basic Concepts of Enriched Category Theory*][Kelly:Enriched]
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace UlmerBialgebras

open CategoryTheory MonoidalCategory

/-- The type of objects of the unit `V`-category: a single object. -/
@[nolint unusedArguments]
def UnitVCat (V : Type v) [Category.{w} V] [MonoidalCategory V] : Type u := PUnit.{u + 1}

namespace UnitVCat

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- The unique object of the unit `V`-category. -/
def star : UnitVCat.{w, v, u} V := PUnit.unit

/-- Any two objects of the unit `V`-category are equal. -/
instance : Subsingleton (UnitVCat.{w, v, u} V) := ⟨fun _ _ => rfl⟩

/-- The underlying category of the unit `V`-category: the endomorphisms of the monoidal unit
`𝟙_ V`, composed in `V`. -/
instance : Category.{w} (UnitVCat.{w, v, u} V) where
  Hom _ _ := 𝟙_ V ⟶ 𝟙_ V
  id _ := 𝟙 _
  comp f g := f ≫ g

variable {V}

/-- The endomorphism of the unit underlying a morphism of the unit `V`-category. -/
def toEnd {X Y : UnitVCat.{w, v, u} V} (f : X ⟶ Y) : (𝟙_ V ⟶ 𝟙_ V) := f

/-- The endomorphism underlying an identity is `𝟙 (𝟙_ V)`. -/
@[simp] lemma toEnd_id (X : UnitVCat.{w, v, u} V) : toEnd (𝟙 X) = 𝟙 (𝟙_ V) := rfl

/-- `toEnd` sends a composite to the composite of the endomorphisms. -/
@[simp] lemma toEnd_comp {X Y Z : UnitVCat.{w, v, u} V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toEnd (f ≫ g) = toEnd f ≫ toEnd g := rfl

/-- **Eckmann–Hilton for the unit object**: the tensor product of two endomorphisms of the
unit, conjugated by the left unitor, is their composite. -/
lemma tensor_endo_unit (f g : 𝟙_ V ⟶ 𝟙_ V) :
    (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g) ≫ (λ_ (𝟙_ V)).hom = f ≫ g := by
  have h1 : (𝟙_ V ◁ g) ≫ (λ_ (𝟙_ V)).hom = (λ_ (𝟙_ V)).hom ≫ g :=
    MonoidalCategory.leftUnitor_naturality g
  have h2 : (f ▷ 𝟙_ V) ≫ (ρ_ (𝟙_ V)).hom = (ρ_ (𝟙_ V)).hom ≫ f :=
    MonoidalCategory.rightUnitor_naturality f
  rw [MonoidalCategory.tensorHom_def, Category.assoc, h1, ← Category.assoc,
    MonoidalCategory.unitors_equal, Category.assoc, reassoc_of% h2,
    ← MonoidalCategory.unitors_equal, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

variable (V)

/-- The unit `V`-category: its single hom-object is the monoidal unit `𝟙_ V`, with the left
unitor as composition. -/
instance : EnrichedOrdinaryCategory V (UnitVCat.{w, v, u} V) where
  Hom _ _ := 𝟙_ V
  id _ := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ V)).hom
  id_comp _ _ := by simp
  comp_id _ _ := by simp [MonoidalCategory.unitors_equal]
  assoc _ _ _ _ := by simp [MonoidalCategory.unitors_equal]
  homEquiv := Equiv.refl _
  homEquiv_id _ := rfl
  homEquiv_comp f g := (tensor_endo_unit (toEnd f) (toEnd g)).symm

variable {V}

/-- In the unit `V`-category, `eHomEquiv V f` is the endomorphism `toEnd f`. -/
@[simp] lemma eHomEquiv_eq {X Y : UnitVCat.{w, v, u} V} (f : X ⟶ Y) :
    eHomEquiv V f = toEnd f := rfl

/-- In the unit `V`-category, the identity `eId V X` is `𝟙 (𝟙_ V)`. -/
@[simp] lemma eId_eq (X : UnitVCat.{w, v, u} V) : eId V X = 𝟙 (𝟙_ V) := rfl

/-- In the unit `V`-category, the composition `eComp V X Y Z` is the left unitor
`(λ_ (𝟙_ V)).hom`. -/
@[simp] lemma eComp_eq (X Y Z : UnitVCat.{w, v, u} V) :
    eComp V X Y Z = (λ_ (𝟙_ V)).hom := rfl

end UnitVCat

variable (V : Type v) [Category.{w} V] [MonoidalCategory V]

/-- The unit `V`-category, as an object of `CAT_V`. It is reducible, so that its objects are
those of `UnitVCat V` at reducible transparency, and `UnitVCat.star V` is an object of it. -/
abbrev unitVCat : VCat.{w, v, u} V := ⟨UnitVCat.{w, v, u} V⟩

/-- The objects of `unitVCat V` are those of `UnitVCat V`. -/
@[simp] lemma unitVCat_carrier : (unitVCat.{w, v, u} V).carrier = UnitVCat.{w, v, u} V := rfl

/-- Any two objects of the unit object of `CAT_V` are equal. -/
instance : Subsingleton (unitVCat.{w, v, u} V).carrier :=
  (inferInstance : Subsingleton (UnitVCat.{w, v, u} V))

/-- The type of objects of the unit `V`-category is `w`-small. -/
instance : Small.{w} (unitVCat.{w, v, u} V).carrier :=
  small_of_injective (f := fun _ : UnitVCat.{w, v, u} V => PUnit.unit.{w + 1})
    (fun _ _ _ => Subsingleton.elim _ _)

variable {V}

namespace UnitVCat

variable {C : Type u} [Category.{w} C] [EnrichedOrdinaryCategory V C]

/-- The action of a `V`-functor out of the unit `V`-category on hom-objects is forced: it is
the enriched identity at the image object. -/
lemma vFunctor_emap (F : VFunctor V (UnitVCat.{w, v, u} V) C) (X Y : UnitVCat.{w, v, u} V) :
    F.emap X Y = eId V (F.obj X) := by
  have h := F.emap_id X
  rw [eId_eq, Category.id_comp] at h
  exact h

/-- The enriched identity of `c` is a unit for the enriched composition. -/
lemma eId_comp_eId (c : C) :
    (λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V c) ≫ eComp V c c c = eId V c := by
  have h := eHomEquiv_comp (V := V) (𝟙 c) (𝟙 c)
  simpa using h.symm

/-- The `V`-functor out of the unit `V`-category determined by an object of `C`. -/
def const (c : C) : VFunctor V (UnitVCat.{w, v, u} V) C where
  toFunctor :=
    { obj := fun _ => c
      map := fun {_ _} t => (eHomEquiv V).symm (toEnd t ≫ eId V c)
      map_id := fun _ => by
        apply (eHomEquiv V).injective
        simp
      map_comp := fun {_ _ _} t s => by
        apply (eHomEquiv V).injective
        rw [eHomEquiv_comp]
        simp only [Equiv.apply_symm_apply, toEnd_comp]
        calc (toEnd t ≫ toEnd s) ≫ eId V c
            = (toEnd t ≫ toEnd s) ≫ ((λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V c)
                ≫ eComp V c c c) := by rw [eId_comp_eId]
          _ = ((λ_ (𝟙_ V)).inv ≫ (toEnd t ⊗ₘ toEnd s) ≫ (λ_ (𝟙_ V)).hom)
                ≫ ((λ_ (𝟙_ V)).inv ≫ (eId V c ⊗ₘ eId V c) ≫ eComp V c c c) := by
              rw [tensor_endo_unit]
          _ = (λ_ (𝟙_ V)).inv ≫ ((toEnd t ⊗ₘ toEnd s) ≫ (eId V c ⊗ₘ eId V c))
                ≫ eComp V c c c := by
              simp only [Category.assoc, Iso.hom_inv_id_assoc]
          _ = _ := by rw [← MonoidalCategory.tensorHom_comp_tensorHom] }

  emap _ _ := eId V c
  emap_comp X Y Z := by
    have h := eId_comp_eId (V := V) c
    change (λ_ (𝟙_ V)).hom ≫ eId V c = (eId V c ⊗ₘ eId V c) ≫ eComp V c c c
    exact ((Iso.inv_comp_eq _).mp h).symm
  emap_hom {X Y} t := by simp

/-- The constant `V`-functor at `c` sends the unique object to `c`. -/
@[simp] lemma const_obj (c : C) (X : UnitVCat.{w, v, u} V) : (const (V := V) c).obj X = c := rfl

/-- The constant `V`-functor at `c` acts on the hom-object by the enriched identity of `c`. -/
@[simp] lemma const_emap (c : C) (X Y : UnitVCat.{w, v, u} V) :
    (const (V := V) c).emap X Y = eId V c := rfl

end UnitVCat

/-- **Evaluation at the unique object**: the comparison functor from the hom-category out of
the unit `V`-category to the underlying ordinary category. -/
@[simps]
def unitVCatEval (C : VCat.{w, v, u} V) : (unitVCat.{w, v, u} V ⟶ C) ⥤ C.carrier where
  obj F := F.obj (UnitVCat.star V)
  map α := α.app (UnitVCat.star V)

/-- Evaluation at the unique object is faithful. -/
instance (C : VCat.{w, v, u} V) : (unitVCatEval C).Faithful where
  map_injective h := VNatTrans.ext (funext fun _ => h)

/-- Evaluation at the unique object is full. -/
instance (C : VCat.{w, v, u} V) : (unitVCatEval C).Full where
  map_surjective {F G} f := by
    -- `f`, typed as a morphism between the values at the unique object
    let f' : F.obj (UnitVCat.star V) ⟶ G.obj (UnitVCat.star V) := f
    refine ⟨{ app := fun _ => f', vnaturality := ?_ }, rfl⟩
    intro X Y
    obtain rfl : X = UnitVCat.star V := rfl
    obtain rfl : Y = UnitVCat.star V := rfl
    rw [UnitVCat.vFunctor_emap F, UnitVCat.vFunctor_emap G, ← eHomEquiv_id, ← eHomEquiv_id,
      eHomEquiv_comp_eHomWhiskerLeft, eHomEquiv_comp_eHomWhiskerRight]
    simp

/-- Evaluation at the unique object is essentially surjective, via the constant `V`-functors. -/
instance (C : VCat.{w, v, u} V) : (unitVCatEval C).EssSurj where
  mem_essImage c := ⟨UnitVCat.const c, ⟨Iso.refl _⟩⟩

/-- Evaluation at the unique object is an equivalence `CAT_V(1, C) ≃ C`. -/
instance (C : VCat.{w, v, u} V) : (unitVCatEval C).IsEquivalence where

end UlmerBialgebras
