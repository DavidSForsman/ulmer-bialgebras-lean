module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import UlmerBialgebras.Examples.MonCalc

/-!
# Comparing the monoid-model theory with internal monoids

For a monoidal category `C`, construct the comparison functor from its category of
`T_Mon`-bialgebras to `Mon C`, and its strict inverse. The inverse identities over the base
category are proved in `UlmerBialgebras/Proofs/Sec3/MonModelCalc.lean`.

## Main results

* `UlmerBialgebras.MonEx.comparison`: the comparison functor from `T_Mon`-bialgebras of `C` to
  `Mon C`.
* `UlmerBialgebras.MonEx.inverseFunctor`: the functor `Mon C ⥤ M^{T_Mon}` regarding a monoid object
  as a `T_Mon`-bialgebra.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (1)
-/

@[expose] public section


universe v u

namespace UlmerBialgebras

namespace MonEx

open CategoryTheory MonoidalCategory

variable {C : Type (max u v)} [Category.{v} C] [MonoidalCategory C]

/-! ## Morphisms of pointed magmas -/

/-- The underlying morphism of `C` of a morphism of pointed magmas. -/
def bs {z z' : SigObj C} (f : z ⟶ z') : ob z ⟶ ob z' := f.base ()

/-- A morphism of `M^σ` is determined by its underlying morphism `bs`. -/
lemma bs_injective {z z' : SigObj C} {f g : z ⟶ z'} (h : bs f = bs g) : f = g := by
  apply Ins.hom_ext
  funext s
  cases s
  exact h

/-- The multiplication square of a morphism of pointed magmas. -/
lemma bs_mul {z z' : SigObj C} (f : z ⟶ z') :
    mul z ≫ bs f = (bs f ⊗ₘ bs f) ≫ mul z' :=
  funext_iff.mp f.w FnSym.mul

/-- The unit triangle of a morphism of pointed magmas. -/
lemma bs_one {z z' : SigObj C} (f : z ⟶ z') : one z ≫ bs f = one z' := by
  have h : one z ≫ bs f = 𝟙 (𝟙_ C) ≫ one z' := funext_iff.mp f.w FnSym.one
  simpa using h

/-- A morphism of pointed magmas, built from a morphism of `C` compatible with the
multiplications and the units. -/
def homMk {z z' : SigObj C} (g : ob z ⟶ ob z')
    (hm : mul z ≫ g = (g ⊗ₘ g) ≫ mul z') (he : one z ≫ g = one z') : z ⟶ z' where
  base := fun _ => g
  w := by
    funext f
    cases f
    · exact hm
    · exact he.trans (Category.id_comp _).symm

/-! ## The objects of `M^T` -/

/-- The category `M^{T_Mon}` of `T_Mon`-bialgebras of a monoidal category. -/
abbrev ThyObj (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] : Type (max u v) :=
  ((monModel C).thyObj oneSig monTheory : Type (max u v))

/-- A `T_Mon`-bialgebra is a monoid object of `C`. -/
instance monObj (t : ThyObj C) : MonObj (ob t.obj) where
  one := one t.obj
  mul := mul t.obj
  one_mul := ((mem_thy_iff t.obj).1 t.property).2.2
  mul_one := ((mem_thy_iff t.obj).1 t.property).2.1
  mul_assoc := ((mem_thy_iff t.obj).1 t.property).1

/-- Conversely, a monoid object of `C` gives a pointed magma satisfying the theory. -/
def ofMonSig (M : Mon C) : SigObj C where
  pt := fun _ => M.X
  cell := fun f =>
    match f with
    | FnSym.mul => (MonObj.mul : M.X ⊗ M.X ⟶ M.X)
    | FnSym.one => (MonObj.one : 𝟙_ C ⟶ M.X)

/-- A monoid object of `C`, as an object of `M^{T_Mon}`. -/
def ofMon (M : Mon C) : ThyObj C :=
  ⟨ofMonSig M, (mem_thy_iff (ofMonSig M)).2
    ⟨MonObj.mul_assoc M.X, MonObj.mul_one M.X, MonObj.one_mul M.X⟩⟩

/-! ## The comparison functor -/

/-- **The comparison functor** from the category `M^{T_Mon}` of `T_Mon`-bialgebras of a
monoidal category `C` to the category of monoid objects of `C`. -/
@[simps]
def comparison (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] : ThyObj C ⥤ Mon C where
  obj t := { X := ob t.obj }
  map {_ _} f :=
    { hom := bs f.hom
      isMonHom_hom :=
        { one_hom := bs_one f.hom
          mul_hom := bs_mul f.hom } }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The comparison functor from bialgebras to monoids in `C` is faithful. -/
instance : (comparison C).Faithful where
  map_injective {_ _} f g h := by
    apply ObjectProperty.hom_ext
    apply bs_injective
    exact congr(Mon.Hom.hom $h)

/-- The strict inverse of the comparison functor: a monoid object of `C`, regarded as a
`T_Mon`-bialgebra. -/
@[simps]
def inverseFunctor (C : Type (max u v)) [Category.{v} C] [MonoidalCategory C] : Mon C ⥤
    ThyObj C where
  obj M := ofMon M
  map g := ⟨homMk g.hom (IsMonHom.mul_hom g.hom) (IsMonHom.one_hom g.hom)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end MonEx

end UlmerBialgebras
