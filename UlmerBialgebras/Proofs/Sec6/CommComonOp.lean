module

public import Mathlib.CategoryTheory.Monoidal.CommComon_
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite

/-!
# Cocommutative comonoids in `Vᵒᵖ` are commutative monoids in `V`

For a braided monoidal category `V`, a cocommutative comonoid structure on `X : Vᵒᵖ` is a
commutative monoid structure on `unop X`, with multiplication `Δᵒᵖ` and unit `εᵒᵖ`. This gives
an equivalence `CommComon Vᵒᵖ ≌ (CommMon V)ᵒᵖ` whose unit and counit are identities. Mathlib's
`Comon_EquivMon_OpOp` is the analogous statement with the opposite placed the other way.

## Main results

* `UlmerBialgebras.CommComonOp.toCommMonOp`: the functor `CommComon Vᵒᵖ ⥤ (CommMon V)ᵒᵖ`.
* `UlmerBialgebras.CommComonOp.ofCommMonOp`: the functor `(CommMon V)ᵒᵖ ⥤ CommComon Vᵒᵖ`.
* `UlmerBialgebras.CommComonOp.commMonOpEquiv`: an equivalence `CommComon Vᵒᵖ ≌ (CommMon V)ᵒᵖ`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 6.11 (case `A = Mod_R^op`)
-/

@[expose] public section

universe v u

namespace UlmerBialgebras.CommComonOp

open CategoryTheory MonoidalCategory Opposite ComonObj MonObj

variable {V : Type u} [Category.{v} V] [MonoidalCategory V]

/-- A comonoid structure on `X : Vᵒᵖ` is a monoid structure on `unop X`. -/
abbrev monObjUnop (X : Vᵒᵖ) [ComonObj X] : MonObj (unop X) where
  one := ε[X].unop
  mul := Δ[X].unop
  one_mul := by rw [← unop_whiskerRight, ← unop_comp, counit_comul, unop_inv_leftUnitor]
  mul_one := by rw [← unop_whiskerLeft, ← unop_comp, comul_counit, unop_inv_rightUnitor]
  mul_assoc := by
    rw [← unop_whiskerRight, ← unop_comp, comul_assoc_flip]
    simp only [unop_comp, unop_inv_associator, unop_whiskerLeft, Category.assoc]

/-- A monoid structure on `Y : V` is a comonoid structure on `op Y`. -/
abbrev comonObjOp (Y : V) [MonObj Y] : ComonObj (op Y) where
  counit := η[Y].op
  comul := μ[Y].op
  counit_comul := by rw [← op_whiskerRight, ← op_comp, MonObj.one_mul, op_hom_leftUnitor]
  comul_counit := by rw [← op_whiskerLeft, ← op_comp, MonObj.mul_one, op_hom_rightUnitor]
  comul_assoc := by
    rw [← op_whiskerLeft, ← op_comp, MonObj.mul_assoc_flip]
    simp only [op_comp, op_inv_associator, op_whiskerRight, Category.assoc]

attribute [local instance] monObjUnop comonObjOp

/-- The unit of `unop X` is the counit of `X`, reversed. -/
lemma monObjUnop_one (X : Vᵒᵖ) [ComonObj X] : η[unop X] = ε[X].unop := rfl

/-- The multiplication of `unop X` is the comultiplication of `X`, reversed. -/
lemma monObjUnop_mul (X : Vᵒᵖ) [ComonObj X] : μ[unop X] = Δ[X].unop := rfl

/-- The counit of `op Y` is the unit of `Y`, reversed. -/
lemma comonObjOp_counit (Y : V) [MonObj Y] : ε[op Y] = η[Y].op := rfl

/-- The comultiplication of `op Y` is the multiplication of `Y`, reversed. -/
lemma comonObjOp_comul (Y : V) [MonObj Y] : Δ[op Y] = μ[Y].op := rfl

/-- A comonoid morphism `f : X ⟶ Y` in `Vᵒᵖ` gives a monoid morphism `f.unop : unop Y ⟶ unop X`. -/
instance isMonHom_unop {X Y : Vᵒᵖ} [ComonObj X] [ComonObj Y] (f : X ⟶ Y) [IsComonHom f] :
    IsMonHom f.unop where
  one_hom := by
    rw [monObjUnop_one, monObjUnop_one, ← unop_comp, IsComonHom.hom_counit]
  mul_hom := by
    rw [monObjUnop_mul, monObjUnop_mul, ← unop_comp, IsComonHom.hom_comul]
    rfl

/-- A monoid morphism `f : X ⟶ Y` in `V` gives a comonoid morphism `f.op : op Y ⟶ op X` in `Vᵒᵖ`. -/
instance isComonHom_op {X Y : V} [MonObj X] [MonObj Y] (f : X ⟶ Y) [IsMonHom f] :
    IsComonHom f.op where
  hom_counit := by
    rw [comonObjOp_counit, comonObjOp_counit, ← op_comp, IsMonHom.one_hom]
  hom_comul := by
    rw [comonObjOp_comul, comonObjOp_comul, ← op_comp, IsMonHom.mul_hom]
    rfl

variable [BraidedCategory V]

/-- If the comonoid `X : Vᵒᵖ` is cocommutative, the monoid `unop X` (with `μ = Δᵒᵖ`) is commutative.
-/
lemma isCommMonObjUnop (X : Vᵒᵖ) [ComonObj X] [IsCommComonObj X] :
    IsCommMonObj (unop X) where
  mul_comm := by
    rw [monObjUnop_mul, ← unop_hom_braiding, ← unop_comp, IsCommComonObj.comul_comm]

/-- If the monoid `Y : V` is commutative, the comonoid `op Y` (with `Δ = μᵒᵖ`) is cocommutative. -/
lemma isCommComonObjOp (Y : V) [MonObj Y] [IsCommMonObj Y] :
    IsCommComonObj (op Y) where
  comul_comm := by
    rw [comonObjOp_comul, ← op_hom_braiding, ← op_comp, IsCommMonObj.mul_comm]

attribute [local instance] isCommMonObjUnop isCommComonObjOp

variable (V)

/-- Cocommutative comonoids in `Vᵒᵖ` to commutative monoids in `V`. -/
@[simps]
def toCommMonOp : CommComon Vᵒᵖ ⥤ (CommMon V)ᵒᵖ where
  obj A := op { X := unop A.X }
  map {_ _} f := op (CommMon.homMk (Mon.Hom.mk (isMonHom_hom :=
    @isMonHom_unop _ _ _ _ _ _ _ f.hom.hom f.hom.isComonHom_hom) f.hom.hom.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Commutative monoids in `V` to cocommutative comonoids in `Vᵒᵖ`. -/
@[simps]
def ofCommMonOp : (CommMon V)ᵒᵖ ⥤ CommComon Vᵒᵖ where
  obj A := { X := op (unop A).X }
  map {_ _} f := ⟨Comon.Hom.mk (isComonHom_hom :=
    @isComonHom_op _ _ _ _ _ _ _ f.unop.hom.hom f.unop.hom.isMonHom_hom) f.unop.hom.hom.op⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **Cocommutative comonoids in `Vᵒᵖ` are the opposite of commutative monoids in `V`.** -/
@[simps]
def commMonOpEquiv : CommComon Vᵒᵖ ≌ (CommMon V)ᵒᵖ where
  functor := toCommMonOp V
  inverse := ofCommMonOp V
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (Category.comp_id f).trans (Category.id_comp f).symm)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f =>
    (Category.comp_id f).trans (Category.id_comp f).symm)
  functor_unitIso_comp X := (Category.comp_id _).trans ((toCommMonOp V).map_id X)

end UlmerBialgebras.CommComonOp
