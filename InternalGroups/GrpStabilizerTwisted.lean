module

public import InternalGroups.GrpStabilizer

/-!
# Twisted actions for stabilizers of regular monomorphisms

The action associated to two homomorphisms sends `(h, z)` to `f(h) z g(h)⁻¹`.

## Main results

* `InternalGroups.twistedAction_lift`: the formula on generalized elements.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

universe v u
open CategoryTheory MonoidalCategory Limits CartesianMonoidalCategory MonObj GrpObj
open scoped MonObj

namespace InternalGroups
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable {H K : C} [GrpObj K]

/-- The twisted action associated to two group homomorphisms. -/
def twistedAction (f g : H ⟶ K) : H ⊗ K ⟶ K :=
  (fst H K ≫ f) * snd H K * (fst H K ≫ g)⁻¹

/-- The twisted action evaluated on generalized elements. -/
lemma twistedAction_lift (f g : H ⟶ K) {T : C} (h : T ⟶ H) (z : T ⟶ K) :
    lift h z ≫ twistedAction f g = (h ≫ f) * z * (h ≫ g)⁻¹ := by
  simp [twistedAction, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]

/-- The orbit map of the identity for the twisted action. -/
def twistedOrbit (f g : H ⟶ K) : H ⟶ K := f * g⁻¹

/-- Fixing the identity in the twisted action means the two homomorphisms agree. -/
theorem twistedOrbit_eq_one_iff (f g : H ⟶ K) {T : C} (x : T ⟶ H) :
    x ≫ twistedOrbit f g = 1 ↔ x ≫ f = x ≫ g := by
  simp [twistedOrbit, MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]

variable [GrpObj H]

/-- The identity of the acting group acts trivially. -/
lemma twistedAction_one (f g : H ⟶ K) [IsMonHom f] [IsMonHom g]
    {T : C} (z : T ⟶ K) : lift (1 : T ⟶ H) z ≫ twistedAction f g = z := by
  simp [twistedAction_lift]

/-- The twisted action is associative on generalized elements. -/
lemma twistedAction_mul (f g : H ⟶ K) [IsMonHom f] [IsMonHom g]
    {T : C} (x y : T ⟶ H) (z : T ⟶ K) :
    lift (x * y) z ≫ twistedAction f g =
      lift x (lift y z ≫ twistedAction f g) ≫ twistedAction f g := by
  simp [twistedAction_lift, MonObj.mul_comp, Semigroup.mul_assoc]

/-- The twisted action defines a module over the source group. -/
@[instance_reducible]
def twistedModObj (f g : H ⟶ K) [IsMonHom f] [IsMonHom g] : ModObj H K where
  smul := twistedAction f g
  one_smul := by
    change (η[H] ▷ K) ≫ twistedAction f g = (λ_ K).hom
    apply CartesianMonoidalCategory.hom_ext_lift
    intro T a z
    have ha : a ≫ η[H] = (1 : T ⟶ H) := by
      rw [Hom.one_def, toUnit_unique a (toUnit T)]
    rw [← Category.assoc, lift_whiskerRight, ha, twistedAction_one,
      leftUnitor_hom, lift_snd]
  mul_smul := by
    change (μ[H] ▷ K) ≫ twistedAction f g =
      (α_ H H K).hom ≫ (H ◁ twistedAction f g) ≫ twistedAction f g
    apply InternalGroups.AugMon.hom_ext_lift_assoc_cartesian
    intro T x y z
    rw [← Category.assoc, lift_whiskerRight, ← Hom.mul_def, twistedAction_mul]
    rw [← Category.assoc, ← Category.assoc, lift_lift_associator_hom,
      lift_whiskerLeft]

attribute [local instance] CategoryTheory.ModObj.regular

/-- The orbit map is equivariant for the twisted action. -/
theorem isModHom_twistedOrbit (f g : H ⟶ K) [IsMonHom f] [IsMonHom g] :
    letI := twistedModObj f g
    IsModHom H (twistedOrbit f g) := by
  let := twistedModObj f g
  constructor
  change μ[H] ≫ twistedOrbit f g = (H ◁ twistedOrbit f g) ≫ twistedAction f g
  apply CartesianMonoidalCategory.hom_ext_lift
  intro T x y
  rw [← Category.assoc, ← Hom.mul_def, ← Category.assoc, lift_whiskerLeft,
    twistedAction_lift]
  simp [twistedOrbit, MonObj.comp_mul, GrpObj.comp_inv, MonObj.mul_comp,
    Semigroup.mul_assoc]

/-- The base point of the twisted orbit map is the group identity. -/
lemma twistedOrbit_basePoint (f g : H ⟶ K) [IsMonHom f] [IsMonHom g] :
    stabBasePoint (G := H) (twistedOrbit f g) = η[K] := by
  simp [stabBasePoint, twistedOrbit, MonObj.comp_mul, GrpObj.comp_inv,
    IsMonHom.one_hom, ← MonObj.one_eq_one]

end InternalGroups
