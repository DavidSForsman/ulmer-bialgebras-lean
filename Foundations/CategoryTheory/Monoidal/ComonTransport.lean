module

public import Mathlib.CategoryTheory.Monoidal.CommComon_

/-!
# Transport of comonoid objects along isomorphisms

Transporting a comonoid structure makes both directions of the isomorphism comonoid
morphisms. In a braided category transport also preserves cocommutativity.

## References

* Mathlib's comonoid objects and morphisms in `Mathlib/CategoryTheory/Monoidal/Comon_.lean`.
-/

@[expose] public section
universe v u
namespace UlmerBialgebras
open CategoryTheory MonoidalCategory
open scoped ComonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] {A Y : C} (e : A ≅ Y)

@[reassoc]
private lemma tensorHom_whiskerLeft_inv {Z : C} (k : A ⟶ Z) :
    (e.hom ⊗ₘ e.hom) ≫ Y ◁ (e.inv ≫ k) = e.hom ⊗ₘ k := by
  rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, e.hom_inv_id_assoc]

@[reassoc]
private lemma tensorHom_whiskerRight_inv {Z : C} (k : A ⟶ Z) :
    (e.hom ⊗ₘ e.hom) ≫ (e.inv ≫ k) ▷ Y = k ⊗ₘ e.hom := by
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id, e.hom_inv_id_assoc]

/-- Transport of a comonoid structure along an isomorphism. -/
@[instance_reducible]
def ComonObj.ofIso [ComonObj A] : ComonObj Y where
  counit := e.inv ≫ ε[A]
  comul := e.inv ≫ Δ[A] ≫ (e.hom ⊗ₘ e.hom)
  counit_comul := by
    rw [Category.assoc, Category.assoc, tensorHom_whiskerRight_inv, tensorHom_def,
      ComonObj.counit_comul_assoc, ← leftUnitor_inv_naturality, e.inv_hom_id_assoc]
  comul_counit := by
    rw [Category.assoc, Category.assoc, tensorHom_whiskerLeft_inv, tensorHom_def',
      ComonObj.comul_counit_assoc, ← rightUnitor_inv_naturality, e.inv_hom_id_assoc]
  comul_assoc := by
    simp only [Category.assoc, tensorHom_whiskerRight_inv_assoc, tensorHom_whiskerLeft_inv]
    congr 1
    rw [← Category.id_comp e.hom, ← tensorHom_comp_tensorHom, id_tensorHom,
      ComonObj.comul_assoc_assoc, ← tensorHom_comp_tensorHom_assoc, tensorHom_id, Category.id_comp,
      associator_naturality]

/-- The comultiplication on the transported comonoid. -/
@[simp]
lemma ComonObj.ofIso_comul [ComonObj A] :
    (ComonObj.ofIso e).comul = e.inv ≫ Δ[A] ≫ (e.hom ⊗ₘ e.hom) := rfl

/-- The isomorphism along which a comonoid structure is transported is a comonoid morphism. -/
lemma ComonObj.isComonHom_ofIso_hom [ComonObj A] :
    letI := ComonObj.ofIso e
    IsComonHom e.hom :=
  letI := ComonObj.ofIso e
  { hom_counit := e.hom_inv_id_assoc _
    hom_comul := e.hom_inv_id_assoc _ }

/-- The inverse of the isomorphism along which a comonoid structure is transported is a comonoid
morphism. -/
lemma ComonObj.isComonHom_ofIso_inv [ComonObj A] :
    letI := ComonObj.ofIso e
    IsComonHom e.inv :=
  letI := ComonObj.ofIso e
  { hom_counit := rfl
    hom_comul := by
      change e.inv ≫ Δ[A] = (e.inv ≫ Δ[A] ≫ (e.hom ⊗ₘ e.hom)) ≫ (e.inv ⊗ₘ e.inv)
      rw [Category.assoc, Category.assoc, tensorHom_comp_tensorHom, e.hom_inv_id,
        id_tensorHom_id, Category.comp_id] }

/-- The transport of a commutative comonoid structure is commutative. -/
lemma ComonObj.isCommComonObj_ofIso [BraidedCategory C] [ComonObj A] [IsCommComonObj A] :
    letI := ComonObj.ofIso e
    IsCommComonObj Y :=
  letI := ComonObj.ofIso e
  { comul_comm := by
      rw [ComonObj.ofIso_comul, Category.assoc, Category.assoc, BraidedCategory.braiding_naturality,
        IsCommComonObj.comul_comm_assoc] }

end UlmerBialgebras
