module

public import UlmerBialgebras.Models.Bialgebra
public import UlmerBialgebras.Syntax.DeduplicateTheory

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Deduplication preserves bialgebra objects

The equifier condition for a theory is exactly the family of its interpreted path equations.
Deduplicating those equations therefore leaves the represented subobject unchanged.

## Main results

* `UlmerBialgebras.Model.deduplicate_condition_iff`: equivalence of the equifier conditions.
* `UlmerBialgebras.Model.deduplicateHom`: the canonical map to the deduplicated bialgebra object.
* `UlmerBialgebras.Model.undeduplicateHom`: its strict inverse.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.14 and Corollary 5.8
-/

universe u v w u₁ u₂ u₃ s₁ s₂ s₃
namespace UlmerBialgebras.Model
open CategoryTheory
variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
    [HasChosenFinProducts.{u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
    [HasChosenEquifiers.{u, v, w} Obj]
    {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

omit [HasChosenEquifiers.{u, v, w} Obj] in
/-- A 1-cell satisfies the deduplicated equations exactly when it satisfies the original ones. -/
lemma deduplicate_condition_iff {a : Obj} (d : a ⟶ M.sigObj sg) :
    d ◁ M.lhsCell sg T.deduplicate = d ◁ M.rhsCell sg T.deduplicate ↔
      d ◁ M.lhsCell sg T = d ◁ M.rhsCell sg T := by
  rw [M.whisker_lhsCell_eq_iff, M.whisker_lhsCell_eq_iff]
  exact T.forall_equationData_deduplicate_iff fun q =>
    d ◁ M.pathCell sg q.2.2.2.1 = d ◁ M.pathCell sg q.2.2.2.2

/-- The original bialgebra object is also an equifier of the deduplicated equation cells. -/
noncomputable def deduplicateEquifier :
    Equifier (M.lhsCell sg T.deduplicate) (M.rhsCell sg T.deduplicate) where
  pt := M.thyObj sg T
  e := M.e sg T
  cond := (M.deduplicate_condition_iff sg T _).mpr (M.thyEquif sg T).cond
  lift d h := (M.thyEquif sg T).lift d ((M.deduplicate_condition_iff sg T d).mp h)
  lift_e _ _ := (M.thyEquif sg T).lift_e _ _
  lift_uniq _ _ _ h := (M.thyEquif sg T).lift_uniq _ _ _ h
  full := (M.thyEquif sg T).full
  faithful := (M.thyEquif sg T).faithful

/-- The canonical 1-cell from original to deduplicated bialgebras. -/
noncomputable def deduplicateHom : M.thyObj sg T ⟶ M.thyObj sg T.deduplicate :=
  (M.thyEquif sg T.deduplicate).lift (M.e sg T)
    ((M.deduplicate_condition_iff sg T _).mpr (M.thyEquif sg T).cond)

/-- The canonical 1-cell from deduplicated to original bialgebras. -/
noncomputable def undeduplicateHom : M.thyObj sg T.deduplicate ⟶ M.thyObj sg T :=
  (M.thyEquif sg T).lift (M.e sg T.deduplicate)
    ((M.deduplicate_condition_iff sg T _).mp (M.thyEquif sg T.deduplicate).cond)

/-- Deduplication commutes strictly with the inclusion into the object of operations. -/
lemma deduplicateHom_e : M.deduplicateHom sg T ≫ M.e sg T.deduplicate = M.e sg T :=
  (M.thyEquif sg T.deduplicate).lift_e _ _

/-- The inverse comparison also commutes strictly with the inclusion. -/
lemma undeduplicateHom_e : M.undeduplicateHom sg T ≫ M.e sg T = M.e sg T.deduplicate :=
  (M.thyEquif sg T).lift_e _ _

/-- Deduplicating and then forgetting the reindexing gives the identity 1-cell. -/
lemma deduplicateHom_comp_undeduplicateHom :
    M.deduplicateHom sg T ≫ M.undeduplicateHom sg T = 𝟙 (M.thyObj sg T) := by
  calc
    _ = (M.thyEquif sg T).lift (M.e sg T) (M.thyEquif sg T).cond :=
      (M.thyEquif sg T).lift_uniq _ _ _ (by
        rw [Category.assoc, M.undeduplicateHom_e, M.deduplicateHom_e])
    _ = _ := ((M.thyEquif sg T).lift_uniq _ _ _ (Category.id_comp _)).symm

/-- Forgetting the reindexing and then deduplicating gives the identity 1-cell. -/
lemma undeduplicateHom_comp_deduplicateHom :
    M.undeduplicateHom sg T ≫ M.deduplicateHom sg T = 𝟙 (M.thyObj sg T.deduplicate) := by
  calc
    _ = (M.thyEquif sg T.deduplicate).lift (M.e sg T.deduplicate)
        (M.thyEquif sg T.deduplicate).cond :=
      (M.thyEquif sg T.deduplicate).lift_uniq _ _ _ (by
        rw [Category.assoc, M.deduplicateHom_e, M.undeduplicateHom_e])
    _ = _ := ((M.thyEquif sg T.deduplicate).lift_uniq _ _ _ (Category.id_comp _)).symm

end UlmerBialgebras.Model
