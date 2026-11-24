module

public import Mathlib.CategoryTheory.Presentable.Adjunction
public import UlmerBialgebras.Proofs.Sec4.FieldUnitsCreation
public import Mathlib.CategoryTheory.Presentable.Type
public import UlmerBialgebras.Basic.AccClosure
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# Accessibility of the field category

The category of models of the concrete field theory in `CAT`, and `FieldCat`, are accessible in
universe `u`, although the model uses `ULiftHom` to live in `Cat.{u+1,u+1}`. This is the
accessibility clause of Corollary 4.21.

## Main results

* `UlmerBialgebras.Paper.fieldModel_isAccessibleCategory`: `M^T` for the concrete field model is an
  accessible category.
* `UlmerBialgebras.Paper.fieldCat_isAccessibleCategory`: `FieldCat` is an accessible category (the
  accessibility clause of Corollary 4.21).
* `UlmerBialgebras.Paper.smallIndexPi_isAccessibleCategory`: a product of accessible categories over
  an index type in `Type` is accessible in universe `u`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3) and Corollary 4.21
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC],
  2.72 Theorem and 2.76 Lemma
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits FieldEx

/-- A product of accessible categories (objects in `Type (u + 1)`, morphisms in `Type u`) over an
index type `ι : Type` is accessible in universe `u`. -/
theorem smallIndexPi_isAccessibleCategory {ι : Type}
    (C : ι → Type (u + 1)) [∀ i, Category.{u} (C i)]
    [∀ i, IsAccessibleCategory.{u} (C i)] :
    IsAccessibleCategory.{u} (∀ i, C i) := by
  have : IsAccessibleCategory.{u}
      (∀ i : ULift.{u} ι, C ((Equiv.ulift : ULift.{u} ι ≃ ι) i)) :=
    UlmerBialgebras.Pi.isAccessibleCategory
  exact (CategoryTheory.Pi.equivalenceOfEquiv C Equiv.ulift).isAccessibleCategory

/-- For an index type `ι : Type`, the functor `Functor.pi' F` into a product of categories is
accessible in universe `u` when every `F i` is. -/
theorem smallIndexPi_isAccessible {ι : Type}
    {A : Type (u + 1)} [Category.{u} A]
    {C : ι → Type (u + 1)} [∀ i, Category.{u} (C i)]
    (F : ∀ i, A ⥤ C i) [∀ i, Functor.IsAccessible.{u} (F i)] :
    Functor.IsAccessible.{u} (Functor.pi' F) := by
  have h : ∀ i, ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      (F i).IsCardinalAccessible κ :=
    fun i => Functor.IsAccessible.exists_cardinal (F := F i)
  choose S hSreg hSacc using h
  obtain ⟨κ, hκ, hle⟩ := exists_regular_ge S
  have := hκ
  have : ∀ i, (F i).IsCardinalAccessible κ := by
    intro i
    have := hSreg i
    have := hSacc i
    exact Functor.isCardinalAccessible_of_le (F i) (hle i)
  have : (Functor.pi' F).IsCardinalAccessible κ := by
    constructor
    intro J _ _
    have : ∀ i, PreservesColimitsOfShape J (F i) := fun i =>
      Functor.preservesColimitsOfShape_of_isCardinalAccessible (F i) κ J
    exact pi'PreservesColimitsOfShape F
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- Field terms preserve filtered colimits, hence are accessible in universe `u`. -/
theorem fieldModel_tm_isAccessible {c : twoSig.Cat} (t : oneSig.CTrm c) :
    Functor.IsAccessible.{u} ((model.{u}).tm oneSig t).toFunctor := by
  have : Fact (Cardinal.aleph0.{u}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  have : Functor.IsCardinalAccessible ((model.{u}).tm oneSig t).toFunctor Cardinal.aleph0 := by
    constructor
    intro J _ _
    have := isFiltered_of_isCardinalFiltered J Cardinal.aleph0
    have : IsSifted J := IsFiltered.isSifted
    exact FieldEx.preservesColimitsOfShape_tm J t
  exact Functor.isAccessible_of_isCardinalAccessible _ Cardinal.aleph0

/-- Accessibility of `M^T` for the concrete field model. -/
theorem fieldModel_isAccessibleCategory : IsAccessibleCategory.{u} ThyObj.{u} := by
  classical
  -- The products of copies of `Set` that carry the sorts, symbols and equations are accessible.
  have : IsAccessibleCategory.{u} SetCat.{u} := inferInstanceAs (IsAccessibleCategory.{u} (Type u))
  have : ∀ i : oneSig.Srt,
      IsAccessibleCategory.{u} ((model.{u}).obj (oneSig.sty i) : Type (u + 1)) :=
    fun _ => inferInstanceAs (IsAccessibleCategory.{u} SetCat.{u})
  have : ∀ i : oneSig.Fn,
      IsAccessibleCategory.{u} ((model.{u}).obj (oneSig.fnty i) : Type (u + 1)) :=
    fun _ => inferInstanceAs (IsAccessibleCategory.{u} SetCat.{u})
  have : ∀ i : theory.Eqn,
      IsAccessibleCategory.{u} ((model.{u}).obj (theory.eqty i) : Type (u + 1)) :=
    fun _ => inferInstanceAs (IsAccessibleCategory.{u} SetCat.{u})
  have : IsAccessibleCategory.{u} (((model.{u}).P0 oneSig).pt : Type (u + 1)) :=
    smallIndexPi_isAccessibleCategory _
  have : IsAccessibleCategory.{u} (((model.{u}).Pfn oneSig).pt : Type (u + 1)) :=
    smallIndexPi_isAccessibleCategory _
  have : IsAccessibleCategory.{u} (((model.{u}).Peq oneSig theory).pt : Type (u + 1)) :=
    smallIndexPi_isAccessibleCategory _
  -- The 1-cells of the datum are accessible functors between them.
  have : ∀ f : oneSig.Fn,
      Functor.IsAccessible.{u} ((model.{u}).tm oneSig (oneSig.fndom f)).toFunctor :=
    fun f => fieldModel_tm_isAccessible (oneSig.fndom f)
  have : ∀ f : oneSig.Fn,
      Functor.IsAccessible.{u} ((model.{u}).tm oneSig (oneSig.fncod f)).toFunctor :=
    fun f => fieldModel_tm_isAccessible (oneSig.fncod f)
  have : Functor.IsAccessible.{u} ((model.{u}).domCell oneSig).toFunctor :=
    smallIndexPi_isAccessible
      (fun f => ((model.{u}).tm oneSig (oneSig.fndom f)).toFunctor)
  have : Functor.IsAccessible.{u} ((model.{u}).codCell oneSig).toFunctor :=
    smallIndexPi_isAccessible
      (fun f => ((model.{u}).tm oneSig (oneSig.fncod f)).toFunctor)
  have : IsAccessibleCategory.{u} SigObj.{u} := Ins.isAccessibleCategory
  have : Functor.IsAccessible.{u} ((model.{u}).u oneSig).toFunctor :=
    Ins.forget_isAccessible
  have hsig : ∀ {c : twoSig.Cat} (t : oneSig.CTrm c),
      Functor.IsAccessible.{u} ((model.{u}).sigTm oneSig t).toFunctor := by
    intro c t
    rw [(model.{u}).sigTm_eq oneSig t]
    have := fieldModel_tm_isAccessible t
    change Functor.IsAccessible.{u}
      (((model.{u}).u oneSig).toFunctor ⋙ ((model.{u}).tm oneSig t).toFunctor)
    infer_instance
  have : ∀ r : theory.Eqn,
      Functor.IsAccessible.{u} ((model.{u}).sigTm oneSig (theory.dom r)).toFunctor :=
    fun r => hsig (theory.dom r)
  have : ∀ r : theory.Eqn,
      Functor.IsAccessible.{u} ((model.{u}).sigTm oneSig (theory.cod r)).toFunctor :=
    fun r => hsig (theory.cod r)
  have : Functor.IsAccessible.{u}
      (((model.{u}).Peq oneSig theory).lift
        (fun r => (model.{u}).sigTm oneSig (theory.dom r))).toFunctor :=
    smallIndexPi_isAccessible
      (fun r => ((model.{u}).sigTm oneSig (theory.dom r)).toFunctor)
  have : Functor.IsAccessible.{u}
      (((model.{u}).Peq oneSig theory).lift
        (fun r => (model.{u}).sigTm oneSig (theory.cod r))).toFunctor :=
    smallIndexPi_isAccessible
      (fun r => ((model.{u}).sigTm oneSig (theory.cod r)).toFunctor)
  exact Equif.isAccessibleCategory
    (η := ((model.{u}).lhsCell oneSig theory).toNatTrans) (θ := ((model.{u}).rhsCell oneSig
        theory).toNatTrans)

/-- Accessibility transfers to the category of fields through the comparison equivalence
(the accessibility clause of Corollary 4.21 of [forsman2026syntactic]). -/
theorem fieldCat_isAccessibleCategory : IsAccessibleCategory.{u} FieldCat.{u} := by
  have := fieldModel_isAccessibleCategory.{u}
  exact fieldEquiv.{u}.isAccessibleCategory

end UlmerBialgebras.Paper
