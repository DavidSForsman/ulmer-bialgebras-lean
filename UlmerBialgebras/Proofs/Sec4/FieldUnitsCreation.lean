module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Examples.FieldLimits

/-!
# The creation clauses of Corollary 4.21

Relate the nonzero-element functor of the field model to `fieldUnits`,
transfer preservation through the comparison equivalence, and use
conservativity plus the existing limits/colimits to obtain creation.
Accessibility is a separate input and is not asserted in this file.

## Main results

* `UlmerBialgebras.Paper.fieldUnitsCreatesConnectedLimits`: the unit-group functor `fieldUnits`
  creates limits of connected shapes (Corollary 4.21).
* `UlmerBialgebras.Paper.fieldUnitsCreatesSiftedColimits`: `fieldUnits` creates colimits of sifted
  shapes (Corollary 4.21).
* `UlmerBialgebras.Paper.fieldUnits_createsConnectedLimits_and_siftedColimits`: both creation
  clauses together, for small shapes in universe `u`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3), Corollary 4.12 and Corollary 4.21
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper

open CategoryTheory Limits FieldEx

noncomputable section

/-- The underlying nonzero-element functor of the syntactic field model. -/
def fieldModelNonzero : ThyObj.{u} ⥤ Type u :=
  ((model.{u}).thyForget oneSig theory).toFunctor ⋙
    Pi.eval (fun _ : oneSig.Srt => SetCat.{u}) ()

/-- The elements of the model are precisely the units of the associated field. -/
def fieldModelUnitsEquiv (t : ThyObj.{u}) : ob t.obj ≃ (Carrier t.obj)ˣ where
  toFun x := Units.mk0 (Carrier.of x) (fun h =>
    Carrier.of_ne_extra x (h.trans (Carrier.zero_eq_extra (axioms_of t))))
  invFun x := (Carrier.exists_of_of_ne_zero (axioms_of t) x.ne_zero).choose
  left_inv x := by
    apply Carrier.of_inj.mp
    exact (Carrier.exists_of_of_ne_zero (axioms_of t)
      (Units.mk0 (Carrier.of x) (fun h =>
        Carrier.of_ne_extra x
            (h.trans (Carrier.zero_eq_extra (axioms_of t))))).ne_zero).choose_spec.symm
  right_inv x := by
    apply Units.ext
    exact (Carrier.exists_of_of_ne_zero (axioms_of t) x.ne_zero).choose_spec.symm

/-- The comparison equivalence commutes with nonzero-element forgetful functors. -/
def fieldModelUnitsIso : fieldModelNonzero.{u} ≅ comparison.{u} ⋙ fieldUnits.{u} :=
  NatIso.ofComponents (fun t => (fieldModelUnitsEquiv t).toIso) (by
    intro t t' f
    ext x
    apply Units.ext
    rfl)

/-- A field homomorphism inducing a bijection on units is an isomorphism. -/
instance fieldUnitsReflectsIsomorphisms : fieldUnits.{u}.ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    have hsurj : Function.Surjective (fieldUnits.map f) :=
      ((CategoryTheory.isIso_iff_bijective (fieldUnits.map f)).1 inferInstance).2
    have hbij : Function.Bijective (FieldCat.homFn f) := by
      refine ⟨(FieldCat.homFn f).injective, fun y => ?_⟩
      by_cases hy : y = 0
      · exact ⟨0, by simp [hy]⟩
      · obtain ⟨x, hx⟩ := hsurj (Units.mk0 y hy)
        exact ⟨x.val, congrArg (fun z : Y.carrierˣ => z.val) hx⟩
    let e : X.carrier ≃+* Y.carrier := RingEquiv.ofBijective (FieldCat.homFn f) hbij
    change IsIso (FieldCat.isoOfRingEquiv e).hom
    infer_instance

variable (J : Type u) [SmallCategory J]

/-- The forgetful functor `M^T ⥤ Set` of the field model `M = (Set, ×, 1, (-)+1)` preserves
connected limits, by Corollary 4.12 of [forsman2026syntactic] (part of Corollary 4.21). -/
theorem fieldModelNonzero_preservesConnectedLimits [IsConnected J] :
    PreservesLimitsOfShape J fieldModelNonzero.{u} := by
  have h1 := Model.cat_preservesLimitsOfShape_thyForget.{u, u + 1} model.{u} oneSig theory J
    (fun _ => inferInstanceAs (HasLimitsOfShape J SetCat.{u}))
    (fun f => FieldEx.preservesLimitsOfShape_tm J (oneSig.fncod f))
    (fun r => FieldEx.preservesLimitsOfShape_tm J (theory.cod r))
  have : HasLimitsOfShape J SetCat.{u} := inferInstance
  have h2 : PreservesLimitsOfShape J (Pi.eval (fun _ : oneSig.Srt => SetCat.{u}) ()) :=
    piEvalPreservesLimitsOfShape _
  unfold fieldModelNonzero
  exact @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2

/-- The forgetful functor `M^T ⥤ Set` of the field model `M = (Set, ×, 1, (-)+1)` preserves sifted
colimits, by Corollary 4.12 of [forsman2026syntactic] (part of Corollary 4.21). -/
theorem fieldModelNonzero_preservesSiftedColimits [IsSifted J] :
    PreservesColimitsOfShape J fieldModelNonzero.{u} := by
  have h1 := Model.cat_preservesColimitsOfShape_thyForget.{u, u + 1} model.{u} oneSig theory J
    (fun _ => inferInstanceAs (HasColimitsOfShape J SetCat.{u}))
    (fun f => FieldEx.preservesColimitsOfShape_tm J (oneSig.fndom f))
    (fun r => FieldEx.preservesColimitsOfShape_tm J (theory.dom r))
  have h2 : PreservesColimitsOfShape J (Pi.eval (fun _ : oneSig.Srt => SetCat.{u}) ()) :=
    ⟨fun {_} => ⟨fun hc => ⟨piEvalIsColimit hc ()⟩⟩⟩
  unfold fieldModelNonzero
  exact @comp_preservesColimitsOfShape _ _ _ _ _ _ _ _ _ _ h1 h2

/-- Cancel the comparison equivalence on the left, up to its counit. -/
def fieldUnitsCounitIso :
    fieldEquiv.{u}.inverse ⋙ (comparison.{u} ⋙ fieldUnits.{u}) ≅ fieldUnits.{u} :=
  (Functor.associator fieldEquiv.inverse comparison fieldUnits).symm ≪≫
    Functor.isoWhiskerRight fieldEquiv.counitIso fieldUnits ≪≫ Functor.leftUnitor fieldUnits

/-- The unit-group functor `Field ⥤ Set`, `k ↦ k^*`, preserves connected limits (Corollary 4.21 of
[forsman2026syntactic]), transported from the field model along `M^T ≃ Field`. -/
theorem fieldUnits_preservesConnectedLimits [IsConnected J] :
    PreservesLimitsOfShape J fieldUnits.{u} := by
  have := fieldModelNonzero_preservesConnectedLimits J
  have : PreservesLimitsOfShape J (comparison.{u} ⋙ fieldUnits.{u}) :=
    preservesLimitsOfShape_of_natIso fieldModelUnitsIso
  have : PreservesLimitsOfShape J
      (fieldEquiv.{u}.inverse ⋙ (comparison.{u} ⋙ fieldUnits.{u})) := inferInstance
  exact preservesLimitsOfShape_of_natIso fieldUnitsCounitIso

/-- The unit-group functor `Field ⥤ Set`, `k ↦ k^*`, preserves sifted colimits (Corollary 4.21 of
[forsman2026syntactic]), transported from the field model along `M^T ≃ Field`. -/
theorem fieldUnits_preservesSiftedColimits [IsSifted J] :
    PreservesColimitsOfShape J fieldUnits.{u} := by
  have := fieldModelNonzero_preservesSiftedColimits J
  have : PreservesColimitsOfShape J (comparison.{u} ⋙ fieldUnits.{u}) :=
    preservesColimitsOfShape_of_natIso fieldModelUnitsIso
  have : PreservesColimitsOfShape J
      (fieldEquiv.{u}.inverse ⋙ (comparison.{u} ⋙ fieldUnits.{u})) := inferInstance
  exact preservesColimitsOfShape_of_natIso fieldUnitsCounitIso

/-- The connected-limit creation clause of Corollary 4.21 ([forsman2026syntactic]). -/
@[instance_reducible]
def fieldUnitsCreatesConnectedLimits [IsConnected J] :
    CreatesLimitsOfShape J fieldUnits.{u} := by
  haveI := FieldEx.hasLimitsOfShape_fieldCat J
  haveI := fieldUnits_preservesConnectedLimits J
  exact ⟨fun {_} => createsLimitOfReflectsIsomorphismsOfPreserves⟩

/-- The sifted-colimit creation clause of Corollary 4.21 ([forsman2026syntactic]). -/
@[instance_reducible]
def fieldUnitsCreatesSiftedColimits [IsSifted J] :
    CreatesColimitsOfShape J fieldUnits.{u} := by
  haveI := FieldEx.hasColimitsOfShape_fieldCat J
  haveI := fieldUnits_preservesSiftedColimits J
  exact ⟨fun {_} => createsColimitOfReflectsIsomorphismsOfPreserves⟩

/-- The two creation clauses of Corollary 4.21 ([forsman2026syntactic]), leaving accessibility
as the remaining conjunct. -/
theorem fieldUnits_createsConnectedLimits_and_siftedColimits :
    (∀ (J : Type u) [SmallCategory J] [IsConnected J],
      Nonempty (CreatesLimitsOfShape J fieldUnits.{u})) ∧
    (∀ (J : Type u) [SmallCategory J] [IsSifted J],
      Nonempty (CreatesColimitsOfShape J fieldUnits.{u})) :=
  ⟨fun J _ _ => ⟨fieldUnitsCreatesConnectedLimits J⟩,
    fun J _ _ => ⟨fieldUnitsCreatesSiftedColimits J⟩⟩

end

end UlmerBialgebras.Paper
