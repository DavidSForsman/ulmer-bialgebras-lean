module

public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Kan.CatModelLimits

/-!
# Corollary 4.21 for the category of fields

Combining

* the computation of limits and colimits in the category of bialgebras of a model in `CAT`
  (`CatModelLimits.lean`),
* the preservation properties of the interpretations `×`, `1` and `(−) + 1` of the model
  `M = (Set, ×, 1, (−) + 1)` (`FieldModel.lean`, `SetFunctors.lean`, `SiftedPi.lean`), and
* the identification `M^{T_Field} ≌ Field` (`FieldEquiv.lean`),

we obtain **Corollary 4.21 for the category of fields**: the category of fields has all
connected limits and all sifted colimits, and they are computed as in `Set`.

The connectedness hypothesis is essential: the category of fields has no terminal object,
and a product of two fields is not a field.  Likewise for colimits: sifted colimits of
fields are computed as in `Set`, but the category of fields has no initial object.

## Main results

* `UlmerBialgebras.FieldEx.hasLimitsOfShape_thyObj`,
  `UlmerBialgebras.FieldEx.hasColimitsOfShape_thyObj`: the category of `T_Field`-bialgebras has
  connected limits and sifted colimits of `u`-small shape (Corollary 4.21).
* `UlmerBialgebras.FieldEx.hasLimitsOfShape_fieldCat`,
  `UlmerBialgebras.FieldEx.hasColimitsOfShape_fieldCat`: the category of fields has connected limits
  and sifted colimits of `u`-small shape (Corollary 4.21).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (3) and Corollary 4.21
-/

@[expose] public section

universe u

namespace UlmerBialgebras

namespace FieldEx

open CategoryTheory Limits

section Shape

variable (J : Type u) [SmallCategory J]

/-! ## Preservation properties of the interpretations, for `u`-small shapes -/

/-- The product of sets preserves all `u`-small limits. -/
theorem prodFunctorU_preservesLimitsOfShapeS : PreservesLimitsOfShape J prodFunctorU.{u} :=
  preservesLimitsOfShape_prodFunctor

/-- The constant functor at a singleton preserves connected `u`-small limits. -/
theorem unitFunctorU_preservesLimitsOfShapeS [IsConnected J] :
    PreservesLimitsOfShape J unitFunctorU.{u} :=
  inferInstanceAs (PreservesLimitsOfShape J unitFunctor)

/-- The maybe functor preserves connected `u`-small limits. -/
theorem succFunctorU_preservesLimitsOfShapeS [IsConnected J] :
    PreservesLimitsOfShape J succFunctorU.{u} := by
  have : PreservesLimitsOfShape J optionFunctor.{u} := preservesLimitsOfShape_option
  exact Limits.comp_preservesLimitsOfShape (Pi.eval (fun _ : Fin 1 => Type u) 0) optionFunctor

/-- The product of sets preserves sifted colimits, by Lemma 4.16. -/
theorem prodFunctorU_preservesColimitsOfShapeS [IsSifted J] :
    PreservesColimitsOfShape J prodFunctorU.{u} := by
  refine preservesColimitsOfShape_pi_of_componentwise _ (fun i x => ?_)
  fin_cases i
  · have := prodRightPreservesColimitsOfShape (J := J) (x 1)
    exact preservesColimitsOfShape_of_natIso (updateProdUZero x).symm
  · have := prodLeftPreservesColimitsOfShape (J := J) (x 0)
    exact preservesColimitsOfShape_of_natIso (updateProdUOne x).symm

/-- The constant functor at a singleton preserves sifted colimits: its source is the
terminal category, so Lemma 4.16 applies with an empty family of variables. -/
theorem unitFunctorU_preservesColimitsOfShapeS [IsSifted J] :
    PreservesColimitsOfShape J unitFunctorU.{u} :=
  preservesColimitsOfShape_pi_of_componentwise _ (fun i _ => i.elim0)

/-- The maybe functor preserves sifted colimits. -/
theorem succFunctorU_preservesColimitsOfShapeS [IsSifted J] :
    PreservesColimitsOfShape J succFunctorU.{u} := by
  refine preservesColimitsOfShape_pi_of_componentwise _ (fun i x => ?_)
  fin_cases i
  have : PreservesColimitsOfShape J optionFunctor.{u} := preservesColimitsOfShape_option
  exact preservesColimitsOfShape_of_natIso (updateSuccUZero x).symm

/-! ## The interpretation of a term -/

/-- Every closed term of the field signature is interpreted by a functor preserving
connected limits: it is built out of projections, the product, the singleton and the maybe
functor. -/
theorem preservesLimitsOfShape_tm [IsConnected J] :
    ∀ {c : twoSig.Cat} (t : oneSig.CTrm c),
      PreservesLimitsOfShape J ((model.{u}).tm oneSig t).toFunctor := by
  intro c t
  induction t with
  | var v =>
      exact inferInstanceAs (PreservesLimitsOfShape J
        (Pi.eval (fun i : oneSig.Srt => (((model.{u}).obj (oneSig.sty i)) : Type (u + 1))) v))
  | app B args ih =>
      have : ∀ i, PreservesLimitsOfShape J ((model.{u}).tm oneSig (args i)).toFunctor := ih
      have hB : PreservesLimitsOfShape J ((model.{u}).fn B).toFunctor := by
        cases B with
        | tens => exact prodFunctorU_preservesLimitsOfShapeS J
        | unit => exact unitFunctorU_preservesLimitsOfShapeS J
        | succ => exact succFunctorU_preservesLimitsOfShapeS J
      exact @Limits.comp_preservesLimitsOfShape _ _ _ _ _ _ _ _
        (Functor.pi' (fun i => ((model.{u}).tm oneSig (args i)).toFunctor))
          ((model.{u}).fn B).toFunctor inferInstance hB

/-- Every closed term of the field signature is interpreted by a functor preserving sifted
colimits. -/
theorem preservesColimitsOfShape_tm [IsSifted J] :
    ∀ {c : twoSig.Cat} (t : oneSig.CTrm c),
      PreservesColimitsOfShape J ((model.{u}).tm oneSig t).toFunctor := by
  intro c t
  induction t with
  | var v =>
      exact inferInstanceAs (PreservesColimitsOfShape J
        (Pi.eval (fun i : oneSig.Srt => (((model.{u}).obj (oneSig.sty i)) : Type (u + 1))) v))
  | app B args ih =>
      have : ∀ i, PreservesColimitsOfShape J ((model.{u}).tm oneSig (args i)).toFunctor := ih
      have hB : PreservesColimitsOfShape J ((model.{u}).fn B).toFunctor := by
        cases B with
        | tens => exact prodFunctorU_preservesColimitsOfShapeS J
        | unit => exact unitFunctorU_preservesColimitsOfShapeS J
        | succ => exact succFunctorU_preservesColimitsOfShapeS J
      exact @Limits.comp_preservesColimitsOfShape _ _ _ _ _ _ _ _
        (Functor.pi' (fun i => ((model.{u}).tm oneSig (args i)).toFunctor))
          ((model.{u}).fn B).toFunctor inferInstance hB

/-! ## Connected limits and sifted colimits of bialgebras -/

/-- **Corollary 4.21, connected limits**: the category `M^{T_Field}` of `T_Field`-bialgebras
has all connected limits of `u`-small shape. -/
theorem hasLimitsOfShape_thyObj [IsConnected J] : HasLimitsOfShape J ThyObj.{u} :=
  Model.cat_hasLimitsOfShape_thyObj.{u, u + 1} model.{u} oneSig theory J
    (fun _ => inferInstanceAs (HasLimitsOfShape J SetCat.{u}))
    (fun f => preservesLimitsOfShape_tm J (oneSig.fncod f))
    (fun r => preservesLimitsOfShape_tm J (theory.cod r))

/-- **Corollary 4.21, sifted colimits**: the category `M^{T_Field}` of `T_Field`-bialgebras
has all sifted colimits of `u`-small shape. -/
theorem hasColimitsOfShape_thyObj [IsSifted J] : HasColimitsOfShape J ThyObj.{u} :=
  Model.cat_hasColimitsOfShape_thyObj.{u, u + 1} model.{u} oneSig theory J
    (fun _ => inferInstanceAs (HasColimitsOfShape J SetCat.{u}))
    (fun f => preservesColimitsOfShape_tm J (oneSig.fndom f))
    (fun r => preservesColimitsOfShape_tm J (theory.dom r))

/-! ## Connected limits and sifted colimits of fields -/

/-- **Corollary 4.21 for fields**: the category of fields has all connected limits of
`u`-small shape. -/
theorem hasLimitsOfShape_fieldCat [IsConnected J] : HasLimitsOfShape J FieldCat.{u} := by
  have := hasLimitsOfShape_thyObj J
  exact Adjunction.hasLimitsOfShape_of_equivalence fieldEquiv.{u}.inverse

/-- **Corollary 4.21 for fields**: the category of fields has all sifted colimits of
`u`-small shape. -/
theorem hasColimitsOfShape_fieldCat [IsSifted J] : HasColimitsOfShape J FieldCat.{u} := by
  have := hasColimitsOfShape_thyObj J
  exact Adjunction.hasColimitsOfShape_of_equivalence fieldEquiv.{u}.inverse

end Shape

end FieldEx

end UlmerBialgebras
