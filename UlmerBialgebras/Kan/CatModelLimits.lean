module

public import UlmerBialgebras.Models.CatPIE
public import UlmerBialgebras.Kan.LiftLimits
public import UlmerBialgebras.Basic.AccInsEq
public import Foundations.CategoryTheory.Limits.PiLimits
public import Foundations.CategoryTheory.Limits.PiColimits
public import Foundations.CategoryTheory.Limits.OpTranslate
public import UlmerBialgebras.Kan.KanModel

/-!
# Limits and colimits in the category of bialgebras of a model in `CAT`

For a `Σ`-model `M` in the 2-category `CAT` of categories, the object `M^T` of
`T`-bialgebras is by construction an equifier inside an inserter over a product of categories
(`CatPIE.lean`), so limits and colimits in `M^T` can be computed in `M₀ = ∏_s M_{c_s}`
as soon as the relevant coarity (resp. arity) supports preserve them:

* `UlmerBialgebras.Model.cat_hasLimitsOfShape_thyObj` — `M^T` has all `J`-limits which the coarity
  supports `M(t₂)` preserve;
* `UlmerBialgebras.Model.cat_hasColimitsOfShape_thyObj` — `M^T` has all `J`-colimits which the arity
  supports `M(t₁)` preserve;

together with the corresponding preservation statements for the forgetful functors
`u : M^σ → M₀`, `e : M^T → M^σ` and `U : M^T → M₀`.

## Main results

* `UlmerBialgebras.Model.cat_hasLimitsOfShape_thyObj`: if the `M_c` have `J`-limits and the coarity
  supports preserve them, then `M^T` has `J`-limits (an instance of Corollary 4.11 in `CAT`).
* `UlmerBialgebras.Model.cat_hasColimitsOfShape_thyObj`: if the `M_c` have `J`-colimits and the
  arity supports preserve them, then `M^T` has `J`-colimits (an instance of Corollary 4.11 in
  `CAT`).
* `UlmerBialgebras.Model.cat_preservesLimitsOfShape_thyForget`,
  `UlmerBialgebras.Model.cat_preservesColimitsOfShape_thyForget`: under the same hypotheses, the
  forgetful functor `U : M^T → M₀` preserves these limits, resp. colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 4.7 and Corollary 4.11
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras]
-/

@[expose] public section

universe v u

namespace UlmerBialgebras

open CategoryTheory Limits

namespace Model

variable {Sg : TwoSig} (M : Model Sg Cat.{v, max u v}) (sg : OneSig Sg) (T : Theory sg)
variable (J : Type*) [Category J]

/-! ## Limits -/

/-- The product `M₀ = ∏_s M_{c_s}` has all `J`-limits as soon as each `M_c` does. -/
theorem cat_hasLimitsOfShape_P0
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v))) :
    HasLimitsOfShape J ((M.P0 sg).pt : Type (max u v)) := by
  have := hlim
  exact inferInstanceAs (HasLimitsOfShape J (∀ i : sg.Srt, ((M.obj (sg.sty i)) : Type (max u v))))

/-- If every function coarity support preserves `J`-limits, so does the 1-cell
`(M(t₂))_f : M₀ → ∏_f M_{c_f}` they assemble into. -/
theorem cat_preservesLimitsOfShape_codCell
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor) :
    PreservesLimitsOfShape J (M.codCell sg).toFunctor := by
  have : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.tm sg (sg.fncod f)).toFunctor := hfn
  exact inferInstanceAs (PreservesLimitsOfShape J
    (Functor.pi' (fun f : sg.Fn => (M.tm sg (sg.fncod f)).toFunctor)))

/-- The object of operations `M^σ` has all `J`-limits which the coarity supports preserve. -/
theorem cat_hasLimitsOfShape_sigObj
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor) :
    HasLimitsOfShape J (M.sigObj sg : Type (max u v)) := by
  have := M.cat_hasLimitsOfShape_P0 sg J hlim
  have := M.cat_preservesLimitsOfShape_codCell sg J hfn
  exact inferInstanceAs (HasLimitsOfShape J
    (Ins (M.domCell sg).toFunctor (M.codCell sg).toFunctor))

/-- The forgetful functor `u : M^σ → M₀` creates, hence preserves, the `J`-limits which the
coarity supports preserve. -/
theorem cat_preservesLimitsOfShape_u
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor) :
    PreservesLimitsOfShape J (M.u sg).toFunctor := by
  have := M.cat_hasLimitsOfShape_P0 sg J hlim
  have := M.cat_preservesLimitsOfShape_codCell sg J hfn
  exact inferInstanceAs (PreservesLimitsOfShape J
    (Ins.forget (M.domCell sg).toFunctor (M.codCell sg).toFunctor))

/-- If every equational coarity support preserves `J`-limits, so does the right-hand 1-cell
of the equifier defining `M^T`. -/
theorem cat_preservesLimitsOfShape_rhs
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesLimitsOfShape J (M.eqnCoarity sg T r).toFunctor) :
    PreservesLimitsOfShape J
      (((M.Peq sg T).lift (fun r => M.sigTm sg (T.cod r)))).toFunctor := by
  have := M.cat_preservesLimitsOfShape_u sg J hlim hfn
  have : ∀ r : T.Eqn, PreservesLimitsOfShape J (M.sigTm sg (T.cod r)).toFunctor := by
    intro r
    rw [M.sigTm_eq sg (T.cod r)]
    have h2 : PreservesLimitsOfShape J (M.tm sg (T.cod r)).toFunctor := heq r
    exact inferInstanceAs (PreservesLimitsOfShape J
      ((M.u sg).toFunctor ⋙ (M.tm sg (T.cod r)).toFunctor))
  exact inferInstanceAs (PreservesLimitsOfShape J
    (Functor.pi' (fun r : T.Eqn => (M.sigTm sg (T.cod r)).toFunctor)))

/-- **Limits in `M^T`**: the category of `T`-bialgebras has all `J`-limits which the coarity
supports preserve (cf. Corollary 4.11 of [forsman2026syntactic], in `CAT`). -/
theorem cat_hasLimitsOfShape_thyObj
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesLimitsOfShape J (M.eqnCoarity sg T r).toFunctor) :
    HasLimitsOfShape J (M.thyObj sg T : Type (max u v)) := by
  have := M.cat_hasLimitsOfShape_sigObj sg J hlim hfn
  have := M.cat_preservesLimitsOfShape_rhs sg T J hlim hfn heq
  exact inferInstanceAs (HasLimitsOfShape J (Equif (M.lhsCell sg T).toNatTrans (M.rhsCell sg
      T).toNatTrans))

/-- The inclusion `e : M^T → M^σ` preserves the `J`-limits of `M^T`. -/
theorem cat_preservesLimitsOfShape_e
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesLimitsOfShape J (M.eqnCoarity sg T r).toFunctor) :
    PreservesLimitsOfShape J (M.e sg T).toFunctor := by
  have := M.cat_hasLimitsOfShape_sigObj sg J hlim hfn
  have := M.cat_preservesLimitsOfShape_rhs sg T J hlim hfn heq
  exact inferInstanceAs (PreservesLimitsOfShape J
    (Equif.forget (M.lhsCell sg T).toNatTrans (M.rhsCell sg T).toNatTrans))

/-- The forgetful functor `U : M^T → M₀` preserves the `J`-limits of `M^T`. -/
theorem cat_preservesLimitsOfShape_thyForget
    (hlim : ∀ c : Sg.Cat, HasLimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesLimitsOfShape J (M.funCoarity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesLimitsOfShape J (M.eqnCoarity sg T r).toFunctor) :
    PreservesLimitsOfShape J (M.thyForget sg T).toFunctor := by
  have := M.cat_preservesLimitsOfShape_e sg T J hlim hfn heq
  have := M.cat_preservesLimitsOfShape_u sg J hlim hfn
  exact inferInstanceAs (PreservesLimitsOfShape J
    ((M.e sg T).toFunctor ⋙ (M.u sg).toFunctor))

/-! ## Colimits -/

/-- The product `M₀ = ∏_s M_{c_s}` has all `J`-colimits as soon as each `M_c` does. -/
theorem cat_hasColimitsOfShape_P0
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v))) :
    HasColimitsOfShape J ((M.P0 sg).pt : Type (max u v)) := by
  have := hcol
  exact inferInstanceAs (HasColimitsOfShape J (∀ i : sg.Srt, ((M.obj (sg.sty i)) : Type (max u v))))

/-- If every function arity support preserves `J`-colimits, so does the 1-cell
`(M(t₁))_f : M₀ → ∏_f M_{c_f}` they assemble into. -/
theorem cat_preservesColimitsOfShape_domCell
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor) :
    PreservesColimitsOfShape J (M.domCell sg).toFunctor := by
  have : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.tm sg (sg.fndom f)).toFunctor := hfn
  exact inferInstanceAs (PreservesColimitsOfShape J
    (Functor.pi' (fun f : sg.Fn => (M.tm sg (sg.fndom f)).toFunctor)))

/-- The object of operations `M^σ` has all `J`-colimits which the arity supports
preserve. -/
theorem cat_hasColimitsOfShape_sigObj
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor) :
    HasColimitsOfShape J (M.sigObj sg : Type (max u v)) := by
  have := M.cat_hasColimitsOfShape_P0 sg J hcol
  have := M.cat_preservesColimitsOfShape_domCell sg J hfn
  exact inferInstanceAs (HasColimitsOfShape J
    (Ins (M.domCell sg).toFunctor (M.codCell sg).toFunctor))

/-- The forgetful functor `u : M^σ → M₀` preserves the `J`-colimits which the arity supports
preserve. -/
theorem cat_preservesColimitsOfShape_u
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor) :
    PreservesColimitsOfShape J (M.u sg).toFunctor := by
  have := M.cat_hasColimitsOfShape_P0 sg J hcol
  have := M.cat_preservesColimitsOfShape_domCell sg J hfn
  exact inferInstanceAs (PreservesColimitsOfShape J
    (Ins.forget (M.domCell sg).toFunctor (M.codCell sg).toFunctor))

/-- If every equational arity support preserves `J`-colimits, so does the left-hand 1-cell
of the equifier defining `M^T`. -/
theorem cat_preservesColimitsOfShape_lhs
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesColimitsOfShape J (M.eqnArity sg T r).toFunctor) :
    PreservesColimitsOfShape J
      (((M.Peq sg T).lift (fun r => M.sigTm sg (T.dom r)))).toFunctor := by
  have := M.cat_preservesColimitsOfShape_u sg J hcol hfn
  have : ∀ r : T.Eqn, PreservesColimitsOfShape J (M.sigTm sg (T.dom r)).toFunctor := by
    intro r
    rw [M.sigTm_eq sg (T.dom r)]
    have h2 : PreservesColimitsOfShape J (M.tm sg (T.dom r)).toFunctor := heq r
    exact inferInstanceAs (PreservesColimitsOfShape J
      ((M.u sg).toFunctor ⋙ (M.tm sg (T.dom r)).toFunctor))
  exact inferInstanceAs (PreservesColimitsOfShape J
    (Functor.pi' (fun r : T.Eqn => (M.sigTm sg (T.dom r)).toFunctor)))

/-- **Colimits in `M^T`**: the category of `T`-bialgebras has all `J`-colimits which the
arity supports preserve (cf. Corollary 4.11 of [forsman2026syntactic], in `CAT`). -/
theorem cat_hasColimitsOfShape_thyObj
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesColimitsOfShape J (M.eqnArity sg T r).toFunctor) :
    HasColimitsOfShape J (M.thyObj sg T : Type (max u v)) := by
  have := M.cat_hasColimitsOfShape_sigObj sg J hcol hfn
  have := M.cat_preservesColimitsOfShape_lhs sg T J hcol hfn heq
  have := equifProp_isClosedUnderColimitsOfShape (M.lhsCell sg T).toNatTrans (M.rhsCell sg
      T).toNatTrans J
  exact inferInstanceAs (HasColimitsOfShape J (Equif (M.lhsCell sg T).toNatTrans (M.rhsCell sg
      T).toNatTrans))

/-- The inclusion `e : M^T → M^σ` preserves the `J`-colimits of `M^T`. -/
theorem cat_preservesColimitsOfShape_e
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesColimitsOfShape J (M.eqnArity sg T r).toFunctor) :
    PreservesColimitsOfShape J (M.e sg T).toFunctor := by
  have := M.cat_hasColimitsOfShape_sigObj sg J hcol hfn
  have := M.cat_preservesColimitsOfShape_lhs sg T J hcol hfn heq
  have := equifProp_isClosedUnderColimitsOfShape (M.lhsCell sg T).toNatTrans (M.rhsCell sg
      T).toNatTrans J
  exact inferInstanceAs (PreservesColimitsOfShape J
    (Equif.forget (M.lhsCell sg T).toNatTrans (M.rhsCell sg T).toNatTrans))

/-- The forgetful functor `U : M^T → M₀` preserves the `J`-colimits of `M^T`. -/
theorem cat_preservesColimitsOfShape_thyForget
    (hcol : ∀ c : Sg.Cat, HasColimitsOfShape J (M.obj c : Type (max u v)))
    (hfn : ∀ f : sg.Fn, PreservesColimitsOfShape J (M.funArity sg f).toFunctor)
    (heq : ∀ r : T.Eqn, PreservesColimitsOfShape J (M.eqnArity sg T r).toFunctor) :
    PreservesColimitsOfShape J (M.thyForget sg T).toFunctor := by
  have := M.cat_preservesColimitsOfShape_e sg T J hcol hfn heq
  have := M.cat_preservesColimitsOfShape_u sg J hcol hfn
  exact inferInstanceAs (PreservesColimitsOfShape J
    ((M.e sg T).toFunctor ⋙ (M.u sg).toFunctor))

end Model

end UlmerBialgebras
