module

public import UlmerBialgebras.Factorization.SubTheory

/-!
# Finite completeness of the hom-categories of `M^σ` and `M^T`

Corollary 6.9 assumes only that the objects `M_c` interpreting the category symbols are
finitely complete (and not, as in Theorem 6.6 (2), that they are regular).  This file records
the consequences of that hypothesis alone:

* `UlmerBialgebras.Product.hasFiniteLimits_hom`, `UlmerBialgebras.Inserter.hasFiniteLimits_hom`,
  `UlmerBialgebras.Equifier.hasFiniteLimits_hom` — the hom-categories of a PIE limit have finite
  limits as soon as the hom-categories of the base do (and, for an inserter, the second
  1-cell representably preserves finite limits);
* `UlmerBialgebras.Inserter.repPreservesFiniteLimits_u'`,
  `UlmerBialgebras.Equifier.repPreservesFiniteLimits_e'` — the canonical 1-cells representably
  preserve finite limits, assuming only finite completeness of the hom-categories;
* for an **algebraic** theory, the coarity supports are product projections, so all the
  above hypotheses are automatic: `UlmerBialgebras.Model.hasFiniteLimits_hom_sigObj` and
  `UlmerBialgebras.Model.hasFiniteLimits_hom_thyObj`.

## Main results

* `UlmerBialgebras.Product.hasFiniteLimits_hom`, `UlmerBialgebras.Inserter.hasFiniteLimits_hom`,
  `UlmerBialgebras.Equifier.hasFiniteLimits_hom`: the hom-categories of a product, an inserter and
  an equifier have finite limits under finite-limit hypotheses on the base.
* `UlmerBialgebras.Model.hasFiniteLimits_hom_sigObj`: if the hom-categories of the `M_c` have finite
  limits and every function coarity term is a sort, the hom-categories of `M^σ` have finite
  limits.
* `UlmerBialgebras.Model.hasFiniteLimits_hom_thyObj`: if the hom-categories of the `M_c` have finite
  limits and `T` is algebraic (Definition 3.7), the hom-categories of `M^T` have finite
  limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 3.7,
  Theorem 6.6, Corollary 6.9
-/

@[expose] public section

universe u v w s u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

/-- Finite completeness transports along an equivalence of categories. -/
theorem hasFiniteLimits_of_equivalence {A : Type*} [Category A] {B : Type*} [Category B]
    (e : A ≌ B) [HasFiniteLimits B] : HasFiniteLimits A :=
  ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

namespace Product

variable {ι : Type s} {c : ι → Obj} (P : Product c)

/-- The hom-categories of a product have finite limits as soon as those of the factors
do. -/
theorem hasFiniteLimits_hom (x : Obj) (hlim : ∀ i, HasFiniteLimits (x ⟶ c i)) :
    HasFiniteLimits (x ⟶ P.pt) := by
  have := hlim
  have : HasFiniteLimits (∀ i, (x ⟶ c i)) := ⟨fun _ _ _ => inferInstance⟩
  exact hasFiniteLimits_of_equivalence (P.homEquiv x)

end Product

namespace Inserter

variable {a b : Obj} {u v : a ⟶ b} (I : Inserter u v)

/-- The hom-categories of an inserter have finite limits as soon as those of the base do and
the second 1-cell preserves them. -/
theorem hasFiniteLimits_hom (x : Obj) (hlim : HasFiniteLimits (x ⟶ a))
    (hv : PreservesFiniteLimits (postcomp x v)) : HasFiniteLimits (x ⟶ I.pt) := by
  have := hlim
  have := hv
  have : HasFiniteLimits (Ins (postcomp x u) (postcomp x v)) := Ins.hasFiniteLimits
  exact hasFiniteLimits_of_equivalence (I.homEquiv x)

/-- The canonical 1-cell out of an inserter representably preserves finite limits; this is
the representable form of `UlmerBialgebras.Inserter.preservesFiniteLimits_postcomp_u`, assuming only
finite completeness of the hom-categories of the base. -/
theorem repPreservesFiniteLimits_u' (hlim : ∀ x : Obj, HasFiniteLimits (x ⟶ a))
    (hv : RepPreservesFiniteLimits v) : RepPreservesFiniteLimits I.u := fun x =>
  ⟨I.preservesFiniteLimits_postcomp_u x (hlim x) (hv x).some⟩

end Inserter

namespace Equifier

variable {a b : Obj} {u v : a ⟶ b} {η θ : u ⟶ v} (E : Equifier η θ)

/-- The hom-categories of an equifier have finite limits as soon as those of the base do and
the second 1-cell preserves them. -/
theorem hasFiniteLimits_hom (x : Obj) (hlim : HasFiniteLimits (x ⟶ a))
    (hv : PreservesFiniteLimits (postcomp x v)) : HasFiniteLimits (x ⟶ E.pt) := by
  have := hlim
  have := hv
  have : HasFiniteLimits (Equif (postcompNat x η) (postcompNat x θ)) := Equif.hasFiniteLimits
  exact hasFiniteLimits_of_equivalence (E.homEquiv x)

/-- The canonical 1-cell out of an equifier representably preserves finite limits; this is
the representable form of `UlmerBialgebras.Equifier.preservesFiniteLimits_postcomp_e`, assuming only
finite completeness of the hom-categories of the base. -/
theorem repPreservesFiniteLimits_e' (hlim : ∀ x : Obj, HasFiniteLimits (x ⟶ a))
    (hv : RepPreservesFiniteLimits v) : RepPreservesFiniteLimits E.e := fun x =>
  ⟨E.preservesFiniteLimits_postcomp_e x (hlim x) (hv x).some⟩

end Equifier

variable [HasChosenFinProducts.{u, v, w} Obj] {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

section FiniteLimits

variable (hlim : ∀ (x : Obj) (c : Sg.Cat), HasFiniteLimits (x ⟶ M.obj c))

include hlim

variable [HasChosenProductsOfSize.{s₁, u, v, w} Obj]

/-- The hom-categories of `M₀` have finite limits. -/
theorem hasFiniteLimits_hom_P0 (x : Obj) : HasFiniteLimits (x ⟶ (M.P0 sg).pt) :=
  (M.P0 sg).hasFiniteLimits_hom x fun s => hlim x (sg.sty s)

/-- For an algebraic theory the coarity support of a function symbol is a product
projection, hence representably preserves finite limits. -/
theorem repPreservesFiniteLimits_funCoarity (hfn : ∀ f : sg.Fn, (sg.fncod f).IsVar)
    (f : sg.Fn) : RepPreservesFiniteLimits (M.funCoarity sg f) :=
  M.repPreservesFiniteLimits_tm_of_isVar sg (fun x s => hlim x (sg.sty s)) _ (hfn f)

variable [HasChosenProductsOfSize.{s₂, u, v, w} Obj]

/-- For an algebraic theory the coarity supports assemble into a 1-cell representably
preserving finite limits. -/
theorem repPreservesFiniteLimits_codCell (hfn : ∀ f : sg.Fn, (sg.fncod f).IsVar) :
    RepPreservesFiniteLimits (M.codCell sg) :=
  M.codCell_repPreservesFiniteLimits sg (M.repPreservesFiniteLimits_funCoarity sg hlim hfn)

variable [HasChosenInserters.{u, v, w} Obj]

/-- The hom-categories of the object of operations `M^σ` have finite limits, for an
algebraic signature. -/
theorem hasFiniteLimits_hom_sigObj (hfn : ∀ f : sg.Fn, (sg.fncod f).IsVar) (x : Obj) :
    HasFiniteLimits (x ⟶ M.sigObj sg) :=
  (M.sigIns sg).hasFiniteLimits_hom x (M.hasFiniteLimits_hom_P0 sg hlim x)
    ((M.repPreservesFiniteLimits_codCell sg hlim hfn x).some)

/-- The forgetful 1-cell `u : M^σ → M₀` representably preserves finite limits, for an
algebraic signature. -/
theorem repPreservesFiniteLimits_u' (hfn : ∀ f : sg.Fn, (sg.fncod f).IsVar) :
    RepPreservesFiniteLimits (M.u sg) :=
  (M.sigIns sg).repPreservesFiniteLimits_u' (M.hasFiniteLimits_hom_P0 sg hlim)
    (M.repPreservesFiniteLimits_codCell sg hlim hfn)

variable (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

omit [HasChosenProductsOfSize.{s₂, u, v, w} Obj] [HasChosenInserters.{u, v, w} Obj]
  [HasChosenProductsOfSize.{s₃, u, v, w} Obj] in
/-- For an algebraic theory the equational coarity supports representably preserve finite
limits. -/
theorem repPreservesFiniteLimits_eqnCoarity (heq : ∀ r : T.Eqn, (T.cod r).IsVar)
    (r : T.Eqn) : RepPreservesFiniteLimits (M.eqnCoarity sg T r) :=
  M.repPreservesFiniteLimits_tm_of_isVar sg (fun x s => hlim x (sg.sty s)) _ (heq r)

/-- The right-hand 1-cell defining `M^T` representably preserves finite limits, for an
algebraic theory. -/
theorem rhs_repPreservesFiniteLimits' (halg : T.IsAlgebraic) :
    RepPreservesFiniteLimits ((M.Peq sg T).lift fun r => M.sigTm sg (T.cod r)) := by
  refine (M.Peq sg T).repPreservesFiniteLimits_lift _ (fun r => ?_)
  show RepPreservesFiniteLimits (M.sigTm sg (T.cod r))
  rw [M.sigTm_eq]
  exact repPreservesFiniteLimits_comp (M.repPreservesFiniteLimits_u' sg hlim halg.1)
    (M.repPreservesFiniteLimits_eqnCoarity sg hlim T halg.2 r)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- The hom-categories of the object of `T`-bialgebras have finite limits, for an algebraic
theory `T` interpreted in finitely complete objects. -/
theorem hasFiniteLimits_hom_thyObj (halg : T.IsAlgebraic) (x : Obj) :
    HasFiniteLimits (x ⟶ M.thyObj sg T) :=
  (M.thyEquif sg T).hasFiniteLimits_hom x (M.hasFiniteLimits_hom_sigObj sg hlim halg.1 x)
    ((M.rhs_repPreservesFiniteLimits' sg hlim T halg x).some)

/-- The forgetful 1-cell `e : M^T → M^σ` representably preserves finite limits, for an
algebraic theory. -/
theorem repPreservesFiniteLimits_e' (halg : T.IsAlgebraic) :
    RepPreservesFiniteLimits (M.e sg T) :=
  (M.thyEquif sg T).repPreservesFiniteLimits_e'
    (M.hasFiniteLimits_hom_sigObj sg hlim halg.1)
    (M.rhs_repPreservesFiniteLimits' sg hlim T halg)

end FiniteLimits

end Model

end UlmerBialgebras
