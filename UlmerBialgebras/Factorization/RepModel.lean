module

public import UlmerBialgebras.Factorization.RepGlue
public import UlmerBialgebras.Kan.KanModel

/-!
# Representable lifting of factorization systems, regularity and exactness to `M^T`

Let `(Σ, σ)` be a signature pair with a `σ`-theory `T`, and let `M` be a `Σ`-model in a
PIE-complete 2-category `K`.  This file lifts orthogonal factorization systems, regularity
and exactness from the objects `M_c` interpreting the category symbols to the object `M^T`
of `T`-bialgebras, along the forgetful 1-cell `u : M^T → M₀`:

* `UlmerBialgebras.Model.thyRepOFS` — representable form of Theorem 6.6 (1): the representable
  orthogonal factorization system on `M^T` induced by those of the `M_c`;
* `UlmerBialgebras.Model.codCell_repPreservesFiniteLimits` — a first step towards the representable
  form of Theorem 6.6 (2).

Uniqueness (Corollary 6.7) and the representable forms of Theorem 6.6 (2) and (3)
(regularity and exactness) are not formalized in this file.

These representable versions are not numbered results of the current version of the
paper.  The hypotheses concern the *arity supports* `M(t₁)` (`UlmerBialgebras.Model.funArity`,
`UlmerBialgebras.Model.eqnArity`) and the *coarity supports* `M(t₂)`
(`UlmerBialgebras.Model.funCoarity`, `UlmerBialgebras.Model.eqnCoarity`) of Definition 3.16.

## Main results

* `UlmerBialgebras.Model.thyRepOFS`: the representable orthogonal factorization system on `M^T`
  induced by those of the `M_c`, under preservation hypotheses on the arity and coarity supports
  (representable form of Theorem 6.6 (1)).
* `UlmerBialgebras.Model.codCell_repPreservesFiniteLimits`: the 1-cell of coarities representably
  preserves finite limits when each coarity support does.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.16, Theorem 6.6, Corollary 6.7
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
  (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
variable [HasChosenProductsOfSize.{s₁} Obj] [HasChosenProductsOfSize.{s₂} Obj]

/-! ## Factorization systems (representable form of Theorem 6.6 (1)) -/

section OFS

/-- The representable orthogonal factorization system on `M₀ = ∏_s M_{c_s}`. -/
noncomputable def repOFS0 (S : ∀ c : Sg.Cat, RepOFS (M.obj c)) : RepOFS (M.P0 sg).pt :=
  (M.P0 sg).repOFS fun s => S (sg.sty s)

/-- The representable orthogonal factorization system on `∏_f M_{c_f}`. -/
noncomputable def repOFSfn (S : ∀ c : Sg.Cat, RepOFS (M.obj c)) : RepOFS (M.Pfn sg).pt :=
  (M.Pfn sg).repOFS fun f => S (sg.fnty f)

/-- The representable orthogonal factorization system on `∏_r M_{c_r}`. -/
noncomputable def repOFSeq [HasChosenProductsOfSize.{s₃} Obj] (S : ∀ c : Sg.Cat, RepOFS (M.obj c)) :
    RepOFS (M.Peq sg T).pt :=
  (M.Peq sg T).repOFS fun r => S (T.eqty r)

/-- The arities of the function symbols representably preserve the left class. -/
theorem domCell_repPreservesLeft (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f)) :
    RepPreservesLeft (M.repOFS0 sg S) (M.repOFSfn sg S) (M.domCell sg) :=
  (M.Pfn sg).repPreservesLeft_lift _ _ _ hfnE

/-- The coarities of the function symbols representably preserve the right class. -/
theorem codCell_repPreservesRight (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f)) :
    RepPreservesRight (M.repOFS0 sg S) (M.repOFSfn sg S) (M.codCell sg) :=
  (M.Pfn sg).repPreservesRight_lift _ _ _ hfnM

variable [HasChosenInserters.{u, v, w} Obj]

/-- The representable orthogonal factorization system on the object `M^σ` of operations. -/
noncomputable def sigRepOFS (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f)) :
    RepOFS (M.sigObj sg) :=
  (M.sigIns sg).repOFS (M.repOFS0 sg S) (M.repOFSfn sg S)
    (M.domCell_repPreservesLeft sg S hfnE) (M.codCell_repPreservesRight sg S hfnM)

/-- The canonical 1-cell `u_M : M^σ → M₀` representably preserves the left class, from
`sigRepOFS` to `repOFS0`. -/
theorem u_repPreservesLeft (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f)) :
    RepPreservesLeft (M.sigRepOFS sg S hfnE hfnM) (M.repOFS0 sg S) (M.u sg) :=
  (M.sigIns sg).repPreservesLeft_u _ _ _ _

/-- The canonical 1-cell `u_M : M^σ → M₀` representably preserves the right class, from
`sigRepOFS` to `repOFS0`. -/
theorem u_repPreservesRight (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f)) :
    RepPreservesRight (M.sigRepOFS sg S hfnE hfnM) (M.repOFS0 sg S) (M.u sg) :=
  (M.sigIns sg).repPreservesRight_u _ _ _ _

variable [HasChosenProductsOfSize.{s₃} Obj]

/-- The equational arities representably preserve the left class, as 1-cells out of `M^σ`. -/
theorem lhs_repPreservesLeft (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f))
    (heqE : ∀ r : T.Eqn, RepPreservesLeft (M.repOFS0 sg S) (S (T.eqty r))
      (M.eqnArity sg T r)) :
    RepPreservesLeft (M.sigRepOFS sg S hfnE hfnM) (M.repOFSeq sg T S)
      ((M.Peq sg T).lift fun r => M.sigTm sg (T.dom r)) := by
  refine (M.Peq sg T).repPreservesLeft_lift _ _ _ (fun r => ?_)
  rw [M.sigTm_eq]
  exact repPreservesLeft_comp (M.u_repPreservesLeft sg S hfnE hfnM) (heqE r)

/-- The equational coarities representably preserve the right class, as 1-cells out of
`M^σ`. -/
theorem rhs_repPreservesRight (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f))
    (heqM : ∀ r : T.Eqn, RepPreservesRight (M.repOFS0 sg S) (S (T.eqty r))
      (M.eqnCoarity sg T r)) :
    RepPreservesRight (M.sigRepOFS sg S hfnE hfnM) (M.repOFSeq sg T S)
      ((M.Peq sg T).lift fun r => M.sigTm sg (T.cod r)) := by
  refine (M.Peq sg T).repPreservesRight_lift _ _ _ (fun r => ?_)
  rw [M.sigTm_eq]
  exact repPreservesRight_comp (M.u_repPreservesRight sg S hfnE hfnM) (heqM r)

variable [HasChosenEquifiers.{u, v, w} Obj]

/-- **Theorem 6.6 (1), representable form**: the representable orthogonal factorization system
on the object `M^T` of `T`-bialgebras. -/
noncomputable def thyRepOFS (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg S) (S (sg.fnty f)) (M.funArity sg f))
    (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg S) (S (sg.fnty f))
      (M.funCoarity sg f))
    (heqE : ∀ r : T.Eqn, RepPreservesLeft (M.repOFS0 sg S) (S (T.eqty r)) (M.eqnArity sg T r))
    (heqM : ∀ r : T.Eqn, RepPreservesRight (M.repOFS0 sg S) (S (T.eqty r))
      (M.eqnCoarity sg T r)) :
    RepOFS (M.thyObj sg T) :=
  (M.thyEquif sg T).repOFS (M.sigRepOFS sg S hfnE hfnM) (M.repOFSeq sg T S)
    (M.lhs_repPreservesLeft sg T S hfnE hfnM heqE)
    (M.rhs_repPreservesRight sg T S hfnE hfnM heqM)

end OFS

/-! ## Regularity (representable form of Theorem 6.6 (2)) -/

section Regular

/-- The 1-cell of coarities `codCell : M₀ ⟶ ∏_f M_{c_f}` representably preserves finite
limits when each coarity 1-cell `funCoarity sg f` does. -/
theorem codCell_repPreservesFiniteLimits
    (hfnM : ∀ f : sg.Fn, RepPreservesFiniteLimits (M.funCoarity sg f)) :
    RepPreservesFiniteLimits (M.codCell sg) :=
  (M.Pfn sg).repPreservesFiniteLimits_lift _ hfnM

end Regular

/-! ## Exactness (representable form of Theorem 6.6 (3)) -/

section Exact

end Exact

end Model

end UlmerBialgebras
