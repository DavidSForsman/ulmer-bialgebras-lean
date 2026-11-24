module

public import UlmerBialgebras.Factorization.RepModel

/-!
# Term supports and representable factorization systems

The results of `RepModel.lean` are stated in terms of the arity and coarity supports `M(t)`
of Definition 3.16.
Its "in particular" clauses replace those hypotheses by hypotheses on the interpretations
`M(B)` of the *functor symbols*.  The bridge is an induction on terms, carried out here:

* `UlmerBialgebras.Model.interp_repPreservesLeft`, `UlmerBialgebras.Model.interp_repPreservesRight`
  — if every functor symbol is interpreted by a 1-cell representably preserving the left (right)
  class componentwise, then so is the interpretation of every term;
* `UlmerBialgebras.Model.tm_repPreservesLeft`, `UlmerBialgebras.Model.tm_repPreservesRight` — the
  same statement for the supports `M(t) : M₀ → M_c`;
* `UlmerBialgebras.Model.repPreservesFiniteLimits_tm_of_isVar` — a term which is a sort is
  interpreted by a product projection, hence representably preserves finite limits.

## Main results

* `UlmerBialgebras.Model.interp_repPreservesLeft`, `UlmerBialgebras.Model.interp_repPreservesRight`:
  if every functor symbol is interpreted by a 1-cell representably preserving the left (right) class
  componentwise, then so is the interpretation of every term.
* `UlmerBialgebras.Model.tm_repPreservesLeft`, `UlmerBialgebras.Model.tm_repPreservesRight`: the
  same for the supports `M(t)` of closed terms (Definition 3.16).
* `UlmerBialgebras.Model.repPreservesFiniteLimits_tm_of_isVar`: the support of a term which is a
  sort representably preserves finite limits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.16, Corollary 4.12, Corollary 6.7
-/

@[expose] public section

universe u v w u₁ u₂ u₃ s₁ s₂ uᵥ

namespace UlmerBialgebras

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
variable {Sg : TwoSig.{u₁, u₂, u₃}}

namespace Model

variable (M : Model Sg Obj) (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)

/-- If every functor symbol is interpreted by a 1-cell representably preserving the left
class componentwise, then so is the interpretation of every term. -/
theorem interp_repPreservesLeft {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (Sx : RepOFS x)
    (S : ∀ c : Sg.Cat, RepOFS (M.obj c)) (rho : ∀ v, x ⟶ M.obj (vty v))
    (hrho : ∀ v, RepPreservesLeft Sx (S (vty v)) (rho v))
    (hB : ∀ B : Sg.Fun, RepPreservesLeft ((M.P B).repOFS fun i => S (Sg.art B i))
      (S (Sg.fcod B)) (M.fn B))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    RepPreservesLeft Sx (S c) (M.interp rho t) := by
  induction t with
  | var v => exact hrho v
  | app B args ih =>
      exact repPreservesLeft_comp
        ((M.P B).repPreservesLeft_lift Sx _ _ (fun i => ih i)) (hB B)

/-- If every functor symbol is interpreted by a 1-cell representably preserving the right
class componentwise, then so is the interpretation of every term. -/
theorem interp_repPreservesRight {V : Type uᵥ} {vty : V → Sg.Cat} {x : Obj} (Sx : RepOFS x)
    (S : ∀ c : Sg.Cat, RepOFS (M.obj c)) (rho : ∀ v, x ⟶ M.obj (vty v))
    (hrho : ∀ v, RepPreservesRight Sx (S (vty v)) (rho v))
    (hB : ∀ B : Sg.Fun, RepPreservesRight ((M.P B).repOFS fun i => S (Sg.art B i))
      (S (Sg.fcod B)) (M.fn B))
    {c : Sg.Cat} (t : Trm Sg.toFunSig vty c) :
    RepPreservesRight Sx (S c) (M.interp rho t) := by
  induction t with
  | var v => exact hrho v
  | app B args ih =>
      exact repPreservesRight_comp
        ((M.P B).repPreservesRight_lift Sx _ _ (fun i => ih i)) (hB B)

variable [HasChosenProductsOfSize.{s₁} Obj]

/-- The support `M(t)` of a closed term representably preserves the left class, as soon as
every functor symbol does componentwise. -/
theorem tm_repPreservesLeft (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hB : ∀ B : Sg.Fun, RepPreservesLeft ((M.P B).repOFS fun i => S (Sg.art B i))
      (S (Sg.fcod B)) (M.fn B))
    {c : Sg.Cat} (t : sg.CTrm c) :
    RepPreservesLeft (M.repOFS0 sg S) (S c) (M.tm sg t) :=
  M.interp_repPreservesLeft _ S _
    (fun s => (M.P0 sg).repPreservesLeft_π (fun s => S (sg.sty s)) s) hB t

/-- The support `M(t)` of a closed term representably preserves the right class, as soon as
every functor symbol does componentwise. -/
theorem tm_repPreservesRight (S : ∀ c : Sg.Cat, RepOFS (M.obj c))
    (hB : ∀ B : Sg.Fun, RepPreservesRight ((M.P B).repOFS fun i => S (Sg.art B i))
      (S (Sg.fcod B)) (M.fn B))
    {c : Sg.Cat} (t : sg.CTrm c) :
    RepPreservesRight (M.repOFS0 sg S) (S c) (M.tm sg t) :=
  M.interp_repPreservesRight _ S _
    (fun s => (M.P0 sg).repPreservesRight_π (fun s => S (sg.sty s)) s) hB t

/-- A term which is a sort is interpreted by a product projection, hence representably
preserves finite limits. -/
theorem repPreservesFiniteLimits_tm_of_isVar
    (hlim : ∀ (x : Obj) (s : sg.Srt), HasFiniteLimits (x ⟶ M.obj (sg.sty s)))
    {c : Sg.Cat} (t : sg.CTrm c) (ht : t.IsVar) : RepPreservesFiniteLimits (M.tm sg t) := by
  cases t with
  | var s => exact (M.P0 sg).repPreservesFiniteLimits_π hlim s
  | app B args => exact ht.elim

end Model

end UlmerBialgebras
