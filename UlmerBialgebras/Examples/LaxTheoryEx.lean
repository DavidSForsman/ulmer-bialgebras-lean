module

public import UlmerBialgebras.Syntax.PathOps

/-!
# Examples 3.20 (4): generalizing lax limits

For an arbitrary 2-signature `Σ = (C, F, T)` we construct the relative 1-signature

`σ_Lax = (s_c : c, f_B : B(s_{c₁}, …, s_{cₙ}) → s_d)_{c ∈ C, B : c₁⋯cₙ → d ∈ F}`

together with, for every closed term `t : c` over the sorts, a canonical path
`f_t : t → s_c` of the term graph `G_{σ_Lax}` (`UlmerBialgebras.LaxEx.termPath`), defined by

* `f_s = ()` for a sort `s`,
* `f_{B(t₁,…,tₙ)} = B(f_{t₁},…,f_{tₙ})` followed by `f_B`,

and the algebraic theory `T_Lax` (`UlmerBialgebras.LaxEx.theory`) whose equations are the parallel
pairs

`α_{s̄} ∘ f_{t₂(s̄)}` versus `f_{t₁(s̄)} : t₁(s̄) → s_c`,

one for each transformation symbol `α : t₁ → t₂` of `Σ`.

The construction of `B(p₁,…,pₙ)` — the functorial image of a family of paths, one in each
argument — is carried out by changing one argument at a time
(`UlmerBialgebras.OneSig.pathApp`), going from the first slot to the last (the paper's convention
goes last slot to first, but both yield the same 2-cell in every model).

`UlmerBialgebras.LaxEx.theory_isAlgebraic` records that `T_Lax` is an algebraic theory, so that
Corollary 3.23 (1) and Corollary 4.11 apply to it.

## Main results

* `UlmerBialgebras.LaxEx.oneSig`: the relative 1-signature `σ_Lax`.
* `UlmerBialgebras.LaxEx.termPath`: the canonical path `f_t : t → s_c` of a closed term `t : c`.
* `UlmerBialgebras.LaxEx.theory`: the theory `T_Lax` of Examples 3.20 (4).
* `UlmerBialgebras.LaxEx.theory_isAlgebraic`: `T_Lax` is an algebraic theory.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Examples 3.20 (4)
* [R. Street, *Limits indexed by category-valued
  2-functors*][streetLimitsIndexedCategoryvalued1976]
* [S. Lack, *A 2-Categories Companion*][lack2CategoriesCompanion2010]
-/

@[expose] public section

namespace UlmerBialgebras

namespace LaxEx

variable (Sg : TwoSig)

/-- **The relative 1-signature `σ_Lax`**: one sort for every category symbol of `Σ` and one
function symbol `f_B : B(s_{c₁},…,s_{cₙ}) → s_d` for every functor symbol of `Σ`. -/
@[reducible] def oneSig : OneSig Sg where
  Srt := Sg.Cat
  sty := id
  Fn := Sg.Fun
  fnty := Sg.fcod
  fndom := fun B => Trm.app B (fun i => Trm.var (Sg.art B i))
  fncod := fun B => Trm.var (Sg.fcod B)

variable {Sg}

/-- **The canonical path `f_t : t → s_c`** attached to a closed term `t : c` over the sorts
of `σ_Lax`. -/
def termPath : ∀ {c : Sg.Cat} (t : (oneSig Sg).CTrm c), (oneSig Sg).Path t (Trm.var c)
  | _, .var _ => .nil _
  | _, .app B ts =>
      OneSig.Path.comp
        (OneSig.pathApp (args := ts) (args' := fun i => Trm.var (Sg.art B i))
          (fun i => termPath (ts i)))
        (.cons (OneSig.Arr.fn (sg := oneSig Sg) B) (.nil _))

variable (Sg)

/-- The substitution of the sorts for the context variables of a transformation symbol. -/
@[reducible] def subS (a : Sg.Tr) : ∀ i : Fin (Sg.trn a), (oneSig Sg).CTrm (Sg.trt a i) :=
  fun i => Trm.var (Sg.trt a i)

/-- **The algebraic theory `T_Lax`** attached to a 2-signature: one equation for every
transformation symbol `α : t₁ → t₂` of `Σ`, expressing that `α_{s̄}` is compatible with the
canonical paths of `t₁(s̄)` and `t₂(s̄)`. -/
def theory : Theory (oneSig Sg) where
  Eqn := Sg.Tr
  eqty := Sg.trty
  dom := fun a => (Sg.trsrc a).subst (subS Sg a)
  cod := fun a => Trm.var (Sg.trty a)
  lhs := fun a =>
    OneSig.Path.comp
      (.cons (OneSig.Arr.tr (sg := oneSig Sg) a (subS Sg a)) (.nil _))
      (termPath ((Sg.trtgt a).subst (subS Sg a)))
  rhs := fun a => termPath ((Sg.trsrc a).subst (subS Sg a))

/-- **`T_Lax` is an algebraic theory**: all coarity terms are sorts. -/
lemma theory_isAlgebraic : (theory Sg).IsAlgebraic :=
  ⟨fun _ => trivial, fun _ => trivial⟩

end LaxEx

end UlmerBialgebras
