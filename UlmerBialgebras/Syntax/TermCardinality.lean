module

public import UlmerBialgebras.Syntax.Syntax
public import Mathlib.Data.W.Cardinal

/-!
# Finite-tree encoding of typed terms

Typed terms embed into finitely branching W-types over their variables and function symbols.
This supplies the syntax-size estimate needed to remove redundant equation-index bounds.

## Main results

* `UlmerBialgebras.Trm.toWType`: the underlying finite tree of a typed term.
* `UlmerBialgebras.Trm.toWType_type_heq`: this encoding retains the typed term.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Corollary 5.8 and Definition 3.3
-/

@[expose] public section

namespace UlmerBialgebras.Trm

universe u v w t

variable {S : FunSig.{u, v}} {V : Type w} {vty : V → S.Cat}

/-- The finite branching sets for variable and function-symbol nodes. -/
def treeArity (S : FunSig.{u, v}) (V : Type w) : V ⊕ S.Fun → Type
  | .inl _ => Empty
  | .inr B => Fin (S.arn B)

/-- Forget the typing of a term while retaining its variable and function-symbol labels. -/
def toWType : ∀ {c : S.Cat}, Trm S vty c → WType (treeArity S V)
  | _, .var v => .mk (.inl v) Empty.elim
  | _, .app B args => .mk (.inr B) (fun i => toWType (args i))

/-- Equal untyped trees determine the type and the typed term. -/
theorem toWType_type_heq {c d : S.Cat} (t : Trm S vty c) (t' : Trm S vty d)
    (h : toWType t = toWType t') : c = d ∧ HEq t t' := by
  induction t generalizing d with
  | var v =>
    cases t' with
    | var v' =>
      have hv : (Sum.inl v : V ⊕ S.Fun) = Sum.inl v' :=
        (WType.mk.inj h).1
      cases Sum.inl.inj hv
      exact ⟨rfl, HEq.rfl⟩
    | app B args =>
      have hv : (Sum.inl v : V ⊕ S.Fun) = Sum.inr B :=
        (WType.mk.inj h).1
      cases hv
  | app B args ih =>
    cases t' with
    | var v =>
      have hv : (Sum.inr B : V ⊕ S.Fun) = Sum.inl v :=
        (WType.mk.inj h).1
      cases hv
    | app B' args' =>
      have hB : (Sum.inr B : V ⊕ S.Fun) = Sum.inr B' :=
        (WType.mk.inj h).1
      cases Sum.inr.inj hB
      have hf := (WType.mk.inj h).2
      have ha : args = args' := funext fun i =>
        eq_of_heq (ih i (args' i) (funext_iff.mp (eq_of_heq hf) i)).2
      cases ha
      exact ⟨rfl, HEq.rfl⟩

/-- The finite-tree encoding is injective on all typed terms, including their result types. -/
theorem sigmaToWType_injective :
    Function.Injective (fun t : (Σ c, Trm S vty c) => toWType t.2) := by
  rintro ⟨c, t⟩ ⟨d, t'⟩ h
  obtain ⟨rfl, h⟩ := toWType_type_heq t t' h
  exact Sigma.ext rfl h

/-- The total set of typed terms has cardinality at most that of its finite trees. -/
theorem cardinalMk_sigma_le_tree :
    Cardinal.mk (Σ c, Trm S vty c) ≤ Cardinal.lift.{u} (Cardinal.mk (WType (treeArity S V))) := by
  have h := Cardinal.lift_mk_le_lift_mk_of_injective
    (sigmaToWType_injective (S := S) (vty := vty))
  rw [Cardinal.lift_id'.{max v w, u}, Cardinal.lift_umax.{max v w, u}] at h
  exact h

/-- The branching sets of typed-term trees are finite. -/
instance treeArity_finite (a : V ⊕ S.Fun) : Finite (treeArity S V a) := by
  cases a <;> dsimp [treeArity] <;> infer_instance

/-- The set of all typed terms is bounded by the variables and function symbols, plus
countably many finite tree shapes. -/
theorem cardinalMk_sigma_le_max :
    Cardinal.mk (Σ c, Trm S vty c) ≤
      max (Cardinal.lift.{u} (Cardinal.mk (V ⊕ S.Fun))) Cardinal.aleph0 := by
  calc
    _ ≤ Cardinal.lift.{u} (Cardinal.mk (WType (treeArity S V))) := cardinalMk_sigma_le_tree
    _ ≤ Cardinal.lift.{u} (max (Cardinal.mk (V ⊕ S.Fun)) Cardinal.aleph0) :=
      Cardinal.lift_le.mpr (by
        simpa only [Cardinal.lift_uzero] using
          (WType.cardinalMk_le_max_aleph0_of_finite' (β := treeArity S V)))
    _ = _ := by rw [Cardinal.lift_max, Cardinal.lift_aleph0]

/-- Infinite bounds on variables and functor symbols bound all typed terms. -/
theorem cardinalMk_sigma_le_of_bounds (κ : Cardinal.{max u v w t})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hV : Cardinal.lift.{max u v t} (Cardinal.mk V) ≤ κ)
    (hF : Cardinal.lift.{max u w t} (Cardinal.mk S.Fun) ≤ κ) :
    Cardinal.lift.{t} (Cardinal.mk (Σ c, Trm S vty c)) ≤ κ := by
  refine (Cardinal.lift_le.mpr (cardinalMk_sigma_le_max (S := S) (vty := vty))).trans ?_
  rw [Cardinal.lift_max, Cardinal.lift_aleph0]
  apply max_le _ hκ
  rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_add, Cardinal.lift_lift,
    Cardinal.lift_lift, Cardinal.lift_lift, Cardinal.lift_lift]
  exact (add_le_add hV hF).trans (Cardinal.add_eq_self hκ).le

end UlmerBialgebras.Trm
