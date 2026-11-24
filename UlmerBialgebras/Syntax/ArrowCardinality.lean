module

public import UlmerBialgebras.Syntax.TermCardinality
public import Foundations.SetTheory.Cardinal.SumBound

/-!
# Finite-tree encoding of arrows in the term graph

An arrow consists of a generating function or a substituted transformation, surrounded by
finitely many functor-slot contexts. The context labels retain their typed arguments.

## Main results

* `UlmerBialgebras.OneSig.Arr.toWType`: the unary-tree encoding of term-graph arrows.
* `UlmerBialgebras.OneSig.Arr.toWType_type_heq`: the encoding retains endpoints and arrows.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.6 and Corollary 5.8
-/

@[expose] public section

namespace UlmerBialgebras.OneSig.Arr

universe u₁ u₂ u₃ s₁ s₂ t
variable {Sg : TwoSig.{u₁, u₂, u₃}} {sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg}

/-- A finite family of typed terms embeds into a tuple of the total set of terms. -/
theorem cardinalMk_args_le_pow (n : ℕ) (ty : Fin n → Sg.Cat) :
    Cardinal.mk (∀ i : Fin n, sg.CTrm (ty i)) ≤
      Cardinal.mk (Σ c, sg.CTrm c) ^ (n : Cardinal) := by
  let f : (∀ i : Fin n, sg.CTrm (ty i)) → (Fin n → Σ c, sg.CTrm c) :=
    fun a i => ⟨ty i, a i⟩
  have hf : Function.Injective f := by
    intro a b h
    funext i
    exact eq_of_heq (Sigma.mk.inj_iff.mp (funext_iff.mp h i)).2
  calc
    _ ≤ Cardinal.mk (Fin n → Σ c, sg.CTrm c) := Cardinal.mk_le_of_injective hf
    _ = _ := by simp

/-- A generating arrow, retaining the substitution at a transformation symbol. -/
abbrev Atom (sg : OneSig Sg) :=
  sg.Fn ⊕ (Σ a : Sg.Tr, ∀ i : Fin (Sg.trn a), sg.CTrm (Sg.trt a i))

/-- A functor-slot context with its two argument families. -/
abbrev Frame (sg : OneSig Sg) :=
  Σ B : Sg.Fun, Fin (Sg.arn B) ×
    ((∀ i : Fin (Sg.arn B), sg.CTrm (Sg.art B i)) ×
      (∀ i : Fin (Sg.arn B), sg.CTrm (Sg.art B i)))

/-- Generating-arrow labels are bounded by function symbols and finite tuples of terms
substituted into transformation symbols. -/
theorem cardinalMk_atom_le :
    Cardinal.mk (Atom sg) ≤
      Cardinal.lift.{max u₁ u₂ u₃ s₁} (Cardinal.mk sg.Fn) +
        Cardinal.lift.{s₂} (Cardinal.sum (fun a : Sg.Tr =>
          Cardinal.mk (Σ c, sg.CTrm c) ^ (Sg.trn a : Cardinal))) := by
  rw [Atom, Cardinal.mk_sum]
  apply add_le_add le_rfl
  rw [Cardinal.lift_le, Cardinal.mk_sigma]
  exact Cardinal.sum_le_sum _ _ fun a => cardinalMk_args_le_pow (Sg.trn a) (Sg.trt a)

/-- Context labels are bounded by a slot and two finite tuples of typed terms. -/
theorem cardinalMk_frame_le :
    Cardinal.mk (Frame sg) ≤ Cardinal.sum (fun B : Sg.Fun =>
      (Sg.arn B : Cardinal) *
        (Cardinal.mk (Σ c, sg.CTrm c) ^ (Sg.arn B : Cardinal) *
          Cardinal.mk (Σ c, sg.CTrm c) ^ (Sg.arn B : Cardinal))) := by
  rw [Frame, Cardinal.mk_sigma]
  apply Cardinal.sum_le_sum
  intro B
  rw [Cardinal.mk_prod, Cardinal.mk_prod]
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero, Cardinal.lift_id]
  exact mul_le_mul' le_rfl (mul_le_mul'
    (cardinalMk_args_le_pow (Sg.arn B) (Sg.art B))
    (cardinalMk_args_le_pow (Sg.arn B) (Sg.art B)))

/-- An infinite bound on functor symbols and typed terms also bounds all context labels. -/
theorem cardinalMk_frame_le_of_bounds (κ : Cardinal.{max u₁ u₂ u₃ s₁ s₂ t})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hF : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk Sg.Fun) ≤ κ)
    (hT : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Σ c, sg.CTrm c)) ≤ κ) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Frame sg)) ≤ κ := by
  refine (Cardinal.lift_le.mpr (cardinalMk_frame_le (sg := sg))).trans ?_
  rw [Cardinal.lift_sum]
  calc
    _ ≤ Cardinal.sum (fun _ : Sg.Fun => κ) := by
      apply Cardinal.sum_le_sum
      intro B
      simp only [Cardinal.lift_mul, Cardinal.lift_power, Cardinal.lift_natCast]
      have hp : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Σ c, sg.CTrm c)) ^
          (Sg.arn B : Cardinal) ≤ κ :=
        (Cardinal.power_le_power_right hT).trans
          (Cardinal.pow_le hκ Cardinal.natCast_lt_aleph0)
      have hpp := (mul_le_mul' hp hp).trans (Cardinal.mul_eq_self hκ).le
      exact (mul_le_mul' (Cardinal.natCast_le_aleph0.trans hκ) hpp).trans
        (Cardinal.mul_eq_self hκ).le
    _ ≤ κ := by
      rw [Cardinal.sum_const, Cardinal.lift_id'.{u₂, max u₁ u₂ u₃ s₁ s₂ t}]
      exact (mul_le_mul' hF le_rfl).trans (Cardinal.mul_eq_self hκ).le

/-- An infinite bound on the generating symbols and typed terms bounds generating-arrow labels. -/
theorem cardinalMk_atom_le_of_bounds (κ : Cardinal.{max u₁ u₂ u₃ s₁ s₂ t})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hFn : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk sg.Fn) ≤ κ)
    (hTr : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk Sg.Tr) ≤ κ)
    (hT : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Σ c, sg.CTrm c)) ≤ κ) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Atom sg)) ≤ κ := by
  refine (Cardinal.lift_le.mpr (cardinalMk_atom_le (sg := sg))).trans ?_
  rw [Cardinal.lift_add, Cardinal.lift_lift, Cardinal.lift_lift]
  have hs : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.sum (fun a : Sg.Tr =>
      Cardinal.mk (Σ c, sg.CTrm c) ^ (Sg.trn a : Cardinal))) ≤ κ := by
    apply Cardinal.lift_sum_le_of_bounds.{u₃, max u₁ u₂ s₁, max u₁ u₂ u₃ s₁ s₂ t} _ κ hκ hTr
    intro a
    rw [Cardinal.lift_power, Cardinal.lift_natCast]
    exact (Cardinal.power_le_power_right hT).trans
      (Cardinal.pow_le hκ Cardinal.natCast_lt_aleph0)
  exact (add_le_add hFn hs).trans (Cardinal.add_eq_self hκ).le

/-- Generating arrows have no children; functor-slot contexts have one child. -/
def treeArity (sg : OneSig Sg) : Atom sg ⊕ Frame sg → Type
  | .inl _ => Empty
  | .inr _ => Unit

/-- Encode an arrow as a finite unary tree of contexts around a generating arrow. -/
def toWType : ∀ {c : Sg.Cat} {x y : sg.CTrm c},
    sg.Arr x y → WType (treeArity sg)
  | _, _, _, .fn f => .mk (.inl (.inl f)) Empty.elim
  | _, _, _, .tr a sub => .mk (.inl (.inr ⟨a, sub⟩)) Empty.elim
  | _, _, _, .app B i args args' _ g =>
      .mk (.inr ⟨B, i, args, args'⟩) (fun _ => toWType g)

/-- Equal arrow trees retain their types, endpoints, and underlying arrows. -/
theorem toWType_type_heq {c d : Sg.Cat} {x y : sg.CTrm c} {x' y' : sg.CTrm d}
    (g : sg.Arr x y) (g' : sg.Arr x' y') (h : toWType g = toWType g') :
    c = d ∧ HEq x x' ∧ HEq y y' ∧ HEq g g' := by
  -- Induction on the first tree. The root labels of the two trees agree (`WType.mk.inj`):
  -- different constructors give different labels, and equal labels fix the type and the
  -- endpoints; a continuation, where there is one, agrees by the induction hypothesis.
  induction g generalizing d with
  | fn f =>
    cases g' with
    | fn f' =>
      have hl := (WType.mk.inj h).1
      simp only [Sum.inl.injEq] at hl
      cases hl
      exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    | tr a sub =>
      have hl := (WType.mk.inj h).1
      simp at hl
    | app B i args args' hn g =>
      have hl := (WType.mk.inj h).1
      simp at hl
  | tr a sub =>
    cases g' with
    | fn f =>
      have hl := (WType.mk.inj h).1
      simp at hl
    | tr a' sub' =>
      have hl := (WType.mk.inj h).1
      simp only [Sum.inl.injEq, Sum.inr.injEq] at hl
      obtain ⟨rfl, hs⟩ := Sigma.mk.inj_iff.mp hl
      cases eq_of_heq hs
      exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    | app B i args args' hn g =>
      have hl := (WType.mk.inj h).1
      simp at hl
  | app B i args args' hn g ih =>
    cases g' with
    | fn f =>
      have hl := (WType.mk.inj h).1
      simp at hl
    | tr a sub =>
      have hl := (WType.mk.inj h).1
      simp at hl
    | app B' i' as bs hn' g' =>
      have hl := (WType.mk.inj h).1
      simp only [Sum.inr.injEq] at hl
      obtain ⟨rfl, hs⟩ := Sigma.mk.inj_iff.mp hl
      obtain ⟨rfl, hp⟩ := Prod.mk.inj (eq_of_heq hs)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
      have hc := (WType.mk.inj h).2
      have hg := (ih g' (funext_iff.mp (eq_of_heq hc) ())).2.2.2
      cases eq_of_heq hg
      exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- All arrows of the term graph, retaining their types and endpoints. -/
abbrev Total (sg : OneSig Sg) := Σ c : Sg.Cat, Σ x y : sg.CTrm c, sg.Arr x y

/-- Encoding all typed arrows into their trees is injective. -/
theorem sigmaToWType_injective :
    Function.Injective (fun g : Total sg => toWType g.2.2.2) := by
  rintro ⟨c, x, y, g⟩ ⟨d, x', y', g'⟩ h
  obtain ⟨rfl, hx, hy, hg⟩ := toWType_type_heq g g' h
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hg
  rfl

/-- The branching sets of arrow trees are finite. -/
instance treeArity_finite (a : Atom sg ⊕ Frame sg) : Finite (treeArity sg a) := by
  cases a <;> dsimp [treeArity] <;> infer_instance

/-- Term-graph arrows are bounded by their generating and context labels, plus ℵ₀. -/
theorem cardinalMk_total_le_max :
    Cardinal.mk (Total sg) ≤ max (Cardinal.mk (Atom sg ⊕ Frame sg)) Cardinal.aleph0 := by
  calc
    _ ≤ Cardinal.mk (WType (treeArity sg)) :=
      Cardinal.mk_le_of_injective sigmaToWType_injective
    _ ≤ _ := by
      simpa only [Cardinal.lift_uzero] using
        (WType.cardinalMk_le_max_aleph0_of_finite' (β := treeArity sg))

/-- Infinite bounds on function symbols, transformations, functors and terms bound all arrows. -/
theorem cardinalMk_total_le_of_bounds (κ : Cardinal.{max u₁ u₂ u₃ s₁ s₂ t})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hFn : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk sg.Fn) ≤ κ)
    (hTr : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk Sg.Tr) ≤ κ)
    (hF : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk Sg.Fun) ≤ κ)
    (hT : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Σ c, sg.CTrm c)) ≤ κ) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Total sg)) ≤ κ := by
  refine (Cardinal.lift_le.mpr (cardinalMk_total_le_max (sg := sg))).trans ?_
  rw [Cardinal.lift_max, Cardinal.lift_aleph0]
  apply max_le _ hκ
  rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift, Cardinal.lift_lift]
  exact (add_le_add
    (cardinalMk_atom_le_of_bounds.{u₁, u₂, u₃, s₁, s₂, t} κ hκ hFn hTr hT)
    (cardinalMk_frame_le_of_bounds.{u₁, u₂, u₃, s₁, s₂, t} κ hκ hF hT)).trans
      (Cardinal.add_eq_self hκ).le

end UlmerBialgebras.OneSig.Arr
