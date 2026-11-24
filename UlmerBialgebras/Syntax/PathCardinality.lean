module

public import UlmerBialgebras.Syntax.ArrowCardinality

/-!
# Finite-tree encoding of paths in the term graph

A path is a finite sequence of typed arrows ending in a specified identity path.
The unary-tree encoding retains all endpoints, including the endpoint of an empty path.

## Main results

* `UlmerBialgebras.OneSig.Path.toWType`: the tree encoding of term-graph paths.
* `UlmerBialgebras.OneSig.Path.toWType_type_heq`: the encoding retains paths and endpoints.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.6 and Corollary 5.8
-/

@[expose] public section

namespace UlmerBialgebras.OneSig.Path

universe u₁ u₂ u₃ s₁ s₂ t
variable {Sg : TwoSig.{u₁, u₂, u₃}} {sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg}

/-- Identity-path labels have no children; arrow labels have one continuation. -/
def treeArity (sg : OneSig Sg) : (Σ c, sg.CTrm c) ⊕ Arr.Total sg → Type
  | .inl _ => Empty
  | .inr _ => Unit

/-- Encode a path as a unary tree, including its final identity path. -/
def toWType : ∀ {c : Sg.Cat} {x y : sg.CTrm c},
    sg.Path x y → WType (treeArity sg)
  | c, _, _, .nil t => .mk (.inl ⟨c, t⟩) Empty.elim
  | c, x, _, .cons (t' := t) g p => .mk (.inr ⟨c, x, t, g⟩) (fun _ => toWType p)

/-- Encoding an identity path records its type and its term. -/
lemma toWType_nil {c : Sg.Cat} (t : sg.CTrm c) :
    toWType (.nil t) = WType.mk (.inl ⟨c, t⟩) Empty.elim := by rw [toWType]

/-- Encoding a nonempty path exposes its first arrow and its continuation. -/
lemma toWType_cons {c : Sg.Cat} {x y z : sg.CTrm c}
    (g : sg.Arr x y) (p : sg.Path y z) :
    toWType (.cons g p) = WType.mk (.inr ⟨c, x, y, g⟩) (fun _ => toWType p) := by rw [toWType]

/-- Equal path trees determine types, endpoints, and paths. -/
theorem toWType_type_heq {c d : Sg.Cat} {x y : sg.CTrm c} {x' y' : sg.CTrm d}
    (p : sg.Path x y) (p' : sg.Path x' y') (h : toWType p = toWType p') :
    c = d ∧ HEq x x' ∧ HEq y y' ∧ HEq p p' := by
  -- Induction on the first tree. The root labels of the two trees agree (`WType.mk.inj`):
  -- different constructors give different labels, and equal labels fix the type and the
  -- endpoints; a continuation, where there is one, agrees by the induction hypothesis.
  induction p generalizing d with
  | nil t =>
    cases p' with
    | nil t' =>
      simp only [toWType_nil] at h
      have hl := (WType.mk.inj h).1
      simp only [Sum.inl.injEq] at hl
      obtain ⟨rfl, ht⟩ := Sigma.mk.inj_iff.mp hl
      cases eq_of_heq ht
      exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
    | cons g p =>
      simp only [toWType_nil, toWType_cons] at h
      have hl := (WType.mk.inj h).1
      simp at hl
  | cons g p ih =>
    cases p' with
    | nil t' =>
      simp only [toWType_nil, toWType_cons] at h
      have hl := (WType.mk.inj h).1
      simp at hl
    | cons g' p' =>
      simp only [toWType_cons] at h
      have hl := (WType.mk.inj h).1
      simp only [Sum.inr.injEq] at hl
      obtain ⟨rfl, ht⟩ := Sigma.mk.inj_iff.mp hl
      obtain ⟨rfl, ht⟩ := Sigma.mk.inj_iff.mp (eq_of_heq ht)
      obtain ⟨rfl, hg⟩ := Sigma.mk.inj_iff.mp (eq_of_heq ht)
      cases eq_of_heq hg
      have hc := (WType.mk.inj h).2
      obtain ⟨_, _, hy, hp⟩ := ih p' (funext_iff.mp (eq_of_heq hc) ())
      cases eq_of_heq hy
      cases eq_of_heq hp
      exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- All paths, retaining their result types and endpoints. -/
abbrev Total (sg : OneSig Sg) := Σ c : Sg.Cat, Σ x y : sg.CTrm c, sg.Path x y

/-- Encoding the total set of typed paths into trees is injective. -/
theorem sigmaToWType_injective :
    Function.Injective (fun p : Total sg => toWType p.2.2.2) := by
  rintro ⟨c, x, y, p⟩ ⟨d, x', y', p'⟩ h
  obtain ⟨rfl, hx, hy, hp⟩ := toWType_type_heq p p' h
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hp
  rfl

/-- The branching sets of path trees are finite. -/
instance treeArity_finite (a : (Σ c, sg.CTrm c) ⊕ Arr.Total sg) :
    Finite (treeArity sg a) := by
  cases a <;> dsimp [treeArity] <;> infer_instance

/-- The cardinal of all paths is bounded by typed terms and typed arrows, together with ℵ₀. -/
theorem cardinalMk_total_le_max :
    Cardinal.mk (Total sg) ≤
      max (Cardinal.mk ((Σ c, sg.CTrm c) ⊕ Arr.Total sg)) Cardinal.aleph0 := by
  calc
    _ ≤ Cardinal.mk (WType (treeArity sg)) :=
      Cardinal.mk_le_of_injective sigmaToWType_injective
    _ ≤ _ := by
      simpa only [Cardinal.lift_uzero] using
        (WType.cardinalMk_le_max_aleph0_of_finite' (β := treeArity sg))

/-- An infinite bound on typed terms and arrows bounds all paths. -/
theorem cardinalMk_total_le_of_bounds (κ : Cardinal.{max u₁ u₂ u₃ s₁ s₂ t})
    (hκ : Cardinal.aleph0 ≤ κ)
    (hT : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Σ c, sg.CTrm c)) ≤ κ)
    (hA : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Arr.Total sg)) ≤ κ) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ t} (Cardinal.mk (Total sg)) ≤ κ := by
  refine (Cardinal.lift_le.mpr (cardinalMk_total_le_max (sg := sg))).trans ?_
  rw [Cardinal.lift_max, Cardinal.lift_aleph0]
  apply max_le _ hκ
  rw [Cardinal.mk_sum, Cardinal.lift_add, Cardinal.lift_lift, Cardinal.lift_lift]
  exact (add_le_add hT hA).trans (Cardinal.add_eq_self hκ).le

end UlmerBialgebras.OneSig.Path
