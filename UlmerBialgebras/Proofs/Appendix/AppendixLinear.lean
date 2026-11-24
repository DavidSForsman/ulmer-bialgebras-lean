module

public import UlmerBialgebras.Paper.AppendixDefsForest

/-!
# Definition A.4: linear graphs are forests

The graph `0 → 1 → ⋯ → n-1` underlying the linear `V`-categories of Definition A.4 is a forest,
so Lemma A.3 applies to it.

## Main results

* `UlmerBialgebras.Paper.Appendix.linearGraph_isForest`: the linear graph `0 → 1 → ⋯ → n-1` is a
  forest.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Lemma A.3 and Definition A.4
-/

@[expose] public section

universe u

namespace UlmerBialgebras.Paper.Appendix

/-- In the linear graph `0 → 1 → ⋯ → n-1`, a path from `a` to `b` forces `a ≤ b`. -/
lemma linear_le {n : ℕ} {a : (linearGraph.{u} n).Vertex} :
    ∀ {b : (linearGraph.{u} n).Vertex}, (linearGraph.{u} n).Path a b → a.down.val ≤ b.down.val
  | _, .nil => le_rfl
  | _, .cons p e => by
    have := linear_le p
    have h : _ = _ := e.down.down
    omega

/-- The linear graph `0 → 1 → ⋯ → n-1` underlying the linear categories of Definition A.4 is a
    forest (at most one path between any two vertices), so Lemma A.3 applies to it. -/
theorem linearGraph_isForest (n : ℕ) : (linearGraph.{u} n).IsForest := by
  intro a b
  constructor
  intro p
  induction p with
  | nil =>
    intro q
    cases q with
    | nil => rfl
    | cons q e =>
      have := linear_le q
      have h : _ = _ := e.down.down
      omega
  | @cons c d p e ih =>
    intro q
    cases q with
    | nil =>
      have := linear_le p
      have h : _ = _ := e.down.down
      omega
    | @cons c' _ q e' =>
      have hc : c = c' := by
        have h₁ : _ = _ := e.down.down
        have h₂ : _ = _ := e'.down.down
        exact ULift.ext (Fin.ext (by omega))
      subst hc
      have he : e = e' := by
        rcases e with ⟨⟨_⟩⟩; rcases e' with ⟨⟨_⟩⟩; rfl
      rw [ih q, he]

end Appendix

end Paper

end UlmerBialgebras
