module

public import UlmerBialgebras.Paper.AppendixDefsReverse

/-!
# Definitions for Lemma A.3 and Definition A.4

* `DirectedGraph.pathLabel ℓ p`: the label `ℓ(p) = ℓ(p_n) ⊗ ⋯ ⊗ ℓ(p_1)` of a path, in the
  paper's order, with `ℓ(p) = I` for the empty path. It is bracketed as
  `ℓ(p_n) ⊗ (⋯ ⊗ (ℓ(p_1) ⊗ I))`; the trailing unit is a bracketing convention.
* `DirectedGraph.pathLabelCompIso ℓ p q`: the canonical isomorphism `ℓ(q) ⊗ ℓ(p) ≅ ℓ(qp)`
  of Lemma A.3, built from the associators and the left unitor of `V`.
* `linearGraph n`: the graph `0 → 1 → ⋯ → n-1`.
* `linearLabelling n x`: its labelling, where the edge `i → i+1` is labelled `x_i`.

## Main results

* `UlmerBialgebras.Paper.Appendix.DirectedGraph.pathLabel`: the label of a path (Definition A.2).
* `UlmerBialgebras.Paper.Appendix.DirectedGraph.pathLabelCompIso`: the canonical isomorphism
  `ℓ(q) ⊗ ℓ(p) ≅ ℓ(qp)` (Lemma A.3).
* `UlmerBialgebras.Paper.Appendix.linearGraph`, `UlmerBialgebras.Paper.Appendix.linearLabelling`:
  the linear graph `0 → 1 → ⋯ → n-1` and its labelling (Definition A.4).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions A.2, A.4, Lemma A.3
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- The quiver of a directed graph, whose paths are `DirectedGraph.Path`. -/
instance DirectedGraph.quiver (G : DirectedGraph.{u}) : Quiver G.Vertex := ⟨G.Edge⟩

/-- Definition A.2 ([forsman2026syntactic]): the label of a path, `ℓ(p_n) ⊗ ⋯ ⊗ ℓ(p_1)`, bracketed
as `ℓ(p_n) ⊗ (⋯ ⊗ (ℓ(p_1) ⊗ I))`. -/
def DirectedGraph.pathLabel {G : DirectedGraph.{u}} (ℓ : G.Labelling V) {a : G.Vertex} :
    ∀ {b : G.Vertex}, G.Path a b → V
  | _, .nil => 𝟙_ V
  | _, .cons p e => ℓ e ⊗ DirectedGraph.pathLabel ℓ p

/-- Lemma A.3 ([forsman2026syntactic]; free `V`-categories as in Wolff [wolffVcatVgraph1974]): the
canonical isomorphism `ℓ(q) ⊗ ℓ(p) ≅ ℓ(qp)` induced by the monoidal
structure, for paths `p : a → b` and `q : b → c`. The composite path `qp` (first `p`, then `q`)
is `p.comp q`. It is defined by recursion on `q`: for the empty path it is the left unitor
`I ⊗ ℓ(p) ≅ ℓ(p)`, and for `q = q'.cons e` it is the associator
`(ℓ(e) ⊗ ℓ(q')) ⊗ ℓ(p) ≅ ℓ(e) ⊗ (ℓ(q') ⊗ ℓ(p))` followed by `ℓ(e)` tensored with
`ℓ(q') ⊗ ℓ(p) ≅ ℓ(q'p)`. -/
def DirectedGraph.pathLabelCompIso {G : DirectedGraph.{u}} (ℓ : G.Labelling V)
    {a b : G.Vertex} (p : G.Path a b) : ∀ {c : G.Vertex} (q : G.Path b c),
      pathLabel ℓ q ⊗ pathLabel ℓ p ≅ pathLabel ℓ (p.comp q)
  | _, .nil => λ_ (pathLabel ℓ p)
  | _, .cons q e => α_ (ℓ e) (pathLabel ℓ q) (pathLabel ℓ p) ≪≫
      whiskerLeftIso (ℓ e) (pathLabelCompIso ℓ p q)

/-- Definition A.4 ([forsman2026syntactic]): the linear graph `0 → 1 → ⋯ → n-1`. -/
def linearGraph (n : ℕ) : DirectedGraph.{u} where
  Vertex := ULift.{u} (Fin n)
  Edge i j := ULift.{u} (PLift (j.down.val = i.down.val + 1))

/-- Definition A.4 ([forsman2026syntactic]): the edge `i → i+1` is labelled by `x_i`, where
`x : Fin (n - 1) → V`. -/
def linearLabelling (n : ℕ) (x : Fin (n - 1) → V) : (linearGraph.{u} n).Labelling V :=
  fun i j e => x ⟨i.down.val, Nat.lt_sub_of_add_lt (e.down.down ▸ j.down.isLt)⟩

end UlmerBialgebras.Paper.Appendix
