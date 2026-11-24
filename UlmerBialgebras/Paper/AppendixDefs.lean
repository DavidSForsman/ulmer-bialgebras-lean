module

public import UlmerBialgebras.Paper.Sec3Defs
public import UlmerBialgebras.Paper.Sec4Defs
public import UlmerBialgebras.Paper.Sec7Defs
public import UlmerBialgebras.Appendix.VCatTinyDense

/-!
# Definitions for the appendix

Graphs are encoded by their fibres of edges. This is equivalent to a set
of edges with source and target maps. Forest means at most one directed
path between any two vertices, including the empty paths.

The existing enriched-category library composes in the order
`Hom(a,b) ⊗ Hom(b,c)`. The paper writes the factors in the opposite
order. The point and arrow probes below do not involve two nonidentity
factors; the general forest and three-object constructions must account
for this convention explicitly.

## Main results

* `UlmerBialgebras.Paper.Appendix.DirectedGraph`: a directed graph, encoded by its edge fibres
  (Definition A.1).
* `UlmerBialgebras.Paper.Appendix.DirectedGraph.IsForest`: at most one directed path between any two
  vertices (Definition A.1).
* `UlmerBialgebras.Paper.Appendix.EnrichedGraph`: the enriched graphs of Definition A.1.
* `UlmerBialgebras.Paper.Appendix.DirectedGraph.Labelling`: a labelling of the edges by objects of
  the monoidal base (Definition A.2).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definitions A.1, A.2
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.Appendix

open CategoryTheory MonoidalCategory

/-- Definition A.1 ([forsman2026syntactic]): a directed graph, encoded by its edge fibres. -/
structure DirectedGraph where
  Vertex : Type u
  Edge : Vertex → Vertex → Type u

/-- Paths in the free category on a directed graph. -/
abbrev DirectedGraph.Path (G : DirectedGraph.{u}) (a b : G.Vertex) :=
  @Quiver.Path G.Vertex ⟨G.Edge⟩ a b

/-- Definition A.1 ([forsman2026syntactic]): a forest has at most one directed path between
vertices. -/
def DirectedGraph.IsForest (G : DirectedGraph.{u}) : Prop :=
  ∀ a b : G.Vertex, Subsingleton (G.Path a b)

/-- The enriched graphs of Definition A.1. -/
abbrev EnrichedGraph (V : Type v) (Vertices : Type u) :=
  Vertices → Vertices → V

/-- Definition A.2 ([forsman2026syntactic]): an object of the monoidal base labels each edge. -/
abbrev DirectedGraph.Labelling (G : DirectedGraph.{u}) (V : Type v) :=
  ∀ ⦃a b : G.Vertex⦄, G.Edge a b → V

end UlmerBialgebras.Paper.Appendix
