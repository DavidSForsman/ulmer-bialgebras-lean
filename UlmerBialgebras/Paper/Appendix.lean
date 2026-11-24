module

public import UlmerBialgebras.Paper.AppendixDefsReverse
public import UlmerBialgebras.Paper.AppendixDefsForest

/-!
# Appendix A: Lemma A.3, Definition A.4 and Theorem A.5

The point, arrow and three-object probe classifications, the fully faithful part of Theorem A.5
and the related tiny/small-class density results are in `Extras.lean`.

## Main results

* `UlmerBialgebras.Paper.lem_A_3`: a labelled forest has a free enriched category, with hom-objects
  the path labels (Lemma A.3).
* `UlmerBialgebras.Paper.def_A_4_isForest`: the linear graph `0 → 1 → ⋯ → n-1` is a forest
  (Definition A.4).
* `UlmerBialgebras.Paper.appendix_biDense`: the class of point, arrow and three-object linear probes
  is bi-dense (Theorem A.5).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Appendix A (Lemma A.3, Definition A.4, Theorem A.5)
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Theorem A.5** ([forsman2026syntactic], Appendix A;
[hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1).

```latex
Let $\V$ be a monoidal category with an absorbing initial object. Then the class
$$
A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y} \mid x,y \in \Obj(\V)\}
$$
is bi-dense in the $2$-category $\K \coloneqq \V\text{-}\CAT$.
```

**Reading.**
* $\V$ monoidal category with absorbing initial object ↦ `[MonoidalCategory V]`,
  `Z : MonoidalInitial V`.
* $\K \coloneqq \V\text{-}\CAT$ ↦ `Appendix.PaperVCat V` (in paper's tensor convention).
* class $A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y}\}$ ↦
  `Appendix.IsPaperLinearProbe Z`.
* bi-dense in $\K$ ↦ `IsBiDense (Appendix.IsPaperLinearProbe Z)`.
* the carrier universe stays `max u w` (chosen by the author): the proof identifies the carrier of
  a `V`-category with its hom-category from the unit `V`-category, in `Type (max u w)`.
  The local density statement `appendix_local_density` takes carriers in any `Type u`.

**Deviations.**
- different (size): the 2-category `V-CAT` is that of the `V`-categories with objects in
  `Type (max u w)`, at least the universe `Type w` of `V`'s morphisms; a `V`-category with smaller
  objects is isomorphic, through `ULift`, to one of them. The proof identifies the objects of a
  `V`-category with the `V`-functors out of the unit `V`-category, which live in `Type (max u w)`.
-/
theorem appendix_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := Appendix.PaperVCat.{w, v, max u w} V)
      (Appendix.IsPaperLinearProbe.{w, v, max u w} Z) := sorry


/-- **Lemma A.3** ([forsman2026syntactic], Appendix A; Wolff [wolffVcatVgraph1974]).

```latex
Let $G$ be a forest with a $\V$-labelling $\ell$. Then the $\V$-graph $G_\ell$ has a free
$\V$-category $\overline{G}_\ell$, with objects $G_0$ and hom-objects
$$
\overline{G}_\ell(a,b)=\begin{cases}\ell(p), & \text{if } p\colon a\to b \text{ is a path},\\
0, & \text{otherwise}.\end{cases}
$$
The composition $\overline{G}_\ell(b,c)\otimes \overline{G}_\ell(a,b)\to \overline{G}_\ell(a,c)$
is either the unique morphism from the initial object or the canonical isomorphism
$\ell(q)\otimes \ell(p)\cong \ell(qp)$ induced by the monoidal structure, when paths
$p\colon a\to b$ and $q\colon b\to c$ exist.
```

**Reading.**
* $\V$ with absorbing initial object ↦ `[MonoidalCategory V]`, `Z : MonoidalInitial V`.
* forest $G$ with labelling $\ell$ ↦ `G : Appendix.DirectedGraph`, `hG : G.IsForest`,
  `ℓ : G.Labelling V`.
* free $\V$-category $\overline{G}_\ell$ ↦ `C : Appendix.PaperVCat V`.
* objects $G_0$ ↦ `ι : G.Vertex ≃ C.carrier`.
* hom-objects $\overline{G}_\ell(a,b)$ ↦
  `θ : ∀ a b p, unmop (ι a ⟶[Vᴹᵒᵖ] ι b) ≅ Appendix.DirectedGraph.pathLabel ℓ p`
  and initial when no path.
* composition $\overline{G}_\ell(b,c)\otimes \overline{G}_\ell(a,b)\to \overline{G}_\ell(a,c)$ ↦
  `eComp` matches `Appendix.DirectedGraph.pathLabelCompIso ℓ p q` when paths exist,
  and initial morphism otherwise.
* universal property ↦ bijective correspondence of $\V$-functors `C ⟶ D` with vertex and edge maps.

**Deviations.** none recorded.
-/
theorem lem_A_3 (Z : MonoidalInitial V) (G : Appendix.DirectedGraph.{u}) (hG : G.IsForest)
    (ℓ : G.Labelling V) :
    ∃ (C : Appendix.PaperVCat.{w, v, u} V) (ι : G.Vertex ≃ C.carrier)
      (θ : ∀ (a b : G.Vertex) (p : G.Path a b),
        unmop (ι a ⟶[Vᴹᵒᵖ] ι b) ≅ Appendix.DirectedGraph.pathLabel ℓ p)
      (incl : ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (ι a ⟶[Vᴹᵒᵖ] ι b)),
      (∀ a b : G.Vertex, IsEmpty (G.Path a b) →
        Nonempty (Limits.IsInitial (unmop (ι a ⟶[Vᴹᵒᵖ] ι b)))) ∧
      (∀ a b c : G.Vertex, IsEmpty (G.Path a b) ∨ IsEmpty (G.Path b c) →
        Nonempty (Limits.IsInitial (unmop (ι b ⟶[Vᴹᵒᵖ] ι c) ⊗ unmop (ι a ⟶[Vᴹᵒᵖ] ι b)))) ∧
      (∀ (a b c : G.Vertex) (p : G.Path a b) (q : G.Path b c),
        (eComp Vᴹᵒᵖ (ι a) (ι b) (ι c)).unmop ≫ (θ a c (p.comp q)).hom =
          ((θ b c q).hom ⊗ₘ (θ a b p).hom) ≫
            (Appendix.DirectedGraph.pathLabelCompIso ℓ p q).hom) ∧
      (∀ a : G.Vertex, (eId Vᴹᵒᵖ (ι a)).unmop ≫ (θ a a Quiver.Path.nil).hom = 𝟙 (𝟙_ V)) ∧
      (∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b),
        incl e ≫ (θ a b ((Quiver.Path.nil : G.Path a a).cons e)).hom = (ρ_ (ℓ e)).inv) ∧
      ∀ D : Appendix.PaperVCat.{w, v, u} V, Function.Bijective (fun F : C ⟶ D =>
        (⟨fun a => F.obj (ι a), fun a b e => incl e ≫ (F.emap (ι a) (ι b)).unmop⟩ :
          Σ f : G.Vertex → D.carrier,
            ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (f a ⟶[Vᴹᵒᵖ] f b))) := sorry

/-- **Definition A.4** ([forsman2026syntactic], Appendix A).

```latex
For $n\geq1$ and $x_1,\ldots,x_{n-1}\in\V$, the \textbf{linear $\V$-category}
$\mathbf{n}_{x_1,\ldots,x_{n-1}}$ is $\overline{G}_\ell$ for the forest
$0\to1\to\cdots\to n-1$ whose edge $(i-1)\to i$ is labelled by $x_i$ for each $i\leq n-1$.
```

**Reading.**
* linear graph $0\to1\to\cdots\to n-1$ ↦ `Appendix.linearGraph n`.
* is a forest ↦ `Appendix.DirectedGraph.IsForest (Appendix.linearGraph n)`.

**Deviations.**
- stronger: also covers the linear graph with n = 0 (CHALLENGE.md, *Stronger than the paper*).
-/
theorem def_A_4_isForest (n : ℕ) : (Appendix.linearGraph.{u} n).IsForest := sorry

end UlmerBialgebras.Paper
