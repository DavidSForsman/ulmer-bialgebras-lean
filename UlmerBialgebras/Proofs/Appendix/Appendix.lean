module

public import UlmerBialgebras.Paper.AppendixDefsReverse
public import UlmerBialgebras.Paper.AppendixDefsForest
public import UlmerBialgebras.Proofs.Appendix.AppendixReverse
public import UlmerBialgebras.Proofs.Appendix.AppendixForest
public import UlmerBialgebras.Proofs.Appendix.AppendixLinear
public import UlmerBialgebras.Proofs.Appendix.AppendixLinearDensity

/-!
# Appendix A: Lemma A.3, Definition A.4 and Theorem A.5

The point, arrow and three-object probe classifications, the fully faithful part of Theorem A.5
and the related tiny/small-class density results are in `Extras.lean`.

## Main results

* `UlmerBialgebras.Paper.appendix_biDense`: Theorem A.5: the class of point, arrow and three-object
  linear probes is bi-dense in `V-Cat`, in the paper's tensor convention.
* `UlmerBialgebras.Paper.lem_A_3`: Lemma A.3: a labelled forest has a free enriched category, whose
  hom-objects are the labels of paths and initial objects where there is no path.
* `UlmerBialgebras.Paper.def_A_4_isForest`: Definition A.4: the linear graph `0 → 1 → ⋯ → n-1` is a
  forest.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Appendix A
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories in
  particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
* [H. Wolff, *V-cat and V-graph*][wolffVcatVgraph1974]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Theorem A.5** ([forsman2026syntactic]; cf. Hofstra–Karvonen
[hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1): the exact class of the point, arrow and
three-object linear probes is bi-dense, in the paper's tensor convention. -/
theorem appendix_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := Appendix.PaperVCat.{w, v, max u w} V)
      (Appendix.IsPaperLinearProbe.{w, v, max u w} Z) := by
  exact Appendix.Linear.isBiDense_paperLinear Z


/-- **Lemma A.3** ([forsman2026syntactic]): a labelled forest `G` has a free enriched category `Ḡ_ℓ`
(paper convention). Its objects are the vertices (`ι`). Its hom-object `Ḡ_ℓ(a,b)` is identified by
`θ` with `ℓ(p)` when `p : a → b` is a path, and it is initial when there is no path. Its composition
`Ḡ_ℓ(b,c) ⊗ Ḡ_ℓ(a,b) → Ḡ_ℓ(a,c)` is the unique morphism out of an initial object when there is no
path `a → b` or no path `b → c`. For paths `p : a → b` and `q : b → c` it corresponds under `θ` to
the canonical isomorphism `ℓ(q) ⊗ ℓ(p) ≅ ℓ(qp)` (`pathLabelCompIso`). The identities correspond to
the identity of `ℓ(empty path) = I`, and the edge inclusions `incl` to `ℓ(e) ≅ ℓ(e) ⊗ I`, the label
of the one-edge path. Enriched functors out of `Ḡ_ℓ` correspond bijectively, through `incl`, to
vertex maps with edge maps `ℓ(e) → D(f a, f b)`. -/
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
            ∀ ⦃a b : G.Vertex⦄ (e : G.Edge a b), ℓ e ⟶ unmop (f a ⟶[Vᴹᵒᵖ] f b))) :=
  Appendix.Forest.exists_paperVCat_free_of_isForest Z G hG ℓ

/-- **Definition A.4** ([forsman2026syntactic]): the linear graph `0 → 1 → ⋯ → n-1` is a forest, so
Lemma A.3 gives the linear enriched category `n_{x_1,…,x_{n-1}}` for every labelling. -/
theorem def_A_4_isForest (n : ℕ) : (Appendix.linearGraph.{u} n).IsForest :=
  Appendix.linearGraph_isForest n

end UlmerBialgebras.Paper
