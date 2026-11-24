module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.AppendixDefsReverse
public import UlmerBialgebras.Paper.AppendixDefsForest

@[expose] public section

open scoped CategoryTheory.Bicategory

/-!
# Checked statements that are not numbered results of the paper

Statements, with proofs left as `sorry`, of the checked theorems that the paper uses without a
number of their own:

* Section 2.2: the representables `K(x, -)` preserve and jointly reflect products, inserters and
  equifiers (`rep_preserves_prod`, …, `rep_reflects_equif`);
* Appendix A: the point, arrow and three-object probes (`appendix_unit_classification`,
  `appendix_arrow_classification`, `appendix_arrow_transformations`,
  `appendix_three_classification`), the fully faithful part of Theorem A.5
  (`appendix_local_density`) and two related density results (`appendix_tiny_biDense`,
  `appendix_small_biDense`).

## Main results

* `UlmerBialgebras.Paper.rep_preserves_prod`, `UlmerBialgebras.Paper.rep_reflects_prod`: the
  representables `K(x, -)` preserve products and jointly reflect them (Section 2.2); likewise for
  inserters and equifiers.
* `UlmerBialgebras.Paper.appendix_unit_classification`,
  `UlmerBialgebras.Paper.appendix_three_classification`: enriched functors out of the point probe
  classify objects, and those out of the three-object probe classify composable pairs
  `x → C(c₀,c₁)`, `y → C(c₁,c₂)` (Lemma A.3).
* `UlmerBialgebras.Paper.appendix_local_density`: the class of linear probes satisfies
  `UlmerBialgebras.IsACellDense` (the fully faithful part of Theorem A.5).
* `UlmerBialgebras.Paper.appendix_small_biDense`: the small enriched categories are bi-dense.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 2.2 and
  Appendix A
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories
  in particular*][hofstraInnerAutoequivalencesGeneral2024], Lemma 7.1
-/

namespace UlmerBialgebras.Paper

section Representables

universe u v w s

open CategoryTheory Limits

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Section 2.2, preservation of products** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ preserves products ↦ `P.homFunctor x` is bijective on objects, full and faithful:
  the comparison functor $\K(x, \prod c_i) \to \prod \K(x, c_i)$ is an isomorphism of categories.

**Deviations.** none recorded.
-/
theorem rep_preserves_prod {ι : Type s} {c : ι → Obj} (P : Product c) (x : Obj) :
    Function.Bijective (P.homFunctor x).obj ∧ (P.homFunctor x).Full ∧
      (P.homFunctor x).Faithful := sorry

/-- **Section 2.2, reflection of products** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ jointly reflect products ↦ candidate cone `pt`, `π` whose comparison functors
  `Product.candHomFunctor pt π x` are isomorphisms of categories is a product cone `∃ P : Product c,
  P.pt = pt ∧ HEq P.π π`.

**Deviations.**
- different: joint reflection stated as existence of a product cone with the given candidate data
  when comparison functors are isomorphisms (CHALLENGE.md, *Section 2.2, reflection*).
-/
theorem rep_reflects_prod {ι : Type s} {c : ι → Obj} (pt : Obj) (π : ∀ i, pt ⟶ c i)
    (h : ∀ x : Obj, Function.Bijective (Product.candHomFunctor pt π x).obj ∧
      (Product.candHomFunctor pt π x).Full ∧ (Product.candHomFunctor pt π x).Faithful) :
    ∃ P : Product c, P.pt = pt ∧ HEq P.π π := sorry

/-- **Section 2.2, preservation of inserters** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ preserves inserters ↦ `I.homFunctor x` is bijective on objects, full and faithful:
  the comparison functor $\K(x, \mathrm{Ins}(f, g)) \to \mathrm{Ins}(\K(x, f), \K(x, g))$ is an
  isomorphism of categories.

**Deviations.** none recorded.
-/
theorem rep_preserves_ins {a b : Obj} {f g : a ⟶ b} (I : Inserter f g) (x : Obj) :
    Function.Bijective (I.homFunctor x).obj ∧ (I.homFunctor x).Full ∧
      (I.homFunctor x).Faithful := sorry

/-- **Section 2.2, reflection of inserters** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ jointly reflect inserters ↦ candidate inserter data `pt`, `u`, `φ` whose comparison
  functors `Inserter.candHomFunctor pt u φ x` are isomorphisms is an inserter
  `∃ I : Inserter f g, I.pt = pt ∧ HEq I.u u ∧ HEq I.φ φ`.

**Deviations.**
- different: joint reflection stated as existence of an inserter with the given candidate data
  when comparison functors are isomorphisms (CHALLENGE.md, *Section 2.2, reflection*).
-/
theorem rep_reflects_ins {a b : Obj} {f g : a ⟶ b} (pt : Obj) (u : pt ⟶ a)
    (φ : u ≫ f ⟶ u ≫ g)
    (h : ∀ x : Obj, Function.Bijective (Inserter.candHomFunctor pt u φ x).obj ∧
      (Inserter.candHomFunctor pt u φ x).Full ∧ (Inserter.candHomFunctor pt u φ x).Faithful) :
    ∃ I : Inserter f g, I.pt = pt ∧ HEq I.u u ∧ HEq I.φ φ := sorry

/-- **Section 2.2, preservation of equifiers** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ preserves equifiers ↦ `E.homFunctor x` is bijective on objects, full and faithful:
  the comparison functor
  $\K(x, \mathrm{Eq}(\eta, \theta)) \to \mathrm{Eq}(\K(x, \eta), \K(x, \theta))$
  is an isomorphism of categories.

**Deviations.** none recorded.
-/
theorem rep_preserves_equif {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    (x : Obj) :
    Function.Bijective (E.homFunctor x).obj ∧ (E.homFunctor x).Full ∧
      (E.homFunctor x).Faithful := sorry

/-- **Section 2.2, reflection of equifiers** ([forsman2026syntactic], §2.2).

```latex
The universal properties above say precisely that the representable $2$-functors
$\K(x,-)\colon \K\to \CAT$ preserve and jointly reflect PIE limits, which in $\CAT$ are
described in the remark above.
```

**Reading.**
* $\K(x, -)$ jointly reflect equifiers ↦ candidate equifier data `pt`, `e` with `e ◁ η = e ◁ θ`
  whose comparison functors `Equifier.candHomFunctor pt e hcond x` are isomorphisms is an equifier
  `∃ E : Equifier η θ, E.pt = pt ∧ HEq E.e e`.

**Deviations.**
- different: joint reflection stated as existence of an equifier with the given candidate data
  when comparison functors are isomorphisms (CHALLENGE.md, *Section 2.2, reflection*).
-/
theorem rep_reflects_equif {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (pt : Obj) (e : pt ⟶ a)
    (hcond : e ◁ η = e ◁ θ)
    (h : ∀ x : Obj, Function.Bijective (Equifier.candHomFunctor pt e hcond x).obj ∧
      (Equifier.candHomFunctor pt e hcond x).Full ∧ (Equifier.candHomFunctor pt e hcond x).Faithful)
          :
    ∃ E : Equifier η θ, E.pt = pt ∧ HEq E.e e := sorry

end Representables

section Appendix

universe w v u

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Appendix A, point probe** ([forsman2026syntactic], Appendix A).

```latex
\item $\mathbf{1}\to \C$ describes a choice of an object $c$ in $\C$, denoted by
$\Delta_c\colon \textbf{1}\to\C$.
```

**Reading.**
* $\mathbf{1}\to \C$ describes a choice of an object ↦ `unitVCatEval C` is an equivalence and
  bijective on objects: enriched functors out of the point probe classify objects of `C`.

**Deviations.** none recorded.
-/
theorem appendix_unit_classification (C : VCat.{w, v, u} V) :
    (unitVCatEval C).IsEquivalence ∧ Function.Bijective (unitVCatEval C).obj := sorry

/-- **Appendix A, arrow transformations** ([forsman2026syntactic], Appendix A).

```latex
A modification $\Theta\colon F_*\Rrightarrow G_*$, where $F,G\colon \C\to \D$ are $\V$-functors,
is determined by the values $(\alpha_c\coloneqq (\Theta_\textbf{1})_{\Delta_c}\colon I\to
\D(Fc,Gc))_c$ which provides the faithfulness, and the $\V$-naturality of $\alpha$ is encoded
by $\Theta$ at components $\textbf{2}_x$, which shows fullness.
```

**Reading.**
* naturality encoded at $\mathbf{2}_x$ ↦ bijective correspondence between enriched natural
  transformations `F ⟶ G` from `arrowVCat Z x` to `C` and pairs of endpoint components satisfying
  the enriched naturality square.

**Deviations.** none recorded.
-/
theorem appendix_arrow_transformations (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) (F G : arrowVCat.{w, v, u} Z x ⟶ C) :
    Function.Bijective (fun α : F ⟶ G =>
      (⟨(α.app .src, α.app .tgt), α.vnaturality .src .tgt⟩ :
        { p : (F.obj .src ⟶ G.obj .src) × (F.obj .tgt ⟶ G.obj .tgt) //
          F.emap .src .tgt ≫ eHomWhiskerLeft V (F.obj .src) p.2 =
            G.emap .src .tgt ≫ eHomWhiskerRight V p.1 (G.obj .tgt) })) := sorry

/-- **Appendix A, bi-density of tiny categories** ([forsman2026syntactic], Appendix A).

```latex
Let $\V$ be a monoidal category with an absorbing initial object. Then the class
$$
A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y} \mid x,y \in \Obj(\V)\}
$$
is bi-dense in the $2$-category $\K \coloneqq \V\text{-}\CAT$.
```

**Reading.**
* bi-dense class of enriched categories ↦ `IsBiDense (IsTinyVCat (V := V))` in `VCat V`:
  all enriched categories with at most three objects form a bi-dense class in `VCat V`.

**Deviations.**
- weaker: a larger class than Theorem A.5's (all enriched categories with at most three
  objects), so it follows from A.5, because a full sub-2-category that contains a bi-dense one is
  bi-dense (this closure is not formalized; CHALLENGE.md, *Auxiliary checked statements*).
-/
theorem appendix_tiny_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := VCat.{w, v, max u w} V) (IsTinyVCat.{w, v, u} (V := V)) := sorry

/-- **Appendix A, bi-density of small categories** ([forsman2026syntactic], Appendix A).

```latex
Let $\V$ be a monoidal category with an absorbing initial object. Then the class
$$
A \coloneqq \{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y} \mid x,y \in \Obj(\V)\}
$$
is bi-dense in the $2$-category $\K \coloneqq \V\text{-}\CAT$.
```

**Reading.**
* bi-dense class of enriched categories ↦ `IsBiDense (IsSmallVCat V)` in `VCat V`: all small
  enriched categories form a bi-dense class in `VCat V`.

**Deviations.**
- weaker: a larger class than Theorem A.5's (all small enriched categories), so it follows from
  A.5, because a full sub-2-category that contains a bi-dense one is bi-dense (this closure is
  not formalized; CHALLENGE.md, *Auxiliary checked statements*).
-/
theorem appendix_small_biDense (Z : MonoidalInitial V) :
    IsBiDense (Obj := VCat.{w, v, max u w} V) (IsSmallVCat.{w, v, u} V) := sorry

end Appendix

end UlmerBialgebras.Paper
