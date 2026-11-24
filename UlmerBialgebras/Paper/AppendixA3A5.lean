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

section Appendix

universe w v u

open CategoryTheory MonoidalCategory MonoidalOpposite

variable {V : Type v} [Category.{w} V] [MonoidalCategory V]

/-- **Appendix A, arrow probe** ([forsman2026syntactic], Appendix A).

```latex
\item $H\colon\mathbf{2}_x\to\C$ is equivalently described as a choice of objects $c,c'$ and a
morphism $f\colon x\to\C(c,c')$. Motivated by this, we write $H=H_f$.
```

**Reading.**
* $H\colon\mathbf{2}_x\to\C$ is choice of objects and morphism ↦ bijective correspondence of
  enriched functors `arrowVCat Z x ⟶ C` with pairs of objects `c, c'` and morphisms
  `x ⟶ (c ⟶[V] c')`: the arrow probe is free on its label.

**Deviations.** none recorded.
-/
theorem appendix_arrow_classification (Z : MonoidalInitial V) (x : V)
    (C : VCat.{w, v, u} V) :
    Function.Bijective (fun F : arrowVCat.{w, v, u} Z x ⟶ C =>
      (⟨F.obj .src, F.obj .tgt, F.emap .src .tgt⟩ :
        Σ c : C.carrier, Σ c' : C.carrier, x ⟶ (c ⟶[V] c'))) := sorry

/-- **Appendix A, cell-density of linear probes** ([forsman2026syntactic], Appendix A).

```latex
We show that 
$$
\K(\C,\D)\to[\K(-,\C)|_{\A^{\op}},\K(-,\D)|_{\A^{\op}}]_\Psd, F\mapsto F_*,
$$
is fully faithful and essentially surjective on objects.
```

**Reading.**
* monoidal category $\V$ with absorbing initial object ↦ `V : Type v` with
  `[Category.{w} V] [MonoidalCategory V]` and `Z : MonoidalInitial V`.
* $2$-category $\K \coloneqq \V\text{-}\CAT$ in the paper's tensor convention at independent
  carrier universe `u` ↦ `Appendix.PaperVCat.{w, v, u} V`.
* fully faithful part of Theorem A.5 ↦ `IsACellDense` for the class
  `Appendix.IsPaperLinearProbe.{w, v, u} Z` of linear probes $\{\mathbf{1}, \mathbf{2}_x,
  \mathbf{3}_{x,y}\}$ in `Appendix.PaperVCat.{w, v, u} V`.

**Deviations.** none recorded.
-/
theorem appendix_local_density (Z : MonoidalInitial V) :
    IsACellDense (Obj := Appendix.PaperVCat.{w, v, u} V)
      (Appendix.IsPaperLinearProbe.{w, v, u} Z) := sorry

/-- **Appendix A, three-object probe** ([forsman2026syntactic], Appendix A).

```latex
\item $L\colon \mathbf{3}_{x,y}\to\C$ amounts to a choice of objects $c_0,c_1,c_2$ and
morphisms $f\colon x\to\C(c_0,c_1)$, $g\colon y\to\C(c_1,c_2)$, with $L_{0,2}\colon y\otimes
x\to \C(c_0, c_2)$ being $\mu_{c_0,c_1,c_2}\circ(g\otimes f)$, where $\mu$ denotes the
composition of $\C$. We denote by $j_c\colon I\to \C(c,c)$ the identity of an object $c$ in
$\C$.
```

**Reading.**
* $L\colon \mathbf{3}_{x,y}\to\C$ amounts to choice of objects and morphisms ↦ bijective
  correspondence between enriched functors `Appendix.paperThreeVCat Z x y ⟶ C` and composable pairs
  of morphisms in `C` (in paper's tensor convention).

**Deviations.** none recorded.
-/
theorem appendix_three_classification (Z : MonoidalInitial V) (x y : V)
    (C : Appendix.PaperVCat.{w, v, u} V) :
    Function.Bijective (fun F : Appendix.paperThreeVCat.{w, v, u} Z x y ⟶ C =>
      (⟨F.obj .zero, F.obj .one, F.obj .two,
        (F.emap .zero .one).unmop, (F.emap .one .two).unmop⟩ :
        Σ c₀ : C.carrier, Σ c₁ : C.carrier, Σ c₂ : C.carrier,
          (x ⟶ MonoidalOpposite.unmop (c₀ ⟶[Vᴹᵒᵖ] c₁)) ×
            (y ⟶ MonoidalOpposite.unmop (c₁ ⟶[Vᴹᵒᵖ] c₂)))) := sorry

end Appendix

end UlmerBialgebras.Paper
