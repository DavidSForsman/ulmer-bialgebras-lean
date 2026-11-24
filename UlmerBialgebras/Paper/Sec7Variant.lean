module

public import UlmerBialgebras.Paper.Sec7DefsSec7Variant

/-!
# Challenge: Definition 7.1 as a variant of Hofstra–Karvonen bi-density

The paper's Definition 7.1 says that a class `A` of objects of a strict 2-category `K` is
bi-dense if `c ↦ K(-, c)|_{A^op}` is bi-fully faithful, and calls this "a variation of the
bicategorical notion of density introduced in [HK, Definition 6.2]". Hofstra–Karvonen define
bi-density for a pseudofunctor `F : 𝒞 → 𝒟`: the functors
`𝒟(c, d) → [𝒞^op, Cat](𝒟(F-, c), 𝒟(F-, d))` are equivalences. We show that `A` is bi-dense in
the paper's sense iff the inclusion of the full sub-2-category spanned by `A` is bi-dense in
Hofstra–Karvonen's sense.

## Main results

* `UlmerBialgebras.Paper.isBiDense_iff_isBiDense_fullSubBicatι`: `A` is bi-dense in the sense of
  Definition 7.1 iff the inclusion of the full sub-2-category spanned by `A` is bi-dense in the
  sense of Hofstra–Karvonen.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Definition 7.1
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal
  categories in particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
-/

@[expose] public section

universe u v w

namespace UlmerBialgebras.Paper

open CategoryTheory

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Definition 7.1 versus Hofstra–Karvonen** ([forsman2026syntactic], §7;
[hofstraInnerAutoequivalencesGeneral2024], Definition 6.2).

```latex
We say that the class of objects $A$ is \textbf{bi-dense} in $\K$ if the $2$-functor
$c\mapsto \K(-,c)|_{\A^{\op}}\colon \K\to [\A^{\op},\CAT]$ is bi-fully faithful, that is, for all
objects $a,b$ in $\K$, the functor
\[
\K(a,b)\to [\K(-,a)|_{\A^{\op}},\K(-,b)|_{\A^{\op}}]_\Psd,\quad f\mapsto f_*\coloneqq f*(-),
\]
is an equivalence of categories. This is a variation of the bicategorical notion of density
introduced in \cite[Definition~6.2]{hofstraInnerAutoequivalencesGeneral2024}.
```

**Reading.**
* $\K$ strict 2-category ↦ `[Bicategory Obj] [Bicategory.Strict Obj]`.
* class of objects $A$ ↦ `A : ObjectProperty Obj`.
* $A$ bi-dense in the paper's sense ↦ `IsBiDense A`.
* $\A$ full sub-2-category spanned by $A$ ↦ `fullSubBicatι A` is the inclusion pseudofunctor.
* bi-dense in Hofstra–Karvonen's sense ↦ `(fullSubBicatι A).IsBiDense`.

**Deviations.** none recorded.
-/
theorem isBiDense_iff_isBiDense_fullSubBicatι (A : ObjectProperty Obj) :
    IsBiDense A ↔ (fullSubBicatι A).IsBiDense := sorry

end UlmerBialgebras.Paper
