module

public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec5DefsCart
public import UlmerBialgebras.Paper.Sec5DefsKanIns
public import Foundations.CategoryTheory.Factorization.ExactCategory
public import UlmerBialgebras.Kan.SiftedModel
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Creates
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Kan.SiftedApplications

/-!
# Challenge: Sections 5, 6 and 7

Statements of the numbered results of Sections 5–7, with proofs left as `sorry`.

Definition 5.1 (monadicity in a 2-category) is `UlmerBialgebras.Paper.IsMonadic2` in
`UlmerBialgebras/Paper/Sec3Defs2.lean`.

## Main results

* `UlmerBialgebras.Paper.lem_5_2`: `g : d ⟶ c` is monadic iff it is a right adjoint and each
  `g_x : K(x, d) → K(x, c)` creates the coequalizers of `g_x`-split pairs (Lemma 5.2).
* `UlmerBialgebras.Paper.thm_5_7`: under its hypotheses on a bialgebraic datum in `CAT`, `u_B` is
  monadic, `Bialg(B)` has colimits of size at most `κ`, and `Bialg(B)` has the left Kan extensions
  along `k` of `d` for which `d u_B` and `d u_B L₁` have them (Theorem 5.7).
* `UlmerBialgebras.Paper.thm_5_10_1`: a colimit-preserving functor out of a locally presentable
  category into a locally small category is a left adjoint (Theorem 5.10 (1)).
* `UlmerBialgebras.Paper.thm_6_6_1`: under the orthogonality hypotheses on the supports,
  `(U_B⁻¹E', U_B⁻¹M')` is the unique orthogonal factorization system on `Bialg(B)` preserved by
  `U_B` (Theorem 6.6 (1)).
* `UlmerBialgebras.Paper.cor_6_9`: under its hypotheses, if `M^{T₁}` is Barr-exact then so is
  `M^{T₂}` (Corollary 6.9).
* `UlmerBialgebras.Paper.thm_7_4`: if `A` is bi-dense, `d` has and `g` preserves right Kan
  extensions along 1-cells of `𝒜`, and `g` is an `A`-right adjoint, then `g` is a right adjoint
  (Theorem 7.4).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Sections 5, 6, 7
* [F. Ulmer, *Properties of dense and relative adjoint functors*][ulmerPropertiesDenseRelative1968]
* [J. Adámek, *Free algebras and automata realizations in the language of categories*]
  [Adamek1974]
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [M. Barr, *Coequalizers and free triples*][barrCoequalizersFreeTriples1970]
* [J. Adámek, *Colimits of algebras revisited*][adamekColimitsAlgebrasRevisited1977]
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model theory*]
  [MakkaiPare1989AccessibleCategories]
* [E. Riehl, *Categorical homotopy theory*][Riehl2014CategoricalHomotopyTheory], Lemma 11.2.3
* [T. Wißmann, *Minimality notions via factorization systems and examples*]
  [Wissmann2022Minimality], Proposition 3.7
* [G. M. Kelly, *A note on relations relative to a factorization system*][Kelly1991],
  Proposition 2.2(b)
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
* [R. Street, *The formal theory of monads*][STREET1972149]
* [S. Lack, R. Street, *The formal theory of monads II*][lackFormalTheoryMonads2002]
-/

@[expose] public section

universe u v w u' v' w₀ w₁ u₁ v₁ u₂ v₂ u₃ s s₁ s₂ s₃ t₁ t₂ t₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 7: monadicity and local presentability in 2-categories -/

section Sec7

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **The bicategorical Yoneda lemma** ([forsman2026syntactic], §7).

```latex
The bicategorical Yoneda lemma \cite[(1.9)]{Street1980FibrationsBicategories} shows that the class
of all objects of a $2$-category $\K$ is bi-dense.
```

**Reading.**
* "class of all objects is bi-dense" ↦ `IsBiDense (⊤ : ObjectProperty Obj)`.
* bicategory setting ↦ `[Bicategory.{w, v} Obj] [Bicategory.Strict Obj]`.

**Deviations.** none recorded.
-/
theorem yoneda_biDense : IsBiDense (⊤ : ObjectProperty Obj) := sorry

/-- **Theorem 7.4** ([forsman2026syntactic], §7).

```latex
Let $g\colon d\to c$ be a morphism in $\K$. Assume that $d$ has and $g$ preserves all right Kan
extensions along morphisms in $\A$. If $g$ is an $A$-right adjoint, then $g$ is a right adjoint.
```

**Reading.**
* standing bi-density hypothesis ↦ `hA : IsBiDense A`.
* "$\A$-right adjoint" ↦ `IsARightAdjoint A g`.
* "$d$ has and $g$ preserves right Kan extensions along $\A$" ↦ `HasARightKan A d` and
  preservation of right Kan extensions `PreservesRightKan k e g` for all morphisms `k` in `A`.
* "$g$ is a right adjoint" ↦ `∃ f : c ⟶ d, Nonempty (TwoAdj f g)`.

**Deviations.**
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, which
  the proof does not use.
-/
theorem thm_7_4 (A : ObjectProperty Obj) (hA : IsBiDense A) {c d : Obj} (g : d ⟶ c)
    (hd : HasARightKan A d)
    (hg : ∀ ⦃i x : Obj⦄, A i → A x → ∀ (k : i ⟶ x) (e : i ⟶ d), PreservesRightKan k e g)
    (hadj : IsARightAdjoint A g) :
    ∃ f : c ⟶ d, Nonempty (TwoAdj f g) := sorry

/-- **Corollary 7.5** ([forsman2026syntactic], §7).

```latex
Let $g\colon d\to c$ be an $A$-accessible morphism in $\K$. If $d$ has and $g$ preserves
$\A$-limits, then $g$ is a right adjoint. Moreover, if $d$ has and $g$ preserves $\A$-colimits,
then $g$ is a left adjoint.
```

**Reading.**
* "$A$-accessible morphism" ↦ `IsAAccessibleMor'.{w₀} A g`.
* "$d$ has and $g$ preserves $\A$-(co)limits" ↦ `IsRightALocPres A d` (`IsLeftALocPres A d`) and
  `IsCalAContinuous A g` (`IsCalACocontinuous A g`); `IsRightALocPres A d` is
  `IsAAccessibleObj A d ∧ IsCalAComplete A d`, whose accessibility part follows from `hacc`.
* right/left adjoint conclusions ↦ `(∃ f, Nonempty (TwoAdj f g)) ∧ (∃ h, Nonempty (TwoAdj g h))`.

**Deviations.**
- stronger: holds in any strict 2-category with a bi-dense class `A`; the paper's Section 7
  assumes `K` PIE-complete.
-/
theorem cor_7_5 (A : ObjectProperty Obj) (hA : IsBiDense A) {c d : Obj} (g : d ⟶ c)
    (hacc : IsAAccessibleMor'.{w₀} A g) :
    (IsRightALocPres.{w₀} A d → IsCalAContinuous.{w₀} A g →
        ∃ f : c ⟶ d, Nonempty (TwoAdj f g)) ∧
      (IsLeftALocPres.{w₀} A d → IsCalACocontinuous.{w₀} A g →
        ∃ h : c ⟶ d, Nonempty (TwoAdj g h)) :=
  sorry

/-- **Theorem 7.6, Kan extension and cocompleteness** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Assume:
\begin{enumerate}
    \item The morphisms $g$ and $g'$ are right adjoints.
    \item The object $c$ is $A$-cocomplete and has all right Kan extensions along morphisms in $\A$.
    \item The functors $f_a\coloneqq \K(a,f)\colon \K(a,c)\to \K(a,x)$ and $f_a'\coloneqq
    \K(a,f')\colon \K(a,c)\to \K(a,y)$ preserve $\kappa_a$-colimits, where $\kappa_a$ is an
    infinite cardinal, for each $a\in A$. 
\end{enumerate}
```

```latex
Furthermore, if $K\xleftarrow{k}I\xrightarrow{d} \BialgB$ is a span in $\K$ so that $K\in A$, and
the left Kan extensions of $ud$ and $fud$ along $k$ exist, then the left Kan extension of $d$
exists along $k$. In particular, $\BialgB$ is $A$-cocomplete.
```

**Reading.**
* bialgebraic datum in $\K$ ↦ `B : BialgDatum (Obj := Obj)`.
* span $K \leftarrow I \to \BialgB$ with $K \in A$ ↦ `k : I ⟶ X`, `d : I ⟶ E.pt` with `A X`.
* detection of left Kan extensions along $k$ ↦ existence of initial object in `LeftExt k d`.
* "$\BialgB$ is $A$-cocomplete" ↦ `IsACocomplete.{w₀} A E.pt`.
* the monadicity clause is formalized separately as `thm_7_6_monadic`.

**Deviations.**
- stronger: does not assume bi-density of $\A$ or right Kan extensions (CHALLENGE.md, *Same content,
  different form*).
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_6 (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    (∀ {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt), A X →
      (∃ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L)) →
      (∃ L : LeftExt k ((d ≫ B.uB E) ≫ B.f), Nonempty (IsInitial L)) →
        ∃ L : LeftExt k d, Nonempty (IsInitial L)) ∧
      IsACocomplete.{w₀} A E.pt := sorry

/-- **Theorem 7.6, monadicity clause** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Assume:
\begin{enumerate}
    \item The morphisms $g$ and $g'$ are right adjoints.
    \item The object $c$ is $A$-cocomplete and has all right Kan extensions along morphisms in $\A$.
    \item The functors $f_a\coloneqq \K(a,f)\colon \K(a,c)\to \K(a,x)$ and $f_a'\coloneqq
    \K(a,f')\colon \K(a,c)\to \K(a,y)$ preserve $\kappa_a$-colimits, where $\kappa_a$ is an
    infinite cardinal, for each $a\in A$. 
\end{enumerate}
```

```latex
Then $u_\B\colon \BialgB\to c$ is monadic.
```

**Reading.**
* "bi-dense class $A$" ↦ `hA : IsBiDense A`.
* "$g, g'$ right adjoints" ↦ `TwoAdj l B.g`, `TwoAdj l B.g'`.
* "$c$ is $A$-cocomplete and has right Kan extensions along $\A$" ↦
  `IsACocomplete A B.c`, `HasARightKan A B.c`.
* "$f_a, f_a'$ preserve $\kappa_a$-colimits" ↦
  preservation of $\kappa_a$-colimits for `postcomp a B.f` and `postcomp a B.f'`.
* "$u_\B$ is monadic" ↦ `IsMonadic2 (B.uB E)`.

**Deviations.**
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_6_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c) (hRan : HasARightKan A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    IsMonadic2 (B.uB E) := sorry

/-- **Theorem 7.7, local presentability and accessibility** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$, where the morphisms
$f,f',g,g'$ are $A$-accessible. Then the following hold:
\begin{enumerate}
    \item If $c$ has and $g,g'$ preserve $\A$-limits, then $u_\B\colon \BialgB\to c$ is monadic,
    $A$-accessible and $\BialgB$ is right $\A$-locally presentable.
    \item If $c$ has and $f,f'$ preserve $\A$-colimits, then $\BialgB$ is left $\A$-locally
    presentable with $u$ being comonadic and $A$-accessible.
\end{enumerate}
```

**Reading.**
* "$f, f', g, g'$ are $A$-accessible" ↦ `IsAAccessibleMor'.{w₀} A B.f`, etc.
* "$\A$-limits", "$\A$-colimits" ↦ `IsCalAComplete.{w₁}`, `IsCalAContinuous.{w₁}`, etc., at a
  size `w₁` independent of the accessibility size `w₀`.
* clause 1 ↦ `IsAAccessibleMor'.{w₀} A (B.uB E)`, `IsAAccessibleObj.{w₀} A E.pt` and
  `IsCalAComplete.{w₁} A E.pt`; for `w₁ = w₀` the last two are `IsRightALocPres.{w₀} A E.pt`
  by definition.
* clause 2 ↦ the same with `IsCalACocomplete.{w₁}`; at `w₁ = w₀`, `IsLeftALocPres.{w₀} A E.pt`.
* the (co)monadicity conclusions are formalized separately as `thm_7_7_monadic`.

**Deviations.**
- stronger: does not assume bi-density of $\A$ (CHALLENGE.md, *Same content, different form*).
- different (size): the (co)limit size `w₁` is independent of the accessibility size `w₀`; the
  paper's single size is `w₁ = w₀` (CHALLENGE.md, *Size migration*).
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_7 (A : ObjectProperty Obj)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₁} A B.c → IsCalAContinuous.{w₁} A B.g → IsCalAContinuous.{w₁} A B.g' →
      IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt ∧
        IsCalAComplete.{w₁} A E.pt) ∧
    (IsCalACocomplete.{w₁} A B.c → IsCalACocontinuous.{w₁} A B.f →
      IsCalACocontinuous.{w₁} A B.f' →
      IsAAccessibleMor'.{w₀} A (B.uB E) ∧ IsAAccessibleObj.{w₀} A E.pt ∧
        IsCalACocomplete.{w₁} A E.pt) := sorry

/-- **Theorem 7.7, (co)monadicity clauses** ([forsman2026syntactic], §7).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$, where the morphisms
$f,f',g,g'$ are $A$-accessible. Then the following hold:
\begin{enumerate}
    \item If $c$ has and $g,g'$ preserve $\A$-limits, then $u_\B\colon \BialgB\to c$ is monadic,
    $A$-accessible and $\BialgB$ is right $\A$-locally presentable.
    \item If $c$ has and $f,f'$ preserve $\A$-colimits, then $\BialgB$ is left $\A$-locally
    presentable with $u$ being comonadic and $A$-accessible.
\end{enumerate}
```

**Reading.**
* "bi-dense class $A$" ↦ `hA : IsBiDense A`.
* "$u_\B$ is monadic" ↦ `IsMonadic2 (B.uB E)`.
* "$u_\B$ is comonadic" ↦ `IsComonadic2 (B.uB E)`.
* unlike `thm_7_7`, the accessibility and (co)limit sizes are one size `w₀`: the proof goes
  through the adjoint functor theorem for accessible functors (`cor_7_5`), which needs both at the
  same size.

**Deviations.**
- stronger: holds in any strict 2-category; the paper's Section 7 assumes `K` PIE-complete, and
  the statement takes the inserter and the equifier it uses as data (`B.ins`, `E`).
-/
theorem thm_7_7_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₀} A B.c → IsCalAContinuous.{w₀} A B.g → IsCalAContinuous.{w₀} A B.g' →
      IsMonadic2 (B.uB E)) ∧
    (IsCalACocomplete.{w₀} A B.c → IsCalACocontinuous.{w₀} A B.f → IsCalACocontinuous.{w₀} A B.f' →
      IsComonadic2 (B.uB E)) := sorry

end Sec7

end UlmerBialgebras.Paper
