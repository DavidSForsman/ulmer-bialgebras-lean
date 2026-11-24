module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec4DefsExt
public import UlmerBialgebras.Kan.ColimKan
public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Examples.FieldEquiv

/-!
# Challenge: Section 4 (lifting limits and colimits)

Statements of the numbered results of Section 4, with proofs left as `sorry`.

## Main results

* `UlmerBialgebras.Paper.thm_4_7_1_creates`: the projections of a product jointly strictly create
  left and right Kan extensions (Theorem 4.7 (1)).
* `UlmerBialgebras.Paper.thm_4_7_2_right`: `u : Ins(f, g) → a` strictly creates the right Kan
  extensions that `g` preserves (Theorem 4.7 (2)).
* `UlmerBialgebras.Paper.cor_4_8_right`: `u_B` strictly creates the right Kan extensions that `g`
  preserves and whose subterminality `g'` preserves (Corollary 4.8).
* `UlmerBialgebras.Paper.cor_4_17`: if each `M(B)` preserves `I`-colimits componentwise, `I` sifted,
  then `U : M^T → M₀` strictly creates `I`-indexed colimits (Corollary 4.17).
* `UlmerBialgebras.Paper.thm_4_19`: under its hypotheses, `U : M^T → M₀` strictly creates the
  `K`-indexed wide pushouts of diagrams whose legs `U` sends to regular epimorphisms
  (Theorem 4.19).
* `UlmerBialgebras.Paper.cor_4_21`: the category of fields is accessible, and `k ↦ k*` creates
  connected limits and sifted colimits (Corollary 4.21).

## How to read the statements

* Notation: `CHALLENGE.md`, *How to read the Lean*; its `u₁`–`u₃` are `uu₁`–`uu₃` here.
* In the section on models, `Obj`, its chosen limits, `M`, `sg` and `T` are section variables.
* 4.13–4.15, 4.17: `Cat.{v, max u v}` (`catPIEComplete`); 4.19: `Cat.{v, u}`, its limits assumed.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 4
  (Remark 4.5, Lemmas 4.6, 4.16, Theorems 4.7, 4.19, Corollaries 4.8, 4.10–4.15, 4.17, 4.18, 4.21)
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3, 3.4
* [J. Adámek, J. Rosický, E. M. Vitale, *What are sifted colimits?*]
  [AdamekRosickyVitale2010SiftedColimits]
* [J. Adámek, J. Rosický, E. Vitale, *Algebraic Theories: A Categorical Introduction to General
  Algebra*][Adamek-Rosicky-Vitale]
-/

@[expose] public section

universe s u v w u₁ v₁ uu₁ uu₂ uu₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section General

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Remark 4.5** ([forsman2026syntactic], §4).

```latex
If $\LE(d,k)$ has an initial object $(l,\eta\colon d\Rightarrow lk)$, then transposition
along $\eta$ gives an isomorphism $\LE(d,k)\cong l\backslash \K(K,c)$ over $\K(K,c)$.
Conversely, if $\LE(d,k)$ is equivalent to a coslice category, then it has an initial object,
since every coslice category has one.
```

**Reading.**
* $\mathrm{LE}(d, k)$ ↦ `LeftExt k d`: the category of left extensions of `d` along `k`.
* $l \backslash \mathcal{K}(K, c)$ ↦ `Under L₀.ext`: the coslice category under `L₀.ext`.
* "isomorphism ... over $\K(K,c)$" ↦ bijective on objects, full and faithful functor `F` commuting
  with the projection: `F ⋙ Under.forget L₀.ext = LeftExt.forget k d`.
* "equivalent to a coslice category" ↦ `Nonempty (LeftExt k d ≌ Under x)`.

**Deviations.** none recorded.
-/
theorem rem_4_5 {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) :
    (∀ L₀ : LeftExt k d, IsInitial L₀ →
      ∃ F : LeftExt k d ⥤ Under L₀.ext, Function.Bijective F.obj ∧ F.Full ∧ F.Faithful ∧
        F ⋙ Under.forget L₀.ext = LeftExt.forget k d) ∧
    (∀ {C : Type u₁} [Category.{v₁} C] (x : C), Nonempty (LeftExt k d ≌ Under x) →
      ∃ L : LeftExt k d, Nonempty (IsInitial L)) := sorry

/-- **Lemma 4.6 (1)** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Consider morphisms $K\xleftarrow{k} I\xrightarrow{d} a\xrightarrow{u}
b\xrightarrow{f,g} c$ in $\K$. Then the following hold:
```

```latex
\item Let $(a_j)_{j\in J}$ be a family of objects in $\K$. Assume that the product $\prod_j a_j$
exists and equals $a$. Then we have the isomorphism of categories
$$
\LE(d,k) \cong \prod_{j\in J}\LE(d_j,k), (l = (l_j)_j,\eta = (\eta_j)_j)\mapsto (l_j,\eta_j)_j,
\text{ where $d = (d_j)_j.$}
$$
```

**Reading.**
* $\prod_j a_j$ exists ↦ `(P : Product c)`: a chosen product cone in the bicategory `Obj`.
* "isomorphism of categories" ↦ `P.kanFunctorLeft k d` is bijective on objects, full, and faithful.
* $d_j$ ↦ projection component: `P.π` composed with `d`.

**Deviations.** none recorded.
-/
theorem lem_4_6_1 {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ P.pt) :
    Function.Bijective (P.kanFunctorLeft k d).obj ∧ (P.kanFunctorLeft k d).Full ∧
      (P.kanFunctorLeft k d).Faithful := sorry

/-- **Lemma 4.6 (2)** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Consider morphisms $K\xleftarrow{k} I\xrightarrow{d} a\xrightarrow{u}
b\xrightarrow{f,g} c$ in $\K$. Then the following hold:
```

```latex
\item Assume $(u\colon a\to b,\phi\colon fu\Rightarrow gu)$ is the inserter of $f$ and $g$, then
there is an isomorphism of categories $F\colon \LE(d,k)\to \Ins(f_*,g_*)$ so that the diagram
$$
\begin{tikzcd}
{\LE(d,k)} \arrow[rr, "F"] \arrow[rd, "u_*"'] &             & {\Ins(f_*,g_*)} \arrow[ld, "U"] \\
                                              & {\LE(ud,k)} &                                
\end{tikzcd}
$$
commutes. Here $f_*,g_*\colon \LE(ud,k)\to \LE(fud,k)$ are functors defined on objects as follows:
$$
f_*(l'\colon K\to b,\eta'\colon ud\Rightarrow l'k) = (fl',f\eta'),
\quad g_*(l',\eta') = (gl',g\eta'\bullet \phi d).
$$
```

**Reading.**
* $(u, \phi)$ is the inserter ↦ `(J : Inserter f g)`.
* "isomorphism of categories $F$ over $\LE(ud, k)$" ↦ `Inserter.leftExtToIns J k d` is bijective on
  objects, full, faithful, and satisfies
  `Inserter.leftExtToIns J k d ⋙ Ins.forget _ _ = LeftExt.push k d J.u`.

**Deviations.** none recorded.
-/
theorem lem_4_6_2 {a b : Obj} {f g : a ⟶ b} (J : Inserter f g) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ J.pt) :
    Function.Bijective (Inserter.leftExtToIns J k d).obj ∧ (Inserter.leftExtToIns J k d).Full ∧
      (Inserter.leftExtToIns J k d).Faithful ∧
      Inserter.leftExtToIns J k d ⋙ Ins.forget _ _ = LeftExt.push k d J.u := sorry

/-- **Lemma 4.6 (3)** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Consider morphisms $K\xleftarrow{k} I\xrightarrow{d} a\xrightarrow{u}
b\xrightarrow{f,g} c$ in $\K$. Then the following hold:
```

```latex
\item Let $\alpha,\beta\colon f\Rightarrow g$ be transformations in $\K$ and assume $u\colon a\to b$
determines the equifier $\Eq(\alpha,\beta)$. Then there is an isomorphism $F\colon \LE(d,k)\cong
\Eq(\alpha_*,\beta_*)$ in the slice category $\CAT/\LE(ud,k)$, where the horizontal composition
defines the natural transformations $\alpha_*,\beta_*\colon f_*\Rightarrow g_*\colon \LE(ud,k)\to
\LE(fud,k)$ ($g_*(l',\eta')=(gl',\,g\eta'\bullet\alpha ud)$).
```

**Reading.**
* $u$ determines the equifier ↦ `(E : Equifier η θ)`.
* "isomorphism in the slice category" ↦ `Equifier.leftExtToEquif E k d` is bijective on objects,
  full, faithful, and commutes over $\LE(ud, k)$ via
  `Equifier.leftExtToEquif E k d ⋙ Equif.forget _ _ = LeftExt.push k d E.e`.

**Deviations.** none recorded.
-/
theorem lem_4_6_3 {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) :
    Function.Bijective (Equifier.leftExtToEquif E k d).obj ∧
      (Equifier.leftExtToEquif E k d).Full ∧ (Equifier.leftExtToEquif E k d).Faithful ∧
      Equifier.leftExtToEquif E k d ⋙ Equif.forget _ _ = LeftExt.push k d E.e := sorry

/-- **Theorem 4.7 (1), preservation** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "projections preserve all right and left Kan extensions" ↦ `PreservesLeftKan k d (P.π i)` and
  `PreservesRightKan k d (P.π i)` for each index `i`.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_preserves {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) (i : ι) :
    PreservesLeftKan k d (P.π i) ∧ PreservesRightKan k d (P.π i) := sorry

/-- **Theorem 4.7 (1), creation** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "jointly strictly creates all right and left Kan extensions" ↦ `JointlyStrictlyCreatesInitial` on
  the pushed left extensions and `JointlyStrictlyCreatesTerminal` on the pushed right extensions.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_creates {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
      JointlyStrictlyCreatesTerminal (fun i : ι => RightExt.push k d (P.π i)) := sorry

/-- **Theorem 4.7 (1), quotient initiality and subterminality** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $(c_i)_{i \in J}$ be a family of objects in $\K$ whose product $c = \prod_{i\in J} c_i$
exists in $\K$. Then the family $(\pi_i \colon c \to c_i)_{i\in J}$ of projections preserves and
jointly strictly creates all right and left Kan extensions. Additionally, the family of projections
jointly strictly creates and preserves (subterminality) quotient initiality of a (right) left
extension.
```

**Reading.**
* "jointly strictly creates and preserves (subterminality) quotient initiality" ↦ equivalence of
  `QuotientInitial L` with componentwise quotient initiality, together with
  `JointlyStrictlyCreatesQuotientInitial`, and dually for `Subterminal R` and
  `JointlyStrictlyCreatesSubterminal`.

**Deviations.** none recorded.
-/
theorem thm_4_7_1_quotient {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    (∀ L : LeftExt k d,
      QuotientInitial L ↔ ∀ i, QuotientInitial ((LeftExt.push k d (P.π i)).obj L)) ∧
    JointlyStrictlyCreatesQuotientInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
    (∀ R : RightExt k d,
      Subterminal R ↔ ∀ i, Subterminal ((RightExt.push k d (P.π i)).obj R)) ∧
    JointlyStrictlyCreatesSubterminal (fun i : ι => RightExt.push k d (P.π i)) := sorry

/-- **Theorem 4.7 (2), left Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Consider the inserter diagram
\[
\begin{tikzcd}
{\Ins(f,g)} \arrow[d, "u"'] \arrow[r, "u"]        & a \arrow[d, "g"] \\
a \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & b
\end{tikzcd}
\]
in $\K$. Then the morphism $u$ strictly creates left Kan extensions that $f$ preserves, and strictly
creates right Kan extensions that $g$ preserves.
```

**Reading.**
* "morphism $u$ strictly creates left Kan extensions that $f$ preserves" ↦
  `hf : PreservesLeftKan k (d ≫ Ins.u) f` implies `StrictlyCreatesLeftKan k d Ins.u`.

**Deviations.** none recorded.
-/
theorem thm_4_7_2_left {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hf : PreservesLeftKan k (d ≫ Ins.u) f) :
    StrictlyCreatesLeftKan k d Ins.u := sorry

/-- **Theorem 4.7 (2), right Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Consider the inserter diagram
\[
\begin{tikzcd}
{\Ins(f,g)} \arrow[d, "u"'] \arrow[r, "u"]        & a \arrow[d, "g"] \\
a \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & b
\end{tikzcd}
\]
in $\K$. Then the morphism $u$ strictly creates left Kan extensions that $f$ preserves, and strictly
creates right Kan extensions that $g$ preserves.
```

**Reading.**
* "morphism $u$ strictly creates right Kan extensions that $g$ preserves" ↦
  `hg : PreservesRightKan k (d ≫ Ins.u) g` implies `StrictlyCreatesRightKan k d Ins.u`.

**Deviations.** none recorded.
-/
theorem thm_4_7_2_right {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hg : PreservesRightKan k (d ≫ Ins.u) g) :
    StrictlyCreatesRightKan k d Ins.u := sorry

/-- **Theorem 4.7 (3), left Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $\Eq(\eta,\theta)\xrightarrow{u}c$ be the equifier of $\eta,\theta \colon f \Rightarrow g
\colon c \to c'$. Then $u$ strictly creates left (right) Kan extensions whose quotient initiality
(subterminality) is preserved by $f$ $(g)$.
```

**Reading.**
* "strictly creates left Kan extensions whose quotient initiality is preserved by $f$" ↦ hypothesis
  `hf` stating that initial left extensions are pushed by `f` to quotient initial objects, implying
  `StrictlyCreatesLeftKan k d E.e`.

**Deviations.** none recorded.
-/
theorem thm_4_7_3_left {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L)) :
    StrictlyCreatesLeftKan k d E.e := sorry

/-- **Theorem 4.7 (3), right Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $\K$ be a $2$-category. Then the following assertions hold:
```

```latex
\item Let $\Eq(\eta,\theta)\xrightarrow{u}c$ be the equifier of $\eta,\theta \colon f \Rightarrow g
\colon c \to c'$. Then $u$ strictly creates left (right) Kan extensions whose quotient initiality
(subterminality) is preserved by $f$ $(g)$.
```

**Reading.**
* "strictly creates right Kan extensions whose subterminality is preserved by $g$" ↦ hypothesis
  `hg` stating that terminal right extensions are pushed by `g` to subterminal objects, implying
  `StrictlyCreatesRightKan k d E.e`.

**Deviations.** none recorded.
-/
theorem thm_4_7_3_right {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : ∀ R : RightExt k (d ≫ E.e), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ E.e) g).obj R)) :
    StrictlyCreatesRightKan k d E.e := sorry

/-- **Corollary 4.8, left Kan extensions** ([forsman2026syntactic], §4; generalizing
[Ulmer1977Bialgebras], 3.3, 3.4).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Then the canonical
morphism $u_\B\colon \BialgB\to c$ strictly creates those left Kan extensions that $f$ preserves and
whose quotient initiality $f'$ preserves. Dually, $u_\B$ strictly creates those right Kan extensions
that $g$ preserves and whose subterminality is preserved by $g'$.
```

**Reading.**
* $u_\B$ strictly creates left Kan extensions ↦ `hf` (preservation by `B.f`) and `hf'` (preservation
  of quotient initiality by `B.f'`) imply `StrictlyCreatesLeftKan k d (B.uB E)`.

**Deviations.** none recorded.
-/
theorem cor_4_8_left (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) (hf : PreservesLeftKan k (d ≫ B.uB E) B.f)
    (hf' : ∀ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ B.uB E) B.f').obj L)) :
    StrictlyCreatesLeftKan k d (B.uB E) := sorry

/-- **Corollary 4.8, right Kan extensions** ([forsman2026syntactic], §4; generalizing
[Ulmer1977Bialgebras], 3.3, 3.4).

```latex
Let $\B = (c,\ f,g,\ f',g',\ \alpha,\beta)$ be a bialgebraic datum in $\K$. Then the canonical
morphism $u_\B\colon \BialgB\to c$ strictly creates those left Kan extensions that $f$ preserves and
whose quotient initiality $f'$ preserves. Dually, $u_\B$ strictly creates those right Kan extensions
that $g$ preserves and whose subterminality is preserved by $g'$.
```

**Reading.**
* $u_\B$ strictly creates right Kan extensions ↦ `hg` (preservation by `B.g`) and
  `hg'` (preservation of subterminality by `B.g'`) imply `StrictlyCreatesRightKan k d (B.uB E)`.

**Deviations.** none recorded.
-/
theorem cor_4_8_right (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) (hg : PreservesRightKan k (d ≫ B.uB E) B.g)
    (hg' : ∀ R : RightExt k (d ≫ B.uB E), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ B.uB E) B.g').obj R)) :
    StrictlyCreatesRightKan k d (B.uB E) := sorry

/-- **Corollary 4.10** ([forsman2026syntactic], §4).

```latex
For a bialgebraic datum $\B$ over $c$, the canonical morphism $u\colon \BialgB\to c$ strictly
creates $u$-absolute $k$-limits and $k$-colimits for every morphism $k$ in $\K$.
```

**Reading.**
* "$u$-absolute $k$-limits and $k$-colimits" ↦ `IsAbsoluteLeftKan` and `IsAbsoluteRightKan` on the
  pushed extensions.
* "strictly creates" ↦ `StrictlyCreatesLeftKan k d (B.uB E)` and
  `StrictlyCreatesRightKan k d (B.uB E)`.

**Deviations.** none recorded.
-/
theorem cor_4_10 (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) :
    ((∀ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L) →
        IsAbsoluteLeftKan k (d ≫ B.uB E) L) → StrictlyCreatesLeftKan k d (B.uB E)) ∧
    ((∀ R : RightExt k (d ≫ B.uB E), Nonempty (IsTerminal R) →
        IsAbsoluteRightKan k (d ≫ B.uB E) R) → StrictlyCreatesRightKan k d (B.uB E)) :=
  sorry

end General

section Model

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj]
  [HasChosenEquifiers.{u, v, w} Obj]
variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
  (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- **Corollary 4.11, left Kan extensions** ([forsman2026syntactic], §4).

```latex
Consider the canonical morphism $M^T\xrightarrow{u} M_0$. Then $u$ strictly creates those left Kan
extensions that $M(t_1)$ preserves and whose quotient initiality $M(t_1')$ preserves for each
function arity term $t_1$ and equational arity term $t_1'$. Dually, $u$ strictly creates those right
Kan extensions that $M(t_2)$ preserves and whose subterminality $M(t_2')$ preserves for each
function coarity term $t_2$ and equational coarity term $t_2'$.
```

**Reading.**
* $M(t_1)$ preserves left Kan extensions ↦ `hfn` (preservation by `M.funArity sg f`).
* $M(t_1')$ preserves quotient initiality ↦ `heq` (quotient initiality of pushed initial objects
  under `M.eqnArity sg T r`).
* "strictly creates" ↦ `StrictlyCreatesLeftKan k d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem cor_4_11_left {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesLeftKan k (d ≫ M.thyForget sg T) (M.funArity sg f))
    (heq : ∀ r : T.Eqn, ∀ L : LeftExt k (d ≫ M.thyForget sg T), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k _ (M.eqnArity sg T r)).obj L)) :
    StrictlyCreatesLeftKan k d (M.thyForget sg T) := sorry

/-- **Corollary 4.11, right Kan extensions** ([forsman2026syntactic], §4).

```latex
Consider the canonical morphism $M^T\xrightarrow{u} M_0$. Then $u$ strictly creates those left Kan
extensions that $M(t_1)$ preserves and whose quotient initiality $M(t_1')$ preserves for each
function arity term $t_1$ and equational arity term $t_1'$. Dually, $u$ strictly creates those right
Kan extensions that $M(t_2)$ preserves and whose subterminality $M(t_2')$ preserves for each
function coarity term $t_2$ and equational coarity term $t_2'$.
```

**Reading.**
* $M(t_2)$ preserves right Kan extensions ↦ `hfn` (preservation by `M.funCoarity sg f`).
* $M(t_2')$ preserves subterminality ↦ `heq` (subterminality of pushed terminal objects under
  `M.eqnCoarity sg T r`).
* "strictly creates" ↦ `StrictlyCreatesRightKan k d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem cor_4_11_right {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesRightKan k (d ≫ M.thyForget sg T) (M.funCoarity sg f))
    (heq : ∀ r : T.Eqn, ∀ R : RightExt k (d ≫ M.thyForget sg T), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k _ (M.eqnCoarity sg T r)).obj R)) :
    StrictlyCreatesRightKan k d (M.thyForget sg T) := sorry

/-- **Remark 4.11** ([forsman2026syntactic], §4).

```latex
Theorem \ref{thm:pie_kan_creation}(1) shows that all (co)algebraic theories $T$ are
$M$-relatively (co)algebraic in any $\Sigma$-model $M$. Corollary
\ref{cor:strictCreationToBialgebraicDatumObjectsKan} shows, for any morphism $k$ in $\K$, that the
$k$-(co)limits of $\BialgB$ are strictly created via the canonical morphism, when $\B$ is relatively
(co)algebraic.
```

**Reading.**
* "all algebraic theories strictly create right Kan extensions" ↦ `T.IsAlgebraic` implies
  `StrictlyCreatesRightKan k d (M.thyForget sg T)`.
* "all coalgebraic theories strictly create left Kan extensions" ↦ `T.IsCoalgebraic` implies
  `StrictlyCreatesLeftKan k d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem rem_4_11 {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T) :
    (T.IsAlgebraic → StrictlyCreatesRightKan k d (M.thyForget sg T)) ∧
      (T.IsCoalgebraic → StrictlyCreatesLeftKan k d (M.thyForget sg T)) := sorry

/-- **Corollary 4.12, left Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $k\colon I\to K$ be a morphism in $\K$. Assume each morphism $M(B)$ preserves $k$-colimits. Let
$t\colon c$ be a term in $\Term_S^\Sigma$. Then $M(t)\colon M_0\to M_c$ preserves all left Kan
extensions along $k$. In particular, the canonical morphism $u\colon M^T\to M_0$ strictly creates
$k$-colimits.
```

**Reading.**
* "each morphism $M(B)$ preserves $k$-colimits" ↦ `hB : ∀ B d, PreservesLeftKan k d (M.fn B)`.
* "$M(t)$ preserves all left Kan extensions along $k$" ↦ `PreservesLeftKan k d (M.tm sg t)`.
* "$u : M^T \to M_0$ strictly creates $k$-colimits" ↦
  `StrictlyCreatesLeftKan k d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem cor_4_12 {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesLeftKan k d (M.fn B)) :
    (∀ {c : Sg.Cat} (t : sg.CTrm c) (d : I ⟶ (M.P0 sg).pt), PreservesLeftKan k d (M.tm sg t)) ∧
      ∀ d : I ⟶ M.thyObj sg T, StrictlyCreatesLeftKan k d (M.thyForget sg T) := sorry

/-- **Corollary 4.12, right Kan extensions** ([forsman2026syntactic], §4).

```latex
Let $k\colon I\to K$ be a morphism in $\K$. Assume each morphism $M(B)$ preserves $k$-colimits. Let
$t\colon c$ be a term in $\Term_S^\Sigma$. Then $M(t)\colon M_0\to M_c$ preserves all left Kan
extensions along $k$. In particular, the canonical morphism $u\colon M^T\to M_0$ strictly creates
$k$-colimits.
```

**Reading.**
* Dual form for right Kan extensions / limits: `hB` for `PreservesRightKan` implies term
  preservation and strict creation of right Kan extensions along `k`.

**Deviations.**
- stronger: the right Kan form, which the paper does not state (CHALLENGE.md, *Stronger than the
  paper*).
-/
theorem cor_4_12_right {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesRightKan k d (M.fn B)) :
    (∀ {c : Sg.Cat} (t : sg.CTrm c) (d : I ⟶ (M.P0 sg).pt), PreservesRightKan k d (M.tm sg t)) ∧
      ∀ d : I ⟶ M.thyObj sg T, StrictlyCreatesRightKan k d (M.thyForget sg T) := sorry

end Model

/-! ## Classical consequences in `CAT` -/

section Classical

/-- **Corollary 4.13** ([forsman2026syntactic], §4).

```latex
We list some classical results that follow from our framework.
```

```latex
Let $T$ be a monad on a category $\C$. Then the forgetful functor $\C^T\to \C$ from the
Eilenberg--Moore category $\C^T$ of $T$ strictly creates limits and those colimits that $T$
preserves and whose quotient initiality $T^2$ preserves.
```

**Reading.**
* "forgetful functor $\C^T \to \C$" ↦ forgetful 1-cell from $T$-algebras to $C$:
  `T.forget` in `Cat`.
* "strictly creates limits" ↦ `StrictlyCreatesRightKan` along the forgetful 1-cell.
* "strictly creates colimits that $T$ preserves and whose quotient initiality $T^2$ preserves" ↦
  `PreservesLeftKan` for `T.toFunctor` and quotient initiality of pushed initial objects
  under the square functor imply `StrictlyCreatesLeftKan` for `T.forget`.

**Deviations.** none recorded.
-/
theorem cor_4_13 {C : Cat.{v, max u v}} (T : Monad (C : Type (max u v))) (I : Cat.{v, max u v})
    (d : I ⟶ Cat.of T.Algebra) :
    StrictlyCreatesRightKan (toOne I) d T.forget.toCatHom ∧
      (PreservesLeftKan (toOne I) (d ≫ T.forget.toCatHom)
          T.toFunctor.toCatHom →
        (∀ L : LeftExt (toOne I) (d ≫ T.forget.toCatHom),
          Nonempty (IsInitial L) →
            QuotientInitial ((LeftExt.push (toOne I) _
              (T.toFunctor ⋙ T.toFunctor).toCatHom).obj L)) →
        StrictlyCreatesLeftKan (toOne I) d T.forget.toCatHom) := sorry

/-- **Corollary 4.14** ([forsman2026syntactic], §4).

```latex
We list some classical results that follow from our framework.
```

```latex
Let $F\colon \C\to \E$ and $G\colon \D\to \E$ be functors. Then the forgetful functor $U\colon
F\downarrow G\to \C\times \D$ strictly creates those colimits and limits that $F$ and $G$ preserve,
respectively.
```

**Reading.**
* $F \downarrow G$ ↦ `Cat.of (Comma F.toFunctor G.toFunctor)`.
* "forgetful functor to $\C \times \D$" ↦ forgetful 1-cell in `Cat`.
* "strictly creates colimits that $F$ preserves and limits that $G$ preserves" ↦ paired implications
  for `StrictlyCreatesLeftKan` and `StrictlyCreatesRightKan`.

**Deviations.** none recorded.
-/
theorem cor_4_14 {C D E : Cat.{v, max u v}} (F : C ⟶ E) (G : D ⟶ E) (I : Cat.{v, max u v})
    (d : I ⟶ Cat.of (Comma F.toFunctor G.toFunctor)) :
    (PreservesLeftKan (toOne I)
        (d ≫ (Comma.fst _ _).toCatHom)
        F →
      StrictlyCreatesLeftKan (toOne I) d
        ((Comma.fst _ _).prod' (Comma.snd _ _)).toCatHom) ∧
    (PreservesRightKan (toOne I)
        (d ≫ (Comma.snd _ _).toCatHom)
        G →
      StrictlyCreatesRightKan (toOne I) d
        ((Comma.fst _ _).prod' (Comma.snd _ _)).toCatHom) :=
  sorry

/-- **Corollary 4.15** ([forsman2026syntactic], §4).

```latex
We list some classical results that follow from our framework.
```

```latex
Let $c$ be an object of a category $\C$. Then the forgetful functor $U\colon \C/c\to \C$ from the
slice category over $c$ strictly creates all colimits and connected limits.
```

**Reading.**
* "forgetful functor $\C/c \to \C$" ↦ `Over.forget c` in `Cat`.
* "strictly creates all colimits" ↦ `StrictlyCreatesLeftKan` along the forgetful 1-cell.
* "strictly creates all connected limits" ↦ `IsConnected (I : Type (max u v))` implies
  `StrictlyCreatesRightKan` along the forgetful 1-cell.

**Deviations.** none recorded.
-/
theorem cor_4_15 {C : Cat.{v, max u v}} (c : (C : Type (max u v))) (I : Cat.{v, max u v})
    (d : I ⟶ Cat.of (Over c)) :
    StrictlyCreatesLeftKan (toOne I) d (Over.forget c).toCatHom ∧
      (IsConnected (I : Type (max u v)) →
        StrictlyCreatesRightKan (toOne I) d (Over.forget c).toCatHom) := sorry

end Classical

/-! ## Sifted colimits and wide pushouts of regular epimorphisms -/

section Sifted

/-- **Lemma 4.16** ([forsman2026syntactic], §4; sifted categories as in
[AdamekRosickyVitale2010SiftedColimits], [Adamek-Rosicky-Vitale]).

```latex
Let $F\colon \C \to \D$ be a functor, where $\C = \C_1\times\cdots \times \C_n$.
Let $D = (D_i)_i\colon I\to \C$ be a diagram with a colimit and assume $I$ is a sifted category.
Then $F$ preserves the colimit of $D$ if $F$ preserves the colimit of $D$ componentwise, meaning
for any object $(c_i)_i$ in $\C$ the functor $x_i\mapsto F(c_1,\ldots,x_i,\ldots, c_n)\colon
\C_i\to \D$ preserves the colimit of $D_i$ for $i\leq n$.
```

**Reading.**
* "$\C = \C_1 \times \cdots \times \C_n$" ↦ `(∀ i, C i)` with `[Finite ι] [DecidableEq ι]`.
* "componentwise preservation", with `updateFunctor x i ⋙ F` the functor `x_i ↦ F(c_1, …, x_i, …)`
  ↦ `h : ∀ i x, PreservesColimit (D ⋙ Pi.eval C i) (updateFunctor x i ⋙ F)`.
* "preserves the colimit of $D$" ↦ `PreservesColimit D F`.

**Deviations.** none recorded.
-/
theorem lem_4_16 {ι : Type*} [Finite ι] [DecidableEq ι] {C : ι → Type u}
    [∀ i, Category.{v} (C i)] {E : Type*} [Category E] (F : (∀ i, C i) ⥤ E)
    {J : Type w} [Category.{w} J] [IsSifted J] (D : J ⥤ ∀ i, C i) [HasColimit D]
    (h : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimit (D ⋙ Pi.eval C i) (updateFunctor x i ⋙ F)) :
    PreservesColimit D F := sorry

/-- **Corollary 4.17** ([forsman2026syntactic], §4).

```latex
Let $(\Sigma, \sigma)$ be a signature pair with a $\sigma$-theory $T$. Let $M$ be a categorical
$\Sigma$-model and $I$ be a sifted category. If $M(B)$ preserves $I$-colimits componentwise for each
$\Sigma$-functor symbol $B$, then the forgetful functor $U\colon M^T\to M_0$ strictly creates all
$I$-indexed colimits.
```

**Reading.**
* "$M(B)$ preserves $I$-colimits componentwise" ↦ `hB : ∀ B, PreservesColimitsComponentwise M I B`.
* "strictly creates all $I$-indexed colimits" ↦
  `StrictlyCreatesLeftKan (toOne I) d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem cor_4_17 {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    (I : Cat.{v, max u v}) [IsSifted (I : Type (max u v))]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M I B) (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan (toOne I) d (M.thyForget sg T) := sorry

/-- **Corollary 4.18** ([forsman2026syntactic], §4).

```latex
Let $\otimes\colon \C_1\times\cdots\times \C_n\to \C$ be a functor. Assume for each $i\leq n$ that
every regular epimorphism in $\C_i$ is a coequalizer of a reflexive pair. Let $I$ be a set of
cardinality at least $2$. If $\otimes$ preserves $I$-indexed pushouts of regular epimorphisms
componentwise, then it preserves such pushouts and regular epimorphisms.
```

**Reading.**
* "cardinality at least 2" ↦ `(K : Type w) [Nontrivial K]`.
* "regular epis are reflexive coequalizers" ↦ `hC : ∀ i, RegEpisAreReflexiveCoequalizers (C i)`.
* "componentwise preservation" ↦
  `hF : ∀ i x, PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙ F)` (as in `lem_4_16`).
* "preserves pushouts and regular epimorphisms" ↦ `PreservesWidePushoutsOfRegEpis K F` and
  preservation of `RegularEpi`.

**Deviations.** none recorded.
-/
theorem cor_4_18 {n : ℕ} {C : Fin n → Type u} [∀ i, Category.{v} (C i)] {E : Type*}
    [Category E] (F : (∀ i, C i) ⥤ E) (K : Type w) [Nontrivial K]
    (hC : ∀ i, RegEpisAreReflexiveCoequalizers (C i))
    (hF : ∀ (i : Fin n) (x : ∀ j, C j), PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙ F)) :
    PreservesWidePushoutsOfRegEpis K F ∧
      ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), Nonempty (RegularEpi f) → Nonempty (RegularEpi (F.map f)) :=
  sorry

/-- **Theorem 4.19** ([forsman2026syntactic], §4).

```latex
Let $(\Sigma,\sigma)$ be a signature pair,  $T$ a $\sigma$-theory, $M$ a $\Sigma$-model in $\CAT$,
and $I$ a set with cardinality at least $2$. Assume in each category $M_c$ regular epimorphisms are
reflexive coequalizers and each functor $M(B)$ preserves $I$-indexed wide pushouts of regular epis
componentwise. Let $f_i\colon a\to b_i$ be morphisms in $M^T$ such that $Uf_i$ is a regular
epimorphism for each $i\in I$. Then the forgetful functor $U\colon M^T\to M_0$ strictly creates the
$I$-indexed pushout of $(f_i)_{i\in I}$.
```

**Reading.**
* "cardinality at least 2", the wide pushout ↦ `(K : Type w) [Nontrivial K]` and
  `e : WidePushoutShape K ≌ (J : Type u)`, so the size of `K` is free.
* "$Uf_i$ is a regular epimorphism" ↦ `hd`, on the legs of `d` under `U = M.thyForget sg T`.
* "strictly creates the wide pushout" ↦ `StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T)`.

**Deviations.** none recorded.
-/
theorem thm_4_19 [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}] {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, u})
    (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] (K : Type w) [Nontrivial K]
    (hreg : ∀ c : Sg.Cat, RegEpisAreReflexiveCoequalizers (M.obj c : Type u))
    (hB : ∀ (B : Sg.Fun) (i : Fin (Sg.arn B)) (x : ∀ j, (M.obj (Sg.art B j) : Type u)),
      PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙
        (M.fn B).toFunctor))
    (J : Cat.{v, u}) (e : WidePushoutShape K ≌ (J : Type u))
    (d : J ⟶ M.thyObj sg T)
    (hd : ∀ j, Nonempty (RegularEpi ((d ≫ M.thyForget sg T).toFunctor.map
        (e.functor.map (WidePushoutShape.Hom.init j))))) :
    StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T) := sorry

end Sifted

/-! ## Fields -/

/-- **Corollary 4.21** ([forsman2026syntactic], §4).

```latex
The category $\mathbf{Field}$ of fields is accessible, and the forgetful functor $\mathbf{Field}\to
\mathbf{Set}, k\mapsto k^*,$ creates connected limits and sifted colimits.
```

**Reading.**
* "$\mathbf{Field}$", "$k\mapsto k^*$" ↦ `FieldEx.FieldCat.{u}` (not in Mathlib), `fieldUnits.{u}`.
* "$\mathbf{Field}$ is accessible" ↦ `IsAccessibleCategory.{u} FieldEx.FieldCat.{u}`.
* "creates connected limits and sifted colimits" ↦ `Nonempty (CreatesLimitsOfShape J _)` for
  `[IsConnected J]`, and `Nonempty (CreatesColimitsOfShape J _)` for `[IsSifted J]`.

**Deviations.** none recorded.
-/
theorem cor_4_21 :
    IsAccessibleCategory.{u} FieldEx.FieldCat.{u} ∧
      (∀ (J : Type u) [SmallCategory J] [IsConnected J],
        Nonempty (CreatesLimitsOfShape J fieldUnits.{u})) ∧
      (∀ (J : Type u) [SmallCategory J] [IsSifted J],
        Nonempty (CreatesColimitsOfShape J fieldUnits.{u})) := sorry

end UlmerBialgebras.Paper
