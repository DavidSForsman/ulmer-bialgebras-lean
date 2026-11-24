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

/-! ## Section 5: free algebras, monadicity, local presentability -/

section ChainColimits

end ChainColimits

section Sec51

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Lemma 5.2** ([forsman2026syntactic], §5).

```latex
Let $g\colon d\to c$ be a morphism in a $2$-category $\K$. Then $g$ is monadic if and only if $g$
is a right adjoint and $g_x\colon \K(x,d)\to \K(x,c)$ creates $g_x$-split coequalizers for each
object $x$ in $\K$.
```

**Reading.**
* "morphism in a $2$-category $\K$" ↦ `g : d ⟶ c` in
  `[Bicategory.{w, v} Obj] [Bicategory.Strict Obj]`.
* "monadic" ↦ `IsMonadic2 g` (Definition 5.1).
* "right adjoint" ↦ `∃ f : c ⟶ d, Nonempty (TwoAdj f g)`.
* "$g_x$ creates $g_x$-split coequalizers" ↦
  `CreatesColimit (parallelPair h₁ h₂) (postcomp x g)` for each split pair `(h₁, h₂)`.

**Deviations.** none recorded.
-/
theorem lem_5_2 {c d : Obj} (g : d ⟶ c) :
    IsMonadic2 g ↔ (∃ f : c ⟶ d, Nonempty (TwoAdj f g)) ∧
      ∀ (x : Obj) ⦃A B : x ⟶ d⦄ (h₁ h₂ : A ⟶ B), (postcomp x g).IsSplitPair h₁ h₂ →
        Nonempty (CreatesColimit (parallelPair h₁ h₂) (postcomp x g)) := sorry

/-- **Corollary 5.3** ([forsman2026syntactic], §5).

```latex
Consider the following commutative diagram in a $2$-category $\K$:
$$
\begin{tikzcd}
a \arrow[rd, "u"'] \arrow[rr, "g"] &   &b \arrow[ld, "v"] \\
                                   & c &                      
\end{tikzcd}
$$
```

```latex
Assume $g$ is a right adjoint and, for each object $x$ in $\K$, the functor $v_x\colon
\K(x,b)\to\K(x,c)$ is conservative and $u_x\colon \K(x,a)\to\K(x,c)$ creates $u_x$-split
coequalizers. Then $g$ is monadic.
```

**Reading.**
* diagram $u = v g$ ↦ `g ≫ v = u`.
* "$g$ is a right adjoint" ↦ `∃ f : b ⟶ a, Nonempty (TwoAdj f g)`.
* "$v_x$ is conservative" ↦ conservativity of `postcomp x v`.
* "$u_x$ creates $u_x$-split coequalizers" ↦
  `CreatesColimit (parallelPair h₁ h₂) (postcomp x u)` for each split pair `(h₁, h₂)`.
* "$g$ is monadic" ↦ `IsMonadic2 g`.

**Deviations.** none recorded.
-/
theorem cor_5_3 {a b c : Obj} (g : a ⟶ b) (u : a ⟶ c) (v : b ⟶ c) (htri : g ≫ v = u)
    (hg : ∃ f : b ⟶ a, Nonempty (TwoAdj f g))
    (hv : ∀ x : Obj, (postcomp x v).ReflectsIsomorphisms)
    (hu : ∀ (x : Obj) ⦃A B : x ⟶ a⦄ (h₁ h₂ : A ⟶ B), (postcomp x u).IsSplitPair h₁ h₂ →
      Nonempty (CreatesColimit (parallelPair h₁ h₂) (postcomp x u))) :
    IsMonadic2 g := sorry

/-- **Corollary 5.3, bialgebraic clause** ([forsman2026syntactic], §5).

```latex
Consider the following commutative diagram in a $2$-category $\K$:
$$
\begin{tikzcd}
a \arrow[rd, "u"'] \arrow[rr, "g"] &   &b \arrow[ld, "v"] \\
                                   & c &                      
\end{tikzcd}
$$
```

```latex
In particular, for any bialgebraic data $\B$ and $\B'$ in $\K$ over the same object $c$ in $\K$, a
(left) right adjoint $g\colon \BialgB\to \Bialg(\B')$, where $u_{\B'}g = u_\B$, is (co)monadic.
```

**Reading.**
* "bialgebraic data $\B$ and $\B'$ in $\K$ over the same object $c$" ↦
  `B B' : BialgDatum (Obj := Obj)` with `hc : B'.c = B.c`.
* "right adjoint $g$ where $u_{\B'} g = u_\B$" ↦ `g : E.pt ⟶ E'.pt`,
  `∃ f : E'.pt ⟶ E.pt, Nonempty (TwoAdj f g)`, and triangle `g ≫ B'.uB E' = B.uB E`.
* "$g$ is monadic" ↦ `IsMonadic2 g`.
* dual comonadicity clause: comonadic when $g$ is a left adjoint (Solution/CoMonadic.lean).

**Deviations.**
- stronger: holds in any strict 2-category without chosen inserters or equifiers (CHALLENGE.md,
  *Stronger than the paper*).
-/
theorem cor_5_3_bialg (B B' : BialgDatum (Obj := Obj)) (hc : B'.c = B.c)
    (E : Equifier B.α B.β) (E' : Equifier B'.α B'.β) (g : E.pt ⟶ E'.pt)
    (htri : g ≫ (B'.uB E' ≫ castHom hc) = B.uB E) :
    ((∃ f : E'.pt ⟶ E.pt, Nonempty (TwoAdj f g)) → IsMonadic2 g) ∧
      ((∃ h : E'.pt ⟶ E.pt, Nonempty (TwoAdj g h)) → IsComonadic2 g) := sorry

end Sec51

section Thm55

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Theorem 5.5 (1)** ([forsman2026syntactic], §5).

```latex
Let $\kappa$ be an infinite cardinal and let $F,G\colon \C\to \D$ be functors with $\C$
$\kappa_\leq$-cocomplete. Assume that $G$ has an $F$-relative left adjoint $L$.\footnote{An
$F$-relative left adjoint $L$ for $G$ means that there is an isomorphism
$\hom(Lx,y)\cong\hom(Fx,Gy)$ natural in $x$ and $y$. If $G$ has a left adjoint $l$, then $L \cong
lF$ \cite{ulmerPropertiesDenseRelative1968}} Then the following assertions hold:
```

```latex
\item If $\C$ has finite coproducts and $F$ preserves $\kappa$-colimits, then $U\colon
\Ins(F,G)\to \C$ is monadic.
```

**Reading.**
* "$\kappa_\leq$-cocomplete" ↦ `HasChainColimitsUpTo κ C`.
* "$G$ has an $F$-relative left adjoint $L$" ↦ `ra : RelLeftAdjoint F G L`.
* "$F$ preserves $\kappa$-colimits" ↦ `PreservesColimitsOfShape κ.ord.ToType F`.
* "$U\colon \Ins(F,G)\to \C$ is monadic" ↦ `MonadicRightAdjoint (Ins.forget F G)`.

**Deviations.** none recorded.
-/
theorem thm_5_5_1 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (hC : HasChainColimitsUpTo κ C) [HasFiniteCoproducts C]
    (hF : PreservesColimitsOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Ins.forget F G)) := sorry

/-- **Theorem 5.5 (2)** ([forsman2026syntactic], §5).

```latex
Let $\kappa$ be an infinite cardinal and let $F,G\colon \C\to \D$ be functors with $\C$
$\kappa_\leq$-cocomplete. Assume that $G$ has an $F$-relative left adjoint $L$.\footnote{An
$F$-relative left adjoint $L$ for $G$ means that there is an isomorphism
$\hom(Lx,y)\cong\hom(Fx,Gy)$ natural in $x$ and $y$. If $G$ has a left adjoint $l$, then $L \cong
lF$ \cite{ulmerPropertiesDenseRelative1968}} Then the following assertions hold:
```

```latex
\item Let $\alpha,\beta\colon F\Rightarrow G$ be natural transformations. If $\C$ has coequalizers
and $F$ preserves joint epicness of colimiting cocones of $\kappa$-chains, then the forgetful
functor $U\colon \Eq(\alpha,\beta)\to \C$ is monadic.
```

**Reading.**
* "$\kappa_\leq$-cocomplete" ↦ `HasChainColimitsUpTo κ C`.
* "$G$ has an $F$-relative left adjoint $L$" ↦ `ra : RelLeftAdjoint F G L`.
* "$F$ preserves joint epicness of colimiting cocones of $\kappa$-chains" ↦
  `PreservesJointEpiOfShape κ.ord.ToType F`.
* "$U\colon \Eq(\alpha,\beta)\to \C$ is monadic" ↦ `MonadicRightAdjoint (Equif.forget α β)`.

**Deviations.** none recorded.
-/
theorem thm_5_5_2 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (α β : F ⟶ G) (hC : HasChainColimitsUpTo κ C)
    [HasCoequalizers C] (hF : PreservesJointEpiOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Equif.forget α β)) := sorry

end Thm55

section Lem56

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Lemma 5.6** ([forsman2026syntactic], §5).

```latex
Let $\K$ be a $2$-category with a morphism $f\colon c\to c$. Consider the inserter diagram
$$
\begin{tikzcd}
{\Ins(f,\id_c)} \arrow[d, "u"'] \arrow[r, "u"] & c \arrow[d, "\id_c"] \\
c \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & c
\end{tikzcd}
$$
in $\K$. Let $K\xleftarrow{k}I\xrightarrow{d} \Ins(f,\id_c)$ be a span in $\K$. Assume that
$\K(K,c)$ has pushouts and the left Kan extensions $(l_1,\eta_1\colon ud\Rightarrow l_1k)$ and
$(l_2,\eta_2\colon fud\Rightarrow l_2k)$ of $ud$ and $fud$ along $k$ exist. Consider the pushout
induced endofunctor
$$
H = (l_1,\eta_1)+_{l_2} f_*(-)\colon \LE(ud,k)\to \LE(ud,k).
$$
```

```latex
In particular, if $\K(K,c)$ has $\kappa_\leq$-colimits and $f_K$ preserves colimits of
$\kappa$-chains for some infinite cardinal $\kappa$, then $u_*\colon \LE(d,k)\to \LE(ud,k)$ has a
left adjoint and $d\colon I\to \Ins(f,\id_c)$ has a left Kan extension along $k$.
```

**Reading.**
* "$\K(K,c)$ has $\kappa_\leq$-colimits" ↦ `HasChainColimitsUpTo κ (X ⟶ c)`.
* "$f_K$ preserves colimits of $\kappa$-chains" ↦
  `PreservesColimitsOfShape κ.ord.ToType (postcomp X f)`.
* "$u_*$ has a left adjoint and $d$ has a left Kan extension along $k$" ↦
  existence of an adjoint to `LeftExt.push k d Ins.u` and existence of initial object in
  `LeftExt k d`.

**Deviations.** none recorded.
-/
theorem lem_5_6 {c : Obj} (f : c ⟶ c) (Ins : Inserter f (𝟙 c)) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ Ins.pt) (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ)
    [HasPushouts (X ⟶ c)] (hch : HasChainColimitsUpTo κ (X ⟶ c))
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp X f))
    (h1 : ∃ L : LeftExt k (d ≫ Ins.u), Nonempty (IsInitial L))
    (h2 : ∃ L : LeftExt k ((d ≫ Ins.u) ≫ f), Nonempty (IsInitial L)) :
    (LeftExt.push k d Ins.u).IsRightAdjoint ∧ ∃ L : LeftExt k d, Nonempty (IsInitial L) :=
  sorry

/-- **Lemma 5.6, isomorphism clause** ([forsman2026syntactic], §5).

```latex
Let $\K$ be a $2$-category with a morphism $f\colon c\to c$. Consider the inserter diagram
$$
\begin{tikzcd}
{\Ins(f,\id_c)} \arrow[d, "u"'] \arrow[r, "u"] & c \arrow[d, "\id_c"] \\
c \arrow[r, "f"'] \arrow[ru, "\phi" description, Rightarrow] & c
\end{tikzcd}
$$
in $\K$. Let $K\xleftarrow{k}I\xrightarrow{d} \Ins(f,\id_c)$ be a span in $\K$. Assume that
$\K(K,c)$ has pushouts and the left Kan extensions $(l_1,\eta_1\colon ud\Rightarrow l_1k)$ and
$(l_2,\eta_2\colon fud\Rightarrow l_2k)$ of $ud$ and $fud$ along $k$ exist. Consider the pushout
induced endofunctor
$$
H = (l_1,\eta_1)+_{l_2} f_*(-)\colon \LE(ud,k)\to \LE(ud,k).
$$
```

```latex
Then there is an isomorphism of categories $\LE(d,k) \cong \Ins(H,\id)$ over $\LE(ud,k)$ with $H$
preserving those connected colimits that exist in $\K(K,c)$ and are preserved by $f_K\colon
\K(K,c)\to \K(K,c)$.
```

**Reading.**
* $\LE(d, k) \cong \Ins(H, \id)$ over $\LE(ud, k)$ ↦ equivalence
  functor `F : LeftExt k d ⥤ Endofunctor.Algebra ...` compatible with the forgetful functors
  `F ⋙ Endofunctor.Algebra.forget _ = LeftExt.push k d Ins.u`.
* preservation of connected colimits ↦ `PreservesColimit (W ⋙ LeftExt.forget k _) (postcomp X f)`.

**Deviations.** none recorded.
-/
theorem lem_5_6_iso {c : Obj} (f : c ⟶ c) (Ins : Inserter f (𝟙 c)) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) [HasPushouts (X ⟶ c)]
    (e₁ : LeftExt k (d ≫ Ins.u)) (he₁ : IsInitial e₁)
    (e₂ : LeftExt k ((d ≫ Ins.u) ≫ f)) (he₂ : IsInitial e₂) :
    (∃ F : LeftExt k d ⥤ Endofunctor.Algebra (LeftExt.pushoutStep k (Ins.phiAtId d) e₁ he₂),
      Function.Bijective F.obj ∧ F.Full ∧ F.Faithful ∧
        F ⋙ Endofunctor.Algebra.forget _ = LeftExt.push k d Ins.u) ∧
    ∀ {J : Type u'} [Category.{v'} J] [IsConnected J] (W : J ⥤ LeftExt k (d ≫ Ins.u)),
      HasColimit (W ⋙ LeftExt.forget k (d ≫ Ins.u)) →
        PreservesColimit (W ⋙ LeftExt.forget k (d ≫ Ins.u)) (postcomp X f) →
          PreservesColimit W (LeftExt.pushoutStep k (Ins.phiAtId d) e₁ he₂) := sorry

end Lem56

section Thm57

/-- **Theorem 5.7** ([forsman2026syntactic], §5).

```latex
Fix an infinite cardinal $\kappa$. Let $\B = (\C,\ F,G,\ F',G',\ \alpha, \beta)$ be a bialgebraic
datum in $\CAT$. Assume the following:
\begin{enumerate}
    \item Functors $G$ and $G'$ have $F$- and $F'$-relative left adjoints $L_1$ and $L_2$,
    respectively.
    \item The category $\C$ has colimits of size at most $\kappa$.
    \item The functor $F$ preserves the colimiting cocones of $\kappa$-chains and $F'$ their
    joint epicness.
\end{enumerate}
Then $U\colon \BialgB\to \C$ is monadic and $\BialgB$ has colimits of size at most $\kappa$.
Furthermore, if $K\xleftarrow{k} I\xrightarrow{d}\BialgB$ is a span of functors, where the left
Kan extensions of $Ud$ and $L_1Ud$ along $k$ exist, then the left Kan extension of $d$ along $k$
exists.
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{w, max u w}`.
* "Functors $G$ and $G'$ have relative left adjoints" ↦ relative left adjoint hypotheses
  `r₁` and `r₂` on the component functors.
* "$\C$ has colimits of size at most $\kappa$" ↦ `HasColimitsOfSizeLE κ (B.c : Type (max u w))`.
* "$U$ is monadic and $\BialgB$ has colimits of size at most $\kappa$" ↦
  monadicity of `B.uB E` and `HasColimitsOfSizeLE κ (E.pt : Type (max u w))`.
* detection of left Kan extensions ↦ Mathlib's `k.HasLeftKanExtension`: if those of $Ud$ and
  $L_1Ud$ exist, so does that of `d`.
* "a span of functors" $K\xleftarrow{k} I\xrightarrow{d}\BialgB$ ↦ any categories
  `I : Type u₁`, `Kc : Type u₂` with `Category.{v₁} I`, `Category.{v₂} Kc`, of sizes independent of
  `CAT`'s, as in `cor_5_8`.

**Deviations.**
- different (size): in `Cat.{w, max u w}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_5_7 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ)
    (B : BialgDatum (Obj := Cat.{w, max u w})) (E : Equifier B.α B.β)
    (L₁ L₂ : (B.c : Type (max u w)) ⥤ B.c)
    (r₁ : RelLeftAdjoint (B.f).toFunctor B.g.toFunctor L₁)
    (r₂ : RelLeftAdjoint (B.f').toFunctor B.g'.toFunctor L₂)
    (hC : HasColimitsOfSizeLE κ (B.c : Type (max u w)))
    (hF : PreservesColimitsOfShape κ.ord.ToType (B.f).toFunctor)
    (hF' : PreservesJointEpiOfShape κ.ord.ToType (B.f').toFunctor) :
    Nonempty (MonadicRightAdjoint (B.uB E).toFunctor) ∧
      HasColimitsOfSizeLE κ (E.pt : Type (max u w)) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (E.pt : Type (max u w)))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (B.uB E).toFunctor) →
          k.HasLeftKanExtension ((d ⋙ (B.uB E).toFunctor) ⋙ L₁) →
            k.HasLeftKanExtension d := sorry

/-- **Corollary 5.8** ([forsman2026syntactic], §5).

```latex
Let $\kappa$ and $\lambda$ be infinite cardinals. Let $(\Sigma,\sigma)$ be a signature pair with at
most $\lambda$-many symbols with an algebraic $\sigma$-theory $T$. Let $M$ be a categorical
$\Sigma$-model. Assume the following:
\begin{enumerate}
    \item Each category $M_c$ has colimits of size at most $\max(\lambda,\kappa)$.
    \item Each functor $M(B)$ preserves $\kappa$-colimits componentwise.
\end{enumerate}
Then the forgetful functor $M^T\to M_0$ is monadic and $M^T$ has colimits of size at most
$\max(\lambda,\kappa)$. Moreover, for any span $K\xleftarrow{k} I\xrightarrow{d} M^T$ of functors,
the left Kan extension of $d$ along $k$ exists if $Ud$ and $M(t_1)Ud$ have left Kan extensions along
$k$ for every function arity term $t_1$.
```

**Reading.**
* categorical model ↦ `M : Model Sg Cat.{v, u}`.
* algebraic theory ↦ `T : Theory sg`, `T.IsAlgebraic`.
* size bounds compared after `Cardinal.lift`: `Cardinal.lift.{u} κ`, `Cardinal.lift.{u} lam`.
* "forgetful functor $M^T \to M_0$ is monadic" ↦
  `Nonempty (MonadicRightAdjoint (M.thyForget sg T))`.

**Deviations.**
- different (size): in `Cat.{v, u}`, its instances as arguments (CHALLENGE.md, *Size migration*).
-/
theorem cor_5_8 (κ lam : Cardinal.{v}) (hκ : Cardinal.aleph0 ≤ κ) (hlam : Cardinal.aleph0 ≤ lam)
    {Sg : TwoSig.{t₁, t₂, t₃}} (sg : OneSig.{t₁, t₂, t₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, u}] [HasChosenProductsOfSize.{s₂} Cat.{v, u}]
    (T : Theory.{t₁, t₂, t₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, u}]
    (M : Model Sg Cat.{v, u}) [HasChosenInserters Cat.{v, u}] [HasChosenEquifiers Cat.{v, u}]
    (hsize : Cardinal.lift.{v} (Cardinal.mk Sg.Cat) ≤ Cardinal.lift.{t₁} lam ∧
      Cardinal.lift.{v} (Cardinal.mk Sg.Fun) ≤ Cardinal.lift.{t₂} lam ∧
      Cardinal.lift.{v} (Cardinal.mk Sg.Tr) ≤ Cardinal.lift.{t₃} lam ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Srt) ≤ Cardinal.lift.{s₁} lam ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Fn) ≤ Cardinal.lift.{s₂} lam)
    (halg : T.IsAlgebraic)
    (hcol : ∀ c : Sg.Cat, HasColimitsOfSizeLE (max lam κ) (M.obj c : Type u))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M κ.ord.ToType B) :
    Nonempty (MonadicRightAdjoint
        (M.thyForget sg T).toFunctor) ∧
      HasColimitsOfSizeLE (max lam κ) (M.thyObj sg T : Type u) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (M.thyObj sg T : Type u))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (M.thyForget sg T).toFunctor) →
          (∀ f : sg.Fn, k.HasLeftKanExtension
            ((d ⋙ (M.thyForget sg T).toFunctor) ⋙
              (M.funArity sg f).toFunctor)) →
            k.HasLeftKanExtension d := sorry

/-- **Corollary 5.9, small shapes** ([forsman2026syntactic]): the companion of Corollary 5.9
(`UniversalAlgebra.modelCat_monadic`, `UniversalAlgebra.modelCat_strictlyCreates`) for countable
sifted shapes of any size that are small with respect to `C`, stated for an algebraic
single-sorted `Σ_Cart`-theory.

```latex
the forgetful functor $U\colon \C^T\to \C$ is monadic and $U$ strictly creates countable sifted
colimits.
```

**Reading.**
* "countable sifted colimits" ↦ any sifted `J : Type w` with `[Category.{w} J]`, `u`-small and
  locally `v`-small (`[Small.{u} J]`, `[LocallySmall.{v} J]`), with countably many objects, so
  that the shape need not be a 1-cell of `Cat.{v, u}`.
* "creates" ↦ Mathlib's `CreatesColimitsOfShape` for `J` and the forgetful functor (creation up to
  isomorphism, as a `Nonempty`); the strict form is `UniversalAlgebra.modelCat_strictlyCreates`.

**Deviations.**
- different (size): any `[Category.{v} C]`, `Cat.{v, u}` instances (CHALLENGE.md, *Size migration*).
- different: stated for an algebraic single-sorted `Σ_Cart`-theory `T : Theory sg` with
  `Cardinal.mk sg.Srt = 1` and `Cardinal.mk sg.Fn ≤ Cardinal.aleph0`, not for an `MSLanguage`
  theory.
- different: creation in Mathlib's sense, up to isomorphism (chosen by the author).
-/
theorem cor_5_9_small {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{v} C)
    (sg : OneSig.{0, 0, 0, s₁, s₂} Cart.sigCart) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{0, 0, 0, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}]
    (hsingle : Cardinal.mk sg.Srt = 1)
    (hsize : Cardinal.mk sg.Fn ≤ Cardinal.aleph0)
    (halg : T.IsAlgebraic) (J : Type w) [Category.{w} J] [Small.{u} J] [LocallySmall.{v} J]
    [IsSifted J] (hJ : Cardinal.mk J ≤ Cardinal.aleph0) :
    Nonempty (CreatesColimitsOfShape J ((Cart.cartModel C).thyForget sg T).toFunctor) := sorry

end Thm57

section AAFT

/-- **Theorem 5.10 (1)** ([forsman2026syntactic], §5).

```latex
Let $F\colon \C\to \D$ be a functor with $\C$ locally presentable. Then the following hold:
```

```latex
\item If $F$ preserves colimits and $\D$ is locally small, then $F$ is a left adjoint.
```

**Reading.**
* "$\C$ locally presentable" ↦ `IsLocallyPresentable C`.
* "$F$ preserves colimits and $\D$ is locally small" ↦ `PreservesColimitsOfSize.{w, w} F` with
  `D : Type u'` and `[Category.{v'} D]` (locally small).
* "$F$ is a left adjoint" ↦ `F.IsLeftAdjoint`.

**Deviations.** none recorded.
-/
theorem thm_5_10_1 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{v'} D]
    [IsLocallyPresentable.{w} C] [LocallySmall.{w} D] (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F] : F.IsLeftAdjoint := sorry

/-- **Theorem 5.10 (2)** ([forsman2026syntactic], §5).

```latex
Let $F\colon \C\to \D$ be a functor with $\C$ locally presentable. Then the following hold:
```

```latex
\item If $F$ is continuous and accessible, then $F$ is a right adjoint.
```

**Reading.**
* "$\C$ locally presentable" ↦ `IsLocallyPresentable C`.
* "$F$ is continuous and accessible" ↦ `PreservesLimitsOfSize.{w, w} F` and
  `Functor.IsAccessible.{w} F`.
* "accessible" (in the paper's sense: between accessible categories) ↦
  `Functor.IsAccessible.{w} F` plus `IsAccessibleCategory.{w} D` (`C` is locally presentable);
  Mathlib's predicate does not include the latter.
* "$F$ is a right adjoint" ↦ `F.IsRightAdjoint`.

**Deviations.** none recorded.
-/
theorem thm_5_10_2 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]
    [IsLocallyPresentable.{w} C] [IsAccessibleCategory.{w} D] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w} F] [Functor.IsAccessible.{w} F] : F.IsRightAdjoint := sorry

/-- **Theorem 5.11** ([forsman2026syntactic], §5).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$ with $\C$ locally
presentable and $F,F',G,G'$ accessible. Then $U_\B\colon \BialgB\to \C$ is accessible and the
following hold:
\begin{enumerate}
    \item If $G$ is continuous and $G'$ preserves joint monicness of limiting cones, then $\BialgB$
    is locally presentable and the forgetful functor $U_\B\colon \BialgB\to \C$ is monadic.
    \item If $F$ preserves colimiting cocones and $F'$ preserves their joint epicness, then
    $\BialgB$ is locally presentable and $U_\B$ is comonadic.
\end{enumerate}
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{w, u}`: categories with morphisms
  in `Type w` and objects in any universe `Type u`.
* "$\C$ locally presentable and $F,F',G,G'$ accessible" ↦
  `IsLocallyPresentable (B.c : Type u)` and accessibility instances on functors.
* "accessible" (in the paper's sense: between accessible categories) ↦ `Functor.IsAccessible.{w}`
  on `F, G, F', G'` plus `IsAccessibleCategory.{w}` on `B.x` and `B.y` (`B.c` is locally
  presentable); Mathlib's predicate does not include the latter.
* "$U_\B$ is accessible" ↦ `IsAccessibleCategory.{w} (E.pt : Type u)` and
  `Functor.IsAccessible.{w}` for `B.uB E`, the first conjunct.
* item 1 conclusion ↦ `IsLocallyPresentable (E.pt : Type u)` and
  monadicity of the forgetful functor `B.uB E`.
* item 2 conclusion ↦ `IsLocallyPresentable (E.pt : Type u)` and
  comonadicity of the forgetful functor `B.uB E`.

**Deviations.** none recorded.
-/
theorem thm_5_11 (B : BialgDatum (Obj := Cat.{w, u})) (E : Equifier B.α B.β)
    [IsLocallyPresentable.{w} (B.c : Type u)]
    [IsAccessibleCategory.{w} (B.x : Type u)] [IsAccessibleCategory.{w} (B.y : Type u)]
    [Functor.IsAccessible.{w} (B.f).toFunctor]
    [Functor.IsAccessible.{w} (B.g).toFunctor]
    [Functor.IsAccessible.{w} (B.f').toFunctor]
    [Functor.IsAccessible.{w} (B.g').toFunctor] :
    (IsAccessibleCategory.{w} (E.pt : Type u) ∧
      Functor.IsAccessible.{w} (B.uB E).toFunctor) ∧
    ((PreservesLimitsOfSize.{w, w} (B.g).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointMonoOfShape J (B.g').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (MonadicRightAdjoint (B.uB E).toFunctor)) ∧
    ((PreservesColimitsOfSize.{w, w} (B.f).toFunctor ∧
        ∀ (J : Type w) [SmallCategory J],
          PreservesJointEpiOfShape J (B.f').toFunctor) →
      IsLocallyPresentable.{w} (E.pt : Type u) ∧
        Nonempty (ComonadicLeftAdjoint (B.uB E).toFunctor)) := sorry

end AAFT

/-- **Theorem 5.10 (2), cardinal refinement** ([forsman2026syntactic], §5).

```latex
Let $F\colon \C\to \D$ be a functor with $\C$ locally presentable. Then the following hold:
```

```latex
\item If $F$ is continuous and accessible, then $F$ is a right adjoint.
```

**Reading.**
* "$\C$ locally presentable" ↦ `IsCardinalLocallyPresentable C κ`.
* "$\D$ accessible" ↦ `IsCardinalAccessibleCategory D κ'`.
* "$F$ continuous and accessible" ↦ `PreservesLimitsOfSize.{w, w} F` and
  `F.IsCardinalAccessible κ''`.
* conclusion ↦ left adjoint $G \dashv F$ preserving $\kappa''$-presentable objects
  (`G.PreservesCardinalPresentable κ''`).

**Deviations.**
- stronger: left adjoint preserves $\kappa''$-presentable objects at the accessibility rank of $F$
  (CHALLENGE.md, *Refinements checked next to the paper's statements*).
-/
theorem thm_5_10_2_cardinal {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]
    (κ κ' κ'' : Cardinal.{w}) [Fact κ.IsRegular] [Fact κ'.IsRegular] [Fact κ''.IsRegular]
    [IsCardinalLocallyPresentable C κ] [IsCardinalAccessibleCategory D κ'] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w} F] [F.IsCardinalAccessible κ''] :
    ∃ (G : D ⥤ C) (_ : G ⊣ F), G.PreservesCardinalPresentable κ'' := sorry

/-- **Theorem 5.11 (1), cardinal refinement** ([forsman2026syntactic], §5).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$ with $\C$ locally
presentable and $F,F',G,G'$ accessible. Then $U_\B\colon \BialgB\to \C$ is accessible and the
following hold:
```

```latex
\item If $G$ is continuous and $G'$ preserves joint monicness of limiting cones, then $\BialgB$
is locally presentable and the forgetful functor $U_\B\colon \BialgB\to \C$ is monadic.
```

**Reading.**
* $\kappa$-locally presentable category ↦ `IsCardinalLocallyPresentable (B.c : Type (w + 1)) κ`.
* $\kappa$-accessible functors ↦ `Functor.IsCardinalAccessible` on component functors.
* "accessible" (in the paper's sense: between accessible categories) ↦ `Functor.IsAccessible.{w}`
  on `G, G'` plus `IsAccessibleCategory.{w}` on `B.x` and `B.y` (`B.c` is locally presentable);
  Mathlib's predicate does not include the latter.
* conclusion ↦ $\kappa$-locally presentable $\BialgB$, monadic $U_\B$,
  and $\kappa$-accessible $U_\B$.

**Deviations.**
- stronger: stated at one fixed regular cardinal $\kappa$ (CHALLENGE.md, *Refinements checked next
  to the paper's statements*).
-/
theorem thm_5_11_1_cardinal (κ : Cardinal.{w}) [Fact κ.IsRegular]
    (B : BialgDatum (Obj := Cat.{w, w + 1})) (E : Equifier B.α B.β)
    [IsCardinalLocallyPresentable (B.c : Type (w + 1)) κ]
    [IsAccessibleCategory.{w} (B.x : Type (w + 1))] [IsAccessibleCategory.{w} (B.y : Type (w + 1))]
    [(B.f).toFunctor.IsCardinalAccessible κ]
    [Functor.IsAccessible.{w} (B.g).toFunctor]
    [(B.f').toFunctor.IsCardinalAccessible κ]
    [Functor.IsAccessible.{w} (B.g').toFunctor]
    [PreservesLimitsOfSize.{w, w} (B.g).toFunctor]
    (hg' : ∀ (J : Type w) [SmallCategory J],
      PreservesJointMonoOfShape J (B.g').toFunctor) :
    IsCardinalLocallyPresentable (E.pt : Type (w + 1)) κ ∧
      Nonempty (MonadicRightAdjoint (B.uB E).toFunctor) ∧
      (B.uB E).toFunctor.IsCardinalAccessible κ := sorry

/-- **Theorem 5.11, accessibility refinement** ([forsman2026syntactic], §5).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$ with $\C$ locally
presentable and $F,F',G,G'$ accessible. Then $U_\B\colon \BialgB\to \C$ is accessible and the
following hold:
```

**Reading.**
* two sharply-less-than steps ↦ `h₁ : κ.SharplyLT κ'`, `h₂ : κ'.SharplyLT κ''`.
* accessibility of $\BialgB$ and $U_\B$ at rank $\kappa''$ ↦
  `IsCardinalAccessibleCategory.{v} (E.pt : Type u) κ''` and
  `Functor.IsCardinalAccessible` on the forgetful functor.

**Deviations.**
- stronger: accessibility clause with explicit cardinals
  $\kappa \triangleleft \kappa' \triangleleft \kappa''$
  (CHALLENGE.md, *Refinements checked next to the paper's statements*).
-/
theorem thm_5_11_acc_cardinal (B : BialgDatum (Obj := Cat.{v, u}))
    (E : Equifier B.α B.β) {κ κ' κ'' : Cardinal.{v}} [Fact κ.IsRegular] [Fact κ'.IsRegular]
    [Fact κ''.IsRegular] (h₁ : κ.SharplyLT κ') (h₂ : κ'.SharplyLT κ'')
    [IsCardinalAccessibleCategory.{v} (B.c : Type u) κ]
    [(B.f).toFunctor.IsCardinalAccessible κ]
    [(B.g).toFunctor.IsCardinalAccessible κ]
    [(B.f').toFunctor.IsCardinalAccessible κ]
    [(B.g').toFunctor.IsCardinalAccessible κ]
    [(B.f).toFunctor.PreservesCardinalPresentable κ]
    [(B.f').toFunctor.PreservesCardinalPresentable κ] :
    IsCardinalAccessibleCategory.{v} (E.pt : Type u) κ'' ∧
      (B.uB E).toFunctor.IsCardinalAccessible κ'' := sorry

end UlmerBialgebras.Paper
