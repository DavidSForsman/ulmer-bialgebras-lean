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

/-! ## Section 6: factorization systems, regularity, exactness -/

section Sec6

variable {C : Type u} [Category.{v} C]

/-- **Remark 6.2** ([forsman2026syntactic], §6).

```latex
An orthogonal factorization system can be equivalently described as a pair $(\mathcal{E},
\mathcal{M})$ of classes of morphisms of $\C$ such that every morphism in $\C$ admits an
$(\mathcal{E}, \mathcal{M})$-factorization, $\mathcal{E} \perp \mathcal{M}$ and both $\E$ and $\M$
are closed under retracts in the arrow category $\C^{\to}$
\cite[Lemma~11.2.3]{Riehl2014CategoricalHomotopyTheory}. In practice, these closure properties are
useful when verifying that a lifted pair of classes forms an orthogonal factorization system.
```

**Reading.**
* $(\mathcal{E}, \mathcal{M})$ orthogonal factorization system ↦ `∃ S : OFS C, S.E = E ∧ S.M = M`.
* closure under retracts in arrow category ↦ `E.IsStableUnderRetracts` and
  `M.IsStableUnderRetracts`.
* $(\mathcal{E}, \mathcal{M})$-factorization ↦ admission of `(E, M)` factorization.

**Deviations.** none recorded.
-/
theorem rem_6_2 (E M : MorphismProperty C) :
    (∃ S : OFS C, S.E = E ∧ S.M = M) ↔
      ((∀ ⦃x y : C⦄ (f : x ⟶ y), ∃ (z : C) (e : x ⟶ z) (m : z ⟶ y), E e ∧ M m ∧ e ≫ m = f) ∧
        (∀ ⦃x y z w : C⦄ (e : x ⟶ y) (m : z ⟶ w), E e → M m → Orthogonal e m) ∧
        E.IsStableUnderRetracts ∧ M.IsStableUnderRetracts) := sorry

/-- **Theorem 6.3 (1)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item $(\prod_i \mathcal{E}_i',\prod_i \mathcal{M}_i')$ is the unique OFS on $\prod_i \C_i$
preserved by the projections.
```

**Reading.**
* OFS on product category ↦ existence of a product factorization system whose classes
  are given componentwise by `S i`.
* "preserved by projections" ↦ projections preserve and reflect classes.
* uniqueness ↦ any other OFS on the product preserving classes is identical.

**Deviations.** none recorded.
-/
theorem thm_6_3_1 {ι : Type w} {Ci : ι → Type u} [∀ i, Category.{v} (Ci i)] (S : ∀ i, OFS (Ci i)) :
    ∃ P : OFS (∀ i, Ci i),
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.E f ↔ ∀ i, (S i).E (f i)) ∧
      (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P.M f ↔ ∀ i, (S i).M (f i)) ∧
      ∀ P' : OFS (∀ i, Ci i),
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.E f → ∀ i, (S i).E (f i)) →
        (∀ ⦃x y : ∀ i, Ci i⦄ (f : x ⟶ y), P'.M f → ∀ i, (S i).M (f i)) → P' = P := sorry

variable {D : Type u'} [Category.{v'} D]

/-- **Theorem 6.3 (2)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item If $F(\E')\perp G(\M')$, then $(U^{-1}(\mathcal{E}'),U^{-1}(\mathcal{M}'))$ is the unique
OFS on $\Ins(F,G)$ preserved by the forgetful functor $U\colon \Ins(F,G)\to \C$.
```

**Reading.**
* "$F(\E') \perp G(\M')$" ↦ `Orthogonal (F.map e) (G.map m)` for all `e ∈ S.E`, `m ∈ S.M`.
* uniqueness ↦ any other OFS `P'` on `Ins F G` whose classes map into `S.E` and `S.M` under
  base projection satisfies `P' = P`.

**Deviations.** none recorded.
-/
theorem thm_6_3_2 (S : OFS C) (F G : C ⥤ D)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal (F.map e) (G.map m)) :
    ∃ P : OFS (Ins F G),
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.E f ↔ S.E f.base) ∧
      (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P.M f ↔ S.M f.base) ∧
      ∀ P' : OFS (Ins F G),
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.E f → S.E f.base) →
        (∀ ⦃x y : Ins F G⦄ (f : x ⟶ y), P'.M f → S.M f.base) → P' = P := sorry

/-- **Theorem 6.3 (3)** ([forsman2026syntactic], §6).

```latex
Let $\C_i$ and $\C$ be categories equipped with orthogonal factorization systems $(\E_i',\M_i')$ and
$(\E',\M')$, respectively, for each $i\in I$. Let $F,G\colon \C\to \D$ be functors. Then the
following hold.
```

```latex
\item Let $\eta,\theta\colon F\Rightarrow G$ be natural transformations. If $F(\E')\perp_! G(\M')$,
then the equifier $E\colon \Eq(\eta,\theta)\to \C$ has a unique OFS $(E^{-1}(\mathcal{E}'),
E^{-1}(\mathcal{M}'))$ that is preserved by $E$.
```

**Reading.**
* "$F(\E') \perp_! G(\M')$" ↦ `OrthogonalLE1 (F.map e) (G.map m)` for all `e ∈ S.E`, `m ∈ S.M`.
* uniqueness ↦ any other OFS `P'` on `Equif η θ` whose classes map into `S.E` and `S.M` under
  hom projection satisfies `P' = P`.

**Deviations.** none recorded.
-/
theorem thm_6_3_3 (S : OFS C) {F G : C ⥤ D} (η θ : F ⟶ G)
    (horth : ∀ ⦃a b c d : C⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 (F.map e) (G.map m)) :
    ∃ P : OFS (Equif η θ),
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.E f ↔ S.E f.hom) ∧
      (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P.M f ↔ S.M f.hom) ∧
      ∀ P' : OFS (Equif η θ),
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.E f → S.E f.hom) →
        (∀ ⦃x y : Equif η θ⦄ (f : x ⟶ y), P'.M f → S.M f.hom) → P' = P := sorry

/-- **Definition 6.4, regularity** ([forsman2026syntactic], §6).

```latex
Let $\C$ be a category. We say that $\C$ is a \textbf{regular} category if $\C$ has finite limits
and a stable OFS $(\E,\M)$, where $\M$ is the class of monos in $\C$.
```

**Reading.**
* regular category ↦ `CategoryTheory.Regular C` in Mathlib style.
* "stable OFS $(\E,\M)$ where $\M$ is the monos" ↦
  `∃ S : OFS C, S.M = MorphismProperty.monomorphisms C ∧ S.E.IsStableUnderBaseChange`.
* equivalence between Mathlib's notion and the paper's definition.

**Deviations.** none recorded.
-/
theorem def_6_4_regular :
    Regular C ↔ HasFiniteLimits C ∧ ∃ S : OFS C,
      S.M = MorphismProperty.monomorphisms C ∧ S.E.IsStableUnderBaseChange := sorry

/-- **Definition 6.4, exactness** ([forsman2026syntactic], §6).

```latex
Let $\C$ be a category. We say that $\C$ is a \textbf{regular} category if $\C$ has finite limits
and a stable OFS $(\E,\M)$, where $\M$ is the class of monos in $\C$.
```

```latex
A regular category $\C$ is called \textbf{exact} if each internal equivalence relation
$R\rightrightarrows c$ in $\C$ is the kernel pair of some morphism in $\C$.\footnote{A jointly
monomorphic pair of morphisms $R\rightrightarrows c$ in a category $\C$ is called an equivalence
relation if the induced subset of $\hom(x,c)\times \hom(x,c)$ is an equivalence relation for each
object $x$ in $\C$.}
```

**Reading.**
* exact category ↦ `CategoryTheory.BarrExact C`.
* internal equivalence relation ↦ `IsEquivRel r s`.
* kernel pair ↦ `IsKernelPair f r s`.
* equivalence between `BarrExact C` and the paper's definition.

**Deviations.** none recorded.
-/
theorem def_6_4_exact :
    BarrExact C ↔ Regular C ∧ ∀ ⦃R c : C⦄ (r s : R ⟶ c), IsEquivRel r s →
      ∃ (d : C) (f : c ⟶ d), IsKernelPair f r s := sorry

/-- **Lemma 6.5** ([forsman2026syntactic], §6).

```latex
Let $U\colon \D\to \C$ be a pullback preserving functor reflecting monics with $\D$ having finite
limits. Let $\M = U^{-1}(\M')$ and $\E = U^{-1}(\E')$, where $\E'$ and $\M'$ are the classes of
extremal epimorphisms and monomorphisms of $\C$, respectively. Then the following hold:
\begin{enumerate}
    \item If $(\E,\M)$ is an OFS on $\D$ and $\E'$ is stable under pullbacks, then $\D$ is regular.
    \item If $\D$ has coequalizers of kernel pairs, $U$ is a regular epi preserving conservative
    functor, and the category $\C$ is regular, then $\D$ is regular.
    \item If $\D$ has coequalizers of equivalence relations preserved by the functor $U$, $U$ is
    conservative, and the category $\C$ is exact, then $\D$ is exact.
\end{enumerate}
```

**Reading.**
* "pullback preserving reflecting monics" ↦ `[PreservesLimitsOfShape WalkingCospan U]` and `hmono`.
* $\E'$ extremal epimorphisms ↦ `ExtremalEpi (U.map f)`.
* $\M'$ monomorphisms ↦ `Mono (U.map f)`.
* item 1 ↦ `Regular Dc`.
* item 2 ↦ `Regular C → Regular Dc`.
* item 3 ↦ `BarrExact C → BarrExact Dc`.

**Deviations.** none recorded.
-/
theorem lem_6_5 {Dc : Type u'} [Category.{v'} Dc] [HasFiniteLimits Dc] (U : Dc ⥤ C)
    [PreservesLimitsOfShape WalkingCospan U]
    (hmono : ∀ ⦃x y : Dc⦄ (f : x ⟶ y), Mono (U.map f) → Mono f) :
    -- (1)
    ((∃ S : OFS Dc, (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.E f ↔ ExtremalEpi (U.map f)) ∧
        (∀ ⦃x y : Dc⦄ (f : x ⟶ y), S.M f ↔ Mono (U.map f))) →
      MorphismProperty.IsStableUnderBaseChange
        (fun _ _ f => ExtremalEpi f : MorphismProperty C) →
      Regular Dc) ∧
    -- (2)
    (HasCoequalizersOfKernelPairs Dc → U.ReflectsIsomorphisms →
      (∀ ⦃x y : Dc⦄ (f : x ⟶ y), Nonempty (RegularEpi f) → Nonempty (RegularEpi (U.map f))) →
      Regular C → Regular Dc) ∧
    -- (3)
    ((∀ ⦃R x : Dc⦄ (r s : R ⟶ x), IsEquivalenceRelation r s →
        HasCoequalizer r s ∧ PreservesColimit (parallelPair r s) U) →
      U.ReflectsIsomorphisms → BarrExact C → BarrExact Dc) := sorry

end Sec6

/-- **Theorem 6.6 (1)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $F(\E')\perp G(\M')$ and $F'(\E')\perp_! G'(\M')$, then the pair $(\E,\M)$ is the unique
OFS on $\BialgB$ preserved by $U_\B\colon \BialgB\to \C$.
```

**Reading.**
* bialgebraic datum in $\CAT$ ↦ `(B : BialgDatum)` at `Cat.{v, max u v}`.
* "unique OFS on $\BialgB$ preserved by $U_\B$" ↦ existence of an OFS on `E.pt`
  whose classes are the preimages under the forgetful functor of `S.E` and `S.M`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_1 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v)))
    (horth : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      Orthogonal ((B.f).toFunctor.map e) ((B.g).toFunctor.map m))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m)) :
    ∃ P : OFS (E.pt : Type (max u v)),
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.E f ↔ S.E ((B.uB E).toFunctor.map f)) ∧
      (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
        P.M f ↔ S.M ((B.uB E).toFunctor.map f)) ∧
      ∀ P' : OFS (E.pt : Type (max u v)),
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.E f → S.E ((B.uB E).toFunctor.map f)) →
        (∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y),
          P'.M f → S.M ((B.uB E).toFunctor.map f)) → P' = P := sorry

/-- **Theorem 6.6 (2)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item Assume $\C$ is regular, $\M'$ is the class of monomorphisms in $\C$, and $\BialgB$ has a
terminal object. Assume that $F$ preserves regular epis, $F'(\E')\perp_! G'(\M')$, $G$ preserves
pullbacks, and $G'$ the joint monicness of pullback projections. Then $\BialgB$ is regular with
$U$ strictly creating pullbacks and preserving regular epimorphisms.
```

**Reading.**
* "$\C$ regular, $\M'$ monos, $\BialgB$ has terminal object" ↦ `[Regular (B.c : Type (max u v))]`,
  `S.M = MorphismProperty.monomorphisms (B.c : Type (max u v))`,
  `HasTerminal (E.pt : Type (max u v))`.
* "$\BialgB$ is regular" ↦ `Regular (E.pt : Type (max u v))`.
* "$U$ strictly creates pullbacks" ↦ `StrictlyCreatesRightKan (toOne J) d (B.uB E)` for any shape
  `J` equivalent to `WalkingCospan`.
* "$U$ preserves regular epimorphisms" ↦ preservation of regular epimorphisms by the
  forgetful functor `B.uB E`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_2 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    (S : OFS (B.c : Type (max u v))) [Regular (B.c : Type (max u v))]
    (hM : S.M = MorphismProperty.monomorphisms (B.c : Type (max u v)))
    (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Nonempty (RegularEpi ((B.f).toFunctor.map e)))
    (horth' : ∀ ⦃a b c d : (B.c : Type (max u v))⦄ (e : a ⟶ b) (m : c ⟶ d), S.E e → S.M m →
      OrthogonalLE1 ((B.f').toFunctor.map e)
        ((B.g').toFunctor.map m))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    Regular (E.pt : Type (max u v)) ∧
      (∀ (J : Cat.{v, max u v}) (_ : WalkingCospan ≌ (J : Type (max u v)))
        (d : J ⟶ E.pt), StrictlyCreatesRightKan (toOne J) d (B.uB E)) ∧
      ∀ ⦃x y : (E.pt : Type (max u v))⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi ((B.uB E).toFunctor.map f)) := sorry

/-- **Theorem 6.6 (3)** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $\C$ is exact, $\BialgB$ has a terminal object, $F$ preserves coequalizers of kernel
pairs, $F'$ maps regular epis to epis, $G$ preserves pullbacks and $G'$ the joint monicness of
pullback projections, then $\BialgB$ is exact with $U$ strictly creating coequalizers of kernel
pairs.
```

**Reading.**
* "$\C$ exact, $\BialgB$ has terminal object" ↦ `[BarrExact (B.c : Type (max u v))]` and
  `HasTerminal (E.pt : Type (max u v))`.
* "$\BialgB$ is exact" ↦ `BarrExact (E.pt : Type (max u v))`.
* strict creation of coequalizers of kernel pairs is formalized in `thm_6_6_3_coeq`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_3 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))] (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    BarrExact (E.pt : Type (max u v)) := sorry

/-- **Theorem 6.6 (3), creation clause** ([forsman2026syntactic], §6).

```latex
Let $\B = (\C,\ F,G,\ F',G',\ \alpha,\beta)$ be a bialgebraic datum in $\CAT$. Assume that $\C$ is
equipped with an orthogonal factorization system $(\E',\M')$. Denote $\M = U_\B^{-1}(\M')$ and
$\E = U_\B^{-1}(\E')$. Then the following conditions hold:
```

```latex
\item If $\C$ is exact, $\BialgB$ has a terminal object, $F$ preserves coequalizers of kernel
pairs, $F'$ maps regular epis to epis, $G$ preserves pullbacks and $G'$ the joint monicness of
pullback projections, then $\BialgB$ is exact with $U$ strictly creating coequalizers of kernel
pairs.
```

**Reading.**
* "strictly creating coequalizers of kernel pairs" ↦ for any kernel pair `r, s` of `f`,
  `StrictlyCreatesLeftKan (toOne J) ... (B.uB E)` for any shape `J` equivalent to
  `WalkingParallelPair`.
* omits the terminal object hypothesis: the creation clause holds without assuming `HasTerminal`.

**Deviations.**
- stronger: omits the hypothesis that $\BialgB$ has a terminal object (CHALLENGE.md, *Stronger than
  the paper*).
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem thm_6_6_3_coeq (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))]
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor)
    ⦃R a b : (E.pt : Type (max u v))⦄ (f : a ⟶ b) (r s : R ⟶ a) (hk : IsKernelPair f r s) :
    ∀ (J : Cat.{v, max u v}) (e : WalkingParallelPair ≌ (J : Type (max u v))),
      StrictlyCreatesLeftKan (toOne J) (e.inverse ⋙ parallelPair r s).toCatHom
        (B.uB E) := sorry

/-- **Corollary 6.7** ([forsman2026syntactic], §6).

```latex
Let $M$ be a $\Sigma$-model in $\CAT$. Assume each category $M_c$ is equipped with an OFS
$(\E_c,\M_c)$. Let $T$ be a $\sigma$-theory and denote $(\E,\M) \coloneqq (U^{-1}(\prod_s
\E_{c_s}),U^{-1}(\prod_s \M_{c_s}))$, where $U\colon M^T\to M_0$ is the forgetful functor. Then
the following hold:
\begin{enumerate}
\item If $T$ is (co)algebraic and each functor $M(B)$ preserves the (right) left classes
componentwise, then $(\E,\M)$ is the unique OFS on $M^T$ preserved by $U$.
\item If each functor $M(B)$ preserves both classes componentwise, then $(\E,\M)$ is the unique
OFS on $M^T$ that is preserved by $U$.
\end{enumerate}
```

**Reading.**
* categorical model ↦ `M : Model Sg Cat.{v, max u v}`.
* "unique OFS on $M^T$ preserved by $U$" ↦ `HasUniqueLiftedOFS M S sg T`.
* states algebraic case (item 1), coalgebraic case (item 1 dual), and general case (item 2).

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem cor_6_7 {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    (S : ∀ c : Sg.Cat, OFS (M.obj c : Type (max u v))) :
    (T.IsAlgebraic → (∀ B, PreservesLeftClassComponentwise M S B) →
        HasUniqueLiftedOFS M S sg T) ∧
      (T.IsCoalgebraic → (∀ B, PreservesRightClassComponentwise M S B) →
        HasUniqueLiftedOFS M S sg T) ∧
      ((∀ B, PreservesLeftClassComponentwise M S B) →
        (∀ B, PreservesRightClassComponentwise M S B) → HasUniqueLiftedOFS M S sg T) := sorry

/-- **Corollary 6.8** ([forsman2026syntactic], §6).

```latex
Let $\B_i = (\C_i,\ F_i,G_i,\ F_i',G_i',\ \alpha_i,\beta_i)$ be a bialgebraic datum in $\CAT$ for
$i = 1,2$. Consider a commutative diagram
$$
\begin{tikzcd}
\Bialg(\B_1) \arrow[d, "U_1"'] \arrow[r, "\bar{F}"] & \Bialg(\B_2) \arrow[d, "U_2"] \\
\C_1 \arrow[r, "F"']                                & \C_2                         
\end{tikzcd}
$$
of functors, where $U_i = U_{\B_i}$ for $i = 1,2$. Assume the following:
\begin{enumerate}
    \item The category $\C_1$ has and $F$ preserves pullbacks and reflexive coequalizers.
    \item The functor $F$ is conservative.
    \item The function arity functors $F_1, F_2$ preserve reflexive coequalizers and the equational
    arity functors $F_1',F_2'$ map regular epis to epis.
    \item The function coarity functors $G_1$ and $G_2$ preserve pullbacks and the equational
    coarity functors $G_1',G_2'$ preserve the joint monicness of pullback projections.
\end{enumerate}
```

```latex
Then $\Bialg(\B_1)$ has and $\bar{F}$ preserves pullbacks and reflexive coequalizers, and $\bar{F}$
is conservative. Moreover, if $\Bialg(\B_2)$ is exact and $\Bialg(\B_1)$ has a terminal object,
then $\Bialg(\B_1)$ is exact.
```

**Reading.**
* commutative diagram ↦ `Fb ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F`.
* conclusion ↦ pullbacks, reflexive coequalizers, preservation, conservativity, and exactness
  reflection `BarrExact E₂.pt → HasTerminal E₁.pt → BarrExact E₁.pt`.

**Deviations.**
- different (size): in `Cat.{v, max u v}`, independent universes (CHALLENGE.md, *Size migration*).
-/
theorem cor_6_8 (B₁ B₂ : BialgDatum (Obj := Cat.{v, max u v})) (E₁ : Equifier B₁.α B₁.β)
    (E₂ : Equifier B₂.α B₂.β) (F : B₁.c ⟶ B₂.c) (Fb : E₁.pt ⟶ E₂.pt)
    (hsq : Fb ≫ B₂.uB E₂ = B₁.uB E₁ ≫ F)
    [HasPullbacks (B₁.c : Type (max u v))] [HasReflexiveCoequalizers (B₁.c : Type (max u v))]
    [PreservesLimitsOfShape WalkingCospan F.toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair F.toFunctor]
    [F.toFunctor.ReflectsIsomorphisms]
    [PreservesColimitsOfShape WalkingReflexivePair (B₁.f).toFunctor]
    [PreservesColimitsOfShape WalkingReflexivePair (B₂.f).toFunctor]
    (hF'₁ : ∀ ⦃a b : (B₁.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₁.f').toFunctor.map e))
    (hF'₂ : ∀ ⦃a b : (B₂.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B₂.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B₁.g).toFunctor]
    [PreservesLimitsOfShape WalkingCospan (B₂.g).toFunctor]
    (hG'₁ : PreservesJointMonoOfShape WalkingCospan (B₁.g').toFunctor)
    (hG'₂ : PreservesJointMonoOfShape WalkingCospan (B₂.g').toFunctor) :
    HasPullbacks (E₁.pt : Type (max u v)) ∧ HasReflexiveCoequalizers (E₁.pt : Type (max u v)) ∧
      Nonempty (PreservesLimitsOfShape WalkingCospan Fb.toFunctor) ∧
      Nonempty (PreservesColimitsOfShape WalkingReflexivePair Fb.toFunctor) ∧
      Fb.toFunctor.ReflectsIsomorphisms ∧
      (BarrExact (E₂.pt : Type (max u v)) → HasTerminal (E₁.pt : Type (max u v)) →
        BarrExact (E₁.pt : Type (max u v))) := sorry

/-- **Corollary 6.9** ([forsman2026syntactic], §6).

```latex
Let $\sigma_1\subset\sigma_2$ be $1$-signatures relative to $\Sigma$ with the same set of sorts.
Let $T_1\subset T_2$ be algebraic $\sigma_1$- and $\sigma_2$-theories, respectively, with $M$ a
categorical $\Sigma$-model. Assume that each category $M_c$ has finite limits and reflexive
coequalizers and each functor $M(B)$ preserves reflexive coequalizers componentwise. If $M^{T_1}$ is
exact, then so is $M^{T_2}$.
```

**Reading.**
* $\sigma_1 \subset \sigma_2$ with same sorts ↦ `sg.restrictFn jFn`.
* $T_1 \subset T_2$ ↦ `T.restrictSig jFn jEq lhs₁ rhs₁`.
* "$M^{T_1}$ exact implies $M^{T_2}$ exact" ↦
  exactness of the restricted model `M.thyObj (sg.restrictFn jFn) ...` implies
  `BarrExact (M.thyObj sg T)`.

**Deviations.**
- different (size): stated in `Cat.{v, max u v}` (CHALLENGE.md, *Size migration*); the reflexive
  pairs that `M(B)` preserves componentwise are of the shape `WalkingReflexivePair`.
- stronger: allows maps of symbols and equations of the sub-signature to be non-injective
  (CHALLENGE.md, *Stronger than the paper*).
-/
theorem cor_6_9 {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] {Fn₁ : Type s₂} (jFn : Fn₁ → sg.Fn)
    (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    {E : Type s₃} (jEq : E → T.Eqn)
    (lhs₁ rhs₁ : ∀ r : E, (sg.restrictFn jFn).Path (T.dom (jEq r)) (T.cod (jEq r)))
    (hlhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (lhs₁ r) = T.lhs (jEq r))
    (hrhs : ∀ r : E, OneSig.Path.ofRestrictFn jFn (rhs₁ r) = T.rhs (jEq r))
    (halg : T.IsAlgebraic)
    (hlim : ∀ c : Sg.Cat, HasFiniteLimits (M.obj c : Type (max u v)))
    (hrc : ∀ c : Sg.Cat, HasReflexiveCoequalizers (M.obj c : Type (max u v)))
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M WalkingReflexivePair B)
    [BarrExact (M.thyObj (sg.restrictFn jFn) (T.restrictSig jFn jEq lhs₁ rhs₁) :
      Type (max u v))] :
    BarrExact (M.thyObj sg T : Type (max u v)) := sorry

end UlmerBialgebras.Paper
