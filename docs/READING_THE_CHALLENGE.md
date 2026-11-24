# Reading the Challenge Statements

This guide helps a mathematician read the Lean 4 statements of eight results of D. Forsman,
*A Syntactic Approach to Ulmer's Bialgebras* (arXiv:2607.19587) — Theorems 4.7, 4.19, 5.7, 5.11,
6.6, Corollary 6.11, and Theorems 7.6 and 7.7 — and verify that each formal statement says what the
paper says. The numbers follow version 2 of the paper, in `paper/`. Of the section titles
below, only that of Theorem 4.7 is the paper's; the others describe the result.

Lean's Comparator checks that the proofs in the proof layer prove the exact statements in the
statement layer (`UlmerBialgebras/Paper/` and `Companion/Statements/`), using only Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`). Checking that those statements faithfully represent the mathematics of the
paper is a human reading task; this page explains the syntax and traces every project-defined notion
to its definition and Mathlib bridge.

---

## Quick Lean 4 Syntax Primer

- **Binder brackets:**
  - `(x : T)` is an explicit parameter.
  - `{x : T}` is an implicit parameter (inferred by Lean from later arguments).
  - `⦃x : T⦄` is a strict-implicit parameter (inferred only when the term is applied).
  - `[C]` is a typeclass instance, such as `[Category.{v} C]` or `[MonoidalCategory A]`.
- **Conventions:** For diagrammatic composition (`≫`, `⋙`), whiskering, `LeftExt`/`RightExt`
  argument order, `Nonempty` wrappers, `toOne`, `.toFunctor`/`.toCatHom` in `Cat`, chosen PIE
  limits and sizes, $A$- vs. $\mathcal{A}$-predicates, `AsBicat`, and universe parameters, see
  *How to read the Lean* in `CHALLENGE.md`.
- **The `:= sorry` stubs:** Every theorem in `UlmerBialgebras/Paper/` and `Companion/Statements/` ends with `:= sorry` by design. That
  file states the target; `UlmerBialgebras/Proofs/` and `Companion/Proofs/` supplies the sorry-free proof, and the Comparator verifies
  that both sides have the exact same type in the kernel.

---

## 1. Theorem 4.7 — Lifting Kan Extensions Along PIE Limits

**Paper statement (Section 4.1):** In a strict 2-category $\mathcal{K}$:
1. Product projections preserve left and right Kan extensions, jointly strictly create them, and
   jointly strictly create quotient-initial left extensions and subterminal right extensions.
2. For an inserter $u : \operatorname{Ins}(f,g) \to a$, if $f$ preserves a left Kan extension
   along $k$ of $d \circ u$, then $u$ strictly creates it; dually, if $g$ preserves a right Kan
   extension, $u$ strictly creates it.
3. For an equifier $e : \operatorname{Eq}(\eta,\theta) \to a$, if $f$ sends a left Kan extension of
   $d \circ e$ along $k$ to a quotient-initial left extension, then $e$ strictly creates it; dually
   for $g$ and subterminal right extensions.

**Lean statements (`UlmerBialgebras/Paper/Sec4.lean`, ambient strict 2-category `Obj`):**

```lean
theorem thm_4_7_1_preserves {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) (i : ι) :
    PreservesLeftKan k d (P.π i) ∧ PreservesRightKan k d (P.π i) := sorry
```

```lean
theorem thm_4_7_1_creates {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
      JointlyStrictlyCreatesTerminal (fun i : ι => RightExt.push k d (P.π i)) := sorry
```

```lean
theorem thm_4_7_1_quotient {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    (∀ L : LeftExt k d,
      QuotientInitial L ↔ ∀ i, QuotientInitial ((LeftExt.push k d (P.π i)).obj L)) ∧
    JointlyStrictlyCreatesQuotientInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
    (∀ R : RightExt k d,
      Subterminal R ↔ ∀ i, Subterminal ((RightExt.push k d (P.π i)).obj R)) ∧
    JointlyStrictlyCreatesSubterminal (fun i : ι => RightExt.push k d (P.π i)) := sorry
```

```lean
theorem thm_4_7_2_left {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hf : PreservesLeftKan k (d ≫ Ins.u) f) :
    StrictlyCreatesLeftKan k d Ins.u := sorry
```

```lean
theorem thm_4_7_2_right {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hg : PreservesRightKan k (d ≫ Ins.u) g) :
    StrictlyCreatesRightKan k d Ins.u := sorry
```

```lean
theorem thm_4_7_3_left {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L)) :
    StrictlyCreatesLeftKan k d E.e := sorry
```

```lean
theorem thm_4_7_3_right {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : ∀ R : RightExt k (d ≫ E.e), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ E.e) g).obj R)) :
    StrictlyCreatesRightKan k d E.e := sorry
```

**Reading the syntax:** `P.pt`, `Ins.pt`, and `E.pt` are the apex objects of the product, inserter,
and equifier; `P.π i`, `Ins.u`, and `E.e` are their canonical 1-cells. `LeftExt k d` is the
category of left extensions of `d` along `k`, and `LeftExt.push k d u` is postcomposition with `u`.
`Nonempty (IsInitial L)` says that `L` is an initial object in `LeftExt k d`, i.e., a left Kan
extension.

**Notions:**
- **Mathlib:** `CategoryTheory.Bicategory`, `Bicategory.Strict`, `Limits.IsInitial`,
  `Limits.IsTerminal`.
- **Ours:**
  - `Product`, `Inserter`, `Equifier` (`Foundations/CategoryTheory/Bicategory/PIE.lean`):
    2-categorical PIE limits in a strict 2-category.
  - `UlmerBialgebras.LeftExt`, `UlmerBialgebras.RightExt` (`UlmerBialgebras/Kan/Kan.lean`):
    definitional `abbrev`s for Mathlib's `Bicategory.LeftExtension` / `Bicategory.RightExtension`.
  - `QuotientInitial`, `Subterminal` (`UlmerBialgebras/Kan/Kan.lean`): bridged to Mathlib's
    `CategoryTheory.IsSubterminal` by `UlmerBialgebras.subterminal_iff_isSubterminal` and dual
    `UlmerBialgebras.quotientInitial_iff` (`UlmerBialgebras/Kan/SubterminalMathlib.lean`).
  - `PreservesLeftKan`, `StrictlyCreatesLeftKan`, `JointlyStrictlyCreatesInitial`, etc.
    (`UlmerBialgebras/Kan/Kan.lean`): standard 2-categorical Kan creation predicates on the
    extension categories.

---

## 2. Theorem 4.19 — Lifting Wide Pushouts of Regular Epimorphisms to $\Sigma$-Models

**Paper statement (Section 4.2):** Let $M$ be a model of a 2-signature in $\mathrm{CAT}$ whose
categories have every regular epimorphism as a reflexive coequalizer, and let $T$ be a theory over
a 1-signature on it. If every operation $M(B)$ preserves $K$-wide pushouts of regular epimorphisms
in each variable separately, then the forgetful functor $U : \operatorname{Mod}(T) \to \prod M(c)$
strictly creates $K$-wide pushouts of regular epimorphisms.

**Lean statement (`UlmerBialgebras/Paper/Sec4.lean`):**

```lean
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
```

**Reading the syntax:** `M.thyObj sg T` is the category of $T$-models inside `M`, and
`M.thyForget sg T` is its forgetful functor to the product of carrier categories.
`updateFunctor x i ⋙ (M.fn B).toFunctor` fixes all variables of the operation `B` except index `i`.
`J : Cat.{v, u}` with `e : WidePushoutShape K ≌ J` represents a $K$-wide pushout diagram in the
ambient universe of `Cat.{v, u}`, and `StrictlyCreatesLeftKan (toOne J) d U` is the paper's
2-categorical formulation of strict creation of the colimit of `d` (a left Kan extension along the
unique functor `toOne J : J ⟶ 1`).

**Notions:**
- **Mathlib:** `Limits.WidePushoutShape`, `RegularEpi`, `CategoryTheory.Equivalence` (`≌`), `Cat`.
- **Ours:**
  - `HasChosenInserters`, `HasChosenEquifiers`, `HasChosenProductsOfSize`
    (`Foundations/CategoryTheory/Bicategory/PIE.lean`): chosen PIE limits needed to construct
    `M.thyObj sg T`.
  - `TwoSig`, `OneSig`, `Theory` (`UlmerBialgebras/Syntax/Syntax.lean`) and `Model`
    (`UlmerBialgebras/Models/Semantics.lean`): Ulmer's 2-signatures, 1-signatures, equational
    theories, and models in a 2-category with chosen PIE limits.
  - `RegEpisAreReflexiveCoequalizers`, `PreservesWidePushoutsOfRegEpis` (`UlmerBialgebras/Paper/Sec4Defs2.lean`):
    direct translations of the two paper hypotheses.
  - `toOne` (`UlmerBialgebras/Kan/ColimKan.lean`): unique functor to the terminal category, bridged
    to Mathlib's `CreatesColimit` by
    `UlmerBialgebras.nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan`
    (`UlmerBialgebras/Kan/ColimKanCreates.lean`).

---

## 3. Theorem 5.7 — Monadicity and Left Kan Extensions for Bialgebraic Data

**Paper statement (Section 5.1):** Given a bialgebraic datum $B = (c, f, g, f', g', \alpha, \beta)$
in $\mathrm{CAT}$ with equifier $E = \mathrm{Bialg}(B)$ and forgetful functor $U_B : E \to c$,
suppose $g$ has a relative left adjoint $L_1$ along $f$ and $g'$ has a relative left adjoint $L_2$
along $f'$, $c$ has all colimits of size $\le \kappa$ (for an infinite cardinal $\kappa$), $f$
preserves $\kappa$-chain colimits, and $f'$ preserves the joint epicness of
colimiting cocones of $\kappa$-chains. Then
$U_B$ is monadic, $E$ has colimits of size $\le \kappa$, and $E$ admits every left Kan extension
of $d : I \to E$ along $k : I \to K$ for which $U_B d$ and $L_1 U_B d$ have left Kan extensions
along $k$.

**Lean statement (`UlmerBialgebras/Paper/Sec5.lean`):**

```lean
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
```

**Reading the syntax:** `κ.ord.ToType` is the well-ordered category of ordinals below the initial
ordinal of `κ`. The three conjuncts of the conclusion are: (1) `B.uB E` is a monadic right adjoint
(Mathlib's `MonadicRightAdjoint`), (2) `E.pt` has all colimits of size `≤ κ`, and (3) existence of
left Kan extensions along arbitrary functors `k : I ⥤ Kc` (with free universes `u₁, v₁, u₂, v₂`).

**Notions:**
- **Mathlib:** `Cardinal`, `Cardinal.aleph0`, `MonadicRightAdjoint`, `PreservesColimitsOfShape`,
  `Functor.HasLeftKanExtension`.
- **Ours:**
  - `BialgDatum` (`UlmerBialgebras/Paper/Sec3Defs.lean`): packages the bialgebraic datum $(c, x, y, f, g, f', g',
    \alpha, \beta)$ and its forgetful 1-cell `B.uB E`.
  - `RelLeftAdjoint` (`UlmerBialgebras/Monadicity/RelAdjoint.lean`): relative left adjoint
    $L \dashv_f g$, i.e., $\mathrm{Hom}(L a, b) \cong \mathrm{Hom}(f a, g b)$ naturally.
  - `HasColimitsOfSizeLE`, `PreservesJointEpiOfShape` (`UlmerBialgebras/Paper/Sec5Defs2.lean`): colimits of
    diagrams of size $\le \kappa$, and preservation of the joint epicness of colimiting cocones.

---

## 4. Theorem 5.11 — Local Presentability and (Co)Monadicity of Bialgebras

**Paper statement (Section 5.2):** Let $B$ be a bialgebraic datum in $\mathrm{CAT}$ where $c$ is
locally presentable, $x, y$ are accessible, and $f, g, f', g'$ are accessible functors. Then
$\mathrm{Bialg}(B)$ is accessible and $U_B$ is accessible. Moreover:
- if $g$ preserves small limits and $g'$ preserves the joint monicness of limiting
  cones, then
  $\mathrm{Bialg}(B)$ is locally presentable and $U_B$ is monadic;
- if $f$ preserves small colimits and $f'$ preserves the joint epicness of colimiting
  cocones, then
  $\mathrm{Bialg}(B)$ is locally presentable and $U_B$ is comonadic.

**Lean statement (`UlmerBialgebras/Paper/Sec5.lean`):**

```lean
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
```

**Reading the syntax:** `Cat.{w, u}` has hom-sets in `Type w` and objects in any universe `Type u`.
Following the paper's convention (recorded under *Same content, different form* in `CHALLENGE.md`),
"accessible functor" (in the paper's sense: between accessible categories) ↦ `Functor.IsAccessible.{w}`
plus `IsAccessibleCategory.{w}` on its domain and codomain (`B.x`, `B.y`; `B.c` is locally
presentable); Mathlib's predicate does not include the latter. The three conjuncts correspond
directly to the accessibility conclusion, the limit/monadic clause, and the colimit/comonadic
clause.

**Notions:**
- **Mathlib:** `IsLocallyPresentable`, `IsAccessibleCategory`, `Functor.IsAccessible`,
  `PreservesLimitsOfSize`, `PreservesColimitsOfSize`, `MonadicRightAdjoint`,
  `ComonadicLeftAdjoint`.
- **Ours:** `BialgDatum` (`UlmerBialgebras/Paper/Sec3Defs.lean`), `Equifier`
  (`Foundations/CategoryTheory/Bicategory/PIE.lean`), `PreservesJointMonoOfShape` and
  `PreservesJointEpiOfShape` (`UlmerBialgebras/Paper/Sec5Defs2.lean`).

---

## 5. Theorem 6.6 — Factorization Systems, Regularity, and Barr-Exactness of Bialgebras

**Paper statement (Section 6.1):** For a bialgebraic datum $B$ in $\mathrm{CAT}$ with equifier
$E = \mathrm{Bialg}(B)$:
1. An orthogonal factorization system $(\mathcal{E}, \mathcal{M})$ on $c$ lifts uniquely to $E$
   when $f(\mathcal{E}) \perp g(\mathcal{M})$ and $f'(\mathcal{E}) \perp_{\le 1} g'(\mathcal{M})$.
2. If $c$ is regular, $E$ has a terminal object, $f$ preserves regular epimorphisms,
   $f'(\mathcal{E}) \perp_{\le 1} g'(\mathcal{M})$, $g$ preserves pullbacks, and $g'$ preserves
   jointly monic spans, then $E$ is regular, $U_B$ strictly creates pullbacks, and $U_B$ preserves
   regular epimorphisms.
3. If $c$ is Barr-exact, $E$ has a terminal object, $f$ preserves coequalizers of kernel pairs,
   $f'$ sends regular epimorphisms to epimorphisms, $g$ preserves pullbacks, and $g'$ preserves
   jointly monic spans, then $E$ is Barr-exact and $U_B$ strictly creates coequalizers of kernel
   pairs.

**Lean statements (`UlmerBialgebras/Paper/Sec6.lean`):**

```lean
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
```

```lean
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
```

```lean
theorem thm_6_6_3 (B : BialgDatum (Obj := Cat.{v, max u v})) (E : Equifier B.α B.β)
    [BarrExact (B.c : Type (max u v))] (hterm : HasTerminal (E.pt : Type (max u v)))
    (hF : PreservesCoequalizersOfKernelPairs (B.f).toFunctor)
    (hF' : ∀ ⦃a b : (B.c : Type (max u v))⦄ (e : a ⟶ b), Nonempty (RegularEpi e) →
      Epi ((B.f').toFunctor.map e))
    [PreservesLimitsOfShape WalkingCospan (B.g).toFunctor]
    (hG' : PreservesJointMonoOfShape WalkingCospan (B.g').toFunctor) :
    BarrExact (E.pt : Type (max u v)) := sorry
```

```lean
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
```

**Reading the syntax:** `WalkingCospan` is the pullback shape; `WalkingParallelPair` is the
coequalizer shape. `IsKernelPair f r s` says `(r, s)` is the kernel pair of `f`.

**Notions:**
- **Mathlib:** `CategoryTheory.Regular`, `RegularEpi`, `Epi`, `HasTerminal`, `WalkingCospan`,
  `WalkingParallelPair`, `IsKernelPair`, `MorphismProperty.monomorphisms`.
- **Ours:**
  - `OFS`, `Orthogonal` (`Foundations/CategoryTheory/Factorization/OFS.lean`): orthogonal
    factorization system; `Orthogonal` is bridged to Mathlib's `CategoryTheory.HasLiftingProperty`
    by `UlmerBialgebras.orthogonal_iff_hasLiftingProperty`
    (`Foundations/CategoryTheory/Factorization/OrthogonalLifting.lean`).
  - `OrthogonalLE1` (`UlmerBialgebras/Paper/Sec6Defs2.lean`): at-most-one diagonal filler ($\perp_{\le 1}$).
  - `BarrExact` (`Foundations/CategoryTheory/Factorization/ExactCategory.lean`): regular category
    in which every internal equivalence relation (`IsEquivRel`, bridged to Mathlib's
    `IsEquivalenceRelation` by `isEquivRel_iff_isEquivalenceRelation` in
    `Foundations/CategoryTheory/Factorization/RegularMathlib.lean`) is effective.
  - `PreservesCoequalizersOfKernelPairs`
    (`Foundations/CategoryTheory/Factorization/RegularExact.lean`).

---

## 6. Corollary 6.11 — Barr-Exactness of Universal Algebra Models in Cocommutative Comonoids

**Paper statement (Section 6.2):** Let $T$ be an algebraic theory (in universal algebra) containing
a group structure on each sort, and let $R$ be a commutative von Neumann regular ring. Then the
categories of $T$-models in $\mathrm{Comon}^{\mathrm{coc}}(\mathrm{Mod}_R^{\mathrm{op}})$ (in
particular, commutative Hopf algebras with extra algebraic operations) and in
$\mathrm{Comon}^{\mathrm{coc}}(\mathrm{Mod}_R)$ (cocommutative Hopf algebras with extra algebraic
operations) are Barr-exact. More generally, for any symmetric monoidal category $\mathcal{A}$ with
tensor-preserved coreflexive equalizers and reflexive coequalizers, Barr-exactness of
$\mathrm{Grp}(\mathrm{Comon}^{\mathrm{coc}}(\mathcal{A}))$ implies Barr-exactness of
$\mathrm{Mod}_T(\mathrm{Comon}^{\mathrm{coc}}(\mathcal{A}))$.

**Lean statements (`UlmerBialgebras/Paper/Sec6Hopf.lean`):**

```lean
theorem modelCat_barrExact_reduction {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (A : Type u) [Category.{v} A] [MonoidalCategory A]
    [SymmetricCategory A] [HasCoreflexiveEqualizers A] [HasReflexiveCoequalizers A]
    [∀ Z : A, PreservesCoreflexiveEq (tensorLeft Z)]
    [∀ Z : A, PreservesCoreflexiveEq (tensorRight Z)]
    [∀ Z : A, Monad.PreservesColimitOfIsReflexivePair (tensorLeft Z)]
    [∀ Z : A, Monad.PreservesColimitOfIsReflexivePair (tensorRight Z)]
    [BarrExact (Grp (CategoryTheory.CommComon A))]
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon A)) := sorry
```

```lean
theorem modelCat_barrExact {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModU R))) := sorry
```

```lean
theorem modelCat_barrExact_moduleCat {S Fn' : Type u₁} {arity' : Fn' → ℕ}
    {argSorts' : ∀ f, Fin (arity' f) → S} {resSort' : Fn' → S}
    (R : Type u) [CommRing R] (hR : IsVonNeumannRegularRing R)
    (T : (grpExtLanguage S Fn' arity' argSorts' resSort').Theory)
    (hT : ∀ φ ∈ grpEqTheory S, (grpInl S Fn' arity' argSorts' resSort').translateEquation φ ∈ T) :
    BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R)ᵒᵖ)) ∧
      BarrExact (T.ModelCat (CategoryTheory.CommComon (ModuleCat.{u} R))) := sorry
```

**Reading the syntax:** `S` is the set of sorts, `Fn'` the set of additional operation symbols with
arities, argument sorts, and result sorts given by the implicit parameters above. `grpExtLanguage ...`
adjoins those symbols to the many-sorted group signature on `S`, and `hT` asserts that `T` contains
the group axioms on every sort. `CategoryTheory.CommComon A` is Mathlib's category of cocommutative
comonoids in `A`, and `Grp (CategoryTheory.CommComon A)` is Mathlib's category of internal group
objects therein.

**Notions:**
- **Mathlib:** `MonoidalCategory`, `SymmetricCategory`, `CommComon`, `Grp`, `CommRing`,
  `ModuleCat`, `Monad.PreservesColimitOfIsReflexivePair`.
- **Ours:**
  - `BarrExact` (`Foundations/CategoryTheory/Factorization/ExactCategory.lean`).
  - `PreservesCoreflexiveEq` (`Hopf/Cocommutative/CoreflexiveTensor.lean`).
  - `IsVonNeumannRegularRing` (`AffineGroupSchemes/VonNeumannRegular.lean`): every $a \in R$ has
    $x$ with $a x a = a$ (the reading confirmed for "commutative regular ring" in Section 6.2).
  - `grpExtLanguage`, `grpEqTheory`, `T.ModelCat` (`UlmerBialgebras/Paper/Sec6DefsTheoryMorphism.lean`,
    `UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean`): multi-sorted universal algebra theories and their categories
    of models in a cartesian monoidal category, bridged to Mathlib's first-order `Language` by
    `UlmerBialgebras.Paper.ofLanguage_model_iff` (`Companion/Statements/ExtrasAlgTheory.lean`) and
    `UlmerBialgebras.Paper.modelCat_type_iso_foModelCat` (`Companion/Statements/ExtrasAlgTranslations.lean`),
    and to the paper's bialgebraic theories by `UlmerBialgebras.Paper.modelCat_iso_cartThy_univ`
    (`Companion/Statements/ExtrasAlgTheory.lean`).
  - `ModU R` (`UlmerBialgebras/Paper/Sec3DefsLoc.lean`): `ModuleCat.{u} R` (kept alongside the explicit
    `ModuleCat.{u} R` form `modelCat_barrExact_moduleCat`).

---

## 7. Theorem 7.6 — Representable Cocompleteness and Monadicity

**Paper statement (Section 7):** Let $\mathcal{A}$ be a class of objects in a strict 2-category
$\mathcal{K}$, and let $B$ be a bialgebraic datum with equifier $E = \mathrm{Bialg}(B)$ where $g$
and $g'$ are right adjoints, $c$ is $\mathcal{A}$-cocomplete, and for each $a \in \mathcal{A}$ the
postcomposition functors $\mathcal{K}(a, f)$ and $\mathcal{K}(a, f')$ preserve $\kappa_a$-chain
colimits for some infinite cardinal $\kappa_a$. Then:
1. $E$ is $\mathcal{A}$-cocomplete and admits every left Kan extension into an object of
   $\mathcal{A}$ whose images under $U_B$ and $f \circ U_B$ exist.
2. If moreover $\mathcal{A}$ is bi-dense and $c$ admits right Kan extensions from $\mathcal{A}$,
   then $U_B$ is monadic in $\mathcal{K}$.

**Lean statements (`UlmerBialgebras/Paper/Sec7.lean`):**

```lean
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
```

```lean
theorem thm_7_6_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hg : ∃ l, Nonempty (TwoAdj l B.g)) (hg' : ∃ l, Nonempty (TwoAdj l B.g'))
    (hcoc : IsACocomplete.{w₀} A B.c) (hRan : HasARightKan A B.c)
    (κ : ∀ a, A a → Cardinal.{w₀}) (hκ : ∀ a ha, Cardinal.aleph0 ≤ κ a ha)
    (hf : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f))
    (hf' : ∀ a (ha : A a), PreservesColimitsOfShape (κ a ha).ord.ToType (postcomp a B.f')) :
    IsMonadic2 (B.uB E) := sorry
```

**Reading the syntax:** `A : ObjectProperty Obj` is Mathlib's predicate representing a class of
objects of the 2-category `Obj`. `postcomp a f` is the representable hom-category functor
$\mathcal{K}(a, f) : \mathcal{K}(a, c) \to \mathcal{K}(a, x)$. `∃ l, Nonempty (TwoAdj l B.g)`
says `B.g` has a left 2-adjoint `l`.

**Notions:**
- **Mathlib:** `ObjectProperty`, `Cardinal`, `PreservesColimitsOfShape`, `Limits.IsInitial`.
- **Ours:**
  - `TwoAdj` (`UlmerBialgebras/Models/BicatTwoCat.lean`): 2-adjunction in a strict 2-category.
  - `postcomp` (`UlmerBialgebras/Basic/HomCat.lean`): postcomposition functor on hom-categories.
  - `IsBiDense`, `IsACocomplete`, `HasARightKan` (`UlmerBialgebras/Paper/Sec7Defs.lean`): representable
    bi-density, $\mathcal{A}$-cocompleteness, and right Kan extensions from $\mathcal{A}$.
  - `IsMonadic2` (`UlmerBialgebras/Paper/Sec5Defs2.lean`): 2-categorical monadicity (existence of a left 2-adjoint
    such that the Eilenberg–Moore comparison is an equivalence).

---

## 8. Theorem 7.7 — Representable Local Presentability and (Co)Monadicity

**Paper statement (Section 7):** Let $\mathcal{A}$ be a class of objects in a strict 2-category
$\mathcal{K}$, and let $B$ be a bialgebraic datum with equifier $E = \mathrm{Bialg}(B)$ whose
four 1-cells $f, f', g, g'$ are $\mathcal{A}$-accessible.
1. If $c$ is $\mathcal{A}$-complete (in the strong/locally presentable sense) and $g, g'$ are
   $\mathcal{A}$-continuous, then $U_B$ is $\mathcal{A}$-accessible, $E$ is $\mathcal{A}$-accessible
   and $\mathcal{A}$-complete, and (when $\mathcal{A}$ is bi-dense) $U_B$ is monadic.
2. Dually, if $c$ is $\mathcal{A}$-cocomplete and $f, f'$ are $\mathcal{A}$-cocontinuous, then
   $U_B$ is $\mathcal{A}$-accessible, $E$ is $\mathcal{A}$-accessible and
   $\mathcal{A}$-cocomplete, and (when $\mathcal{A}$ is bi-dense) $U_B$ is comonadic.

**Lean statements (`UlmerBialgebras/Paper/Sec7.lean`):**

```lean
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
```

```lean
theorem thm_7_7_monadic (A : ObjectProperty Obj) (hA : IsBiDense A)
    (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)
    (hf : IsAAccessibleMor'.{w₀} A B.f) (hf' : IsAAccessibleMor'.{w₀} A B.f')
    (hg : IsAAccessibleMor'.{w₀} A B.g) (hg' : IsAAccessibleMor'.{w₀} A B.g') :
    (IsCalAComplete.{w₀} A B.c → IsCalAContinuous.{w₀} A B.g → IsCalAContinuous.{w₀} A B.g' →
      IsMonadic2 (B.uB E)) ∧
    (IsCalACocomplete.{w₀} A B.c → IsCalACocontinuous.{w₀} A B.f → IsCalACocontinuous.{w₀} A B.f' →
      IsComonadic2 (B.uB E)) := sorry
```

**Reading the syntax:** `IsAAccessibleMor'.{w₀} A f` says that for every $a \in \mathcal{A}$, the
representable functor $\mathcal{K}(a, f)$ is `w₀`-accessible between accessible hom-categories
(accessibility of the domain and codomain is built into `IsAAccessibleMor'`, matching the paper's
accessible-functor convention); `IsAAccessibleObj.{w₀} A x` says $\mathcal{K}(a, x)$ is
`w₀`-accessible for every $a \in \mathcal{A}$. The $\mathcal{A}$-predicates
(`IsCalAComplete`, `IsCalAContinuous`, and their `Co`-duals) package representable completeness /
continuity for `w₁`-small diagrams across all $a \in \mathcal{A}$.

**Notions:**
- **Mathlib:** `ObjectProperty`.
- **Ours:** `IsBiDense`, `IsAAccessibleObj`, `IsAAccessibleMor'`, `IsCalAComplete`,
  `IsCalACocomplete`, `IsCalAContinuous`, `IsCalACocontinuous` (`UlmerBialgebras/Paper/Sec7Defs.lean`),
  `IsMonadic2`, `IsComonadic2` (`UlmerBialgebras/Paper/Sec5Defs2.lean`), `BialgDatum` (`UlmerBialgebras/Paper/Sec3Defs.lean`),
  `Equifier` (`Foundations/CategoryTheory/Bicategory/PIE.lean`).
