# Challenge and solution for *A Syntactic Approach to Ulmer's Bialgebras*

This file describes the "statements first" layer of the formalization: which Lean statements are
checked, what a reviewer has to read, and how each statement compares with the paper.

| Path | Role |
|---|---|
| `UlmerBialgebras/Paper/Sec*.lean`, `UlmerBialgebras/Paper/Appendix.lean` | The paper's numbered results, each proved by `sorry`. **Review these.** |
| `UlmerBialgebras/Paper/AppendixA3A5.lean`, `Companion/Statements/ExtrasAlgTheory.lean`, `Companion/Statements/ExtrasClassical.lean`, `Companion/Statements/ExtrasTheoryMorphism.lean`, `Companion/Statements/ExtrasAlgTranslations.lean`, `Companion/Statements/ExtrasDoctrinal.lean` | Checked statements that the paper uses without a number: the representable statements of Section 2.2, the probe classifications of Appendix A, and the comparison of classical equational theories with theories over `Σ_Cart`; and additions beyond the paper: the classical theories against Mathlib, morphisms of theories, and the translations of `Σ_Cart`-theories to equational theories and of single-sorted ones to first-order logic; the doctrinal adjunction for Σ-models. **Review these.** |
| `UlmerBialgebras/Paper/*Defs*.lean` | Definitions that the statements need and that the library lacks or states differently. **Review these.** |
| `UlmerBialgebras/Proofs/` and `Companion/Proofs/` | The same statements, with proofs. They may differ from `UlmerBialgebras/Paper/` and `Companion/Statements/` only in the proofs. |
| `comparator.all.json` | The list of checked statements (`theorem_names`) and the allowed axioms `propext`, `Quot.sound` and `Classical.choice`. It is also a configuration file for Lean's [Comparator](https://github.com/leanprover/comparator). |
| `scripts/check_compiled_types.lean` | Checks that each checked statement has exactly the same elaborated type in `UlmerBialgebras/Proofs/` and `Companion/Proofs/` as in `UlmerBialgebras/Paper/` and `Companion/Statements/`. |
| `scripts/check_axioms.py` | Lists the axioms used by each checked statement. |
| `UlmerBialgebras/`, `Foundations/` | The library. Its definitions are part of the trusted base wherever a statement uses them. |

## Status

<!-- BEGIN GENERATED STATUS -->
- There are **175 checked statements**. All 175 are proved with the permitted axioms.
- The author reviews the statements and their definitions against the paper; approvals and known deviations are recorded in `docs/STATE.yml`.
<!-- END GENERATED STATUS -->

## What a reviewer has to check

Proofs need not be read. The two checks above guarantee that `UlmerBialgebras/Proofs/` and `Companion/Proofs/` proves exactly the
statements of `UlmerBialgebras/Paper/` and `Companion/Statements/`, with the allowed axioms only. What remains is:

1. **The statements** in `UlmerBialgebras/Paper/Sec*.lean`, `UlmerBialgebras/Paper/Appendix.lean` and
   `Companion/Statements/Extras*.lean` say what the paper says. The section "How the statements compare with
   the paper" below lists every difference.
2. **The definitions in `UlmerBialgebras/Paper/*Defs*.lean`** say what the paper says. They are grouped by
   topic:
   - `UlmerBialgebras/Paper/Sec3Defs.lean`, `UlmerBialgebras/Paper/Sec4Defs.lean`, `UlmerBialgebras/Paper/Sec7Defs.lean`, `UlmerBialgebras/Paper/Sec3Defs2.lean`, `UlmerBialgebras/Paper/Sec4Defs2.lean`, `UlmerBialgebras/Paper/Sec5Defs2.lean`, `UlmerBialgebras/Paper/Sec6Defs2.lean`: bialgebraic data and the predicates of Sections 4–7 (for example
     `IsMonadic2`, `HasUniqueLiftedOFS`, `IsBiDense`, the `A`-properties of Section 7);
   - `UlmerBialgebras/Paper/Sec4DefsExt.lean`, `UlmerBialgebras/Paper/Sec5DefsKanIns.lean`, `UlmerBialgebras/Paper/Sec4DefsRelativelyAlgebraic.lean`: the extension categories
     of Remark 4.5 and Lemmas 4.6 and 5.6, and Definition 4.9;
   - `UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`, `UlmerBialgebras/Paper/Sec3DefsMonadAlgObject.lean`, `UlmerBialgebras/Paper/Sec3DefsTransposedDatum.lean`: Examples 3.4, 3.9
     and 3.12, Remark 3.17 and Remark 3.2;
   - `UlmerBialgebras/Paper/Sec3DefsMonModel.lean`, `UlmerBialgebras/Paper/Sec3DefsHopfModel.lean`, `UlmerBialgebras/Paper/Sec3DefsLaxLimit.lean`, `UlmerBialgebras/Paper/Sec5DefsCart.lean`,
     `UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean`: the models of Examples 3.19 and 3.20, and classical equational theories;
   - `Companion/Statements/DefsClassical.lean`, `UlmerBialgebras/Paper/Sec6DefsTheoryMorphism.lean`, `Companion/Statements/DefsAlgTranslations.lean`: the theories of
     monoids, commutative monoids and groups, the language of groups with further symbols, and the
     translation of `Σ_Cart`-theories (additions beyond the paper). The many-sorted languages,
     their models, morphisms of theories and the translation to first-order logic are library
     definitions in `UlmerBialgebras/UniversalAlgebra/`;
   - `UlmerBialgebras/Paper/Sec5DefsDoctrinal.lean`: the mates of the structure 2-cells of a lax morphism, and the identity
     lax data;
   - `UlmerBialgebras/Paper/Sec6DefsGrp.lean`, `UlmerBialgebras/Paper/Sec6DefsHopf.lean`, `UlmerBialgebras/Paper/Sec3DefsLoc.lean`, `UlmerBialgebras/Paper/Sec6DefsLoc.lean`: Lemma 6.10 and Corollary 6.11;
   - `UlmerBialgebras/Paper/Sec7DefsSec7Variant.lean`: the Hofstra–Karvonen form of bi-density;
   - `DefsAppendix*.lean`: Appendix A.
3. **The library definitions** that the statements use say what the paper says:
   - strict 2-categories: Mathlib's `Bicategory` together with `Bicategory.Strict`; `CAT` is Mathlib's `CategoryTheory.Cat.bicategory`;
   - PIE limits: `Product`, `Inserter`, `Equifier`, `PIEComplete`, `Ins`, `Equif`;
   - syntax and models: `TwoSig`, `OneSig`, `Theory`, `Model`, `LaxMor`, `OplaxMor`, the objects
     `sigObj` and `thyObj` with the path evaluation `pathCell`, and the induced 1-cells
     `LaxMor.sigMor` and `OplaxMor.sigMor` of Lemma 3.21;
   - Kan extensions: `LeftExt`, `RightExt` and the preservation and creation predicates of
     `UlmerBialgebras/Kan/Kan.lean`;
   - factorization and exactness: `OFS`, `Orthogonal`, `IsEquivRel` (only in `def_6_4_exact`), and
     the Barr-exact categories `CategoryTheory.BarrExact` (`ExactCategory.lean`; this is a
     definition of this repository, despite its namespace);
   - adjunctions and density: `TwoAdj` (Mathlib's adjunctions in a bicategory), `RelLeftAdjoint`,
     `AHomFamily`, `IsACellDense`;
   - the example models `MonEx` and `FieldEx`.

## How to read the Lean

Every file in `UlmerBialgebras/Paper/` and `Companion/Statements/` states results with `:= sorry` as a target for `UlmerBialgebras/Proofs/` and `Companion/Proofs/` and the
Comparator. The table below translates the recurring Lean 4 / Mathlib notations back to the paper.

| Paper | Lean |
|---|---|
| Composition $g \circ f$, $G \circ F$ | Diagrammatic order: `f ≫ g` (morphisms / 1-cells / 2-cells), `F ⋙ G` (functors); whiskering is `k ◁ η` and `η ▷ k`. |
| Extension categories $\mathrm{LE}(d, k)$, $\mathrm{RE}(d, k)$ | Reversed arguments: `LeftExt k d`, `RightExt k d` (`k : I ⟶ X` first, `d : I ⟶ c` second), `abbrev`s for Mathlib's `Bicategory.LeftExtension` / `Bicategory.RightExtension`. |
| "There exists an initial object / regular epi / ..." | `Nonempty (IsInitial L)`, `Nonempty (RegularEpi f)`, `Nonempty (CreatesLimitsOfShape J F)`, `Nonempty (MonadicRightAdjoint U)`: Mathlib defines these as data-carrying `Type`-valued structures; `Nonempty` turns them into `Prop` without weakening the claim. |
| Ordinary $I$-indexed (co)limits in $\mathrm{CAT}$ | Kan extensions along `toOne I : I ⟶ One` (the unique functor to the terminal category): e.g., `StrictlyCreatesLeftKan (toOne I) d U`. |
| Functor vs. 1-cell in $\mathrm{CAT}$ | In Mathlib's bicategory `Cat`, 1-cells are bundled as `Cat.Hom`; `.toFunctor` views a 1-cell as a functor `C ⥤ D`, and `.toCatHom` turns a functor into a 1-cell. |
| Chosen PIE limits for $M^\sigma$, $M^T$ | Instance arguments `[HasChosenFinProducts Obj]`, `[HasChosenInserters Obj]`, `[HasChosenEquifiers Obj]`, and three `[HasChosenProductsOfSize.{s} Obj]` at independent universes `s₁, s₂, s₃` indexing sorts (`sg.Srt`), function symbols (`sg.Fn`), and equations (`T.Eqn`). |
| $A$-properties vs. $\mathcal{A}$-properties (Defs. 7.2–7.3) | `IsAComplete`, `IsACocomplete`, `IsAContinuous`, `IsACocontinuous`, `IsAAccessibleObj`, `IsAAccessibleMor'` act on each hom-category $\mathcal{K}(a, -)$ ($a \in A$); `IsCalAComplete`, `IsCalACocomplete`, `IsCalAContinuous`, `IsCalACocontinuous` (`Cal` = $\mathcal{A}$) also require/preserve Kan extensions along 1-cells in $\mathcal{A}$. `IsAAccessibleMor'` is primed to mark that it bundles `IsAccessibleCategory` on domain and codomain alongside Mathlib's `Functor.IsAccessible`, matching the paper's convention. |
| Strict 2-category adjunctions | `TwoAdj f g` is `Bicategory.Adjunction (B := AsBicat Obj) f g`. `AsBicat Obj` is a definitional identity `abbrev` for `Obj`, kept so `TwoAdj` uses Mathlib's bicategory adjunction/mate API without imposing extra instances on `Obj`. |
| Universes | In `[Bicategory.{w, v} Obj]` (`Obj : Type u`), `u` = objects, `v` = 1-cells, `w` = 2-cells. In `Cat.{v, u}`, `u` = objects and `v` = morphisms (`Cat.{v, max u v}` keeps inserters and comma categories in the same universe). In Section 7, `w₀` (and `w₁`) is the independent diagram-size universe. In `TwoSig.{u₁, u₂, u₃}`, `u₁, u₂, u₃` index category, functor, and transformation symbols; `s₁, s₂, s₃` index sorts, function symbols, and equations. |

## Conventions

- **Composition is diagrammatic:** `f ≫ g` means "first `f`, then `g`". The paper's `g f` is
  `f ≫ g`.
- **Isomorphism of categories** is a functor that is bijective on objects, full and faithful, as
  in Section 2.2. "Over `X`" is an equality of functors with the forgetful functors to `X`. Some
  statements give the inverse functor instead, with `F ⋙ G = 𝟭` and `G ⋙ F = 𝟭`.
- **Bialgebraic data** (Definition 3.1) carry their inserter as data. Results about `Bialg(B)`
  quantify over an arbitrary equifier `E` of the two equations, and `u_B` is `E.e ≫ ins.u`.
- **Monadicity in `CAT`** is Mathlib's `MonadicRightAdjoint`. **Monadicity in a 2-category**
  (Definition 5.1) is `IsMonadic2`: a left adjoint `f` such that, for every object `x`, the
  comparison functor of the induced adjunction `K(x, f) ⊣ K(x, g)` is an equivalence. "Creates"
  in Lemma 5.2 and Corollary 5.3 is Mathlib's `CreatesColimit` (creation up to isomorphism, as in
  the paper).
- **Bi-density** (Definition 7.1, `IsBiDense`) asks for pseudonatural transformations that are
  natural in the 2-cells of `𝒜` as well.
- **Regular and exact categories** (Definition 6.4) are Mathlib's `CategoryTheory.Regular` and the
  repository's `CategoryTheory.BarrExact` (regular, with every equivalence relation effective).
  The checked statements `def_6_4_regular` and `def_6_4_exact` show that they agree with the
  paper's definitions through orthogonal factorization systems.
- **Extremal epimorphisms** (Lemma 6.5 (1)) are Mathlib's `ExtremalEpi`.
- **Sizes.**
  - Statements about `CAT` itself (Section 2) use `Cat.{v, max u v}`, which contains the small
    categories and the locally small large ones.
  - Statements about models in `CAT` take objects and morphisms in independent universes
    (`Cat.{v, u}` or `Cat.{v, max u v}`), so large categories such as `Set = Type v` and
    `ModuleCat.{u} R` instantiate them directly. The copy `ModU R` of `ModuleCat.{u} R` with hom-sets
    lifted by `ULiftHom` survives only in `modelCat_barrExact`, next to
    `modelCat_barrExact_moduleCat`, which states Corollary 6.11 for `ModuleCat.{u} R` itself.
  - In the syntax, signatures, sorts, symbols and equations are types in `Type`.
  - Completeness is relative to a size: `PIEComplete.{s}` (PIE-complete_s) has chosen products of
    `Type s`-indexed families (`HasChosenProductsOfSize.{s}`), chosen finite products, inserters and
    equifiers. The statements for `M^σ` and `M^T` take products at three independent sizes.
  - In Section 7, the `A`-properties (`IsAComplete`, `IsAAccessibleObj`, …) take a size universe
    `w₀` that is independent of the universes of `K`. The paper's "small" refers to its universe of
    sets, while `K(a, c)` is a large, locally small category. Measuring size in the universe of
    2-cells would make every complete hom-category a preorder, by Freyd's argument.
    A test, the development repository's `UlmerBialgebrasTest/NonVacuity/Sanity72.lean`, checks that in `CAT`, for `A = {1}`, the object
    `Set` is `A`-complete, `A`-cocomplete and `A`-accessible.

## How the statements compare with the paper

The definition audit compared every checked statement and definition with the
paper and with Mathlib. The results are below.

### Assumptions and generalizations

No statement assumes more, or applies to fewer objects, than the paper. Section 3's models live in
a 2-category `K` with chosen finite products (`[HasChosenFinProducts K]`), as in the paper, which
fixes a 2-category with finite products before it defines models. Many statements are more
general than the paper's; the changes since the definition audit:
- The generalizations:
  - **Example 3.4**: `Σ_A` is defined for any bicategory `A` and needs no chosen products.
  - **Corollary 6.11 and Lemma 6.10**: stated for `ModuleCat.{u} R` itself
    (now `modelCat_barrExact_moduleCat`, `lem_6_10`); the reduction step (now
    `modelCat_barrExact_reduction`) takes objects and morphisms in independent universes.
  - **Example 3.20 (2)**: `ex_3_20_2` takes any `[Category.{v} C]` on
    `C : Type (max u v)`, so it applies to `ModuleCat.{u} R`.
  - **The `cartThy` family**: the theory-category isomorphisms
    (`modelCat_iso_cartThy_univ`, `grp_modelCat_iso`, `*_cartThy_iso`, …) are stated without
    `AsSmall`; their old forms are tests in the development repository's `UlmerBialgebrasTest/Specializations/`.
  - **Example 3.12**: `ex_3_12_lax` and `ex_3_12_oplax` are derived from the forms for
    pseudofunctors out of any bicategory (`ex_3_12_lax_bicat`, `ex_3_12_oplax_bicat`).
- Corollaries 5.8 and 5.9 no longer bound the number of equations (the proof
  deduplicates them); Example 4.20 (2) no longer assumes `[Nontrivial K]`; Lemma 4.6 (1) and
  Theorem 4.7 (1) allow products indexed by any universe.
- The size migration and the universes of signatures:
  - **Independent universes.** Corollaries 4.13–4.15 and 4.17, Theorem 4.19, Theorem 5.7,
    Theorem 6.6 and Corollaries 6.7–6.8 are stated for categories at independent universes
    (`Cat.{v, max u v}`).
  - **Signatures.** The Section 3 statements (3.11, 3.15, 3.18, 3.21–3.23) take signatures in
    any universes (`TwoSig.{u₁, u₂, u₃}`).
  - **Products.** `ex_2_3_1` has products of any size `w`.
  - **Example 3.20 (1) and (4)** are general.
  - **Proposition 3.11** asks for chosen finite products, as the paper does.
  - **Example 4.20 (1)–(3)** (`ex_4_20_1_coeq`, `ex_4_20_1_eq`, `ex_4_20_2_pushout`,
    `ex_4_20_2_pullback`, `ex_4_20_3`) take any `[Category.{v} C]`, with the products, inserters
    and equifiers of `Cat.{v, u}` as instance arguments. A shape of a constructed kind is any
    `J : Cat.{v, u}` equivalent to the standard one, as in `ex_4_20_general`.
  - **Corollary 5.8** (`cor_5_8`) is stated in `Cat.{v, u}`, for signatures in any universes
    (`TwoSig.{t₁, t₂, t₃}`) with sorts, function symbols and equations in independent universes;
    the size bounds are compared after `Cardinal.lift`. **Corollary 5.9** (`modelCat_monadic`,
    `modelCat_strictlyCreates`) takes `C` with objects and morphisms in independent universes, so it
    applies to `Set`. **Corollary 6.9** and the trusted
    definitions `restrictFn` and `LaxLimit.ThyObj` take signatures in any universes. These
    statements take the products, inserters and equifiers of `Cat.{v, u}` as instance arguments.
  - **Corollary 3.24** (`cor_3_24`) holds for categories in any universes. Its proof is
    Mathlib's `Functor.mapMon`, not the paper's route through Corollary 3.23 (1); the author
    accepted this route.
  - **Lemma 6.10** (`lem_6_10`) is stated for `ModuleCat.{u} R` itself (`Loc.modCatModel R`, in
    `Cat.{u, u + 1}`); the earlier form for the copy with hom-sets lifted to `Type (u + 1)`
    (`Loc.modModel R`) follows by change of universe and is kept in
    the development repository's `UlmerBialgebrasTest/Specializations/Sec6Loc.lean`.
  - **Corollary 6.11**: `modelCat_barrExact_reduction` takes `A` with objects and morphisms in
    independent universes, and `modelCat_barrExact_moduleCat` states the corollary for
    `ModuleCat.{u} R` itself (`modelCat_barrExact` keeps the copy `ModU R` with lifted hom-sets).
  - Every statement whose form comes from the size migration records it as one deviation line,
    `different (size): … (CHALLENGE.md, *Size migration*)`; `stronger` is kept for mathematical
    strengthenings (fewer hypotheses, more general objects, more conclusions).

### Stronger than the paper

- **Examples 3.4, 3.9 and 3.12** also hold for a bicategory `A` and pseudofunctors `A → K`
  (`UlmerBialgebras/Paper/Sec3DefsPsFun.lean`; `UlmerBialgebras/Paper/Sec3ExBicat.lean`: `ex_3_12_lax_bicat`, `ex_3_12_oplax_bicat`); the paper takes a small
  2-category and strict 2-functors.
- **Example 3.20 (2)** (`ex_3_20_2`) needs only a braided monoidal category; the paper states it
  for symmetric ones.
- **Example 4.20** uses, in each statement, only the part of the paper's hypotheses (symmetric
  monoidal closed, complete, cocomplete, `⊗` preserving finite limits) that it needs.
- **Corollary 5.9** (`modelCat_strictlyCreates`): the clause that `U` strictly creates countable
  sifted colimits bounds only the objects of the shape, with hom-sets of any size; the paper's
  countable shapes also bound the morphisms.
- **Lemma 3.18 (3.3)** (`lem_3_18_2`) holds for any substitution between arbitrary contexts, at
  any environment; the paper evaluates at `M_0`.
- **Corollary 7.5** (`cor_7_5`) holds in any strict 2-category with a bi-dense class `A`; the
  paper's Section 7 assumes `K` PIE-complete.
- **Corollary 5.3 (in particular)** (`cor_5_3_bialg`) holds in any strict 2-category, without
  chosen inserters or equifiers.
- **Theorem 6.6 (3)**: the clause that `U` strictly creates coequalizers of kernel pairs
  (`thm_6_6_3_coeq`) omits the hypothesis that `Bialg(B)` has a terminal object, which it does not
  use.
- **Corollary 6.9** (`cor_6_9`) allows the maps of symbols and equations of the sub-signature to be
  non-injective.
- **Lemma 6.10** (`lem_6_10`) proves joint conservativity and the preservation properties for
  every family of lifts of the localizations, not only for the induced one.
- **Corollary 6.11** also proves the case the paper cites from Gran, Sterck and Vercruysse:
  `Hopf_k^coc` is Barr-exact for every field `k`, and `modelCat_barrExact_reduction` takes any
  symmetric monoidal `A`.
- **Definition A.4** (`def_A_4_isForest`) also covers the linear graph with `n = 0`.
- **Refinements checked next to the paper's statements**: `thm_5_10_2_cardinal` (the left
  adjoint of Theorem 5.10 (2) preserves κ″-presentable objects), `thm_5_11_1_cardinal`
  (Theorem 5.11 (1) at one fixed regular cardinal κ), `thm_5_11_acc_cardinal` (the accessibility
  clause of Theorem 5.11 with explicit cardinals κ ⊲ κ′ ⊲ κ″), and `cor_4_12_right` (the right
  Kan form of Corollary 4.12).

### Same content, different form

- **Accessible functors.** The paper follows Adámek–Rosický: an accessible functor goes between
  accessible categories by definition. Mathlib's `Functor.IsAccessible` asks only for some regular
  `κ` with `F` `κ`-accessible. So where a statement takes an accessible functor (Example 2.3 (2),
  Theorems 5.10 (2) and 5.11, and `IsAAccessibleMor'` of Definition 7.2), it also assumes
  `IsAccessibleCategory` on the domain and codomain, unless the paper's hypotheses already give it
  (a locally presentable category is accessible). This is the paper's convention made explicit,
  not a strengthening.
- **Remark 3.2** (`rem_3_2_adj`, `rem_3_2_rel`) quantifies over an arbitrary inserter `I'` of
  `r, id_c`. The canonical comparison `Rem32.comparison : I' ⟶ Ins(f, g)` is an isomorphism over
  `c` (the paper's `Ins(f, g) ≅ Ins(r, id_c)`), the transposed equations have an equifier, and
  every such equifier is isomorphic over `c` to `Bialg(B)`. The transposed datum is
  `Rem32.transposedDatum` (`UlmerBialgebras/Paper/Sec3DefsTransposedDatum.lean`).
- **Examples 3.20 (1), (2) and (4)**: "`M^T` is the category of monoids (Hopf monoids, monad
  algebras, commutative monoids)" is an isomorphism of categories over `C` with Mathlib's
  `Mon C`, `Hopf C`, `T.Algebra` or `CommMon C`.
- **Example 3.20 (1) for an arbitrary `Σ_Mon`-model** (`ex_3_20_1_magma`, `ex_3_20_1_iff`): the
  objects of `M^σ` are the pointed magmas `(x, m, e)`, and such an object lies in `M^T` exactly
  when the associativity and unit laws hold. The notation is in `UlmerBialgebras/Paper/Sec3DefsMonModel.lean`.
  Some components are composed with `eqToHom` along equalities of objects that do not hold
  definitionally.
- **Proposition 3.11** for lax morphisms uses the paper's formula for the composite
  (`LaxData.comp`).
- **Examples 3.4, 3.9 and 3.12** (`ex_3_12_lax`, `ex_3_12_oplax`): lax (oplax) natural
  transformations between strict 2-functors correspond bijectively to lax (oplax) morphisms of
  their models, and modifications to 2-cells. Pseudo (strict) transformations correspond to strong
  (strict) morphisms. The 2-category `A` is arbitrary: `Σ_A` and its model `M_F` live in `A`'s
  universes (`Type ua`, `Bicategory.{wa, va} A`), not in universe 0.
- **Remark 3.17** is stated by `IsThyRep` (an isomorphism of categories `K(x, E) ≅ K(x, M)^T`,
  strictly 2-natural in `x`) with `rem_3_17_unique`, `rem_3_17_exists` and `rem_3_17_em` (the
  Eilenberg–Moore object). It was earlier stated by rem_3_17_em_isAlg, rem_3_17_em_one
  and rem_3_17_em_two; their old forms are tests in the development repository's `UlmerBialgebrasTest/Specializations/`.
- **Remark 4.5 and Lemma 4.6** (`rem_4_5`, `lem_4_6_1`–`lem_4_6_3`) use the encoding of
  isomorphisms of categories above. In Lemma 4.6 (1) the comparison is `Product.kanFunctorLeft`.
- **Definition 4.9** is `BialgDatum.IsRelativelyAlgebraic` and `IsRelativelyCoalgebraic`
  (`UlmerBialgebras/Paper/Sec4DefsRelativelyAlgebraic.lean`), with the checked consequences in
  `UlmerBialgebras/Paper/Sec4RelativelyAlgebraic.lean`.
- **Corollary 4.10** reads: if every left Kan extension of `u_B d` along `k` is absolute, then
  `u_B` strictly creates the left Kan extensions of `d` along `k`. This is the paper's statement,
  since Kan extensions are unique up to isomorphism.
- **Lemma 5.6** is split in two: `lem_5_6_iso` states the isomorphism `LE(d, k) ≅ Ins(H, id)` over
  `LE(ud, k)` and the preservation clause, and `lem_5_6` the "in particular" clause. `H` is
  `LeftExt.pushoutStep`, and `Ins(H, id)` is Mathlib's category `Endofunctor.Algebra H`.
- **Theorem 6.6 (2)** states "`U` strictly creates pullbacks" as strict creation of the limits of
  the shape `WidePullbackShape (ULift WalkingPair)`.
- **Section 2.2, reflection** (`rep_reflects_prod`, `rep_reflects_ins`, `rep_reflects_equif`): a
  cone whose comparison functors `K(x, pt) → …` are isomorphisms of categories for every `x` is a
  product, inserter or equifier.
- **Theorems 7.6 and 7.7**: the (co)monadicity clauses are the separate statements
  `thm_7_6_monadic` and `thm_7_7_monadic`.
- **Theorem 7.6**, Kan extension and cocompleteness clauses (`thm_7_6`): the paper states all the
  conclusions under shared hypotheses. Bi-density of `𝒜` and the right Kan extensions are used
  only by the monadicity conclusion, which `thm_7_6_monadic` keeps; the paper's proof of the last
  part cites Lemma 5.6 alone. So `thm_7_6` does not assume them (an assumption removed).
- **Theorem 7.7**, accessibility and local presentability clauses (`thm_7_7`): bi-density is used
  only by the (co)monadicity conclusions, which `thm_7_7_monadic` keeps, so `thm_7_7` does not
  assume it (an assumption removed).

## Notes on particular results

### Addition beyond the paper: doctrinal adjunction

Eight checked statements (`Companion/Statements/ExtrasDoctrinal.lean`, definitions in
`UlmerBialgebras/Paper/Sec5DefsDoctrinal.lean`), the ingredient behind the proof of Theorem 7.4. For a lax
morphism `G : M → N` of Σ-models and adjunctions `F_c ⊣ G_c` in `K`:

- `mate_oplaxMor`, `laxMor_iff_oplaxMor_mate`, `mateStr_bijective`: the mates of the structure
  2-cells of `G` make the `F_c` an oplax morphism `N → M`, and for fixed cells this is a bijection
  between lax structures on the `G_c` and oplax structures on the `F_c`.
- `idData_laxMor`: identity lax morphisms (Proposition 3.11, which the library had only for
  composites).
- `doctrinal_adjunction`, `doctrinal_adjunction_strong`: if the mates are invertible, the `F_c`
  form a lax morphism `F`, and the units and counits of the `F_c ⊣ G_c` are 2-cells of lax
  morphisms (`LaxTwoCell`), so `F ⊣ G` among lax morphisms; if `G` is strong, so is `F`.
  `G` need not be strong when `F` is: the free abelian group functor `(Set, ×, 1) → (Ab, ⊗, ℤ)`
  is strong monoidal, its right adjoint only lax (`ℤ/2 × ℤ/2 → ℤ/2 ⊗ ℤ/2` is not injective).
- `laxNat_mate_oplaxNat`: the case of lax natural transformations (Example 3.12), the mate part
  of Houston's Proposition 2.35: the mates of a lax transformation with left adjoint components
  form an oplax transformation.
- `laxNat_adjunction`: the adjunction part of Houston's Proposition 2.35, through the
  correspondence of Example 3.12: if the mates are invertible, their inverses form a lax
  transformation `τ : G ⇒ F`, and the units and counits of the `l_a ⊣ σ_a` are 2-cells of lax
  morphisms between the corresponding morphisms of `Σ_A`-models, so `τ ⊣ σ`.

### Additions beyond the paper: classical theories, theory morphisms, translations

Sixteen checked statements that the paper does not contain:

- **Classical theories against Mathlib** (`Companion/Statements/ExtrasClassical.lean`): the models of the
  equational theories of monoids, commutative monoids and groups in a category with finite
  products are isomorphic to Mathlib's `Mon C`, `CommMon C` and `Grp C`, over `C`
  (`monTheory_modelCat_iso`, `cmonTheory_modelCat_iso`, `grpTheory_modelCat_iso`), and to the
  `Σ_Cart`-models of their translations (`*_cartThy_iso`). The forgetful functors to `Mon C` match
  the reducts along the theory morphisms `T_Mon → T_CMon` and `T_Mon → T_Grp` (`cmon_mon_forget`,
  `grp_mon_forget`).
- **Morphisms of theories** (`Companion/Statements/ExtrasTheoryMorphism.lean`): a morphism `T₁ → T₂` sends
  sorts to sorts and function symbols to terms, and the translated axioms of `T₁` must be
  derivable from `T₂` in equational logic. It induces `φ^* : Mod(T₂) ⥤ Mod(T₁)` over the sorts;
  morphisms compose, and `φ^*` is functorial. Inclusions `T ⊆ T'` and reducts are instances.
- **Translations** (`Companion/Statements/ExtrasAlgTranslations.lean`): a `Σ_Cart`-theory `T` gives an
  equational theory `T'` (one operation for each function symbol and each factor of its
  coarity), with `Mod_C(T') ≅ C^T` over `C^S` (`cartTheory_modelCat_iso`, the converse of
  `modelCat_iso_cartThy_univ`); and for one sort, the models of an equational theory in `Type u`
  are Mathlib's first-order models of its universal closures, possibly empty
  (`modelCat_type_iso_foModelCat`).


### Corollary 6.11

`UniversalAlgebra.modelCat_barrExact` states the paper's result for a commutative von Neumann
regular ring `R`, for both `A = Mod_R^op` (affine `R`-schemes) and `A = Mod_R`. The theory `T` is
an equational theory of universal algebra over the language of groups in each sort with further
function symbols (`grpExtLanguage`), containing the translated group axioms; its models are
`T.ModelCat`. `Comon_A^coc` is Mathlib's `CommComon A` with Fox's cartesian structure. The
`Σ_Cart` form `grpExt_barrExact` of `UlmerBialgebras/Proofs/Sec6/Sec6Hopf.lean` is a separate result: the checked
statements are not proved from it.

The proof follows the paper's steps, except the first, which is regrouped (proof score 3;
`docs/STATE.yml`, its proof_route):
- **Reduction** (`modelCat_barrExact_reduction`): if `Hopf_A^coc = Grp (CommComon A)` is
  Barr-exact, so is `(Comon_A^coc)^T`. It goes through `isExactCat_modelCat` and
  `isExactCat_cartThy_of_grp`: the dictionary `GrpModels.grpModelEquiv : B^{T_Grp} ≌ (S → Grp B)`
  identifies models of the theory of groups with families of internal groups, and Corollary 6.9
  (`isExactCat_thyObj_of_restrict`) lifts exactness to every algebraic extension `T`.
- **`A = Mod_R^op`:** `CommComon (ModU R)ᵒᵖ` is equivalent to the opposite of commutative
  `R`-algebras, and affine group schemes over `R` are Barr-exact (`AffGrp.isBarrExact_affGrp_vnr`,
  proved by localization from Takeuchi's theorem over fields; the paper cites the field case).
- **`A = Mod_R`:** exactness descends along the localizations at the maximal ideals to the residue
  fields (`Loc.isBarrExact_grp_commComon_of_field`), by Lemma 6.5(3) for the family of
  localizations (`isBarrExact_of_family_transfer`). The localizations of modules are lifted to
  comonoids by a direct construction, not by the general Lemma 6.10 (`lem_6_10`), which the proof
  does not use. Over a field, `Hopf_k^coc` is Barr-exact by Newman's bi-ideal
  correspondence (`InternalGroups.isBarrExact_cocommHopf_of_field`). Newman's categorical bi-ideal
  map of every internal group of `Comon_k^coc` is bijective
  (`InternalGroups.biIdealMap_bijective_of_field`), because it is conjugate to Newman's algebraic
  correspondence `K ↦ H K⁺` between sub-Hopf algebras and left bi-ideals, whose two closure
  identities are proved. Gran, Sterck and Vercruysse first proved this field case.

### Appendix A

- **Lemma A.3** (`lem_A_3`): every labelled forest has a free enriched category. Its hom-object
  from `a` to `b` is identified with `ℓ(p) = ℓ(p_n) ⊗ ⋯ ⊗ ℓ(p_1)` for the path `p : a → b`, and is
  initial if there is no path. Composition, identities and edge inclusions are stated, and
  enriched functors out of it correspond to vertex maps with edge maps. The construction works
  over any base with an absorbing initial object.
- **Definition A.4** (`def_A_4_isForest`): the linear graphs `0 → ⋯ → n-1` are forests, so the
  linear categories are free categories in the sense of Lemma A.3.
- **Theorem A.5** (`appendix_biDense`): the point, the arrows and the three-object linear
  categories form a bi-dense class. The proof (`UlmerBialgebras/Proofs/Appendix/AppendixLinearDensity.lean`) does not
  depend on the auxiliary density results below.
- **Auxiliary checked statements** (`UlmerBialgebras/Paper/AppendixA3A5.lean`): the classification of the unit,
  arrow and three-object probes, the arrow transformations, the fully faithful part of A.5, and two
  larger bi-dense classes (all categories with at most three objects, and all small enriched
  categories). The larger classes do not replace Theorem A.5: they are weaker, since they follow
  from it (a full sub-2-category that contains a bi-dense one is bi-dense).
- **Tensor order.** The library composes `Hom(a,b) ⊗ Hom(b,c)`, the paper `Hom(b,c) ⊗ Hom(a,b)`.
  `UlmerBialgebras/Paper/AppendixDefsReverse.lean` translates between the two through the monoidal opposite of
  the base. No symmetry or braiding is assumed.
