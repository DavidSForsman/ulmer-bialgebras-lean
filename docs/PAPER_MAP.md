# Paper ↔ Lean map

One row per numbered result of D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*
(`paper/sections/*.tex`, current numbering). The columns are:

- **Checked theorem**: the statements in `UlmerBialgebras/Paper/` and `Companion/Statements/` that are listed in the three Comparator configurations.
  `scripts/check_compiled_types.lean` checks that `UlmerBialgebras/Proofs/` and `Companion/Proofs/` proves exactly these statements, and
  `scripts/check_axioms.py` that the proofs use only `propext`, `Quot.sound` and
  `Classical.choice`.
- **Proof**: the file of the proof in `UlmerBialgebras/Proofs/` and `Companion/Proofs/`.
- **Main declarations**: library declarations that the proof calls directly. This is a pointer,
  not a complete list.
- **Fidelity**: how the Lean statement compares with the paper's, computed from the ledger
  (`fidelity` in `docs/STATE.yml`, the vocabulary of the statement prose): *exact*, *stronger*,
  *weaker*, *different* or *scope* (parts omitted).
- **Status**: computed from the development build: *formal* (every
  checked theorem of the row is proved with the standard axioms), *cond{X}* (proved from a
  hypothesis `X` that stands for a cited result), *stated* (a
  checked theorem is not proved yet) or *definition* (formalized as definitions, with no statement
  to check). A remark in brackets is hand-written; it says *partial* exactly when the ledger has
  `scope: partial`.

The three lists contain 175 checked statements, and every one appears below. File paths may change
when files are moved; the declaration names are stable.

## 2. 2-Categorical Preliminaries and PIE Limits

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 2.1 | PIE Limits in a 2-Category | — | — | `Foundations/CategoryTheory/Bicategory/PIE.lean` | exact | definition |
| Remark 2.2 | PIE Limits in CAT | `rem_2_2_ins`, `rem_2_2_equif` | `UlmerBialgebras/Proofs/Sec2/Sec2.lean` |  | scope | formal (partial: products of categories not stated separately) |
| Example 2.3 |  | `ex_2_3_1`, `ex_2_3_2_prod`, `ex_2_3_2_prod_lift`, `ex_2_3_2_ins`, `ex_2_3_2_equif` | `UlmerBialgebras/Proofs/Sec2/Sec2.lean` | `isAccessibleCategory`, `eval_isAccessible`, `pi'_isAccessible`, `forget_isAccessible` | scope | formal (partial: Lack–Tendas V-ACC omitted) |

## 3. Bialgebras

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 3.1 | Bialgebraic Data and Their Bialgebras | — | — | `UlmerBialgebras/Paper/Sec3Defs.lean` | exact | definition |
| Remark 3.2 |  | `rem_3_2_adj`, `rem_3_2_rel` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean`, `UlmerBialgebras/Proofs/Sec3/TransposedDatum.lean` | `Rem32.comparison_iso_and_isoOver_transposed`, `comparisonInv`, `equifOfTransposed`, `isoOver_transposed` | exact | formal |
| Definition 3.3 | The 2-Signature Sigma | — | — | `UlmerBialgebras/Examples/SignatureEx.lean`, `UlmerBialgebras/Syntax/Syntax.lean` | exact | definition |
| Example 3.4 |  | — | — | `UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`, `UlmerBialgebras/Paper/Sec3DefsPsFun.lean`, `UlmerBialgebras/Paper/Sec3Ex.lean` | stronger | definition |
| Definition 3.5 | The 1-Signature sigma | — | — | `UlmerBialgebras/Syntax/Syntax.lean` | exact | definition |
| Definition 3.6 | The Term Graph | — | — | `UlmerBialgebras/Syntax/Syntax.lean` | exact | definition |
| Definition 3.7 | Arity, Coarity, and Bialgebraic Theories | — | — | `UlmerBialgebras/Syntax/Syntax.lean` | exact | definition |
| Definition 3.8 | Sigma-Models | — | — | `UlmerBialgebras/Models/CoModel.lean`, `UlmerBialgebras/Models/Semantics.lean` | exact | definition |
| Example 3.9 |  | — | — | `UlmerBialgebras/Paper/Sec3DefsTwoFun.lean`, `UlmerBialgebras/Paper/Sec3DefsPsFun.lean` | stronger | definition |
| Definition 3.10 | Lax, Oplax, and Strong Morphisms | — | — | `UlmerBialgebras/Models/Lax.lean`, `UlmerBialgebras/Models/Oplax.lean` | exact | definition |
| Proposition 3.11 |  | `prop_3_11_lax`, `prop_3_11_strong`, `prop_3_11_oplax` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `comp_str_isIso` | exact | formal |
| Example 3.12 |  | `ex_3_12_lax`, `ex_3_12_oplax`, `ex_3_12_lax_bicat`, `ex_3_12_oplax_bicat` | `UlmerBialgebras/Proofs/Sec3/Sec3Ex.lean`, `UlmerBialgebras/Proofs/Sec3/Sec3ExBicat.lean` | `laxEquiv`, `laxModifEquiv`, `laxIsPseudo_iff`, `laxIsStrict_iff`, `PsFun.laxEquiv`, `PsFun.oplaxEquiv` | stronger | formal; gap: explicit modification 2-cell coherence and round-trip equivalences (`TwoFun.laxModifEquiv`, `PsFun.laxEquiv` in `UlmerBialgebras/Proofs/Sec3/Sec3Ex.lean`, `UlmerBialgebras/Proofs/Sec3/Sec3ExBicat.lean`) |
| Definition 3.13 | The Object of Operations M^sigma | — | — | `UlmerBialgebras/Models/Bialgebra.lean`, `UlmerBialgebras/Examples/FieldCalc.lean` | exact | definition |
| Definition 3.14 | Path Evaluation and the Object of Bialgebras M^T | — | — | `UlmerBialgebras/Models/Bialgebra.lean`, `UlmerBialgebras/Models/CoBialgebra.lean` | exact | definition |
| Proposition 3.15 |  | `prop_3_15` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `thyEquif` | exact | formal |
| Definition 3.16 |  | — | — | `UlmerBialgebras/Kan/KanModel.lean` (also `UlmerBialgebras/Factorization/RepModel.lean`, `UlmerBialgebras/Factorization/RepTerm.lean`) | exact | definition |
| Remark 3.17 |  | `rem_3_17_unique` (uniqueness, Yoneda), `rem_3_17_exists` (`M^T` from given limits represents `K(-, M)^T`), `rem_3_17_em` (the Eilenberg–Moore example, as an iff) | `UlmerBialgebras/Proofs/Sec3/Sec3MonadAlgObject.lean` | `IsThyRep`, `Model.thyObjOf`, `Model.canonAlg`, `Model.algComparison`, `Model.homThyMap`, `MndK.model`, `MndK.IsAlg`, `MndK.emAlg` | exact | formal; isomorphism of categories as bijective on objects, full and faithful; uniqueness on objects; gap: strict 2-Yoneda uniqueness and Eilenberg–Moore iff (`rem_3_17_unique`, `rem_3_17_em` in `UlmerBialgebras/Proofs/Sec3/Sec3MonadAlgObject.lean`) |
| Lemma 3.18 |  | `lem_3_18_1`, `lem_3_18_2` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `interp_subst`, `eta_subst` | stronger | formal |
| Examples 3.19 | Examples of 2-Signatures | — | — | `UlmerBialgebras/Paper/Sec5DefsCart.lean`, `UlmerBialgebras/Examples/SignatureEx.lean` | exact | definition (`Σ_Cart`, `Σ_Mon`, `Σ_SMon`, `Σ_Adj`, `Σ_Mnd`, `Σ_Distr`) |
| Examples 3.20 |  | `ex_3_20_1`, `ex_3_20_1_magma`, `ex_3_20_1_iff`, `ex_3_20_3`, `ex_3_20_2`, `ex_3_20_4_algebraic`, `ex_3_20_4_mnd`, `ex_3_20_4_mon`, `ex_3_20_4_smon` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean`, `UlmerBialgebras/Proofs/Sec3/Sec3Theories.lean` | `comparison_comp_inverseFunctor`, `inverseFunctor_comp_comparison`, `sigObj_bijective`, `hom_base_injective` | stronger | formal; gap: explicit round-trip functor equivalences for monoids, monoidal categories, and fields (`mem_thy_iff` in `UlmerBialgebras/Proofs/Sec3/MonModelCalc.lean`, `comparison_comp_inverseFunctor` in `UlmerBialgebras/Examples/FieldCalc.lean`, `UlmerBialgebras/Proofs/Sec3/LaxLimitEquiv.lean`) |
| Lemma 3.21 |  | `lem_3_21_1`, `lem_3_21_2` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `sigMor`, `sigMor_u`, `sigIns`, `theta_path` | exact | formal |
| Theorem 3.22 | Induced Functor of Algebras Theorem | `thm_3_22` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `exists_unique_thyMor` | exact | formal |
| Corollary 3.23 |  | `cor_3_23_1`, `cor_3_23_2`, `cor_3_23_3` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` | `exists_unique_thyMor_of_algebraic`, `exists_thyMor_of_co`, `exists_unique_thyMor_of_strong` | exact | formal |
| Corollary 3.24 |  | `cor_3_24` | `UlmerBialgebras/Proofs/Sec3/Sec3.lean` |  | different | formal |

## 4. Lifting Limits and Colimits

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 4.1 |  | — | — | `UlmerBialgebras/Kan/Kan.lean` | exact | definition |
| Definition 4.2 | Kan Extensions | — | — | `UlmerBialgebras/Kan/Kan.lean`, `UlmerBialgebras/Paper/Sec4DefsExt.lean` | exact | definition |
| Definition 4.3 |  | — | — | `UlmerBialgebras/Kan/Kan.lean` | exact | definition ((1)–(4), for a functor and jointly, with the duals) |
| Definition 4.4 | Preservation and Strict Creation of Kan Extensions | — | — | `UlmerBialgebras/Kan/Kan.lean` | exact | definition (preserves, reflects, strictly creates, creates; left and right) |
| Remark 4.5 |  | `rem_4_5` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `toUnder`, `toUnder_obj_bijective`, `exists_isInitial_of_equivalence_under` | exact | formal |
| Lemma 4.6 |  | `lem_4_6_1`, `lem_4_6_2`, `lem_4_6_3` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `existsUnique_leftExt`, `kanFunctorLeft`, `leftExtToIns_obj_bijective`, `leftExtToEquif_obj_bijective` | exact | formal; gap: product Kan extension construction and morphism-level extension category equivalences (`existsUnique_leftExt` in `UlmerBialgebras/Kan/KanProduct.lean`, `leftExtToIns`, `leftExtToEquif` in `UlmerBialgebras/Proofs/Sec4/ExtensionCategories.lean`) |
| Theorem 4.7 | Lifting Kan Extensions Along PIE Limits | `thm_4_7_1_preserves`, `thm_4_7_1_creates`, `thm_4_7_1_quotient`, `thm_4_7_2_left`, `thm_4_7_2_right`, `thm_4_7_3_left`, `thm_4_7_3_right` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `preserves_leftKan`, `preservesLeftKan_iff`, `product`, `jointlyStrictlyCreates_leftKan` | exact | formal |
| Corollary 4.8 |  | `cor_4_8_left`, `cor_4_8_right` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `Equifier`, `PreservesLeftKan`, `LeftExt`, `QuotientInitial` | exact | formal |
| Definition 4.9 | relatively algebraic and coalgebraic data | `def_4_9_algebraic_datum`, `def_4_9_coalgebraic_datum`, `def_4_9_theories` | `UlmerBialgebras/Proofs/Sec4/Sec4RelativelyAlgebraic.lean` | `BialgDatum.IsRelativelyAlgebraic`, `BialgDatum.IsRelativelyCoalgebraic` | exact | formal |
| Corollary 4.10 |  | `cor_4_10` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `Equifier`, `LeftExt`, `StrictlyCreatesLeftKan`, `RightExt` | exact | formal |
| Corollary 4.11 |  | `cor_4_11_left`, `cor_4_11_right`, `rem_4_11` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `left_of_bialgebraic`, `transport_hom_property`, `LeftCreation`, `right_of_bialgebraic` | exact | formal; gap: explicit coalgebraic dual and isomorphism-transport proofs (`right_of_bialgebraic`, `transport_hom_property` in `UlmerBialgebras/Proofs/Sec4/ModelKanRoute.lean`) |
| Corollary 4.12 |  | `cor_4_12`, `cor_4_12_right` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `tm_preserves_leftKan`, `thy_strictlyCreates_leftKan_of_fn` | stronger | formal; gap: variable/constant base cases in the term induction and explicit coalgebraic dual (`tm_preserves_leftKan`, `thy_strictlyCreates_rightKan_of_fn` in `UlmerBialgebras/Kan/KanModel.lean`) |
| Corollary 4.13 |  | `cor_4_13` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `monadDatum`, `monadEquif`, `toOne`, `preservesRightKan_of_preservesLimitsOfShape` | exact | formal; gap: componentwise-to-product preservation step for algebraic theory terms (`cor_4_13` in `UlmerBialgebras/Proofs/Sec4/Sec4.lean`) |
| Corollary 4.14 |  | `cor_4_14` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `strictlyCreates_leftKan`, `commaIns`, `toOne`, `preservesLeftKan_comp` | exact | formal |
| Corollary 4.15 |  | `cor_4_15` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `strictlyCreates_leftKan`, `overIns`, `toOne`, `preservesLeftKan_of_preservesColimitsOfShape` | exact | formal |
| Lemma 4.16 |  | `lem_4_16` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `preservesColimit_pi_of_componentwise` | exact | formal; gap: general finite-arity induction from binary products to `Fin n`-indexed products (`preservesColimit_pi_of_componentwise` in `UlmerBialgebras/Kan/SiftedPi.lean`) |
| Corollary 4.17 |  | `cor_4_17` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `thy_strictlyCreates_colimits` | exact | formal |
| Corollary 4.18 |  | `cor_4_18` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `preservesWidePushouts_and_regularEpis_pi` | exact | formal; gap: explicit sifted replacement category $\bar{I}$, proof of siftedness, and colimit comparison (`preservesWidePushouts_and_regularEpis_pi` in `UlmerBialgebras/Proofs/Sec4/RegEpiWidePushoutPi.lean`) |
| Theorem 4.19 |  | `thm_4_19` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `thy_strictlyCreates_widePushouts` | exact | formal |
| Example 4.20 |  | `ex_4_20_1_coeq`, `ex_4_20_1_eq`, `ex_4_20_2_pushout`, `ex_4_20_2_pullback`, `ex_4_20_3`, `ex_4_20_3_small`, `ex_4_20_2_vect`, `ex_4_20_general`, `ex_4_20_general_2` | `UlmerBialgebras/Proofs/Sec4/Sec4Hopf.lean`, `UlmerBialgebras/Proofs/Sec4/Sec4Ex420.lean` | `thy_strictlyCreates_reflexiveCoequalizers`, `colimitsComponentwise`, `thy_strictlyCreates_coreflexiveEqualizers`, `limitsComponentwise`, `nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan`, `thy_strictlyCreates_widePushouts_of_regularEpi`, `thy_strictlyCreates_widePullbacks_of_regularMono`, `preservesWidePushoutsOfRegEpis_of_kernelPairs` | stronger, different | formal |
| Corollary 4.21 |  | `cor_4_21` | `UlmerBialgebras/Proofs/Sec4/Sec4.lean` | `fieldCat_isAccessibleCategory`, `fieldUnits_createsConnectedLimits_and_siftedColimits` | exact | formal |

## 5. Detection of Colimits and Monadicity

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 5.1 |  | — | — | `UlmerBialgebras/Paper/Sec3Defs2.lean`, `UlmerBialgebras/Paper/Sec5.lean` | exact | definition |
| Lemma 5.2 |  | `lem_5_2` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `postcomp`, `postcompAdj` | exact | formal |
| Corollary 5.3 |  | `cor_5_3`, `cor_5_3_bialg` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `subst`, `postcomp`, `postcompCompIso`, `Equifier` | stronger | formal |
| Definition 5.4 |  | — | — | `UlmerBialgebras/Paper/Sec3Defs2.lean` | exact | definition |
| Theorem 5.5 |  | `thm_5_5_1`, `thm_5_5_2` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `monadicRightAdjointForget`, `hasChainColimitsLE_of_upTo`, `monadicRightAdjointForgetOfJointEpi` | exact | formal; gap: transfinite free-algebra iteration and Beck reflexive-coequalizer verification (`monadicRightAdjointForget` in `UlmerBialgebras/Monadicity/BigMonadicity.lean`, `monadicRightAdjointForgetOfJointEpi` in `UlmerBialgebras/Proofs/Sec5/EquifJointEpi.lean`) |
| Lemma 5.6 |  | `lem_5_6`, `lem_5_6_iso` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `isRightAdjoint_push_and_exists_initial_leftExt`, `exists_leftExt_iso_algebra_pushoutStep` | exact | formal; gap: lifting of the pushout 2-cell to the inserter and fiber initiality (`isRightAdjoint_push_and_exists_initial_leftExt` in `UlmerBialgebras/Proofs/Sec7/InserterKanExtension.lean`) |
| Theorem 5.7 |  | `thm_5_7` | `UlmerBialgebras/Proofs/Sec5/Sec5_7.lean` | `ColimitsOfAlgebras.hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint`, `ConcreteBialg.concreteMonadic` | different | formal |
| Corollary 5.8 |  | `cor_5_8` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `hasLeftKanExtension_of_thyForget` | different | formal; gap: structural induction on terms showing $M(t)$ preserves $\gamma$-chain colimits and admits relative left adjoints (`hasLeftKanExtension_of_thyForget` in `UlmerBialgebras/Proofs/Sec5/ModelDatumMonadicity.lean`) |
| Corollary 5.9 |  | `modelCat_monadic`, `modelCat_strictlyCreates`, `cor_5_9_small` | `UlmerBialgebras/Proofs/Sec5/UniversalAlgebra/Monadicity.lean`, `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `cartThy_monadic` (Σ_Cart form), `modelCat_iso_cartThy_univ`, `strictlyCreatesLeftKan_of_inv`, `hasLeftKanExtension_of_thyForget`, `thy_strictlyCreates_colimits`, `nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan` | stronger, different | formal |
| Theorem 5.10 | Accessible Adjoint Functor Theorem | `thm_5_10_1`, `thm_5_10_2`, `thm_5_10_2_cardinal` | `UlmerBialgebras/Proofs/Sec5/Sec5Proofs.lean` | `functor`, `isLeftAdjoint_of_preservesColimits_of_isLocallyPresentable`, `hasLimitsOfSize_of_isLocallyPresentable`, `isRightAdjoint_of_isAccessible_of_preservesLimits` | stronger | formal |
| Theorem 5.11 |  | `thm_5_11`, `thm_5_11_1_cardinal`, `thm_5_11_acc_cardinal` | `UlmerBialgebras/Proofs/Sec5/Sec5_7.lean` | `uB_comonadic_monadic_of_jointMono_cat`, `isMonadic2_uB_of_jointMono` | stronger | formal; gap: closure of accessible categories under inserters and equifiers cited from [LPC] 2.72/2.76 (`UlmerBialgebras/Basic/AccessibleInserter.lean`, `UlmerBialgebras/Basic/AccessibleEquifier.lean`, `UlmerBialgebras/Basic/AccClosure.lean`) |

## 6. Factorization Systems, Regularity, and Exactness

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 6.1 | Orthogonal Factorization System | — | — | `Foundations/CategoryTheory/Factorization/OFS.lean` | exact | definition |
| Remark 6.2 |  | `rem_6_2` | `UlmerBialgebras/Proofs/Sec6/Sec6Factorization.lean` | `orth`, `e_isStableUnderRetracts`, `m_isStableUnderRetracts` | exact | formal |
| Theorem 6.3 | Lifting OFS Along PIE Limits | `thm_6_3_1`, `thm_6_3_2`, `thm_6_3_3` | `UlmerBialgebras/Proofs/Sec6/Sec6Factorization.lean` | `prodOFS`, `prodOFS_unique`, `ext_of_le` | exact | formal |
| Definition 6.4 |  | `def_6_4_regular`, `def_6_4_exact` | `UlmerBialgebras/Proofs/Sec6/Sec6Factorization.lean` | `isRegularCat_iff_regular`, `e_eq_extremalEpi`, `BarrExact.mk'`, `isEquivRel_iff_isEquivalenceRelation` | exact | formal |
| Lemma 6.5 |  | `lem_6_5` | `UlmerBialgebras/Proofs/Sec6/Sec6Factorization.lean` | `regular_exact_transfer_of_preservesPullbacks`, `isRegularCat_iff_regular`, `isExactCat_iff_barrExact`, `e_eq_extremalEpi` | exact | formal |
| Theorem 6.6 |  | `thm_6_6_1`, `thm_6_6_2`, `thm_6_6_3`, `thm_6_6_3_coeq` | `UlmerBialgebras/Proofs/Sec6/Sec6Bialgebra.lean` | `Equifier`, `Orthogonal`, `ext_of_le`, `isRegularCat_iff_regular`, `isExactCat_iff_barrExact` | stronger, different | formal |
| Corollary 6.7 |  | `cor_6_7` | `UlmerBialgebras/Proofs/Sec6/Sec6Proofs.lean` | `fn_repPreservesLeft`, `hasUniqueLiftedOFS_of_rep`, `tm_repPreservesLeft`, `tm_repPreservesRight_of_isVar` | different | formal |
| Corollary 6.8 |  | `cor_6_8` | `UlmerBialgebras/Proofs/Sec6/Sec6Proofs.lean` | `Equifier`, `isExactCat_iff_barrExact`, `down` | different | formal |
| Corollary 6.9 |  | `cor_6_9` | `UlmerBialgebras/Proofs/Sec6/Sec6Proofs.lean` | `thyObj`, `thySubSigForget`, `hasFiniteLimits_hom_thyObj` | stronger, different | formal |
| Lemma 6.10 |  | `lem_6_10` | `UlmerBialgebras/Proofs/Sec6/Sec6Loc.lean` | `IsVonNeumannRegular.isField_localizationAtPrime` | stronger | formal |
| Corollary 6.11 |  | `modelCat_barrExact_reduction`, `modelCat_barrExact`, `modelCat_barrExact_moduleCat` | `UlmerBialgebras/Proofs/Sec6/UniversalAlgebra/Exactness.lean` | `isExactCat_modelCat`, `Loc.isBarrExact_grp_commComon_op`, `Loc.isBarrExact_grp_commComon_of_field`, `isExactCat_thyObj_of_restrict`, `ofRestrictFn_toPath`, `grp_modelCat_iso`, `cocomm_hasFiniteLimits`, `CommComon.hasReflexiveCoequalizers`, `cocomm_standing`, `isExactCat_grpExtTheory_univ`, `isExactCat_iff_barrExact`, `isBarrExact_iff_barrExact` | stronger, different | formal |

## 7. Monadicity and Local Presentability in 2-Categories

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition 7.1 |  | `yoneda_biDense` (Yoneda remark), `isBiDense_iff_isBiDense_fullSubBicatι` (Hofstra–Karvonen comparison) | `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean`, `UlmerBialgebras/Proofs/Sec7/Sec7Variant.lean` | `Paper.IsBiDense` (`UlmerBialgebras/Paper/Sec7Defs.lean`), `CategoryTheory.Pseudofunctor.IsBiDense` (`Foundations/CategoryTheory/Bicategory/BiDense.lean`), `BiDenseBridge.Φ`, `fullSubBicatι` | exact | formal (with checked consequences) |
| Definition 7.2 | A Properties | — | — | `UlmerBialgebras/Paper/Sec7Defs.lean`, the development repository's `UlmerBialgebrasTest/NonVacuity/Sanity72.lean` | exact | definition |
| Definition 7.3 | A-local presentability | — | — | `UlmerBialgebras/Paper/Sec7Defs.lean` | exact | definition |
| Theorem 7.4 |  | `thm_7_4` | `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` | `exists_leftAdjoint_of_isARightAdjoint` | stronger | formal; gap: naturality of the hom-set bijections and doctrinal assembly of pointwise left adjoints into a 2-functor (`exists_leftAdjoint_of_isARightAdjoint` in `UlmerBialgebras/Proofs/Sec5/BiDense.lean`, `UlmerBialgebras/Density/ACotensorAdjoint.lean`) |
| Corollary 7.5 |  | `cor_7_5` | `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` | `postcomp`, `exists_rightAdjoint_of_isALeftAdjoint` | stronger | formal |
| Theorem 7.6 |  | `thm_7_6`, `thm_7_6_monadic` | `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` | `Equifier`, `TwoAdj`, `postcomp`, `LeftExt`; sharpened: `isMonadic2_uB_of_relLeftAdj2_sizeLE` (the development repository's `Solution/BoundedMonadicity.lean`) | stronger | formal; gap: probe-wise transfer of $\mathcal{A}$-joint epimorphy and 2-categorical monadicity assembly (`isMonadic2_uB_of_relLeftAdj2_sizeLE` in the development repository's `Solution/BoundedMonadicity.lean`, `thm_7_6` in `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean`) |
| Theorem 7.7 |  | `thm_7_7`, `thm_7_7_monadic` | `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` | `Equifier`, `uB_isAAccessibleMor'`, `uB_isAComplete_and_continuous`, `uB_hasAndPreservesARightKan` | stronger, different | formal; gap: term induction for $\mathcal{A}$-accessibility/continuity of $M(t)$ and PIE-limit closure (`uB_isAAccessibleMor'`, `uB_isAComplete_and_continuous` in `UlmerBialgebras/Proofs/Sec5/BiDense.lean`) |

## Appendix A: Bi-Density of Small V-Categories in V-CAT

| Result | Title | Checked theorem | Proof | Main declarations | Fidelity | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Definition A.1 |  | — | — | `UlmerBialgebras/Paper/AppendixDefs.lean` | exact | definition |
| Definition A.2 |  | — | — | `UlmerBialgebras/Paper/AppendixDefs.lean`, `UlmerBialgebras/Paper/AppendixDefsForest.lean` | exact | definition |
| Lemma A.3 |  | `lem_A_3`; the one- and two-edge cases `appendix_arrow_classification`, `appendix_three_classification` | `UlmerBialgebras/Proofs/Appendix/Appendix.lean`; the cases in `UlmerBialgebras/Proofs/Appendix/AppendixA3A5.lean` | `arrowFunctorDataEquiv`, `paperThreeFunctorDataEquiv`, `exists_paperVCat_free_of_isForest` | exact | formal; gap: existence of a degree-1 leaf vertex in any finite nonempty forest and enriched colimit gluing (`exists_paperVCat_free_of_isForest` in `UlmerBialgebras/Proofs/Appendix/AppendixForest.lean`) |
| Definition A.4 |  | `def_A_4_isForest` | `UlmerBialgebras/Proofs/Appendix/Appendix.lean` | `linearGraph_isForest` | stronger | formal |
| Theorem A.5 | Bi-Density of 𝒜 in V-CAT | `appendix_biDense`; the fully faithful part `appendix_local_density` | `UlmerBialgebras/Proofs/Appendix/AppendixA3A5.lean`, `UlmerBialgebras/Proofs/Appendix/Appendix.lean` | `isACellDense_of_probes`, `isBiDense_paperLinear` | different | formal; gap: Yoneda factorization reconstructing $F(c, c')$ from probe evaluations and pseudonaturality coherence (`isACellDense_of_probes` in `UlmerBialgebras/Appendix/VCatCellDense.lean`, `isBiDense_paperLinear` in `UlmerBialgebras/Proofs/Appendix/AppendixLinearDensity.lean`) |

## Further checked statements

Statements that the paper uses without a number of their own. They are stated in
`UlmerBialgebras/Paper/AppendixA3A5.lean` and proved in `UlmerBialgebras/Proofs/Appendix/AppendixA3A5.lean`.

The additions beyond the paper on many-sorted equational theories are stated in
`Companion/Statements/ExtrasAlgTheory.lean` (definitions in `UlmerBialgebras/Paper/Sec6DefsAlgTheory.lean` and
`UlmerBialgebras/UniversalAlgebra/Basic.lean`) and proved in
`UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean`.

| Checked theorem | Docstring label | Proof | Main declarations |
| --- | --- | --- | --- |
| `modelCat_iso_cartThy_univ` | The same in arbitrary universes, via `AsSmall C` (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean` | `CartIso.modelCat_iso_cartThy`, `modelCat_transport` |
| `modelCat_type_iso_cartThy` | The Set case, the instance `C := Type u` (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean` | `modelCat_iso_cartThy_univ` |
| `ofLanguage_model_iff` | Set models are Mathlib's first-order models `M ⊨ T` (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean` | `Theory.toFOTheory`, `ofStructure` |
| `ofLanguage_isHom_iff` | Set homomorphisms are Mathlib's `M →[L] N` (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean` | `ofStructure` |
| `grp_modelCat_iso` | The theory of groups vs `grpTheory S` (Cor 6.11), iso over `C^S` in any universes (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasAlgTheory.lean` | `GrpIso.cartThy_iso_grpModel` |
| `appendix_arrow_transformations` | Transformations from the arrow probe are exactly the two endpoint components satisfying one enriched naturality square | `Companion/Proofs/Extras.lean` | `arrowTransformationEquiv` |
| `appendix_small_biDense` | Related density result (auxiliary, not a result of the paper): small enriched categories are bi-dense | `Companion/Proofs/Extras.lean` |  |
| `appendix_tiny_biDense` | Related density result (auxiliary, not a result of the paper): all enriched categories with at most three objects are bi-dense | `Companion/Proofs/Extras.lean` |  |
| `appendix_unit_classification` | Definition A.4 ([forsman2026syntactic]), point probe: enriched functors out of `1` classify objects | `Companion/Proofs/Extras.lean` | `unitFunctorDataEquiv` |
| `rep_preserves_equif` | Section 2.2 | `Companion/Proofs/Extras.lean` | `homProp` |
| `rep_preserves_ins` | Section 2.2 | `Companion/Proofs/Extras.lean` | `homCell`, `postcomp` |
| `rep_preserves_prod` | Section 2.2 | `Companion/Proofs/Extras.lean` |  |
| `rep_reflects_equif` | Section 2.2 | `Companion/Proofs/Extras.lean` | `Equifier`, `homMk`, `forget` |
| `rep_reflects_ins` | Section 2.2 | `Companion/Proofs/Extras.lean` | `assoc₁'`, `Inserter` |
| `rep_reflects_prod` | Section 2.2 | `Companion/Proofs/Extras.lean` | `Product` |

The additions beyond the paper on classical theories, morphisms of theories and translations
are stated in `Companion/Statements/ExtrasClassical.lean`,
`Companion/Statements/ExtrasTheoryMorphism.lean` and `Companion/Statements/ExtrasAlgTranslations.lean` (definitions in
`Companion/Statements/DefsClassical.lean`, `UlmerBialgebras/Paper/Sec6DefsTheoryMorphism.lean` and
`Companion/Statements/DefsAlgTranslations.lean`, and `UlmerBialgebras/UniversalAlgebra/TheoryMorphism.lean`
and `Companion/UlmerBialgebras/UniversalAlgebra/FirstOrder.lean`) and proved in the `UlmerBialgebras/Proofs/` and `Companion/Proofs/` files of the
same names.

| Checked theorem | Docstring label | Proof | Main declarations |
| --- | --- | --- | --- |
| `monTheory_modelCat_iso` | Models of the theory of monoids are Mathlib's `Mon C` (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `ClassicalModels.modelToMon`, `monToModel` |
| `cmonTheory_modelCat_iso` | Commutative monoids, `CommMon C` (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `ClassicalModels.modelToCMon`, `cmonToModel` |
| `grpTheory_modelCat_iso` | Groups, `Grp C` (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `ClassicalModels.modelToGrp`, `grpToModel` |
| `cmon_mon_forget` | `CommMon C ⥤ Mon C` is the reduct along `T_Mon → T_CMon` (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `monCMonMorphism` |
| `grp_mon_forget` | `Grp C ⥤ Mon C` is the reduct along `T_Mon → T_Grp` (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `monGrpMorphism` |
| `monTheory_cartThy_iso` | `Mon C` as `Σ_Cart`-models (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `modelCat_iso_cartThy_univ` |
| `cmonTheory_cartThy_iso` | `CommMon C` as `Σ_Cart`-models (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `modelCat_iso_cartThy_univ` |
| `grpTheory_cartThy_iso` | `Grp C` as `Σ_Cart`-models (addition beyond the paper) | `Companion/Proofs/ExtrasClassical.lean` | `modelCat_iso_cartThy_univ` |
| `modelFunctor_forget` | `φ^*` lies over the sort map (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `TheoryMorphism.modelFunctor` |
| `isTheoryMorphism_comp` | Morphisms of theories compose (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `Derives.subst`, `Derives.translate` |
| `modelFunctor_id` | `id^* = 𝟭` (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `modelCat_eqToHom_toFun` |
| `modelFunctor_comp` | `(ψ ∘ φ)^* = ψ^* ⋙ φ^*` (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `translate_comp` |
| `ofLE_forget` | The inclusion `T ⊆ T'` keeps the objects (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `TheoryMorphism.ofLE` |
| `ofRestrict_forget` | The reduct keeps the objects (addition beyond the paper) | `Companion/Proofs/ExtrasTheoryMorphism.lean` | `TheoryMorphism.ofRestrict` |
| `cartTheory_modelCat_iso` | `Σ_Cart`-theories are equational theories (addition beyond the paper) | `Companion/Proofs/ExtrasAlgTranslations.lean` | `CartToAlg.modelCat_iso_thyCat`, `interpArr_eq`, `modelCat_transport` |
| `modelCat_type_iso_foModelCat` | Single-sorted equational theories are first-order theories (addition beyond the paper) | `Companion/Proofs/ExtrasAlgTranslations.lean` | `AlgFO.toFO`, `AlgFO.ofFO` |

The doctrinal adjunction for Σ-models is stated in `Companion/Statements/ExtrasDoctrinal.lean`
(definitions in `UlmerBialgebras/Paper/Sec5DefsDoctrinal.lean`), and for transformations between pseudofunctors in
`Companion/Statements/ExtrasDoctrinalBicat.lean`; the statements are approved and
all are proved (`UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean`).

| Checked theorem | Docstring label | Proof | Main declarations |
| --- | --- | --- | --- |
| `mate_oplaxMor` | Mates of a lax morphism form an oplax morphism (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Doctrinal.mateOplaxData`, `Doctrinal.mateStr` |
| `laxMor_iff_oplaxMor_mate` | Lax structures are oplax structures on the left adjoints (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Doctrinal.mateOplaxData` |
| `mateStr_bijective` | The mate correspondence (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Doctrinal.mateStr`, `Doctrinal.prodUnit` |
| `idData_laxMor` | Identity lax morphisms (Proposition 3.11) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Doctrinal.LaxData.idData` |
| `doctrinal_adjunction` | Doctrinal adjunction (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Doctrinal.invLaxData`, `LaxTwoCell` |
| `doctrinal_adjunction_strong` | Doctrinal adjunction for strong morphisms (addition beyond the paper) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `doctrinal_adjunction` |
| `laxNat_mate_oplaxNat` | Mates of a lax transformation (Houston, Prop 2.35; Example 3.12) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `Bicategory.mateEquiv` |
| `laxNat_adjunction` | Adjunctions of lax transformations (Houston, Prop 2.35, through Example 3.12) | `UlmerBialgebras/Proofs/Sec5/ExtrasDoctrinal.lean` | `laxNat_mate_oplaxNat`, `ex_3_12_lax`, `LaxTwoCell` |
| `laxTrans_mate_oplaxTrans` | Mates of a lax transformation (Houston, Prop 2.35, through Example 3.12; pseudofunctors) | `Companion/Proofs/ExtrasDoctrinalBicat.lean` | `mate_oplaxMor`, `PsFun.oplaxEquiv` |
| `laxTrans_adjunction` | Adjunctions of lax transformations (Houston, Prop 2.35, through Example 3.12; pseudofunctors) | `Companion/Proofs/ExtrasDoctrinalBicat.lean` | `doctrinal_adjunction`, `PsFun.laxEquiv`, `PsFun.laxModifEquiv`, `PsFun.toLaxData_vComp` |

The additional Hopf and coalgebra results (HOPF-CHECKED) are stated in
`Companion/Statements/ExtrasHopf.lean` and proved in `Companion/Proofs/ExtrasHopf.lean` directly from the existing
library theorems. The embeddings retain their commutative-ring generality; the other results
are over fields.

| Checked theorem | Docstring label | Proof | Main declarations |
| --- | --- | --- | --- |
| `coalgebra_embeds_hopf` | Every coalgebra over a commutative ring embeds into a commutative Hopf algebra (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `Coalgebra.exists_injective_coalgHom_hopfAlgebra` |
| `cocomm_coalgebra_embeds_hopf` | Every cocommutative coalgebra embeds into a commutative cocommutative Hopf algebra (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `Coalgebra.exists_injective_coalgHom_cocomm_hopfAlgebra` |
| `cocomm_comonoid_embeds_group` | Every cocommutative comonoid of modules over a commutative ring embeds into a group object (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `InternalGroups.embedsInGrpObj_commComon_moduleCat` |
| `grp_cocomm_comonoid_monos_regular` | Every mono of group objects in cocommutative coalgebras over a field is regular (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `InternalGroups.isRegularMonoCategory_grp_commComon_of_field` |
| `cocomm_hopf_monos_regular` | Every mono of cocommutative Hopf algebras over a field is regular (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `InternalGroups.isRegularMonoCategory_cocommHopf_of_field` |
| `cocomm_hopf_barr_exact` | Cocommutative Hopf algebras over a field form a Barr-exact category (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `InternalGroups.isBarrExact_cocommHopf_of_field` |
| `cocomm_comonoid_cartesian_closed` | Cocommutative coalgebras over a field form a cartesian closed category (additional checked result) | `Companion/Proofs/ExtrasHopf.lean` | `UlmerBialgebras.CommComon.monoidalClosed_moduleCat` |

## Notes on the paper's current text

`paper/` is version 2 of the paper. Compared with the earlier draft, only the remark on adjoints inducing isomorphisms between bialgebras changed (the inserter of `Ins(lf, id_c)` is named `u''` throughout), together with the order of the bibliography; no numbering changed. Compared with earlier versions:
- **Theorem 4.7 (1):** the quotient-initiality clause now says "extension" instead of "Kan
  extension". `thm_4_7_1_quotient`, which is stated for all extensions, is now an exact match.
  Before, it was a generalization.
- **Definition of accessible categories (the paragraph before Theorem 5.10):** the paper now
  defines `κ`-accessible categories through a small set of `κ`-presentable objects and
  `κ`-directed colimits. Mathlib's `IsCardinalAccessibleCategory`, used in the statements, uses
  `κ`-filtered colimits. The two agree by a standard result (see [LPC], Ch. 1). This is a
  difference of definition only; no statement changes.
- **Theorem 5.10 (2):** the paper now says "if `F` is continuous and accessible". An accessible
  functor is a functor between accessible categories, so `thm_5_10_2`'s
  `[IsAccessibleCategory D]` is implied, and the statement is an exact match.
- The paper no longer uses the pure-subobject characterization of accessible categories. Its
  formalization was separated into the development repository's `Candidates/Accessible/`.


## Steps left implicit in the paper (+gap notes)

For each result whose proof-route note in `docs/STATE.yml` ends in `+gap`, the bullet below names
the step the paper leaves implicit and the file and declaration where the formalization fills it:

- **Example 3.12 (`3.12`):** the paper remarks "similarly one recovers 2-natural transformations
  and modifications," leaving implicit the 2-cell coherence verification identifying modifications
  of lax and oplax morphisms over `Σ_TwoFun` / `Σ_PsFun` with 2-categorical modifications and the
  round-trip equivalence proofs. Filled in `UlmerBialgebras/Proofs/Sec3/Sec3Ex.lean` (`TwoFun.laxModifEquiv`,
  `TwoFun.oplaxModifEquiv`, `TwoFun.laxEquiv`, `TwoFun.oplaxEquiv`) and `UlmerBialgebras/Proofs/Sec3/Sec3ExBicat.lean`
  (`PsFun.laxEquiv`, `PsFun.oplaxEquiv`).
- **Remark 3.17 (`3.17`):** the paper invokes the 2-categorical Yoneda lemma for the uniqueness of
  $M^T$ and states the universal property of the Eilenberg–Moore object without writing out the
  strict 2-Yoneda isomorphism proof or the bijection between the universal properties of
  $M^{T_{\mathrm{Lax}}}$ and the Eilenberg–Moore object. Filled in `UlmerBialgebras/Proofs/Sec3/Sec3MonadAlgObject.lean`
  (`rem_3_17_unique`, `rem_3_17_exists`, `rem_3_17_em`) and `UlmerBialgebras/Paper/Sec3DefsMonadAlgObject.lean`
  (`Model.algComparison`, `MndK.emAlg`).
- **Examples 3.20 (`3.20`):** for each example theory (magmas/monoids, monoidal categories, fields,
  and algebraic/coalgebraic theories), the paper states the equivalence of $M^T$ with the classical
  category of models, leaving out the round-trip functor calculations and coherence proofs. Filled
  in `UlmerBialgebras/Proofs/Sec3/MonModelCalc.lean` (`mem_thy_iff`), `UlmerBialgebras/Examples/MonCalc.lean`,
  `UlmerBialgebras/Examples/FieldCalc.lean` (`comparison_comp_inverseFunctor`,
  `inverseFunctor_comp_comparison`), `UlmerBialgebras/Proofs/Sec3/LaxLimitEquiv.lean`, and
  `UlmerBialgebras/Proofs/Sec3/Sec3Theories.lean`.
- **Lemma 4.6 (`4.6`):** in item (1), the paper cites Mac Lane for the pointwise construction of
  left Kan extensions in $\mathbf{Cat}$; in items (2) and (3), the paper gives the object
  bijections for the extension categories of inserters and equifiers and leaves the morphism
  bijections and naturality in $r$ implicit. Filled in `UlmerBialgebras/Kan/KanProduct.lean`
  (`existsUnique_leftExt`, `kanFunctorLeft`) and `UlmerBialgebras/Proofs/Sec4/ExtensionCategories.lean`
  (`leftExtToIns`, `leftExtOfIns`, `leftExtToEquif`, `leftExtOfEquif`).
- **Corollary 4.11 (`4.11`):** the paper proves the relatively algebraic left-lifting statement and
  states that the coalgebraic right-lifting version and the isomorphism-transport remark follow by
  duality. Filled in `UlmerBialgebras/Proofs/Sec4/ModelKanRoute.lean` (`right_of_bialgebraic`,
  `transport_hom_property`) and `UlmerBialgebras/Proofs/Sec4/Sec4.lean` (`cor_4_11_right`, `rem_4_11`).
- **Corollary 4.12 (`4.12`):** in the induction on terms $t$ showing $M(t)$ preserves left Kan
  extensions, the paper writes out the function-symbol step $B(t_1, \dots, t_n)$ and omits the
  variable and constant base cases as well as the dual coalgebraic proof. Filled in
  `UlmerBialgebras/Kan/KanModel.lean` (`Model.tm_preserves_leftKan`,
  `Model.thy_strictlyCreates_leftKan_of_fn`, `Model.tm_preserves_rightKan`,
  `Model.thy_strictlyCreates_rightKan_of_fn`) and `UlmerBialgebras/Proofs/Sec4/Sec4.lean` (`cor_4_12`,
  `cor_4_12_right`).
- **Corollary 4.13 (`4.13`):** the paper proves the 1-sorted Eilenberg–Moore case and remarks
  "similarly one obtains the classic result for algebraic theories," leaving out the step passing
  from componentwise limit preservation of $M(B)$ to preservation by the tuple functor
  $(M(t_1), \dots, M(t_n)) : \prod_s M_{\sigma(s)} \to \prod_i M_{c_i}$. Filled in
  `UlmerBialgebras/Proofs/Sec4/Sec4.lean` (`cor_4_13`).
- **Lemma 4.16 (`4.16`):** the paper proves the binary product case ($n = 2$) using the finality of
  $\Delta : \mathcal{I} \to \mathcal{I} \times \mathcal{I}$ for sifted $\mathcal{I}$, leaving the
  induction to arbitrary finite arity $n \in \mathbb{N}$ (including $n = 0$) and `Fin n`-indexed
  product categories implicit. Filled in `UlmerBialgebras/Kan/SiftedPi.lean`
  (`preservesColimit_pi_of_componentwise`, `preservesColimitsOfShape_pi_of_componentwise`).
- **Corollary 4.18 (`4.18`):** the paper states that there is a sifted diagram
  $D : \bar{I} \to \mathcal{C}_1 \times \mathcal{C}_2$ choosing reflexive pairs whose coequalizers
  compute the $I$-indexed wide pushout of regular epimorphisms, without constructing $\bar{I}$,
  proving $\bar{I}$ is sifted, or establishing the colimit comparison with the wide pushout shape.
  Filled in `UlmerBialgebras/Proofs/Sec4/RegEpiWidePushoutPi.lean`
  (`preservesWidePushouts_and_regularEpis_pi`).
- **Theorem 5.5 (`5.5`):** in part (1), the paper sketches the ordinal free-algebra construction
  ("similarly to Adámek's theorem") without writing out the transfinite sequence, connecting maps,
  and colimit convergence at $\gamma$; in part (2), applying Beck's monadicity theorem requires
  constructing all reflexive coequalizers in $\operatorname{Ins}(F, G)$ and $\mathcal{C}^B$ and
  verifying that $u_B$ preserves them and reflects isomorphisms. Filled in
  `UlmerBialgebras/Monadicity/BigMonadicity.lean` (`monadicRightAdjointForget`,
  `hasChainColimitsLE_of_upTo`) and `UlmerBialgebras/Proofs/Sec5/EquifJointEpi.lean`
  (`monadicRightAdjointForgetOfJointEpi`).
- **Lemma 5.6 (`5.6`):** in the pushout-step argument in $\mathcal{E}(j, d)$, the paper leaves
  implicit the unique lifting of the pushout 2-cell in $\mathcal{C}$ to $\operatorname{Ins}(F, G)$
  and the verification that the resulting cocone is initial in the fiber over the pushed extension.
  Filled in `UlmerBialgebras/Proofs/Sec7/InserterKanExtension.lean`
  (`isRightAdjoint_push_and_exists_initial_leftExt`, `exists_leftExt_iso_algebra_pushoutStep`).
- **Corollary 5.8 (`5.8`):** to apply Theorem 5.7 to $U : M^T \to M_0$, the paper assumes the
  atomic functors preserve colimits of $\gamma$-chains and have relative left adjoints, leaving
  implicit the structural induction on terms $t$ showing that composite term functors $M(t)$ also
  preserve $\gamma$-chain colimits and admit relative left adjoints. Filled in
  `UlmerBialgebras/Proofs/Sec5/ModelDatumMonadicity.lean` (`hasLeftKanExtension_of_thyForget`).
- **Theorem 5.11 (`5.11`):** the paper deduces accessibility of $u_B : \mathcal{C}^B \to \mathcal{C}$
  by citing the closure of $\mathbf{ACC}$ under inserters and equifiers ([LPC] Theorem 2.72 and
  Exercise 2.76). Here that closure is proved from Makkai–Paré presentable-object generation in
  `UlmerBialgebras/Basic/AccessibleInserter.lean` (`isCardinalAccessibleCategory_general`,
  `exists_colimitsOfShape_general`), `UlmerBialgebras/Basic/AccessibleEquifier.lean`
  (`isCardinalAccessibleCategory_general`), and `UlmerBialgebras/Basic/AccClosure.lean`
  (`isAccessibleCategory`, `forget_isAccessible`, `liftFunctor_isAccessible`).
- **Theorem 7.4 (`7.4`):** the paper exhibits a four-step chain of hom-set bijections for
  $a \in \mathcal{A}$ to show the comparison $L c' \to R^* c'$ is an isomorphism and concludes by
  bi-density and doctrinal adjunction that the global left 2-adjoint exists, leaving implicit the
  naturality verification identifying the composite bijection with precomposition by the canonical
  oplax mate and the doctrinal assembly of pointwise left adjoints into a 2-functor. Filled in
  `UlmerBialgebras/Proofs/Sec5/BiDense.lean` (`exists_leftAdjoint_of_isARightAdjoint`) and
  `UlmerBialgebras/Density/ACotensorAdjoint.lean`.
- **Theorem 7.6 (`7.6`):** in lifting hom-wise monadicity (Theorem 5.5(2)) along the
  representables $\mathcal{K}(a, -)$ for $a \in \mathcal{A}$, the paper leaves implicit the
  probe-wise transfer of $\mathcal{A}$-joint epimorphy and the assembly of the pointwise monadic
  adjunctions into a 2-adjunction via Theorem 7.4. Filled in the development repository's `Solution/BoundedMonadicity.lean`
  (`isMonadic2_uB_of_relLeftAdj2_sizeLE`) and `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` (`thm_7_6`,
  `thm_7_6_monadic`).
- **Theorem 7.7 (`7.7`):** the paper deduces $\mathcal{A}$-accessibility and completeness of $M^T$
  by citing closure of accessible categories under PIE limits, leaving out the induction on terms
  $t$ showing that each term functor $M(t)$ is $\mathcal{A}$-accessible and $\mathcal{A}$-continuous
  and the explicit PIE-limit closure proofs. Filled in `UlmerBialgebras/Proofs/Sec5/BiDense.lean`
  (`uB_isAAccessibleMor'`, `uB_isAComplete_and_continuous`, `uB_hasAndPreservesARightKan`) and
  `UlmerBialgebras/Proofs/Sec7/Sec7Proofs.lean` (`thm_7_7`, `thm_7_7_monadic`).
- **Lemma A.3 (`A.3`):** the paper states that the proof proceeds "via a straightforward induction
  on $|E|$ by choosing a leaf $v \in V$ when $|E| \ge 1$," leaving out the combinatorial proof that
  every finite nonempty acyclic graph has a degree-1 leaf vertex and the enriched colimit gluing
  step removing that leaf edge. Filled in `UlmerBialgebras/Proofs/Appendix/AppendixForest.lean`
  (`exists_paperVCat_free_of_isForest`, `arrowFunctorDataEquiv`, `paperThreeFunctorDataEquiv`) and
  `UlmerBialgebras/Proofs/Appendix/Appendix.lean` (`lem_A_3`).
- **Theorem A.5 (`A.5`):** in constructing a $\mathcal{V}$-functor $F : \mathcal{C} \to \mathcal{D}$
  with $F_* \cong \Lambda$ from a pseudonatural transformation on the probes
  $\{\mathbf{1}, \mathbf{2}_x, \mathbf{3}_{x,y}\}$, the paper sketches how the three probe shapes
  encode objects, morphisms, and composition, leaving out the Yoneda factorization reconstructing
  the hom-morphisms $F(c, c') : \mathcal{C}(c, c') \to \mathcal{D}(Fc, Fc')$ and the coherence
  verification on general linear forests. Filled in
  `UlmerBialgebras/Appendix/VCatCellDense.lean` (`isACellDense_of_probes`),
  `UlmerBialgebras/Proofs/Appendix/AppendixLinearDensity.lean` (`isBiDense_paperLinear`), and `UlmerBialgebras/Proofs/Appendix/Appendix.lean`
  (`appendix_biDense`).
