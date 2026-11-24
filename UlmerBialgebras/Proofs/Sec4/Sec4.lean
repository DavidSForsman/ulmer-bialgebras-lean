module

public import UlmerBialgebras.Proofs.Sec4.ModelKanRoute
public import UlmerBialgebras.Kan.KanBialgebra
public import UlmerBialgebras.Kan.CoKan
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutModel
public import UlmerBialgebras.Proofs.Sec4.FieldAccessibility
public import UlmerBialgebras.Proofs.Sec4.SiftedSingle
public import UlmerBialgebras.Proofs.Sec4.ProductQuotient
public import UlmerBialgebras.Proofs.Sec4.ConcreteInserters
public import UlmerBialgebras.Proofs.Sec4.MonadEquifier
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Proofs.Sec4.ExtensionCategories
public import UlmerBialgebras.Proofs.Sec4.RegEpiWidePushoutPi
public import UlmerBialgebras.Kan.ColimKan
public import Foundations.CategoryTheory.Limits.PiColimits
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Examples.FieldEquiv
public import UlmerBialgebras.Kan.KanComp
public import UlmerBialgebras.Kan.KanInserter
public import UlmerBialgebras.Kan.KanEquifier

/-!
# Solution: Section 4 (lifting limits and colimits)

Proofs of the numbered results of Section 4, restating the theorems of
`UlmerBialgebras/Paper/Sec4.lean`.

## Main results

* `UlmerBialgebras.Paper.thm_4_7_1_creates`: Theorem 4.7 (1), the projections of a product jointly
  strictly create left and right Kan extensions.
* `UlmerBialgebras.Paper.thm_4_7_2_left`: Theorem 4.7 (2), `u : Ins(f, g) → a` strictly creates the
  left Kan extensions that `f` preserves.
* `UlmerBialgebras.Paper.cor_4_8_left`: Corollary 4.8, `u_B` strictly creates the left Kan
  extensions that `f` preserves and whose quotient initiality `f'` preserves.
* `UlmerBialgebras.Paper.cor_4_17`: Corollary 4.17, for `I` sifted, if every `M(B)` preserves
  `I`-colimits componentwise, `U : M^T → M₀` strictly creates `I`-indexed colimits.
* `UlmerBialgebras.Paper.thm_4_19`: Theorem 4.19, `U` strictly creates the wide pushouts of
  morphisms it sends to regular epimorphisms.
* `UlmerBialgebras.Paper.cor_4_21`: Corollary 4.21, the category of fields is accessible and
  `k ↦ k*` creates connected limits and sifted colimits.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 4
* [F. Ulmer, *Bialgebras in locally presentable categories*][Ulmer1977Bialgebras], 3.3, 3.4
* [J. Adámek, J. Rosický, E. M. Vitale, *What are sifted
  colimits?*][AdamekRosickyVitale2010SiftedColimits]
* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories: A Categorical Introduction to General
  Algebra*][Adamek-Rosicky-Vitale]
-/

@[expose] public section

universe s u v w u₁ v₁ uu₁ uu₂ uu₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section General

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Remark 4.5** ([forsman2026syntactic]): if `LE(d, k)` has an initial object `L₀ = (l, η)`, then
transposition along `η` identifies `LE(d, k)` with the coslice `l \ K(X, c)`: there is an
isomorphism of categories over `K(X, c)`. Conversely, if `LE(d, k)` is equivalent to a coslice
category, then it has an initial object. -/
theorem rem_4_5 {I X c : Obj} (k : I ⟶ X) (d : I ⟶ c) :
    (∀ L₀ : LeftExt k d, IsInitial L₀ →
      ∃ F : LeftExt k d ⥤ Under L₀.ext, Function.Bijective F.obj ∧ F.Full ∧ F.Faithful ∧
        F ⋙ Under.forget L₀.ext = LeftExt.forget k d) ∧
    (∀ {C : Type u₁} [Category.{v₁} C] (x : C), Nonempty (LeftExt k d ≌ Under x) →
      ∃ L : LeftExt k d, Nonempty (IsInitial L)) :=
  ⟨fun _ h => ⟨LeftExt.toUnder h, LeftExt.toUnder_obj_bijective h, inferInstance, inferInstance,
    rfl⟩, fun x ⟨e⟩ => LeftExt.exists_isInitial_of_equivalence_under x e⟩

/-- **Lemma 4.6 (1)** ([forsman2026syntactic]): for a product `a = ∏ⱼ aⱼ`, the functor
`(l, η) ↦ (πⱼ l, πⱼ η)ⱼ` is an isomorphism of categories `LE(d, k) ≅ ∏ⱼ LE(dⱼ, k)`, where
`dⱼ = πⱼ d`. -/
theorem lem_4_6_1 {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ P.pt) :
    Function.Bijective (P.kanFunctorLeft k d).obj ∧ (P.kanFunctorLeft k d).Full ∧
      (P.kanFunctorLeft k d).Faithful :=
  ⟨⟨fun _ L' h => (P.existsUnique_leftExt k d ((P.kanFunctorLeft k d).obj L')).unique
      (funext_iff.1 h) (fun _ => rfl),
    fun b => let ⟨L, hL, _⟩ := P.existsUnique_leftExt k d b; ⟨L, funext hL⟩⟩,
    inferInstance, inferInstance⟩

/-- **Lemma 4.6 (2)** ([forsman2026syntactic]): for an inserter `(u, φ)` of `f, g : a → b`, the
functor `F : LE(d, k) → Ins(f_*, g_*)`, `(l, η) ↦ ((u l, u η), φ l)`, is an isomorphism of
categories, and `U F = u_*`. Here `f_*, g_* : LE(u d, k) → LE(f u d, k)` are
`(l', η') ↦ (f l', f η')` and `(l', η') ↦ (g l', (g η') • (φ d))`. -/
theorem lem_4_6_2 {a b : Obj} {f g : a ⟶ b} (J : Inserter f g) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ J.pt) :
    Function.Bijective (Inserter.leftExtToIns J k d).obj ∧ (Inserter.leftExtToIns J k d).Full ∧
      (Inserter.leftExtToIns J k d).Faithful ∧
      Inserter.leftExtToIns J k d ⋙ Ins.forget _ _ = LeftExt.push k d J.u :=
  ⟨Inserter.leftExtToIns_obj_bijective J k d, inferInstance, inferInstance, rfl⟩

/-- **Lemma 4.6 (3)** ([forsman2026syntactic]): for an equifier `e` of `η, θ : f ⟹ g`, the functor
`F : LE(d, k) → Eq(η_*, θ_*)`, `(l, η) ↦ (e l, e η)`, is an isomorphism of categories over
`LE(e d, k)`. Here `η_*, θ_* : f_* ⟹ g_*` have components `η l'`, `θ l'`, and
`g_*(l', η') = (g l', (g η') • (η e d))`. -/
theorem lem_4_6_3 {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) :
    Function.Bijective (Equifier.leftExtToEquif E k d).obj ∧
      (Equifier.leftExtToEquif E k d).Full ∧ (Equifier.leftExtToEquif E k d).Faithful ∧
      Equifier.leftExtToEquif E k d ⋙ Equif.forget _ _ = LeftExt.push k d E.e :=
  ⟨Equifier.leftExtToEquif_obj_bijective E k d, inferInstance, inferInstance, rfl⟩

/-- **Theorem 4.7 (1)** ([forsman2026syntactic]): the projections of a product preserve all left and
right Kan extensions. -/
theorem thm_4_7_1_preserves {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) (i : ι) :
    PreservesLeftKan k d (P.π i) ∧ PreservesRightKan k d (P.π i) := by
  exact ⟨P.preserves_leftKan k d i, (Co.preservesLeftKan_iff k d (P.π i)).1
    ((Co.product P).preserves_leftKan (Co.hom k) (Co.hom d) i)⟩

/-- **Theorem 4.7 (1)** ([forsman2026syntactic]): the projections jointly strictly create all left
and right Kan extensions. -/
theorem thm_4_7_1_creates {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
      JointlyStrictlyCreatesTerminal (fun i : ι => RightExt.push k d (P.π i)) := by
  exact ⟨P.jointlyStrictlyCreates_leftKan k d, (Co.jointlyStrictlyCreatesInitial_iff k d P.π).1
    ((Co.product P).jointlyStrictlyCreates_leftKan (Co.hom k) (Co.hom d))⟩

/-- The projections of a product jointly strictly create quotient initiality of left
extensions: a family of left extensions of the components lifts uniquely (Lemma 4.6 (1)), and
the lift is quotient initial when every member is. -/
lemma product_jointlyStrictlyCreatesQuotientInitial {ι : Type s} {c : ι → Obj} (P : Product c)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ P.pt) :
    JointlyStrictlyCreatesQuotientInitial (fun i : ι => LeftExt.push k d (P.π i)) := by
  intro b hb
  refine ⟨Product.existsUnique_leftExt P k d b, fun L hL => ?_⟩
  exact (product_quotientInitial_iff P k d L).2 (fun i => by rw [hL i]; exact hb i)

/-- **Theorem 4.7 (1)** ([forsman2026syntactic]), "Additionally": the projections jointly preserve,
reflect and strictly create quotient initiality of left extensions, and subterminality of right
extensions. (The paper says "of a left Kan extension"; the statement for left extensions is the one
Corollary 4.11 uses.) -/
theorem thm_4_7_1_quotient {ι : Type s} {c : ι → Obj} (P : Product c) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ P.pt) :
    (∀ L : LeftExt k d,
      QuotientInitial L ↔ ∀ i, QuotientInitial ((LeftExt.push k d (P.π i)).obj L)) ∧
    JointlyStrictlyCreatesQuotientInitial (fun i : ι => LeftExt.push k d (P.π i)) ∧
    (∀ R : RightExt k d,
      Subterminal R ↔ ∀ i, Subterminal ((RightExt.push k d (P.π i)).obj R)) ∧
    JointlyStrictlyCreatesSubterminal (fun i : ι => RightExt.push k d (P.π i)) := by
  refine ⟨product_quotientInitial_iff P k d, product_jointlyStrictlyCreatesQuotientInitial P k d,
    fun R => ?_, ?_⟩
  swap
  · exact (Co.jointlyStrictlyCreatesQuotientInitial_iff k d P.π).1
      (product_jointlyStrictlyCreatesQuotientInitial (Co.product P) (Co.hom k) (Co.hom d))
  refine (Co.quotientInitial_iff (Co.ofRight R)).symm.trans ?_
  refine (product_quotientInitial_iff (Co.product P) (Co.hom k) (Co.hom d) (Co.ofRight R)).trans ?_
  apply forall_congr'
  intro i
  rw [Co.quotientInitial_iff]
  exact iff_of_eq congr(Subterminal $(Co.toRight_push k d (P.π i) (Co.ofRight R)))

/-- **Theorem 4.7 (2)** ([forsman2026syntactic]): `u : Ins(f, g) → a` strictly creates the left Kan
extensions that `f` preserves. -/
theorem thm_4_7_2_left {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hf : PreservesLeftKan k (d ≫ Ins.u) f) :
    StrictlyCreatesLeftKan k d Ins.u := Ins.strictlyCreates_leftKan k d hf

/-- **Theorem 4.7 (2)** ([forsman2026syntactic]): `u : Ins(f, g) → a` strictly creates the right Kan
extensions that `g` preserves. Dual of the left half: the inserter of `(f, g)` is the inserter of
`(g, f)` in `K^co`. -/
theorem thm_4_7_2_right {a b : Obj} {f g : a ⟶ b} (Ins : Inserter f g) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ Ins.pt) (hg : PreservesRightKan k (d ≫ Ins.u) g) :
    StrictlyCreatesRightKan k d Ins.u := by
  refine (Co.strictlyCreatesLeftKan_iff k d Ins.u).1 ?_
  exact Inserter.strictlyCreates_leftKan (Co.inserter Ins) (Co.hom k) (Co.hom d)
    ((Co.preservesLeftKan_iff k (d ≫ Ins.u) g).2 hg)

/-- **Theorem 4.7 (3)** ([forsman2026syntactic]): the equifier strictly creates the left Kan
extensions whose quotient initiality is preserved by `f`. -/
theorem thm_4_7_3_left {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hf : ∀ L : LeftExt k (d ≫ E.e), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ E.e) f).obj L)) :
    StrictlyCreatesLeftKan k d E.e := E.strictlyCreates_leftKan k d hf

/-- **Theorem 4.7 (3)** ([forsman2026syntactic]): the equifier strictly creates the right Kan
extensions whose subterminality is preserved by `g`. Dual of the left half, applied to the equifier
in `K^co`. -/
theorem thm_4_7_3_right {a b : Obj} {f g : a ⟶ b} {η θ : f ⟶ g} (E : Equifier η θ)
    {I X : Obj} (k : I ⟶ X) (d : I ⟶ E.pt)
    (hg : ∀ R : RightExt k (d ≫ E.e), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ E.e) g).obj R)) :
    StrictlyCreatesRightKan k d E.e := by
  refine (Co.strictlyCreatesLeftKan_iff k d E.e).1 ?_
  refine Equifier.strictlyCreates_leftKan (Co.equifier E) (Co.hom k) (Co.hom d) ?_
  intro L hL
  rw [Co.quotientInitial_iff]
  exact (iff_of_eq congr(Subterminal $(Co.toRight_push k (d ≫ E.e) g L))).mpr
    (hg _ ((Co.isInitial_iff L).1 hL))

/-- **Corollary 4.8** ([forsman2026syntactic]): `u_B : Bialg(B) → c` strictly creates the left Kan
extensions that `f` preserves and whose quotient initiality `f'` preserves. -/
theorem cor_4_8_left (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) (hf : PreservesLeftKan k (d ≫ B.uB E) B.f)
    (hf' : ∀ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k (d ≫ B.uB E) B.f').obj L)) :
    StrictlyCreatesLeftKan k d (B.uB E) := by
  exact Inserter.strictlyCreates_leftKan_equifier B.ins E k d hf hf'

/-- **Corollary 4.8** ([forsman2026syntactic]), dual: `u_B` strictly creates the right Kan
extensions that `g` preserves and whose subterminality is preserved by `g'`. This is the dual of the
left half, via `K^co`. -/
theorem cor_4_8_right (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) (hg : PreservesRightKan k (d ≫ B.uB E) B.g)
    (hg' : ∀ R : RightExt k (d ≫ B.uB E), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k (d ≫ B.uB E) B.g').obj R)) :
    StrictlyCreatesRightKan k d (B.uB E) := by
  exact Inserter.strictlyCreates_rightKan_equifier B.ins E k d hg hg'

/-- **Corollary 4.10** ([forsman2026syntactic]): `u_B` strictly creates `u_B`-absolute Kan
extensions. -/
theorem cor_4_10 (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β) {I X : Obj}
    (k : I ⟶ X) (d : I ⟶ E.pt) :
    ((∀ L : LeftExt k (d ≫ B.uB E), Nonempty (IsInitial L) →
        IsAbsoluteLeftKan k (d ≫ B.uB E) L) → StrictlyCreatesLeftKan k d (B.uB E)) ∧
    ((∀ R : RightExt k (d ≫ B.uB E), Nonempty (IsTerminal R) →
        IsAbsoluteRightKan k (d ≫ B.uB E) R) → StrictlyCreatesRightKan k d (B.uB E)) :=
  ⟨fun h => cor_4_8_left B E k d (fun L hL => (h L hL).2 B.f)
      (fun L hL => quotientInitial_of_isInitial ((h L hL).2 B.f').some),
    fun h => cor_4_8_right B E k d (fun R hR => (h R hR).2 B.g)
      (fun R hR => subterminal_of_isTerminal ((h R hR).2 B.g').some)⟩

end General

section Model

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj] [HasChosenFinProducts.{u,
  v, w} Obj]
  [HasChosenInserters.{u, v, w} Obj]
  [HasChosenEquifiers.{u, v, w} Obj]
variable {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Obj) (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg)
  [HasChosenProductsOfSize.{s₁, u, v, w} Obj] [HasChosenProductsOfSize.{s₂, u, v, w} Obj]
  (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg) [HasChosenProductsOfSize.{s₃, u, v, w} Obj]

/-- **Corollary 4.11** ([forsman2026syntactic]), left Kan extensions, from Proposition 3.15 and
Corollary 4.8. -/
theorem cor_4_11_left {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesLeftKan k (d ≫ M.thyForget sg T) (M.funArity sg f))
    (heq : ∀ r : T.Eqn, ∀ L : LeftExt k (d ≫ M.thyForget sg T), Nonempty (IsInitial L) →
      QuotientInitial ((LeftExt.push k _ (M.eqnArity sg T r)).obj L)) :
    StrictlyCreatesLeftKan k d (M.thyForget sg T) := by
  obtain ⟨E, hpt, he⟩ := (prop_3_15 M sg T).2
  have hcreate := ModelKanRoute.left_of_bialgebraic M sg T k E
    (fun d => cor_4_8_left (modelDatum M sg T) E k d)
  exact (ModelKanRoute.transport_hom_property hpt he
    (ModelKanRoute.LeftCreation M sg T k) hcreate) d hfn heq

/-- **Corollary 4.11** ([forsman2026syntactic]), right Kan extensions, using the dual half of
Corollary 4.8. -/
theorem cor_4_11_right {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T)
    (hfn : ∀ f : sg.Fn, PreservesRightKan k (d ≫ M.thyForget sg T) (M.funCoarity sg f))
    (heq : ∀ r : T.Eqn, ∀ R : RightExt k (d ≫ M.thyForget sg T), Nonempty (IsTerminal R) →
      Subterminal ((RightExt.push k _ (M.eqnCoarity sg T r)).obj R)) :
    StrictlyCreatesRightKan k d (M.thyForget sg T) := by
  obtain ⟨E, hpt, he⟩ := (prop_3_15 M sg T).2
  have hcreate := ModelKanRoute.right_of_bialgebraic M sg T k E
    (fun d => cor_4_8_right (modelDatum M sg T) E k d)
  exact (ModelKanRoute.transport_hom_property hpt he
    (ModelKanRoute.RightCreation M sg T k) hcreate) d hfn heq

/-- **Remark after Corollary 4.11** ([forsman2026syntactic]): for an algebraic theory, `u` strictly
creates all right Kan extensions; for a coalgebraic theory, all left Kan extensions. -/
theorem rem_4_11 {I X : Obj} (k : I ⟶ X) (d : I ⟶ M.thyObj sg T) :
    (T.IsAlgebraic → StrictlyCreatesRightKan k d (M.thyForget sg T)) ∧
      (T.IsCoalgebraic → StrictlyCreatesLeftKan k d (M.thyForget sg T)) :=
          ⟨fun h => M.thy_strictlyCreates_rightKan_of_algebraic sg T h k d, fun h =>
          M.thy_strictlyCreates_leftKan_of_coalgebraic sg T h k d⟩

/-- **Corollary 4.12** ([forsman2026syntactic]): if every `M(B)` preserves `k`-colimits, then so
does every `M(t)`, and `u : M^T → M₀` strictly creates `k`-colimits. -/
theorem cor_4_12 {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesLeftKan k d (M.fn B)) :
    (∀ {c : Sg.Cat} (t : sg.CTrm c) (d : I ⟶ (M.P0 sg).pt), PreservesLeftKan k d (M.tm sg t)) ∧
      ∀ d : I ⟶ M.thyObj sg T, StrictlyCreatesLeftKan k d (M.thyForget sg T) :=
          ⟨fun t d => M.tm_preserves_leftKan sg k hB t d, fun d =>
          M.thy_strictlyCreates_leftKan_of_fn sg T k hB d⟩

/-- **Corollary 4.12, right Kan form** ([forsman2026syntactic]): if every generating
functor preserves right Kan extensions along `k`, so does every term, and the theory forgetful
1-cell strictly creates these extensions. -/
theorem cor_4_12_right {I X : Obj} (k : I ⟶ X)
    (hB : ∀ (B : Sg.Fun) (d : I ⟶ (M.P B).pt), PreservesRightKan k d (M.fn B)) :
    (∀ {c : Sg.Cat} (t : sg.CTrm c) (d : I ⟶ (M.P0 sg).pt), PreservesRightKan k d (M.tm sg t)) ∧
      ∀ d : I ⟶ M.thyObj sg T, StrictlyCreatesRightKan k d (M.thyForget sg T) :=
  ⟨fun t d => M.tm_preserves_rightKan sg k hB t d,
    fun d => M.thy_strictlyCreates_rightKan_of_fn sg T k hB d⟩

end Model

/-! ## Classical consequences in `CAT` -/

section Classical

/-- **Corollary 4.13** ([forsman2026syntactic]) (Eilenberg–Moore): the forgetful functor `C^T → C`
strictly creates all limits, and those colimits that `T` preserves and whose quotient initiality
`T²` preserves. Both conditions concern the colimit of the given diagram `U d` only. -/
theorem cor_4_13 {C : Cat.{v, max u v}} (T : Monad (C : Type (max u v))) (I : Cat.{v, max u v})
    (d : I ⟶ Cat.of T.Algebra) :
    StrictlyCreatesRightKan (toOne I) d T.forget.toCatHom ∧
      (PreservesLeftKan (toOne I) (d ≫ T.forget.toCatHom)
          T.toFunctor.toCatHom →
        (∀ L : LeftExt (toOne I) (d ≫ T.forget.toCatHom),
          Nonempty (IsInitial L) →
            QuotientInitial ((LeftExt.push (toOne I) _
              (T.toFunctor ⋙ T.toFunctor).toCatHom).obj L)) →
        StrictlyCreatesLeftKan (toOne I) d T.forget.toCatHom) := by
  have : PreservesLimitsOfShape (I : Type (max u v)) (Cat.Hom.toFunctor (𝟙 C : C ⟶ C)) :=
    inferInstanceAs (PreservesLimitsOfShape (I : Type (max u v)) (𝟭 (C : Type (max u v))))
  refine ⟨cor_4_8_right (monadDatum T) (monadEquif T) (toOne I) d
      (preservesRightKan_of_preservesLimitsOfShape (𝟙 C) _) ?_, fun hT hQ => ?_⟩
  -- Limits: the right extension pushed along `U` is jointly monic, componentwise in `Cᵀ`.
  · intro R hR
    refine subterminal_of_jointlyMono' _ (fun Y p q hpq => ?_)
    have hc : ∀ i, ((RightExt.push (toOne I) _ (monadDatum T).g').obj R).counit.toNatTrans.app i =
        (monadDatum T).g'.toFunctor.map (R.counit.toNatTrans.app i) := fun i => by
      rw [RightExt.push_obj_counit, Cat.Hom₂.comp_app, Cat.eqToHom_app, Cat.whiskerRight_app,
        eqToHom_refl, Category.id_comp]
    refine Prod.ext (jointlyMono_of_isTerminal' R hR.some _ _ fun i => ?_)
      (jointlyMono_of_isTerminal' R hR.some _ _ fun i => ?_)
    · have := (Prod.ext_iff.1 (hpq i)).1
      rw [hc] at this
      exact this
    · have := (Prod.ext_iff.1 (hpq i)).2
      rw [hc] at this
      exact this
  -- Colimits: the left extension pushed along `U` is jointly epic; on the first component by the
  -- quotient initiality pushed along `T²` (`hQ`), on the second by the colimit itself.
  · refine cor_4_8_left (monadDatum T) (monadEquif T) (toOne I) d hT ?_
    intro L hL
    refine quotientInitial_of_jointlyEpi' _ (fun Y p q hpq => ?_)
    have hc : ∀ i, ((LeftExt.push (toOne I) _ (monadDatum T).f').obj L).unit.toNatTrans.app i =
        (monadDatum T).f'.toFunctor.map (L.unit.toNatTrans.app i) := fun i => by
      rw [LeftExt.push_obj_unit, Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.eqToHom_app,
        eqToHom_refl, Category.comp_id]
    have hc2 : ∀ i, ((LeftExt.push (toOne I) (d ≫ T.forget.toCatHom)
        (T.toFunctor ⋙ T.toFunctor).toCatHom).obj L).unit.toNatTrans.app i =
        ((T : (C : Type (max u v)) ⥤ C) ⋙ (T : (C : Type (max u v)) ⥤ C)).map
          (L.unit.toNatTrans.app i) := fun i => by
      change ((Bicategory.whiskerRight L.unit (T.toFunctor ⋙ T.toFunctor).toCatHom) ≫
        eqToHom (Category.assoc (toOne I) L.ext
          (T.toFunctor ⋙ T.toFunctor).toCatHom)).toNatTrans.app i = _
      simp only [Cat.whiskerRight_app, eqToHom_refl, Category.comp_id]
      rfl
    refine Prod.ext (jointlyEpi_of_quotientInitial' _ (hQ L hL) _ _ fun i => ?_)
      ((isColimitCoconeOfLeftExt hL.some).hom_ext fun i => ?_)
    · have := (Prod.ext_iff.1 (hpq i)).1
      rw [hc] at this
      rw [hc2]
      simp only [Cat.coe_of, Cat.Hom.comp_toFunctor, Cat.of_α, Functor.toCatHom_toFunctor,
        Functor.comp_obj, LeftExt.push_obj_ext, Functor.comp_map, Functor.prod'_obj, Functor.id_obj]
      exact this
    · have := (Prod.ext_iff.1 (hpq i)).2
      rw [hc] at this
      exact this

/-- **Corollary 4.14** ([forsman2026syntactic]) (comma categories): `F ↓ G → C × D` strictly creates
those colimits that `F` preserves and those limits that `G` preserves: a colimit of a diagram `d` in
`F ↓ G` whose first component `F` preserves, and a limit whose second component `G` preserves. -/
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
  ⟨fun hF => by
      have : PreservesColimitsOfShape (I : Type (max u v))
          (CategoryTheory.Prod.fst (C : Type (max u v)) (D : Type (max u v))).toCatHom.toFunctor :=
        inferInstanceAs (PreservesColimitsOfShape (I : Type (max u v))
          (CategoryTheory.Prod.fst (C : Type (max u v)) (D : Type (max u v))))
      exact Inserter.strictlyCreates_leftKan (commaIns F G) (toOne I) d
        (preservesLeftKan_comp
          (preservesLeftKan_of_preservesColimitsOfShape (I := I)
            (C := Cat.of (Prod (C : Type (max u v)) (D : Type (max u v)))) (D := C)
            (CategoryTheory.Prod.fst (C : Type (max u v)) (D : Type (max u v))).toCatHom _) hF),
    fun hG => by
      have : PreservesLimitsOfShape (I : Type (max u v))
          (CategoryTheory.Prod.snd (C : Type (max u v)) (D : Type (max u v))).toCatHom.toFunctor :=
        inferInstanceAs (PreservesLimitsOfShape (I : Type (max u v))
          (CategoryTheory.Prod.snd (C : Type (max u v)) (D : Type (max u v))))
      exact thm_4_7_2_right (commaIns F G) (toOne I) d
        (preservesRightKan_comp
          (preservesRightKan_of_preservesLimitsOfShape (I := I)
            (C := Cat.of (Prod (C : Type (max u v)) (D : Type (max u v)))) (D := D)
            (CategoryTheory.Prod.snd (C : Type (max u v)) (D : Type (max u v))).toCatHom _) hG)⟩

/-- **Corollary 4.15** ([forsman2026syntactic]) (slices): `C/c → C` strictly creates all colimits
and all connected limits. -/
theorem cor_4_15 {C : Cat.{v, max u v}} (c : (C : Type (max u v))) (I : Cat.{v, max u v})
    (d : I ⟶ Cat.of (Over c)) :
    StrictlyCreatesLeftKan (toOne I) d (Over.forget c).toCatHom ∧
      (IsConnected (I : Type (max u v)) →
        StrictlyCreatesRightKan (toOne I) d (Over.forget c).toCatHom) :=
  by
  have : PreservesColimitsOfShape (I : Type (max u v)) (Cat.Hom.toFunctor (𝟙 C : C ⟶ C)) :=
    inferInstanceAs (PreservesColimitsOfShape (I : Type (max u v)) (𝟭 (C : Type (max u v))))
  exact ⟨Inserter.strictlyCreates_leftKan (overIns c) (toOne I) d
      (preservesLeftKan_of_preservesColimitsOfShape (𝟙 C) _),
    fun hI => by
      let _ := hI
      have : PreservesLimitsOfShape (I : Type (max u v))
          ((Functor.const (C : Type (max u v))).obj c).toCatHom.toFunctor :=
        inferInstanceAs
          (PreservesLimitsOfShape (I : Type (max u v)) ((Functor.const (C : Type (max u v))).obj c))
      exact thm_4_7_2_right (overIns c) (toOne I) d
        (preservesRightKan_of_preservesLimitsOfShape
          ((Functor.const (C : Type (max u v))).obj c).toCatHom _)⟩

end Classical

/-! ## Sifted colimits and wide pushouts of regular epimorphisms -/

section Sifted

/-- **Lemma 4.16** ([forsman2026syntactic]): for a sifted `J`, a functor `F` on a finite product of
categories preserves the colimit of `D` as soon as it preserves it componentwise. -/
theorem lem_4_16 {ι : Type*} [Finite ι] [DecidableEq ι] {C : ι → Type u}
    [∀ i, Category.{v} (C i)] {E : Type*} [Category E] (F : (∀ i, C i) ⥤ E)
    {J : Type w} [Category.{w} J] [IsSifted J] (D : J ⥤ ∀ i, C i) [HasColimit D]
    (h : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimit (D ⋙ Pi.eval C i) (updateFunctor x i ⋙ F)) :
    PreservesColimit D F := by
  have := Fintype.ofFinite ι
  exact preservesColimit_pi_of_componentwise F D h

/-- **Corollary 4.17** ([forsman2026syntactic]): if each `M(B)` preserves `I`-colimits
componentwise, `I` sifted, then `U : M^T → M₀` strictly creates all `I`-indexed colimits. -/
theorem cor_4_17 {Sg : TwoSig.{uu₁, uu₂, uu₃}} (M : Model Sg Cat.{v, max u v})
    (sg : OneSig.{uu₁, uu₂, uu₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] (T : Theory.{uu₁, uu₂, uu₃, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
    (I : Cat.{v, max u v}) [IsSifted (I : Type (max u v))]
    (hB : ∀ B : Sg.Fun, PreservesColimitsComponentwise M I B) (d : I ⟶ M.thyObj sg T) :
    StrictlyCreatesLeftKan (toOne I) d (M.thyForget sg T) := thy_strictlyCreates_colimits M sg T I
        hB d

/-- **Corollary 4.18** ([forsman2026syntactic]): if regular epis are reflexive coequalizers in each
`Cᵢ` and `⊗` preserves `K`-indexed pushouts of regular epis componentwise, `|K| ≥ 2`, then `⊗`
preserves them and preserves regular epimorphisms. -/
theorem cor_4_18 {n : ℕ} {C : Fin n → Type u} [∀ i, Category.{v} (C i)] {E : Type*}
    [Category E] (F : (∀ i, C i) ⥤ E) (K : Type w) [Nontrivial K]
    (hC : ∀ i, RegEpisAreReflexiveCoequalizers (C i))
    (hF : ∀ (i : Fin n) (x : ∀ j, C j), PreservesWidePushoutsOfRegEpis K (updateFunctor x i ⋙ F)) :
    PreservesWidePushoutsOfRegEpis K F ∧
      ∀ ⦃x y : ∀ i, C i⦄ (f : x ⟶ y), Nonempty (RegularEpi f) →
        Nonempty (RegularEpi (F.map f)) := by
  exact RegEpiWide.preservesWidePushouts_and_regularEpis_pi F hC hF

/-- **Theorem 4.19** ([forsman2026syntactic]): `U : M^T → M₀` strictly creates the `K`-indexed wide
pushouts of morphisms of `M^T` that `U` sends to regular epimorphisms. -/
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
    StrictlyCreatesLeftKan (toOne J) d (M.thyForget sg T) := by
  exact RegEpiWide.thy_strictlyCreates_widePushouts M sg T K hreg hB J e d hd

end Sifted

/-! ## Fields -/

/-- **Corollary 4.21** ([forsman2026syntactic]): the category of fields is accessible, and `k ↦ k*`
creates connected limits and sifted colimits. -/
theorem cor_4_21 :
    IsAccessibleCategory.{u} FieldEx.FieldCat.{u} ∧
      (∀ (J : Type u) [SmallCategory J] [IsConnected J],
        Nonempty (CreatesLimitsOfShape J fieldUnits.{u})) ∧
      (∀ (J : Type u) [SmallCategory J] [IsSifted J],
        Nonempty (CreatesColimitsOfShape J fieldUnits.{u})) := by
  exact ⟨fieldCat_isAccessibleCategory, fieldUnits_createsConnectedLimits_and_siftedColimits⟩

end UlmerBialgebras.Paper

