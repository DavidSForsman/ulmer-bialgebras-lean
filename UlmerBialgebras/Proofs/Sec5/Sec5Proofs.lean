module

public import UlmerBialgebras.Proofs.Sec5.Support.Sec57General
public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Paper.Sec5DefsCart
public import UlmerBialgebras.Paper.Sec5DefsKanIns
public import UlmerBialgebras.Proofs.Sec6.LocModel
public import UlmerBialgebras.Kan.SiftedModel
public import UlmerBialgebras.Basic.AccClosure
public import UlmerBialgebras.Factorization.LiftOFS
public import UlmerBialgebras.Monadicity.LPAdjoint
public import UlmerBialgebras.Monadicity.AccAdjoint
public import Foundations.CategoryTheory.Presentable.LPComplete
public import UlmerBialgebras.Proofs.Sec6.KernelPairs
public import UlmerBialgebras.Proofs.Sec6.RegularTransfer
public import UlmerBialgebras.Proofs.Sec6.ExactnessBridge
public import Foundations.CategoryTheory.Factorization.FunctorOFS
public import UlmerBialgebras.Kan.SiftedApplications
public import UlmerBialgebras.Proofs.Sec6.ModelOFS
public import UlmerBialgebras.Proofs.Sec5.EquifJointEpi
public import UlmerBialgebras.Proofs.Sec5.CastHomConservative
public import UlmerBialgebras.Proofs.Sec5.CoMonadic
public import UlmerBialgebras.Proofs.Sec5.BialgDatumCo
public import UlmerBialgebras.Proofs.Sec5.InsKanAbstract
public import UlmerBialgebras.Proofs.Sec5.InsKanIso
public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Monad.Monadicity
public import UlmerBialgebras.Monadicity.SplitCreate
public import UlmerBialgebras.Monadicity.AccTransfer
public import UlmerBialgebras.Monadicity.AccCompleteIff
public import UlmerBialgebras.Proofs.Sec5.ModelDatumMonadicity
public import UlmerBialgebras.Proofs.Sec5.ChainCofinality
public import UlmerBialgebras.Density.CellCompatDense
public import UlmerBialgebras.Density.RetractDense
public import UlmerBialgebras.Proofs.Sec5.BiDense
public import UlmerBialgebras.Proofs.Sec7.InserterKanExtension
public import UlmerBialgebras.Proofs.Sec6.SubSigExact
public import UlmerBialgebras.Kan.ColimKanCreates

/-!
# Solution: Section 5

Proofs of the numbered results of Section 5. Theorem 5.7 (`UlmerBialgebras.Paper.thm_5_7`)
is assembled in `Solution.Sec5_7` from the relative inserter/equifier proof of Theorem 5.5
and Lemma 5.6. Theorem 5.11 (`UlmerBialgebras.Paper.thm_5_11`) uses the sharpened Theorem 7.7.

Definition 5.1 (monadicity in a 2-category) is `UlmerBialgebras.Paper.IsMonadic2` in
`UlmerBialgebras/Paper/Sec3Defs2.lean`.

## Main results

* `UlmerBialgebras.Paper.lem_5_2`: Lemma 5.2, a characterization of monadic 1-cells.
* `UlmerBialgebras.Paper.cor_5_3`: Corollary 5.3, for `u = v g` with `g` a right adjoint, every
  `v_x` conservative and every `u_x` creating coequalizers of `u_x`-split pairs, `g` is monadic.
* `UlmerBialgebras.Paper.thm_5_5_1`: Theorem 5.5 (1), if `G` has an `F`-relative left adjoint, `C`
  has chain colimits up to `κ` and finite coproducts, and `F` preserves colimits of `κ`-chains, then
  `Ins(F, G) → C` is monadic.
* `UlmerBialgebras.Paper.thm_5_5_2`: Theorem 5.5 (2), the corresponding monadicity of
  `Eq(α, β) → C`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 5, 6
  and 7
* [F. Ulmer, *Properties of dense and relative adjoint functors*][ulmerPropertiesDenseRelative1968]
* [J. Adámek, *Free algebras and automata realizations in the language of categories*][Adamek1974]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Corollary 2.47,
  2.72 Theorem, 2.76 Lemma
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
* [E. Riehl, *Categorical homotopy theory*][Riehl2014CategoricalHomotopyTheory], Lemma 11.2.3
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [T. Wißmann, *Minimality notions via factorization systems and examples*][Wissmann2022Minimality]
* [R. Houston, *Linear Logic without Units*][houstonLinearLogicUnits2013], Proposition 2.35
* [P. Hofstra, M. Karvonen, *Inner autoequivalences in general and those of monoidal categories in
  particular*][hofstraInnerAutoequivalencesGeneral2024], Definition 6.2
* [R. Street, *Fibrations in bicategories*][Street1980FibrationsBicategories], (1.9)
-/

@[expose] public section

universe u v w u' v' w₀ u₁ v₁ u₂ v₂ s₁ s₂ s₃ t₁ t₂ t₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-! ## Section 5: free algebras, monadicity, local presentability -/

section ChainColimits

end ChainColimits

section Sec51

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Lemma 5.2** ([forsman2026syntactic]): a 1-cell `g : d ⟶ c` is monadic if and only if it is a
right adjoint and each `g_x : K(x, d) → K(x, c)` creates the coequalizers of `g_x`-split pairs. -/
theorem lem_5_2 {c d : Obj} (g : d ⟶ c) :
    IsMonadic2 g ↔ (∃ f : c ⟶ d, Nonempty (TwoAdj f g)) ∧
      ∀ (x : Obj) ⦃A B : x ⟶ d⦄ (h₁ h₂ : A ⟶ B), (postcomp x g).IsSplitPair h₁ h₂ →
        Nonempty (CreatesColimit (parallelPair h₁ h₂) (postcomp x g)) := by
  constructor
  · rintro ⟨f, A, heq⟩
    refine ⟨⟨f, ⟨A⟩⟩, fun x _ _ h₁ h₂ hsp => ?_⟩
    let : MonadicRightAdjoint (postcomp x g) := ⟨postcomp x f, A.postcompAdj x, heq x⟩
    exact ⟨Monad.createsGSplitCoequalizersOfMonadic (postcomp x g) h₁ h₂⟩
  · rintro ⟨⟨f, ⟨A⟩⟩, hcr⟩
    refine ⟨f, A, fun x => ?_⟩
    let : Monad.CreatesColimitOfIsSplitPair (postcomp x g) :=
      ⟨fun h₁ h₂ hsp => (hcr x h₁ h₂ hsp).some⟩
    exact (Monad.monadicOfCreatesGSplitCoequalizers (A.postcompAdj x)).eqv



/-- **Corollary 5.3** ([forsman2026syntactic]): for a commutative triangle `u = v g` with `g` a
right adjoint, every `v_x` conservative and every `u_x` creating the coequalizers of `u_x`-split
pairs, the 1-cell `g` is monadic. -/
theorem cor_5_3 {a b c : Obj} (g : a ⟶ b) (u : a ⟶ c) (v : b ⟶ c) (htri : g ≫ v = u)
    (hg : ∃ f : b ⟶ a, Nonempty (TwoAdj f g))
    (hv : ∀ x : Obj, (postcomp x v).ReflectsIsomorphisms)
    (hu : ∀ (x : Obj) ⦃A B : x ⟶ a⦄ (h₁ h₂ : A ⟶ B), (postcomp x u).IsSplitPair h₁ h₂ →
      Nonempty (CreatesColimit (parallelPair h₁ h₂) (postcomp x u))) :
    IsMonadic2 g := by
  -- By Lemma 5.2 it suffices that `g_x` creates the coequalizers of `g_x`-split pairs. Such a pair
  -- is `u_x`-split, so `u_x = g_x ⋙ v_x` creates its coequalizer; `v_x` preserves the split
  -- coequalizer and reflects isomorphisms, so `g_x` creates it too.
  refine (lem_5_2 g).2 ⟨hg, fun x A B h₁ h₂ hsp => ?_⟩
  subst htri
  have := hv x
  obtain ⟨Z, π, ⟨q⟩⟩ := hsp.splittable
  have hspV : (postcomp x g ⋙ postcomp x v).IsSplitPair h₁ h₂ := ⟨⟨_, _, ⟨q.map (postcomp x v)⟩⟩⟩
  obtain ⟨hcrU⟩ := hu x h₁ h₂ (isSplitPair_of_iso (postcompCompIso x g v) hspV)
  have := hcrU
  have : CreatesColimit (parallelPair h₁ h₂) (postcomp x g ⋙ postcomp x v) :=
    createsColimitOfNatIso (postcompCompIso x g v)
  have hq := q.isCoequalizer
  have hqV : IsColimit ((postcomp x v).mapCocone (Cofork.ofπ π q.condition)) :=
    (isColimitMapCoconeCoforkEquiv (postcomp x v) q.condition).symm
        (q.map (postcomp x v)).isCoequalizer
  have : HasColimit (parallelPair ((postcomp x g).map h₁) ((postcomp x g).map h₂)) :=
    ⟨⟨⟨_, hq⟩⟩⟩
  have : PreservesColimit (parallelPair ((postcomp x g).map h₁) ((postcomp x g).map h₂))
      (postcomp x v) := preservesColimit_of_preserves_colimit_cocone hq hqV
  have : HasColimit (parallelPair ((parallelPair h₁ h₂ ⋙ postcomp x g).map
      WalkingParallelPairHom.left) ((parallelPair h₁ h₂ ⋙ postcomp x g).map
        WalkingParallelPairHom.right)) :=
    (inferInstance : HasColimit (parallelPair ((postcomp x g).map h₁) ((postcomp x g).map h₂)))
  have : PreservesColimit (parallelPair ((parallelPair h₁ h₂ ⋙ postcomp x g).map
      WalkingParallelPairHom.left) ((parallelPair h₁ h₂ ⋙ postcomp x g).map
        WalkingParallelPairHom.right)) (postcomp x v) :=
    (inferInstance : PreservesColimit (parallelPair ((postcomp x g).map h₁)
      ((postcomp x g).map h₂)) (postcomp x v))
  have : HasColimit (parallelPair h₁ h₂ ⋙ postcomp x g) :=
    hasColimit_of_iso (diagramIsoParallelPair (parallelPair h₁ h₂ ⋙ postcomp x g))
  have : PreservesColimit (parallelPair h₁ h₂ ⋙ postcomp x g) (postcomp x v) :=
    preservesColimit_of_iso_diagram _
        (diagramIsoParallelPair (parallelPair h₁ h₂ ⋙ postcomp x g)).symm
  exact ⟨createsColimitOfCompConservative (postcomp x g) (postcomp x v) _⟩

/-- Casting along an equality of objects commutes with reversal of 2-cells. -/
lemma castHom_co {a b : Obj} (h : a = b) :
    castHom (Obj := Co Obj) (congrArg Co.op h) = Co.hom (castHom h) := by
  cases h
  rfl

/-- The monadic half of Corollary 5.3 for bialgebraic data. -/
theorem bialg_monadic_of_rightAdjoint (B B' : BialgDatum (Obj := Obj)) (hc : B'.c = B.c)
    (E : Equifier B.α B.β) (E' : Equifier B'.α B'.β) (g : E.pt ⟶ E'.pt)
    (htri : g ≫ (B'.uB E' ≫ castHom hc) = B.uB E)
    (hg : ∃ f : E'.pt ⟶ E.pt, Nonempty (TwoAdj f g)) : IsMonadic2 g := by
  have hv : ∀ x : Obj, (postcomp x (B'.uB E' ≫ castHom hc)).ReflectsIsomorphisms := fun x => by
    have := postcomp_castHom_reflectsIsomorphisms hc x
    rw [postcomp_comp₁]
    infer_instance
  exact cor_5_3 g (B.uB E) _ htri hg hv
    (fun x _ _ h₁ h₂ hsp => B.uB_createsColimit_of_isSplitPair E x h₁ h₂ hsp)

/-- **Corollary 5.3** ([forsman2026syntactic]), bialgebraic data: for bialgebraic data `B`, `B'`
over the same object `c`, a 1-cell `g : Bialg(B) → Bialg(B')` with `u_{B'} g = u_B` is monadic if it
is a right adjoint and comonadic if it is a left adjoint. The comonadic half is the dual of the
monadic half, via `K^co`. -/
theorem cor_5_3_bialg (B B' : BialgDatum (Obj := Obj)) (hc : B'.c = B.c)
    (E : Equifier B.α B.β) (E' : Equifier B'.α B'.β) (g : E.pt ⟶ E'.pt)
    (htri : g ≫ (B'.uB E' ≫ castHom hc) = B.uB E) :
    ((∃ f : E'.pt ⟶ E.pt, Nonempty (TwoAdj f g)) → IsMonadic2 g) ∧
      ((∃ h : E'.pt ⟶ E.pt, Nonempty (TwoAdj g h)) → IsComonadic2 g) := by
  refine ⟨bialg_monadic_of_rightAdjoint B B' hc E E' g htri, fun hg => ?_⟩
  refine (isComonadic2_iff_monadic_co g).2 ?_
  refine bialg_monadic_of_rightAdjoint (Obj := Co Obj) B.co B'.co (congrArg Co.op hc)
    (Equifier.co (Obj := Obj) E) (Equifier.co (Obj := Obj) E')
    (Co.hom (Obj := Obj) g) ?_ ?_
  · have h : Co.hom g ≫ (Co.hom (B'.uB E') ≫ Co.hom (castHom hc)) = Co.hom (B.uB E) := htri
    rw [← castHom_co hc] at h
    rw [BialgDatum.uB_co, BialgDatum.uB_co]
    exact h
  · obtain ⟨h, ⟨A⟩⟩ := hg
    exact ⟨Co.hom (Obj := Obj) h, ⟨Co.adj (Obj := Obj) A⟩⟩

end Sec51

section Thm55

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Theorem 5.5 (1)** ([forsman2026syntactic]): if `G` has an `F`-relative left adjoint, `C` is
`κ_≤`-cocomplete with finite coproducts and `F` preserves colimits of `κ`-chains, then
`Ins(F, G) → C` is monadic. -/
theorem thm_5_5_1 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (hC : HasChainColimitsUpTo κ C) [HasFiniteCoproducts C]
    (hF : PreservesColimitsOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Ins.forget F G)) :=
  ⟨Ins.monadicRightAdjointForget hκ ra (hasChainColimitsLE_of_upTo hC) hF⟩

/-- **Theorem 5.5 (2)** ([forsman2026syntactic]): if `G` has an `F`-relative left adjoint, `C` is
`κ_≤`-cocomplete with coequalizers and `F` preserves the joint epicness of colimiting cocones of
`κ`-chains, then `Eq(α, β) → C` is monadic. -/
theorem thm_5_5_2 (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ) (F G : C ⥤ D) (L : C ⥤ C)
    (ra : RelLeftAdjoint F G L) (α β : F ⟶ G) (hC : HasChainColimitsUpTo κ C)
    [HasCoequalizers C] (hF : PreservesJointEpiOfShape κ.ord.ToType F) :
    Nonempty (MonadicRightAdjoint (Equif.forget α β)) :=
  ⟨Equif.monadicRightAdjointForgetOfJointEpi hκ ra α β (hasChainColimitsLE_of_upTo hC) hF⟩

end Thm55

section Lem56

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- **Lemma 5.6** ([forsman2026syntactic]) ("in particular" clause): for `f : c ⟶ c`, if `K(X, c)`
has pushouts and `κ_≤`-colimits, `K(X, f)` preserves colimits of `κ`-chains and the left Kan
extensions of `u d` and `f u d` along `k` exist, then `u_* : LE(d, k) → LE(ud, k)` has a left
adjoint and `d` has a left Kan extension along `k`. -/
theorem lem_5_6 {c : Obj} (f : c ⟶ c) (Ins : Inserter f (𝟙 c)) {I X : Obj} (k : I ⟶ X)
    (d : I ⟶ Ins.pt) (κ : Cardinal.{w}) (hκ : Cardinal.aleph0 ≤ κ)
    [HasPushouts (X ⟶ c)] (hch : HasChainColimitsUpTo κ (X ⟶ c))
    (hf : PreservesColimitsOfShape κ.ord.ToType (postcomp X f))
    (h1 : ∃ L : LeftExt k (d ≫ Ins.u), Nonempty (IsInitial L))
    (h2 : ∃ L : LeftExt k ((d ≫ Ins.u) ≫ f), Nonempty (IsInitial L)) :
    (LeftExt.push k d Ins.u).IsRightAdjoint ∧ ∃ L : LeftExt k d, Nonempty (IsInitial L) :=
  AbsKan.isRightAdjoint_push_and_exists_initial_leftExt f Ins k d κ hκ hch hf h1 h2

/-- **Lemma 5.6** ([forsman2026syntactic]) (isomorphism and preservation): for `f : c ⟶ c`, if
`K(X, c)` has pushouts and `e₁ = (l₁, η₁)`, `e₂ = (l₂, η₂)` are left Kan extensions of `u d` and
`f u d` along `k`, let `H = (l₁, η₁) +_{l₂} f_*(-) : LE(ud, k) → LE(ud, k)` be the pushout
endofunctor (`LeftExt.pushoutStep`, with `φ d = Ins.phiAtId d`). There is an isomorphism of
categories `LE(d, k) ≅ Ins(H, id)` over `LE(ud, k)`, where `Ins(H, id)` is the category of
`H`-algebras, and `H` preserves those connected colimits that exist in `K(X, c)` and are preserved
by `f_X = K(X, f)`. -/
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
          PreservesColimit W (LeftExt.pushoutStep k (Ins.phiAtId d) e₁ he₂) :=
  AbsKan.exists_leftExt_iso_algebra_pushoutStep f Ins k d e₁ he₁ e₂ he₂

end Lem56

section Cor58

/-- **Corollary 5.8** ([forsman2026syntactic]): for an algebraic theory with at most `λ` symbols,
over a categorical model whose categories have colimits of size at most `max lam κ` and whose
functor symbols preserve `κ`-chain colimits componentwise, `U : M^T → M₀` is monadic, `M^T` has
colimits of size at most `max lam κ`, and `M^T` has the left Kan extensions detected by `U` via the
function arity supports. -/
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
            k.HasLeftKanExtension d :=
  ModelDatumMonadicity.hasLeftKanExtension_of_thyForget κ lam hκ hlam sg T M hsize halg hcol hB

attribute [local instance] BraidedCategory.ofCartesianMonoidalCategory

/-- For a cartesian closed `C`, the functor symbols `⊗` and `𝟙` of the cartesian model preserve
    `I`-colimits componentwise: `x × -` and `- × x` are left adjoints (used for Corollary 5.9). -/
theorem cart_colimitsComponentwise {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C] (I : Type w₀) [Category.{w} I] :
    ∀ B, PreservesColimitsComponentwise (Cart.cartModel C) I B := by
  open MonoidalCategory CartesianMonoidalCategory in
  intro B
  cases B with
  | tens =>
    intro i x
    refine ⟨?_⟩
    have key : ∀ (i : Fin 2) (x : ∀ _ : Fin 2, C),
        PreservesColimitsOfShape (I : Type w₀) (updateFunctor x i ⋙ MonEx.tensFunctor C) := by
      intro i x
      fin_cases i
      · have : PreservesColimitsOfShape (I : Type w₀) (tensorRight (x 1)) :=
          preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (x 1))
        exact preservesColimitsOfShape_of_natIso (MonEx.updateTensZero x).symm
      · exact preservesColimitsOfShape_of_natIso (MonEx.updateTensOne x).symm
    exact key i x
  | unit => exact fun i _ => i.elim0

/-- **Corollary 5.9, the `Σ_Cart` form** ([forsman2026syntactic]): for a cartesian closed category
`C` with countable colimits and any algebraic single-sorted `Σ_Cart`-theory `T` with a countable
signature, the category `C^T` has countable colimits, the forgetful functor `U : C^T → C` is
monadic, and `U` strictly creates countable sifted colimits. The checked statements of
Corollary 5.9 (`UniversalAlgebra.modelCat_monadic`, `UniversalAlgebra.modelCat_strictlyCreates`)
are proved from it. -/
theorem cartThy_monadic {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    [MonoidalClosed C]
    (hcol : HasColimitsOfSizeLE Cardinal.aleph0.{v} C)
    (sg : OneSig.{0, 0, 0, s₁, s₂} Cart.sigCart) [HasChosenProductsOfSize.{s₁} Cat.{v, u}]
    [HasChosenProductsOfSize.{s₂} Cat.{v, u}] (T : Theory.{0, 0, 0, s₁, s₂, s₃} sg)
    [HasChosenProductsOfSize.{s₃} Cat.{v, u}] [HasChosenInserters Cat.{v, u}]
    [HasChosenEquifiers Cat.{v, u}]
    (hsingle : Cardinal.mk sg.Srt = 1)
    (hsize : Cardinal.mk sg.Fn ≤ Cardinal.aleph0)
    (halg : T.IsAlgebraic) :
    Nonempty (MonadicRightAdjoint
        ((Cart.cartModel C).thyForget sg T).toFunctor) ∧
      HasColimitsOfSizeLE Cardinal.aleph0.{v} ((Cart.cartModel C).thyObj sg T : Type u) ∧
      ∀ (I : Cat.{v, u}) [IsSifted (I : Type u)]
        (_hI : Cardinal.mk (I : Type u) ≤ Cardinal.aleph0)
        (d : I ⟶ (Cart.cartModel C).thyObj sg T),
        StrictlyCreatesLeftKan (toOne I) d ((Cart.cartModel C).thyForget sg T) := by
  have hcol' : ∀ c : Unit, HasColimitsOfSizeLE (max Cardinal.aleph0.{v} Cardinal.aleph0.{v})
      ((Cart.cartModel C).obj c : Type u) := by
    intro c
    rw [max_self]
    exact hcol
  have hfin : ∀ (X : Type) [Countable X], Cardinal.lift.{v} (Cardinal.mk X) ≤
      Cardinal.lift.{0} Cardinal.aleph0.{v} := fun X _ => by
    rw [Cardinal.lift_aleph0, Cardinal.lift_le_aleph0]
    exact Cardinal.mk_le_aleph0
  have hsize' :
      Cardinal.lift.{v} (Cardinal.mk Unit) ≤ Cardinal.lift.{0} Cardinal.aleph0.{v} ∧
      Cardinal.lift.{v} (Cardinal.mk Cart.CartFun) ≤ Cardinal.lift.{0} Cardinal.aleph0.{v} ∧
      Cardinal.lift.{v} (Cardinal.mk Cart.CartTr) ≤ Cardinal.lift.{0} Cardinal.aleph0.{v} ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Srt) ≤ Cardinal.lift.{s₁} Cardinal.aleph0.{v} ∧
      Cardinal.lift.{v} (Cardinal.mk sg.Fn) ≤ Cardinal.lift.{s₂} Cardinal.aleph0.{v} := by
    refine ⟨hfin Unit, hfin _, hfin _, ?_, ?_⟩
    · rw [hsingle, Cardinal.lift_one, Cardinal.lift_aleph0]
      exact Cardinal.one_le_aleph0
    · rw [Cardinal.lift_aleph0, Cardinal.lift_le_aleph0]
      exact hsize
  have h58 := ModelDatumMonadicity.hasLeftKanExtension_of_thyForget.{v, u, 0, 0, 0, 0, 0, 0, 0,
      s₁, s₂, s₃}
      Cardinal.aleph0.{v}
      Cardinal.aleph0.{v} le_rfl le_rfl sg T (Cart.cartModel C) hsize' halg hcol'
      (cart_colimitsComponentwise _)
  refine ⟨h58.1, ?_, ?_⟩
  · rw [max_self] at h58
    exact h58.2.1
  · intro I hIsifted _ d
    exact thy_strictlyCreates_colimits (Cart.cartModel C) sg T I (cart_colimitsComponentwise I) d


/-- **Corollary 5.9, small shapes** ([forsman2026syntactic]): under the hypotheses of
`cartThy_monadic`, `U` creates the colimits of any countable sifted shape that is small with
respect to `C`. -/
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
    Nonempty (CreatesColimitsOfShape J ((Cart.cartModel C).thyForget sg T).toFunctor) :=
  nonempty_createsColimitsOfShape_of_strictlyCreatesLeftKan _ J fun J' _ e σ d =>
    have : IsSifted (Cat.of J' : Type u) := IsSifted.isSifted_of_equiv e.symm
    have : Countable J := Cardinal.mk_le_aleph0_iff.mp hJ
    have : Countable J' := Countable.of_equiv J σ
    (cartThy_monadic hcol sg T hsingle hsize halg).2.2 (Cat.of J')
      (Cardinal.mk_le_aleph0 (α := J')) d

end Cor58

section AAFT

/-- **Theorem 5.10 (1)** ([forsman2026syntactic]) (accessible adjoint functor theorem): a colimit
preserving functor out of a locally presentable category into a locally small category is a left
adjoint. -/
theorem thm_5_10_1 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{v'} D]
    [IsLocallyPresentable.{w} C] [LocallySmall.{w} D] (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w} F] : F.IsLeftAdjoint := by
  let e := ShrinkHoms.equivalence.{w} D
  have : (F ⋙ e.functor).IsLeftAdjoint :=
    isLeftAdjoint_of_preservesColimits_of_isLocallyPresentable (F ⋙ e.functor)
  exact Functor.isLeftAdjoint_of_iso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F e.unitIso.symm ≪≫
      Functor.rightUnitor F)

/-- **Theorem 5.10 (2)** ([forsman2026syntactic]): a continuous accessible functor from a locally
presentable category to an accessible category is a right adjoint. -/
theorem thm_5_10_2 {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]
    [IsLocallyPresentable.{w} C] [IsAccessibleCategory.{w} D] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w} F] [Functor.IsAccessible.{w} F] : F.IsRightAdjoint := by
  have := hasLimitsOfSize_of_isLocallyPresentable C
  exact isRightAdjoint_of_isAccessible_of_preservesLimits F

/-- An accessible limit-preserving functor from a locally presentable category has a left
adjoint preserving presentability at the accessibility rank of `F`. -/
theorem thm_5_10_2_cardinal {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w} D]
    (κ κ' κ'' : Cardinal.{w}) [Fact κ.IsRegular] [Fact κ'.IsRegular] [Fact κ''.IsRegular]
    [IsCardinalLocallyPresentable C κ] [IsCardinalAccessibleCategory D κ'] (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w} F] [F.IsCardinalAccessible κ''] :
    ∃ (G : D ⥤ C) (_ : G ⊣ F), G.PreservesCardinalPresentable κ'' := by
  have : IsLocallyPresentable.{w} C := ⟨κ, inferInstance, inferInstance⟩
  have : IsAccessibleCategory.{w} D := ⟨κ', inferInstance, inferInstance⟩
  have : Functor.IsAccessible.{w} F := Functor.isAccessible_of_isCardinalAccessible F κ''
  have : F.IsRightAdjoint := thm_5_10_2 F
  refine ⟨Functor.leftAdjoint F, Adjunction.ofIsRightAdjoint F, ⟨?_⟩⟩
  intro X hX
  have : IsCardinalPresentable X κ'' := hX
  exact (Adjunction.ofIsRightAdjoint F).isCardinalPresentable_leftAdjoint_obj κ'' X


end AAFT


end UlmerBialgebras.Paper
