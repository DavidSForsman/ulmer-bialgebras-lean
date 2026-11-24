module

public import Foundations.CategoryTheory.Presentable.StrongGeneratorAdjunction
public import UlmerBialgebras.Basic.AccInsEq
public import UlmerBialgebras.Proofs.Sec5.CatBoundedMonadicity
public import UlmerBialgebras.Proofs.Sec5.CardinalMonadicity

/-!
# Monadicity and local `κ`-presentability at a fixed regular cardinal, in `CAT`

Let `B` be a bialgebraic datum in `CAT`, `κ` a regular cardinal, `C = B.c` locally
`κ`-presentable, `L₁` an `f`-relative left adjoint of `g` which is `κ`-accessible (for example
`L₁ = l ∘ f` with `l ⊣ g` and `f` `κ`-accessible), `L₂` an `f'`-relative left adjoint of `g'`, and
let `f'` preserve the joint epicness of colimiting `κ`-filtered cocones. Then `Bialg(B)` is
locally `κ`-presentable, for the same `κ`, and `u_B` is monadic and `κ`-accessible.

These are the case `K = CAT`, `A = {1}` of the hom-wise statements in any strict 2-category
(`UlmerBialgebras/Proofs/Sec5/CardinalMonadicity.lean`), transported along `CAT(1, C) ≃ C`; the
class `{1}` is
bi-dense (`UlmerBialgebras.Paper.isBiDense_one`) and every category has right Kan
extensions along it (`UlmerBialgebras.Paper.CatTwo.hasARightKan_one`). The proof follows the route
suggested by the author:

1. `u_B` is monadic and `Bialg(B)` is cocomplete by Theorem 5.7 (in its sharpened form
   `UlmerBialgebras.Paper.isMonadic2_uB_of_relLeftAdj2_sizeLE`), applied at every regular
   `μ ≥ κ`: a `μ`-chain is `κ`-filtered, so `L₁` and `f'` satisfy its hypotheses at `μ`.
2. `u_B` preserves `κ`-filtered colimits. On `CAT(1, -)`, the inserter `Ins(f, g)` is the
   inserter `Ins(L₁, id)` (Remark 3.2, `UlmerBialgebras.Paper.Rem32.transposedIns`), whose
   forgetful functor is `κ`-accessible since `L₁` is
   (`UlmerBialgebras.Ins.forget_isCardinalAccessible`). The equifier is closed under the
   `κ`-filtered colimits of the inserter, since `f'` preserves their joint epicness
   (`UlmerBialgebras.Paper.equifCreatesColimitOfJointEpi`).
3. A monadic, `κ`-accessible functor into a locally `κ`-presentable category from a cocomplete
   category has a locally `κ`-presentable domain
   (`CategoryTheory.MonadicRightAdjoint.isCardinalLocallyPresentable`, via strong generators of
   free algebras).

The relative left adjoint `L₂` is used only for step 1; step 2 needs only `L₁` and `f'`.

## Main results

* `UlmerBialgebras.Paper.CatTwo.postcomp_one_isCardinalAccessible`,
  `UlmerBialgebras.Paper.CatTwo.isCardinalAccessible_of_postcomp_one`: `κ`-accessibility along
  `CAT(1, C) ≃ C`.
* `UlmerBialgebras.Paper.CatTwo.isCardinalLocallyPresentable_homOne`: local `κ`-presentability
  of `CAT(1, C)`.
* `UlmerBialgebras.Paper.uB_isCardinalAccessible_of_relLeftAdjoint`: `u_B` is `κ`-accessible.
* `UlmerBialgebras.Paper.uB_isCardinalLocallyPresentable_of_jointMono`: Theorem 5.11 (1) at a
  fixed regular `κ`.

The cocompleteness of `Bialg(B)` and Theorem 5.7 with local `κ`-presentability at a fixed regular
`κ` (`hasColimitsOfSize_bialg_of_relLeftAdjoint`,
`uB_isCardinalLocallyPresentable_of_relLeftAdjoint`,
`uB_isCardinalLocallyPresentable_of_rightAdjoint`) are in the companion file
the development repository's `Solution/CatCardinalMonadicityExtra.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.7,
  Theorem 5.11 (1), Remark 3.2 and Theorem 7.6
* [Adámek, J. and Rosický, J., *Locally presentable and accessible
  categories*][LPC], Theorem 1.20 and Chapter 2
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras.Paper.CatTwo

open CategoryTheory UlmerBialgebras Limits

section Transport

variable {c d : Cat.{v, u}} (κ : Cardinal.{v}) [Fact κ.IsRegular]

/-- If `g` is `κ`-accessible, so is `CAT(1, g)`. -/
lemma postcomp_one_isCardinalAccessible (g : d ⟶ c) [g.toFunctor.IsCardinalAccessible κ] :
    (postcomp One.{v, u} g).IsCardinalAccessible κ := by
  have : (postcomp One.{v, u} g ⋙ homOneEval c).IsCardinalAccessible κ := by
    rw [postcomp_one_comp_homOneEval]; infer_instance
  exact Functor.isCardinalAccessible_of_natIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (homOneEval c).asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _ :
      (postcomp One.{v, u} g ⋙ homOneEval c) ⋙ (homOneEval c).asEquivalence.inverse ≅ _) κ

/-- If `CAT(1, g)` is `κ`-accessible, so is `g`. -/
lemma isCardinalAccessible_of_postcomp_one (g : d ⟶ c)
    [(postcomp One.{v, u} g).IsCardinalAccessible κ] : g.toFunctor.IsCardinalAccessible κ := by
  have : (homOneEval d ⋙ g.toFunctor).IsCardinalAccessible κ := by
    rw [← postcomp_one_comp_homOneEval]; infer_instance
  exact Functor.isCardinalAccessible_of_natIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homOneEval d).asEquivalence.counitIso g.toFunctor ≪≫
      Functor.leftUnitor _ :
      (homOneEval d).asEquivalence.inverse ⋙ (homOneEval d ⋙ g.toFunctor) ≅ _) κ

/-- If `c` has `κ`-filtered colimits, so does `CAT(1, c)`. -/
instance hasCardinalFilteredColimits_homOne [HasCardinalFilteredColimits.{v} (c : Type u) κ] :
    HasCardinalFilteredColimits.{v} (One.{v, u} ⟶ c) κ where
  hasColimitsOfShape' J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape (c : Type u) κ J
    exact Adjunction.hasColimitsOfShape_of_equivalence (homOneEval c)

/-- If `c` is locally `κ`-presentable, so is `CAT(1, c)`. -/
lemma isCardinalLocallyPresentable_homOne [IsCardinalLocallyPresentable (c : Type u) κ] :
    IsCardinalLocallyPresentable (One.{v, u} ⟶ c) κ :=
  (homOneEval c).asEquivalence.symm.isCardinalLocallyPresentable κ

end Transport

end UlmerBialgebras.Paper.CatTwo

namespace UlmerBialgebras.Paper

open CategoryTheory UlmerBialgebras Limits CatTwo

/-- **`u_B` is `κ`-accessible** (fixed-cardinal form of Theorems 5.7 and 5.11 (1) of
[forsman2026syntactic]). Let `B` be a bialgebraic datum in `CAT`, `κ` regular, `B.c` with
`κ`-filtered colimits, `L₁` a `κ`-accessible `f`-relative left adjoint of `g`, and let `f'`
preserve the joint epicness of colimiting `κ`-filtered cocones. Then `u_B` is `κ`-accessible. -/
theorem uB_isCardinalAccessible_of_relLeftAdjoint (κ : Cardinal.{v}) [Fact κ.IsRegular]
    (B : BialgDatum (Obj := Cat.{v, u})) (E : Equifier B.α B.β) (L₁ : (B.c : Type u) ⥤ B.c)
    (r₁ : RelLeftAdjoint (B.f).toFunctor B.g.toFunctor L₁)
    [HasCardinalFilteredColimits.{v} (B.c : Type u) κ] [L₁.IsCardinalAccessible κ]
    (hF' : ∀ (J : Type v) [SmallCategory J] [IsCardinalFiltered J κ],
      PreservesJointEpiOfShape J (B.f').toFunctor) :
    (B.uB E).toFunctor.IsCardinalAccessible κ := by
  have : L₁.toCatHom.toFunctor.IsCardinalAccessible κ := inferInstanceAs (L₁.IsCardinalAccessible
      κ)
  have : (postcomp One.{v, u} (L₁.toCatHom : B.c ⟶ B.c)).IsCardinalAccessible κ :=
    postcomp_one_isCardinalAccessible κ L₁.toCatHom
  have := B.postcomp_uB_isCardinalAccessible_of_relLeftAdj2 E (relLeftAdj2OfRelLeftAdjoint (f :=
      B.f) (g := B.g) (L := L₁.toCatHom) r₁)
    One.{v, u} κ fun J _ _ => postcomp_one_preservesJointEpiOfShape B.f' (hF' J)
  exact isCardinalAccessible_of_postcomp_one κ (B.uB E)

/-- **Theorem 5.11 (1) at a fixed regular `κ`** ([forsman2026syntactic], Theorem 5.11 (1), with
the cardinal fixed). Let `B` be a bialgebraic datum in `CAT`, `κ` regular, `B.c` locally
`κ`-presentable, `B.x, B.y` accessible, `f, f'` `κ`-accessible, `g, g'` accessible (for some
cardinal), `g` continuous and `g'` preserving the joint monicness of small limiting cones. Then
`Bialg(B)` is locally `κ`-presentable, and `u_B` is monadic and `κ`-accessible. -/
theorem uB_isCardinalLocallyPresentable_of_jointMono (κ : Cardinal.{w}) [Fact κ.IsRegular]
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
      (B.uB E).toFunctor.IsCardinalAccessible κ := by
  have : IsLocallyPresentable.{w} (B.c : Type (w + 1)) := ⟨κ, inferInstance, inferInstance⟩
  have : Functor.IsAccessible.{w} (B.f).toFunctor :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  have : Functor.IsAccessible.{w} (B.f').toFunctor :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  obtain ⟨-, h1, -⟩ := uB_comonadic_monadic_of_jointMono_cat B E
  obtain ⟨hE, hU⟩ := h1 ⟨inferInstance, hg'⟩
  have : HasColimitsOfSize.{w, w} (E.pt : Type (w + 1)) :=
    hasColimitsOfSize_of_isLocallyPresentable _
  have : HasLimitsOfSize.{w, w} (B.c : Type (w + 1)) :=
    hasLimitsOfSize_of_isLocallyPresentable _
  have : (B.g).toFunctor.IsRightAdjoint :=
    isRightAdjoint_of_isAccessible_of_preservesLimits _
  let r₁ := RelLeftAdjoint.ofAdjunction
    (Adjunction.ofIsRightAdjoint (B.g).toFunctor) B.f.toFunctor
  have := uB_isCardinalAccessible_of_relLeftAdjoint κ B E _ r₁
    (fun J _ _ =>
      have := (B.f').toFunctor.preservesColimitsOfShape_of_isCardinalAccessible
        κ J
      preservesJointEpiOfShape_of_preservesColimitsOfShape _)
  obtain ⟨hU⟩ := hU
  exact ⟨MonadicRightAdjoint.isCardinalLocallyPresentable
    (B.uB E).toFunctor κ, ⟨hU⟩, this⟩

end UlmerBialgebras.Paper
