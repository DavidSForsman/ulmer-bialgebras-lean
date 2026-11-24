module

public import UlmerBialgebras.Proofs.Sec7.Sec7Proofs
public import UlmerBialgebras.Proofs.Sec5.CatAccessibleMonadicity
public import UlmerBialgebras.Proofs.Sec5.CatCardinalMonadicity
public import UlmerBialgebras.Proofs.Sec5.ExplicitCardinalAccessibility

/-! # Solution: Sections 5–7

The section proofs are in `Solution.Sec5Proofs`, `Solution.Sec6Proofs` and
`Solution.Sec7Proofs`; Theorem 5.7 (`thm_5_7`) is proved here by the inserter/equifier
construction of Theorem 5.5 and Lemma 5.6 (`Solution.ColimitsOfAlgebras`). Theorem 5.11
(`thm_5_11`) uses the sharpened Theorem 7.7 (`Solution.CatAccessibleMonadicity`).

## Main results

* `UlmerBialgebras.Paper.thm_5_7`: Theorem 5.7, by relative free inserters and equifiers,
  reflective colimits, and the Kan-extension construction of Lemma 5.6.
* `UlmerBialgebras.Paper.thm_5_11`: Theorem 5.11, as the case `K = CAT`, `A = {1}` of the sharpened
  Theorem 7.7.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Sections 5, 6
  and 7
-/

@[expose] public section

universe u v w u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

/-- **Theorem 5.7** ([forsman2026syntactic]): monadicity and detection of left Kan extensions for a
bialgebraic datum in `CAT`.

The proof follows Theorem 5.5 and Lemma 5.6 through the concrete inserter/equifier
construction, transported to the chosen bialgebra category by `CatBridge.equifTo`. -/
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
            k.HasLeftKanExtension d :=
  ColimitsOfAlgebras.hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint
    κ hκ B E L₁ L₂ r₁ r₂ hC hF hF'

/-- **Theorem 5.11** ([forsman2026syntactic]): for a bialgebraic datum in `CAT` over a locally
presentable category with accessible supports, `U_B` is accessible (an accessible functor between
accessible categories, so in particular `Bialg(B)` is accessible), and (1) if `G` is continuous and
`G'` preserves joint monicness of limiting cones, `Bialg(B)` is locally presentable and `U_B` is
monadic; (2) if `F` is cocontinuous and `F'` preserves joint epicness of colimiting cocones,
`Bialg(B)` is locally presentable and `U_B` is comonadic.

This is the case `K = CAT`, `A = {1}` of the sharpened Theorem 7.7,
`uB_comonadic_monadic_of_jointMono_cat`. -/
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
        Nonempty (ComonadicLeftAdjoint (B.uB E).toFunctor)) :=
  uB_comonadic_monadic_of_jointMono_cat B E

/-- The monadic clause of Theorem 5.11 at one fixed regular cardinal. -/
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
      (B.uB E).toFunctor.IsCardinalAccessible κ :=
  uB_isCardinalLocallyPresentable_of_jointMono κ B E hg'


/-- The accessibility clause of Theorem 5.11 with two explicit sharply-less-than steps. -/
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
      (B.uB E).toFunctor.IsCardinalAccessible κ'' := uB_isCardinalAccessible_of_sharplyLT B E h₁ h₂


end UlmerBialgebras.Paper
