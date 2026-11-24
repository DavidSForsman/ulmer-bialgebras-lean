module

public import Foundations.CategoryTheory.Presentable.StrongGeneratorAdjunction
public import UlmerBialgebras.Basic.AccInsEq
public import UlmerBialgebras.Proofs.Sec5.Sec7Sharp
public import UlmerBialgebras.Proofs.Sec5.EquifJointEpi
public import UlmerBialgebras.Proofs.Sec3.TransposedDatum

/-!
# Monadicity and local `κ_a`-presentability at fixed regular cardinals, in a 2-category

Let `K` be a strict 2-category, `A` a class of objects of `K`, `B` a bialgebraic datum in `K`, `r`
and `r'` relative left adjoints of `g` and `g'` (relative to `f` and `f'`), and for each `a ∈ A`
let `κ_a` be a regular cardinal such that

* `K(a, c)` is locally `κ_a`-presentable;
* `K(a, r)` is `κ_a`-accessible;
* `K(a, f')` preserves the joint epicness of colimiting `κ_a`-filtered cocones.

Then, for the **same** `κ_a`, each `K(a, Bialg(B))` is locally `κ_a`-presentable and each
`K(a, u_B)` is `κ_a`-accessible; if `A` is bi-dense and `c` has right Kan extensions along `𝒜`,
`u_B` is monadic. This is the fixed-cardinal form of the sharpened Theorems 7.6 and 7.7 (1)
(the development repository's `Solution/BoundedMonadicity.lean`), and its case `K = CAT`, `A = {1}`
is the fixed-cardinal
Theorem 5.7 (`UlmerBialgebras/Proofs/Sec5/CatCardinalMonadicity.lean`).

The proof is the hom-wise form of the one in `CAT`:

1. `K(a, u_B)` is `κ_a`-accessible: `K(a, Ins(f, g))` is the inserter `Ins(K(a, r), id)`
   (Remark 3.2, `UlmerBialgebras.Paper.Rem32.transposedIns`), whose forgetful functor is
   `κ_a`-accessible, and the equifier is closed under its `κ_a`-filtered colimits since `K(a, f')`
   preserves their joint epicness (`UlmerBialgebras.Paper.equifCreatesColimitOfJointEpi`).
2. `K(a, Bialg(B))` is cocomplete, by the sharpened Theorem 7.6
   (`UlmerBialgebras.Paper.isMonadic2_uB_of_relLeftAdj2_sizeLE`) at the regular cardinals
   `μ_b ≥ κ_b`; this also gives the monadicity of `u_B`.
3. `K(a, u_B)` is monadic (Definition 5.1) and `κ_a`-accessible, so its domain is locally
   `κ_a`-presentable (`CategoryTheory.MonadicRightAdjoint.isCardinalLocallyPresentable`).

## Main results

* `UlmerBialgebras.Paper.IsACardinalAccessibleMor`: each `K(a, h)`, `a ∈ A`, is
  `κ_a`-accessible.
* `UlmerBialgebras.Paper.BialgDatum.postcomp_uB_isCardinalAccessible_of_relLeftAdj2`:
  `K(a, u_B)` is `κ`-accessible.

Steps 2 and 3, the cocompleteness and the local `κ_a`-presentability of `K(a, Bialg(B))`, are in
the companion file the development repository's `Solution/CardinalMonadicityExtra.lean`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorems 7.6, 7.7, 5.7, Definition 5.1 and Remark 3.2
* [Adámek, J. and Rosický, J., *Locally presentable and accessible
  categories*][LPC], Theorem 1.20 and Chapter 2
-/

@[expose] public section

universe u v w w₀

namespace UlmerBialgebras.Paper

open CategoryTheory UlmerBialgebras Limits

/-- A functor preserving the colimits of shape `J` preserves the joint epicness of colimiting
cocones of shape `J`. -/
lemma preservesJointEpiOfShape_of_preservesColimitsOfShape {J : Type w₀} [Category J]
    {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    [PreservesColimitsOfShape J F] : PreservesJointEpiOfShape J F :=
  fun _ _ hc _ _ _ h => (isColimitOfPreserves F hc).hom_ext h

/-- A cardinal at least a regular `κ` that is itself regular indexes a `κ`-filtered chain. -/
lemma isCardinalFiltered_ord_toType {κ μ : Cardinal.{w}} [Fact κ.IsRegular] (hμ : μ.IsRegular)
    (hκμ : κ ≤ μ) : IsCardinalFiltered μ.ord.ToType κ :=
  have : Fact μ.IsRegular := ⟨hμ⟩
  IsCardinalFiltered.of_le _ hκμ

section HomWise

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]

/-- A 1-cell `h` is **hom-wise `κ`-accessible on `A`**: for each `a ∈ A`, the functor
`K(a, h)` is `κ_a`-accessible. -/
abbrev IsACardinalAccessibleMor (A : ObjectProperty Obj) (κ : ∀ a, A a → Cardinal.{w₀})
    [∀ a ha, Fact (κ a ha).IsRegular] {c x : Obj} (h : c ⟶ x) : Prop :=
  ∀ a (ha : A a), (postcomp a h).IsCardinalAccessible (κ a ha)

namespace BialgDatum

variable (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)

/-- **`K(a, u_B)` is `κ`-accessible.** Let `r` be a relative left adjoint of `B.g` (relative to
`B.f`), `κ` regular, `a ⟶ B.c` with `κ`-filtered colimits, `K(a, r)` `κ`-accessible, and let
`K(a, B.f')` preserve the joint epicness of colimiting `κ`-filtered cocones. Then `K(a, u_B)` is
`κ`-accessible. -/
theorem postcomp_uB_isCardinalAccessible_of_relLeftAdj2 {r : B.c ⟶ B.c}
    (R : RelLeftAdj2 B.f B.g r) (a : Obj) (κ : Cardinal.{w₀}) [Fact κ.IsRegular]
    [HasCardinalFilteredColimits.{w₀} (a ⟶ B.c) κ] [(postcomp a r).IsCardinalAccessible κ]
    (hf' : ∀ (J : Type w₀) [SmallCategory J] [IsCardinalFiltered J κ],
      PreservesJointEpiOfShape J (postcomp a B.f')) :
    (postcomp a (B.uB E)).IsCardinalAccessible κ := by
  let I := Rem32.transposedIns R B.ins
  have hu : (postcomp a B.ins.u).IsCardinalAccessible κ := by
    change (postcomp a I.u).IsCardinalAccessible κ
    rw [← Inserter.homFunctor_comp_forget I a]
    infer_instance
  have he : (postcomp a E.e).IsCardinalAccessible κ := ⟨fun J _ _ => by
    rw [← Equifier.homFunctor_comp_forget E a]
    have := (postcomp a B.ins.u).preservesColimitsOfShape_of_isCardinalAccessible κ J
    have hJ : PreservesJointEpiOfShape J (postcomp a (B.ins.u ≫ B.f')) := by
      rw [postcomp_comp₁]
      exact preservesJointEpiOfShape_comp _ _ (hf' J)
    have : HasColimitsOfShape J (a ⟶ B.c) :=
      HasCardinalFilteredColimits.hasColimitsOfShape _ κ J
    have : PreservesColimitsOfShape J (postcomp a r) :=
      (postcomp a r).preservesColimitsOfShape_of_isCardinalAccessible κ J
    have : HasColimitsOfShape J (a ⟶ B.ins.pt) := by
      have : HasColimitsOfShape J (Ins (postcomp a r) (postcomp a (𝟙 B.c))) := inferInstance
      exact Adjunction.hasColimitsOfShape_of_equivalence (Inserter.homFunctor I a)
    have : PreservesColimitsOfShape J
        (Equif.forget (postcompNat a B.α) (postcompNat a B.β)) :=
      ⟨fun {D} => by
        have := equifCreatesColimitOfJointEpi hJ D
        infer_instance⟩
    infer_instance⟩
  rw [postcomp_comp₁]
  infer_instance

end BialgDatum

end HomWise

end UlmerBialgebras.Paper
