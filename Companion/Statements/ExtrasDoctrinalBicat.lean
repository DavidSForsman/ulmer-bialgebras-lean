module

public import UlmerBialgebras.Paper.Sec5DefsDoctrinal
public import UlmerBialgebras.Paper.Sec3DefsPsFun
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Doctrinal adjunction for transformations between pseudofunctors

The results of `Companion/Statements/ExtrasDoctrinal.lean` on lax natural transformations between
strict
2-functors, for Mathlib's lax and oplax transformations between pseudofunctors `A → K` out of a
bicategory `A` (`F.toLax`, `G.toLax`), into a strict 2-category `K` with chosen finite products.
They follow from doctrinal adjunction for `Σ_A`-models through the correspondence of Example 3.12
(`ex_3_12_lax_bicat`, `ex_3_12_oplax_bicat`).

* `laxTrans_mate_oplaxTrans`: the mates of the naturality 2-cells of a lax transformation whose
  components have left adjoints form an oplax transformation (Houston, Proposition 2.35).
* `laxTrans_adjunction`: if these mates are invertible, the left adjoints with the inverse mates
  form a lax transformation `τ`, and the units and counits of the adjunctions are modifications
  `𝟙 ⟶ τ ≫ σ` and `σ ≫ τ ⟶ 𝟙`, so `τ ⊣ σ` among lax transformations. The naturality 2-cells of
  `τ` are invertible, so `τ` is strong.

## Main results

* `UlmerBialgebras.Paper.laxTrans_mate_oplaxTrans`
* `UlmerBialgebras.Paper.laxTrans_adjunction`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 3.12, Theorem 7.4
* [R. Houston, *Linear logic without units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory
open scoped CategoryTheory.Bicategory

variable {A : Type ua} [Bicategory.{wa, va} A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K]
  [HasChosenFinProducts.{u, v, w} K]

/-- **Mates of a lax transformation** (Houston, Proposition 2.35, through Example 3.12 of
[forsman2026syntactic]): for a lax transformation `σ : F ⇒ G` between pseudofunctors `A → K` and
adjunctions `l_a ⊣ σ_a`, the `l_a` with the mates `G f ≫ l_b ⇒ l_a ≫ F f` of the naturality
2-cells `σ_a ≫ G f ⇒ F f ≫ σ_b` (Mathlib's `Bicategory.mateEquiv`) form an oplax
transformation `G ⇒ F`. -/
theorem laxTrans_mate_oplaxTrans {F G : Pseudofunctor A K} (σ : Lax.LaxTrans F.toLax G.toLax)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) :
    ∃ τ : Lax.OplaxTrans G.toLax F.toLax, (∀ a, τ.app a = l a) ∧
      ∀ {a b : A} (f : a ⟶ b),
        HEq (τ.naturality f) ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)) :=
  sorry

/-- **Adjunctions of lax transformations** (Houston, Proposition 2.35, through Example 3.12 of
[forsman2026syntactic]): let `σ : F ⇒ G` be a lax transformation between pseudofunctors
`A → K`, with adjunctions `l_a ⊣ σ_a` whose mates `G f ≫ l_b ⇒ l_a ≫ F f` of the naturality
2-cells are invertible. Then the `l_a` with the inverse mates form a lax transformation
`τ : G ⇒ F`, and the units and counits of the `l_a ⊣ σ_a` are modifications `𝟙 ⟶ τ ≫ σ` and
`σ ≫ τ ⟶ 𝟙`. So `τ ⊣ σ`. -/
theorem laxTrans_adjunction {F G : Pseudofunctor A K} (σ : Lax.LaxTrans F.toLax G.toLax)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a))
    [∀ {a b : A} (f : a ⟶ b),
      IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f))] :
    ∃ τ : Lax.LaxTrans G.toLax F.toLax, (∀ a, τ.app a = l a) ∧
      (∀ {a b : A} (f : a ⟶ b),
        HEq (τ.naturality f) (inv ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.naturality f)))) ∧
      ∃ (η : Lax.LaxTrans.Modification (Lax.LaxTrans.id G.toLax) (τ.vComp σ))
        (ε : Lax.LaxTrans.Modification (σ.vComp τ) (Lax.LaxTrans.id F.toLax)),
        (∀ a, HEq (η.app a) (adj a).unit') ∧ (∀ a, HEq (ε.app a) (adj a).counit') := sorry

end UlmerBialgebras.Paper
