module

public import UlmerBialgebras.Paper.Sec5DefsDoctrinal
public import UlmerBialgebras.Paper.Sec3DefsTwoFun
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-!
# Doctrinal adjunction for Σ-models

The ingredient behind the proof of Theorem 7.4 of [forsman2026syntactic], stated for Σ-models of
any 2-signature. Let `M, N` be Σ-models in a PIE-complete strict 2-category `K`, `G : M → N` a lax
morphism (Definition 3.10) and `F_c ⊣ G_c` adjunctions in `K` for the category symbols `c`.

* `mate_oplaxMor`: the mates of the structure 2-cells of `G` (`Doctrinal.mateStr`) make the `F_c`
  an **oplax** morphism `N → M`, compatible with every transformation symbol.
* `laxMor_iff_oplaxMor_mate`, `mateStr_bijective`: conversely, for fixed cells `F_c ⊣ G_c`, the
  mate is a bijection between structure 2-cells, and lax structures on the `G_c` correspond to
  oplax structures on the `F_c`.
* `idData_laxMor`: the identity data is a lax morphism (Proposition 3.11).
* `doctrinal_adjunction`: if every mate is invertible, the `F_c` with the inverse mates form a lax
  morphism `F : N → M`, and the units and counits of the `F_c ⊣ G_c` are 2-cells of lax
  morphisms `1 ⇒ G ∘ F` and `F ∘ G ⇒ 1` (`LaxTwoCell`). The triangle laws hold componentwise, so
  `F ⊣ G` is an adjunction in the 2-category of Σ-models and lax morphisms.
* `doctrinal_adjunction_strong`: if `G` is strong too, both 1-cells are strong, so the adjunction
  lives in the 2-category of strong morphisms (the case of Theorem 7.4, where `g_*` is strict).
* `laxNat_mate_oplaxNat`: the case of lax natural transformations (Example 3.12; Houston's
  Proposition 2.35): the mates of the naturality 2-cells of a lax transformation whose components
  have left adjoints form an oplax transformation.

**`G` need not be strong when `F` is.** For `Σ_Mon`, the free abelian group functor
`(Set, ×, 1) → (Ab, ⊗, ℤ)` is strong monoidal, but its right adjoint, the forgetful functor, is
only lax: `ℤ/2 × ℤ/2 → ℤ/2 ⊗ ℤ/2 = ℤ/2` is not injective. So `doctrinal_adjunction` does not make
`G` strong.

## Main results

* `UlmerBialgebras.Paper.mate_oplaxMor`
* `UlmerBialgebras.Paper.laxMor_iff_oplaxMor_mate`
* `UlmerBialgebras.Paper.mateStr_bijective`
* `UlmerBialgebras.Paper.idData_laxMor`
* `UlmerBialgebras.Paper.doctrinal_adjunction`
* `UlmerBialgebras.Paper.doctrinal_adjunction_strong`
* `UlmerBialgebras.Paper.laxNat_mate_oplaxNat`

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.10, Proposition 3.11, Example 3.12, Theorem 7.4
* [R. Houston, *Linear logic without units*][houstonLinearLogicUnits2013], Proposition 2.35
-/

@[expose] public section

universe u v w ua va wa

namespace UlmerBialgebras.Paper

open CategoryTheory Doctrinal

section SigmaModels

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
  [HasChosenFinProducts.{u, v, w} Obj] {Sg : TwoSig}
  {M N : Model Sg Obj} {Fc : ∀ c, N.obj c ⟶ M.obj c}

/-- **Mates of a lax morphism form an oplax morphism** (addition beyond
[forsman2026syntactic]): for a lax morphism `G : M → N` of Σ-models and adjunctions
`F_c ⊣ G_c`, the cells `F_c` with the mates of the structure 2-cells of `G` are an oplax morphism
`N → M`. -/
theorem mate_oplaxMor (G : LaxMor M N) (A : ∀ c, TwoAdj (Fc c) (G.cell c)) :
    ∃ F : OplaxMor N M, F.toOplaxData = mateOplaxData G.toLaxData A := sorry

/-- **Lax structures are oplax structures on the left adjoints** (addition beyond
[forsman2026syntactic]): lax data `G : M → N` with adjunctions `F_c ⊣ G_c` is a lax morphism iff
its mates form an oplax morphism `N → M`. -/
theorem laxMor_iff_oplaxMor_mate (G : LaxData M.toPreModel N.toPreModel)
    (A : ∀ c, TwoAdj (Fc c) (G.cell c)) :
    (∃ G' : LaxMor M N, G'.toLaxData = G) ↔
      ∃ F : OplaxMor N M, F.toOplaxData = mateOplaxData G A := sorry

/-- **The mate correspondence** (addition beyond [forsman2026syntactic]): for adjunctions
`F_c ⊣ G_c`, taking mates is a bijection from the lax structure 2-cells
`G_c̄ ≫ N(B) ⇒ M(B) ≫ G_d` to the oplax ones `N(B) ≫ F_d ⇒ F_c̄ ≫ M(B)`. -/
theorem mateStr_bijective {Gc : ∀ c, M.obj c ⟶ N.obj c} (A : ∀ c, TwoAdj (Fc c) (Gc c))
    (B : Sg.Fun) :
    Function.Bijective (mateStr A B :
      (prodR Gc B ≫ N.fn B ⟶ M.fn B ≫ Gc (Sg.fcod B)) →
        (N.fn B ≫ Fc (Sg.fcod B) ⟶ prodL Fc B ≫ M.fn B)) := sorry

/-- **Identity lax morphisms** (Proposition 3.11 of [forsman2026syntactic]): the identity data
of a Σ-model is a lax morphism. -/
theorem idData_laxMor (M : Model Sg Obj) :
    ∃ I : LaxMor M M, I.toLaxData = LaxData.idData M.toPreModel := sorry

/-- **Doctrinal adjunction** (addition beyond [forsman2026syntactic]; Kelly): for a lax
morphism `G : M → N` and adjunctions `F_c ⊣ G_c` whose mates are invertible, the `F_c` with the
inverse mates form a lax morphism `F : N → M`, and the units and counits of the `F_c ⊣ G_c` are
2-cells of lax morphisms `1_N ⇒ F ≫ G` and `G ≫ F ⇒ 1_M`. Their triangle laws are those of the
`F_c ⊣ G_c`, so `F ⊣ G` in the 2-category of Σ-models and lax morphisms. -/
theorem doctrinal_adjunction (G : LaxMor M N) (A : ∀ c, TwoAdj (Fc c) (G.cell c))
    [∀ B, IsIso ((mateOplaxData G.toLaxData A).str B)] :
    ∃ F : LaxMor N M, F.toLaxData = invLaxData (mateOplaxData G.toLaxData A) ∧
      ∃ (η : LaxTwoCell (LaxData.idData N.toPreModel)
          (LaxData.comp (invLaxData (mateOplaxData G.toLaxData A)) G.toLaxData))
        (ε : LaxTwoCell (LaxData.comp G.toLaxData (invLaxData (mateOplaxData G.toLaxData A)))
          (LaxData.idData M.toPreModel)),
        (∀ c, η.app c = (A c).unit') ∧ (∀ c, ε.app c = (A c).counit') := sorry

/-- **Doctrinal adjunction for strong morphisms** (addition beyond
[forsman2026syntactic]): if moreover `G` is strong, then so is `F`, and the adjunction of
`doctrinal_adjunction` lives in the 2-category of Σ-models and strong morphisms. -/
theorem doctrinal_adjunction_strong (G : LaxMor M N) (hG : ∀ B, IsIso (G.str B))
    (A : ∀ c, TwoAdj (Fc c) (G.cell c)) [∀ B, IsIso ((mateOplaxData G.toLaxData A).str B)] :
    ∃ F : LaxMor N M, F.toLaxData = invLaxData (mateOplaxData G.toLaxData A) ∧
      (∀ B, IsIso (F.str B)) ∧
      ∃ (η : LaxTwoCell (LaxData.idData N.toPreModel)
          (LaxData.comp (invLaxData (mateOplaxData G.toLaxData A)) G.toLaxData))
        (ε : LaxTwoCell (LaxData.comp G.toLaxData (invLaxData (mateOplaxData G.toLaxData A)))
          (LaxData.idData M.toPreModel)),
        (∀ c, η.app c = (A c).unit') ∧ (∀ c, ε.app c = (A c).counit') := sorry

end SigmaModels

section LaxNat

open TwoFun
open scoped CategoryTheory.Bicategory

variable {A : Type ua} [Bicategory.{wa, va} A] [Bicategory.Strict A]
variable {K : Type u} [Bicategory.{w, v} K] [Bicategory.Strict K]
  [HasChosenFinProducts.{u, v, w} K]

omit [HasChosenFinProducts.{u, v, w} K] in
/-- **Mates of a lax transformation** (Houston, Proposition 2.35; the case of `Σ_A`-models of
Example 3.12 of [forsman2026syntactic]): for a lax natural transformation `σ : F ⇒ G` between
strict 2-functors `A → K` and adjunctions `l_a ⊣ σ_a`, the `l_a` with the mates
`G f ≫ l_b ⇒ l_a ≫ F f` of the naturality 2-cells `σ_a ≫ G f ⇒ F f ≫ σ_b` (Mathlib's
`Bicategory.mateEquiv`) form an oplax natural transformation `G ⇒ F`. -/
theorem laxNat_mate_oplaxNat {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a)) :
    ∃ τ : OplaxNat G F, (∀ a, τ.app a = l a) ∧
      ∀ {a b : A} (f : a ⟶ b),
        HEq (τ.nat f) ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)) := sorry

/-- **Adjunctions of lax transformations** (Houston, Proposition 2.35, read through the
correspondence of Example 3.12 of [forsman2026syntactic]): let `σ : F ⇒ G` be a lax natural
transformation between strict 2-functors `A → K`, with adjunctions `l_a ⊣ σ_a` whose mates
`G f ≫ l_b ⇒ l_a ≫ F f` of the naturality 2-cells are invertible. Then the `l_a` with the inverse
mates form a lax natural transformation `τ : G ⇒ F`, and under the correspondences `e`, `e'` of
Example 3.12 (`ex_3_12_lax`) between lax transformations and lax morphisms of `Σ_A`-models, the
units and counits of the `l_a ⊣ σ_a` are 2-cells of lax morphisms `1 ⇒ e' τ ≫ e σ` and
`e σ ≫ e' τ ⇒ 1`, that is, modifications. So `τ ⊣ σ`. -/
theorem laxNat_adjunction {F G : StrictTwoFunctor K A} (σ : LaxNat F G)
    (l : ∀ a, G.obj a ⟶ F.obj a) (adj : ∀ a, TwoAdj (l a) (σ.app a))
    [∀ {a b : A} (f : a ⟶ b), IsIso ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f))]
    (e : LaxNat F G ≃ LaxMor F.model G.model) (he : ∀ σ a, (e σ).cell a = σ.app a)
    (he' : ∀ σ {a b : A} (f : a ⟶ b), HEq ((e σ).str ⟨a, b, f⟩)
      ((HasChosenFinProducts.finProd (fun _ : Fin 1 => F.obj a)).π 0 ◁ σ.nat f))
    (e' : LaxNat G F ≃ LaxMor G.model F.model) (he₂ : ∀ τ a, (e' τ).cell a = τ.app a)
    (he₂' : ∀ τ {a b : A} (f : a ⟶ b), HEq ((e' τ).str ⟨a, b, f⟩)
      ((HasChosenFinProducts.finProd (fun _ : Fin 1 => G.obj a)).π 0 ◁ τ.nat f)) :
    ∃ τ : LaxNat G F, (∀ a, τ.app a = l a) ∧
      (∀ {a b : A} (f : a ⟶ b),
        HEq (τ.nat f) (inv ((Bicategory.mateEquiv (adj a) (adj b)).symm (σ.nat f)))) ∧
      ∃ (η : LaxTwoCell (LaxData.idData G.model.toPreModel)
          (LaxData.comp (e' τ).toLaxData (e σ).toLaxData))
        (ε : LaxTwoCell (LaxData.comp (e σ).toLaxData (e' τ).toLaxData)
          (LaxData.idData F.model.toPreModel)),
        (∀ a, HEq (η.app a) (adj a).unit') ∧ (∀ a, HEq (ε.app a) (adj a).counit') := sorry

end LaxNat

end UlmerBialgebras.Paper
