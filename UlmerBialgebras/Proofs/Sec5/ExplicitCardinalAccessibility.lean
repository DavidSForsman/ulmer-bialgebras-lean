module

public import UlmerBialgebras.Basic.AccExplicit
public import UlmerBialgebras.Proofs.Sec5.CatCardinalMonadicity

/-!
# Accessibility of bialgebras with explicit cardinals

The accessibility clauses of Theorems 5.11 and 7.7 are proved by the Makkai–Paré generation step,
which raises the cardinal: from `λ` to any `κ` with `λ ⊲ κ`, for an inserter and again for an
equifier. Under the extra hypothesis that the arities preserve presentable objects, this gives an
explicit cardinal. Let `κ ⊲ κ' ⊲ κ''` be regular cardinals, `B` a bialgebraic datum, and let
`K(a, c)` be `κ`-accessible, `K(a, f), K(a, g), K(a, f'), K(a, g')` `κ`-accessible and
`K(a, f), K(a, f')` preserve `κ`-presentable objects. Then:

1. `K(a, Ins(f, g))` is `κ'`-accessible, and `K(a, u)` is `κ'`-accessible and preserves
   `κ'`-presentable objects (`UlmerBialgebras.Ins.isCardinalPresentable_pt_of_sharplyLT`);
2. `K(a, f')` preserves `κ'`-presentable objects
   (`UlmerBialgebras.isCardinalPresentable_map_of_sharplyLT`), so the generation step applies to
   the equifier at `κ' ⊲ κ''`: `K(a, Bialg(B))` is `κ''`-accessible and `K(a, u_B)` is
   `κ''`-accessible.

No adjoint and no limit is involved, so the same statement serves the monadic and the comonadic
clauses. Note on Theorem 5.11 (2): on paper, Theorem 5.11 (2) asks `f` to be a left adjoint and
`f'` only to preserve joint epicness; the Lean variant
`uB_isCardinalAccessible_of_sharplyLT_of_adjunction` assumes `f ⊣ r` and `f' ⊣ r'`. They
preserve `κ`-presentable objects as soon as their right adjoints are `κ`-accessible
(`CategoryTheory.Adjunction.preservesCardinalPresentable`). The coarity `g` must be
`κ`-accessible here: by the counterexample `exists_not_isCardinalAccessibleCategory`, written as
a comonadic `Bialg(B)` (argued on paper only, not formalized), the hypotheses of
Theorem 5.11 (2) with `g` only accessible do not give `κ`-accessibility at the fixed `κ`.

Whether one jump suffices (`κ'` in place of `κ''`, by closing under the cell witnesses and the
equation witnesses at once) is not settled here.

## Main results

* `UlmerBialgebras.Paper.BialgDatum.postcomp_insU_isCardinalAccessible_of_sharplyLT`: step 1.
* `UlmerBialgebras.Paper.BialgDatum.postcomp_uB_isCardinalAccessible_of_sharplyLT`: the
  hom-wise statement, in any strict 2-category (the accessibility clause of Theorem 7.7 with
  explicit cardinals).
* `UlmerBialgebras.Paper.CatTwo.postcomp_one_preservesCardinalPresentable`: preservation of
  presentable objects along `CAT(1, C) ≃ C`.
* `UlmerBialgebras.Paper.uB_isCardinalAccessible_of_sharplyLT`: the case `K = CAT`, `a = 1` (the
  accessibility clause of Theorem 5.11 with explicit cardinals).
* `UlmerBialgebras.Paper.uB_isCardinalAccessible_of_sharplyLT_of_adjunction`: the same with `f, f'`
  left adjoints whose right adjoints are `κ`-accessible (the comonadic clause of Theorem 5.11).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorems 5.11 and 7.7
* [M. Makkai, R. Paré, *Accessible Categories: The Foundations of Categorical Model
  Theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], 2.72 Theorem,
  2.76 Lemma
-/

@[expose] public section

universe u v w w₀

namespace UlmerBialgebras.Paper

open CategoryTheory UlmerBialgebras Limits Cardinal

namespace BialgDatum

variable {Obj : Type u} [Bicategory.{w, v} Obj] [Bicategory.Strict Obj]
variable (B : BialgDatum (Obj := Obj)) (E : Equifier B.α B.β)

/-- **The inserter at a sharply larger cardinal, hom-wise.** Let `κ ⊲ κ'`, `K(a, B.c)`
`κ`-accessible, `K(a, B.x)` locally `w₀`-small, `K(a, B.f), K(a, B.g)` `κ`-accessible, and let
`K(a, B.f)` preserve `κ`-presentable objects. Then `K(a, Ins(f, g))` is `κ'`-accessible, and
`K(a, u)` is `κ'`-accessible and preserves `κ'`-presentable objects. -/
theorem postcomp_insU_isCardinalAccessible_of_sharplyLT (a : Obj) {κ κ' : Cardinal.{w₀}}
    [Fact κ.IsRegular] [Fact κ'.IsRegular] (h : κ.SharplyLT κ')
    [IsCardinalAccessibleCategory.{w₀} (a ⟶ B.c) κ] [LocallySmall.{w₀} (a ⟶ B.x)]
    [(postcomp a B.f).IsCardinalAccessible κ] [(postcomp a B.g).IsCardinalAccessible κ]
    [(postcomp a B.f).PreservesCardinalPresentable κ] :
    IsCardinalAccessibleCategory.{w₀} (a ⟶ B.ins.pt) κ' ∧
      (postcomp a B.ins.u).IsCardinalAccessible κ' ∧
      (postcomp a B.ins.u).PreservesCardinalPresentable κ' := by
  have hF : ∀ X : a ⟶ B.c, IsCardinalPresentable X κ →
      IsCardinalPresentable ((postcomp a B.f).obj X) κ := fun _ _ => inferInstance
  have : IsCardinalAccessibleCategory.{w₀} (Ins (postcomp a B.f) (postcomp a B.g)) κ' :=
    Ins.isCardinalAccessibleCategory_general hF h
  have := Ins.forget_preservesCardinalPresentable_of_sharplyLT (G := postcomp a B.g) hF h
  have : IsCardinalAccessibleCategory.{w₀} (a ⟶ B.c) κ' := h.isCardinalAccessibleCategory _
  have : (postcomp a B.f).IsCardinalAccessible κ' :=
    Functor.isCardinalAccessible_of_le (postcomp a B.f) h.le
  have := Functor.preservesCardinalPresentable_of_isEquivalence (Inserter.homFunctor B.ins a) κ'
  refine ⟨(Inserter.homFunctor B.ins a).asEquivalence.symm.isCardinalAccessibleCategory κ', ?_,
    ?_⟩
  · rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance
  · rw [← Inserter.homFunctor_comp_forget B.ins a]
    infer_instance

/-- **The accessibility clause of Theorem 7.7 with explicit cardinals**, hom-wise
([forsman2026syntactic], Theorem 7.7, with the cardinal made explicit). Let `κ ⊲ κ' ⊲ κ''`,
`K(a, B.c)` `κ`-accessible, `K(a, B.x), K(a, B.y)` locally `w₀`-small,
`K(a, B.f), K(a, B.g), K(a, B.f'), K(a, B.g')` `κ`-accessible, and let `K(a, B.f), K(a, B.f')`
preserve `κ`-presentable objects. Then `K(a, Bialg(B))` is `κ''`-accessible and `K(a, u_B)` is
`κ''`-accessible. -/
theorem postcomp_uB_isCardinalAccessible_of_sharplyLT (a : Obj) {κ κ' κ'' : Cardinal.{w₀}}
    [Fact κ.IsRegular] [Fact κ'.IsRegular] [Fact κ''.IsRegular] (h₁ : κ.SharplyLT κ')
    (h₂ : κ'.SharplyLT κ'')
    [IsCardinalAccessibleCategory.{w₀} (a ⟶ B.c) κ] [LocallySmall.{w₀} (a ⟶ B.x)]
    [LocallySmall.{w₀} (a ⟶ B.y)]
    [(postcomp a B.f).IsCardinalAccessible κ] [(postcomp a B.g).IsCardinalAccessible κ]
    [(postcomp a B.f').IsCardinalAccessible κ] [(postcomp a B.g').IsCardinalAccessible κ]
    [(postcomp a B.f).PreservesCardinalPresentable κ]
    [(postcomp a B.f').PreservesCardinalPresentable κ] :
    IsCardinalAccessibleCategory.{w₀} (a ⟶ E.pt) κ'' ∧
      (postcomp a (B.uB E)).IsCardinalAccessible κ'' := by
  obtain ⟨_, _, _⟩ := B.postcomp_insU_isCardinalAccessible_of_sharplyLT a h₁
  have : (postcomp a B.f').PreservesCardinalPresentable κ' :=
    ⟨fun X hX => isCardinalPresentable_map_of_sharplyLT (postcomp a B.f') h₁
      (fun _ _ => isCardinalPresentable_of_le _ h₁.le) X hX⟩
  have : (postcomp a B.f').IsCardinalAccessible κ' :=
    Functor.isCardinalAccessible_of_le (postcomp a B.f') h₁.le
  have : (postcomp a B.g').IsCardinalAccessible κ' :=
    Functor.isCardinalAccessible_of_le (postcomp a B.g') h₁.le
  have : (postcomp a (B.ins.u ≫ B.f')).PreservesCardinalPresentable κ' := by
    rw [postcomp_comp₁]
    infer_instance
  have : (postcomp a (B.ins.u ≫ B.f')).IsCardinalAccessible κ' := by
    rw [postcomp_comp₁]
    infer_instance
  have : (postcomp a (B.ins.u ≫ B.g')).IsCardinalAccessible κ' := by
    rw [postcomp_comp₁]
    infer_instance
  have : IsCardinalAccessibleCategory.{w₀} (Equif (postcompNat a B.α) (postcompNat a B.β)) κ'' :=
    Equif.isCardinalAccessibleCategory_general (fun _ _ => inferInstance) h₂
  have : IsCardinalAccessibleCategory.{w₀} (a ⟶ B.ins.pt) κ'' := h₂.isCardinalAccessibleCategory _
  have : (postcomp a (B.ins.u ≫ B.f')).IsCardinalAccessible κ'' :=
    Functor.isCardinalAccessible_of_le (postcomp a (B.ins.u ≫ B.f')) h₂.le
  have : (postcomp a B.ins.u).IsCardinalAccessible κ'' :=
    Functor.isCardinalAccessible_of_le (postcomp a B.ins.u) h₂.le
  have : (postcomp a E.e).IsCardinalAccessible κ'' := by
    rw [← Equifier.homFunctor_comp_forget E a]
    infer_instance
  refine ⟨(Equifier.homFunctor E a).asEquivalence.symm.isCardinalAccessibleCategory κ'', ?_⟩
  rw [postcomp_comp₁]
  infer_instance

end BialgDatum

namespace CatTwo

variable {c d : Cat.{v, u}} (κ : Cardinal.{v}) [Fact κ.IsRegular]

/-- If `g` preserves `κ`-presentable objects, so does `CAT(1, g)`. -/
lemma postcomp_one_preservesCardinalPresentable (g : d ⟶ c)
    [g.toFunctor.PreservesCardinalPresentable κ] :
    (postcomp One.{v, u} g).PreservesCardinalPresentable κ := by
  have := Functor.preservesCardinalPresentable_of_isEquivalence (homOneEval d) κ
  have := Functor.preservesCardinalPresentable_of_isEquivalence
    (homOneEval c).asEquivalence.inverse κ
  have : (postcomp One.{v, u} g ⋙ homOneEval c).PreservesCardinalPresentable κ := by
    rw [postcomp_one_comp_homOneEval]
    infer_instance
  exact Functor.PreservesCardinalPresentable.of_iso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (homOneEval c).asEquivalence.unitIso.symm ≪≫
      Functor.rightUnitor _ :
      (postcomp One.{v, u} g ⋙ homOneEval c) ⋙ (homOneEval c).asEquivalence.inverse ≅ _) κ

end CatTwo

open CatTwo

/-- **The accessibility clause of Theorem 5.11 with explicit cardinals** ([forsman2026syntactic],
Theorem 5.11, with the cardinal made explicit). Let `B` be a bialgebraic datum in `CAT`,
`κ ⊲ κ' ⊲ κ''`, `B.c` `κ`-accessible, `f, g, f', g'` `κ`-accessible, and let `f, f'` preserve
`κ`-presentable objects. Then `Bialg(B)` is `κ''`-accessible and `u_B` is `κ''`-accessible. -/
theorem uB_isCardinalAccessible_of_sharplyLT (B : BialgDatum (Obj := Cat.{v, u}))
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
      (B.uB E).toFunctor.IsCardinalAccessible κ'' := by
  have : IsCardinalAccessibleCategory.{v} (One.{v, u} ⟶ B.c) κ :=
    (homOneEval B.c).asEquivalence.symm.isCardinalAccessibleCategory κ
  have : LocallySmall.{v} (One.{v, u} ⟶ B.x) := locallySmall_of_faithful (homOneEval B.x)
  have : LocallySmall.{v} (One.{v, u} ⟶ B.y) := locallySmall_of_faithful (homOneEval B.y)
  have := postcomp_one_isCardinalAccessible κ B.f
  have := postcomp_one_isCardinalAccessible κ B.g
  have := postcomp_one_isCardinalAccessible κ B.f'
  have := postcomp_one_isCardinalAccessible κ B.g'
  have := postcomp_one_preservesCardinalPresentable κ B.f
  have := postcomp_one_preservesCardinalPresentable κ B.f'
  obtain ⟨_, _⟩ := B.postcomp_uB_isCardinalAccessible_of_sharplyLT E One.{v, u} h₁ h₂
  exact ⟨(homOneEval E.pt).asEquivalence.isCardinalAccessibleCategory κ'',
    isCardinalAccessible_of_postcomp_one κ'' (B.uB E)⟩

/-- **The comonadic clause of Theorem 5.11 with explicit cardinals** ([forsman2026syntactic],
Theorem 5.11 (2), with the cardinal made explicit): as
`UlmerBialgebras.Paper.uB_isCardinalAccessible_of_sharplyLT`, with `f ⊣ r` and `f' ⊣ r'` for
`κ`-accessible `r, r'` in place of the accessibility of `f, f'` and their preservation of
`κ`-presentable objects. The coarities `g, g'` are assumed `κ`-accessible. -/
theorem uB_isCardinalAccessible_of_sharplyLT_of_adjunction (B : BialgDatum (Obj := Cat.{v, u}))
    (E : Equifier B.α B.β) {κ κ' κ'' : Cardinal.{v}} [Fact κ.IsRegular] [Fact κ'.IsRegular]
    [Fact κ''.IsRegular] (h₁ : κ.SharplyLT κ') (h₂ : κ'.SharplyLT κ'')
    [IsCardinalAccessibleCategory.{v} (B.c : Type u) κ]
    {r : (B.x : Type u) ⥤ B.c} {r' : (B.y : Type u) ⥤ B.c}
    (adj : (B.f).toFunctor ⊣ r) (adj' : (B.f').toFunctor ⊣ r')
    [r.IsCardinalAccessible κ] [r'.IsCardinalAccessible κ]
    [(B.g).toFunctor.IsCardinalAccessible κ]
    [(B.g').toFunctor.IsCardinalAccessible κ] :
    IsCardinalAccessibleCategory.{v} (E.pt : Type u) κ'' ∧
      (B.uB E).toFunctor.IsCardinalAccessible κ'' := by
  have := adj.preservesCardinalPresentable κ
  have := adj'.preservesCardinalPresentable κ
  have := adj.leftAdjoint_preservesColimits
  have := adj'.leftAdjoint_preservesColimits
  exact uB_isCardinalAccessible_of_sharplyLT B E h₁ h₂

end UlmerBialgebras.Paper
