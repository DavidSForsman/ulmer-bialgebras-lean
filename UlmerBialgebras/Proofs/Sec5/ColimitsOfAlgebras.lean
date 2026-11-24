module

public import UlmerBialgebras.Proofs.Sec5.ConcreteBialg
public import UlmerBialgebras.Proofs.Sec5.CatBridge

/-!
# Theorem 5.7

A bialgebraic datum `B` in `CAT` is identified with a concrete one
(`UlmerBialgebras/Proofs/Sec5/CatBridge.lean`):
`u_B = P ⋙ U` with `P : Bialg(B) ⥤ Equif α₀ β₀` an equivalence of categories and `U` the
concrete forgetful functor. The concrete results (`UlmerBialgebras/Proofs/Sec5/ConcreteBialg.lean`)
then transfer
along `P`.

## Main results

* `UlmerBialgebras.Paper.ColimitsOfAlgebras.hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint`:
  Theorem 5.7, `u_B` is monadic, `E.pt` has colimits of size at most `κ`, and a diagram `d` in
  `E.pt` has a left Kan extension along `k` when `d ⋙ u_B` and `d ⋙ u_B ⋙ L₁` do.
* `UlmerBialgebras.Paper.ColimitsOfAlgebras.monadic_hasColimits_hasLeftKan_equif`: the same three
  conclusions for the concrete equifier `Equif α β` over `Ins f g`.
* `UlmerBialgebras.Paper.ColimitsOfAlgebras.monadic_comp`: monadicity transfers along an equivalence
  of categories.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.7
* [F. E. J. Linton, *Coequalizers in categories of algebras*][Linton1969]
* [M. Barr, *Coequalizers and free triples*][barrCoequalizersFreeTriples1970]
* [J. Adámek, *Colimits of algebras revisited*][adamekColimitsAlgebrasRevisited1977]
-/

@[expose] public section

universe w v u u₁ v₁ u₂ v₂ u₃

namespace UlmerBialgebras.Paper.ColimitsOfAlgebras

open CategoryTheory Limits Functor CatBridge ConcreteBialg

/-- Let `r₁ : RelLeftAdjoint f g L₁` and `r₂ : RelLeftAdjoint f' g' L₂`, let `C` have colimits of
size at most `κ` (with `ℵ₀ ≤ κ`), let `f` preserve colimits and `f'` joint epimorphisms of shape
`κ.ord.ToType`, and let `V` be the forgetful functor of `Ins f g`. Then for `α β : V ⋙ f' ⟶ V ⋙ g'`
the forgetful functor `U : Equif α β ⥤ C` is monadic, `Equif α β` has colimits of size at most `κ`,
and a diagram `d` in `Equif α β` has a left Kan extension along `k` when `d ⋙ U` and
`d ⋙ U ⋙ L₁` have. -/
theorem monadic_hasColimits_hasLeftKan_equif {C X Y : Type u} [Category.{v} C] [Category.{v} X]
    [Category.{v} Y]
    {κ : Cardinal.{v}} (hκ : Cardinal.aleph0 ≤ κ)
    {f g : C ⥤ X} {f' g' : C ⥤ Y} {L₁ L₂ : C ⥤ C}
    (r₁ : RelLeftAdjoint f g L₁) (r₂ : RelLeftAdjoint f' g' L₂)
    (hC : HasColimitsOfSizeLE κ C) (hF : PreservesColimitsOfShape κ.ord.ToType f)
    (hF' : PreservesJointEpiOfShape κ.ord.ToType f')
    (V : Ins f g ⥤ C) (hV : V = Ins.forget f g) (α β : V ⋙ f' ⟶ V ⋙ g') :
    Nonempty (MonadicRightAdjoint (Equif.forget α β ⋙ Ins.forget f g)) ∧
      HasColimitsOfSizeLE κ (Equif α β) ∧
      ∀ {I : Type u₁} [Category.{v₁} I] {K : Type u₂} [Category.{v₂} K] (d : I ⥤ Equif α β)
        (k : I ⥤ K),
        k.HasLeftKanExtension (d ⋙ (Equif.forget α β ⋙ Ins.forget f g)) →
        k.HasLeftKanExtension ((d ⋙ (Equif.forget α β ⋙ Ins.forget f g)) ⋙ L₁) →
          k.HasLeftKanExtension d := by
  subst hV
  exact ⟨⟨concreteMonadic hκ r₁ r₂ hC hF hF' α β⟩,
    equif_hasColimitsOfSizeLE hκ r₁ r₂ hC hF hF' α β,
    fun d k h1 h2 => equif_hasLeftKanExtension hκ r₁ r₂ hC hF hF' α β d k h1 h2⟩

section Transfer

variable {A : Type u₁} [Category.{v₁} A] {Q : Type u₂} [Category.{v₁} Q] {C : Type u₃}
    [Category.{v₁} C] (e : A ≌ Q)

/-- Monadicity transfers along an equivalence of categories. -/
theorem monadic_comp (U : Q ⥤ C) [MonadicRightAdjoint U] :
    Nonempty (MonadicRightAdjoint (e.functor ⋙ U)) := by
  let P := e.functor
  have : (P ⋙ U).IsRightAdjoint := inferInstance
  have : Monad.CreatesColimitOfIsSplitPair (P ⋙ U) := by
    refine ⟨fun {a b} x y hxy => ?_⟩
    have : U.IsSplitPair (P.map x) (P.map y) := hxy
    have hU : CreatesColimit (parallelPair (P.map x) (P.map y)) U :=
      Monad.createsGSplitCoequalizersOfMonadic U (P.map x) (P.map y)
    have ePair : parallelPair x y ⋙ P ≅ parallelPair (P.map x) (P.map y) :=
      diagramIsoParallelPair (parallelPair x y ⋙ P)
    let eU : parallelPair (P.map x) (P.map y) ⋙ U ≅
        parallelPair (U.map (P.map x)) (U.map (P.map y)) :=
      diagramIsoParallelPair (parallelPair (P.map x) (P.map y) ⋙ U)
    have : HasColimit (parallelPair (U.map (P.map x)) (U.map (P.map y))) := inferInstance
    have : HasColimit (parallelPair (P.map x) (P.map y) ⋙ U) := hasColimit_of_iso eU
    have : HasColimit (parallelPair (P.map x) (P.map y)) := hasColimit_of_created _ U
    have : HasColimit (parallelPair x y ⋙ P) := hasColimit_of_iso ePair
    have : CreatesColimit (parallelPair x y) P :=
      createsColimitOfFullyFaithfulOfIso' (colimit.isColimit (parallelPair x y ⋙ P))
        (e.inverse.obj (colimit (parallelPair x y ⋙ P)))
        (e.counitIso.app _)
    have : CreatesColimit (parallelPair x y ⋙ P) U := createsColimitOfIsoDiagram U ePair.symm
    infer_instance
  exact ⟨Monad.monadicOfCreatesGSplitCoequalizers (Adjunction.ofIsRightAdjoint _)⟩

include e in
/-- Cocompleteness for diagrams of size `≤ κ` transfers from `Q` to `A` along an equivalence. -/
theorem hasColimitsOfSizeLE_of_equiv {κ : Cardinal.{w}} (hQ : HasColimitsOfSizeLE κ Q) :
    HasColimitsOfSizeLE κ A := by
  intro J _ hJ
  have := hQ J hJ
  exact Adjunction.hasColimitsOfShape_of_equivalence e.functor

/-- Along an equivalence `e : A ≌ Q`, if `d ⋙ e.functor` has a left Kan extension along `k` then
so does `d`. -/
theorem hasLeftKanExtension_of_equiv {I K : Type*} [Category I] [Category K] (d : I ⥤ A)
    (k : I ⥤ K) (h : k.HasLeftKanExtension (d ⋙ e.functor)) : k.HasLeftKanExtension d :=
  hasLeftKanExtension_of_reflective e.functor e.symm.toAdjunction d k

end Transfer

/-- **Theorem 5.7** ([forsman2026syntactic]). Let `B` be a bialgebra datum in `Cat` and `E` an
equifier of `B.α` and `B.β`, with `r₁ : RelLeftAdjoint B.f B.g L₁` and
`r₂ : RelLeftAdjoint B.f' B.g' L₂`. If `B.c` has colimits of size at most `κ` (with `ℵ₀ ≤ κ`),
`B.f` preserves colimits and `B.f'` joint epimorphisms of shape `κ.ord.ToType`, then `u_B` is
monadic, `E.pt` has colimits of size at most `κ`, and a diagram `d` in `E.pt` has a left Kan
extension along `k` when `d ⋙ u_B` and `d ⋙ u_B ⋙ L₁` have. -/
theorem hasColimitsOfSizeLE_and_leftKan_of_relLeftAdjoint (κ : Cardinal.{v})
    (hκ : Cardinal.aleph0 ≤ κ)
    (B : BialgDatum (Obj := Cat.{v, u})) (E : Equifier B.α B.β)
    (L₁ L₂ : (B.c : Type u) ⥤ B.c)
    (r₁ : RelLeftAdjoint (B.f).toFunctor B.g.toFunctor L₁)
    (r₂ : RelLeftAdjoint (B.f').toFunctor B.g'.toFunctor L₂)
    (hC : HasColimitsOfSizeLE κ (B.c : Type u))
    (hF : PreservesColimitsOfShape κ.ord.ToType (B.f).toFunctor)
    (hF' : PreservesJointEpiOfShape κ.ord.ToType (B.f').toFunctor) :
    Nonempty (MonadicRightAdjoint (B.uB E).toFunctor) ∧
      HasColimitsOfSizeLE κ (E.pt : Type u) ∧
      ∀ {I : Type u₁} {Kc : Type u₂} [Category.{v₁} I] [Category.{v₂} Kc]
        (d : I ⥤ (E.pt : Type u))
        (k : I ⥤ Kc), k.HasLeftKanExtension (d ⋙ (B.uB E).toFunctor) →
          k.HasLeftKanExtension ((d ⋙ (B.uB E).toFunctor) ⋙ L₁) →
            k.HasLeftKanExtension d := by
  obtain ⟨⟨hmon⟩, hcol, hkan⟩ :=
    monadic_hasColimits_hasLeftKan_equif hκ r₁ r₂ hC hF hF' _ rfl (α₀ B) (β₀ B)
  let e := (equifTo B E).asEquivalence
  refine ⟨?_, hasColimitsOfSizeLE_of_equiv e hcol, fun d k hk1 hk2 =>
    hasLeftKanExtension_of_equiv e d k (hkan (d ⋙ equifTo B E) k hk1 hk2)⟩
  rw [uB_eq B E]
  exact monadic_comp e _

end UlmerBialgebras.Paper.ColimitsOfAlgebras
