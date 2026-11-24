module

public import UlmerBialgebras.Proofs.Sec5.EquifJointEpi
public import UlmerBialgebras.Proofs.Sec5.StarKan
public import UlmerBialgebras.Proofs.Sec5.ReflectiveKan
public import UlmerBialgebras.Proofs.Sec5.SizeLE
public import UlmerBialgebras.Monadicity.SplitCreate

/-!
# Theorem 5.7 for a concrete bialgebraic datum

Let `f, g : C ⥤ X` and `f', g' : C ⥤ Y` have relative left adjoints `L₁`, `L₂`, let `C` have
colimits of size at most an infinite `κ`, let `f` preserve colimits of `κ`-chains and let `f'`
preserve their joint epicness. For equations `α, β : U ⋙ f' ⟶ U ⋙ g'` on `Ins f g`, the
forgetful functor `Equif α β ⥤ Ins f g ⥤ C` is monadic, `Equif α β` has colimits of size at
most `κ`, and it has the left Kan extensions detected by `U` and `L₁`.

## Main results

* `UlmerBialgebras.Paper.ConcreteBialg.concreteMonadic`: the forgetful functor
  `Equif α β ⥤ Ins f g ⥤ C` is monadic (Theorem 5.7).
* `UlmerBialgebras.Paper.ConcreteBialg.equif_hasColimitsOfSizeLE`: `Equif α β` has colimits of size
  at most `κ` (Theorem 5.7).
* `UlmerBialgebras.Paper.ConcreteBialg.equif_hasLeftKanExtension`: a diagram `d : I ⥤ Equif α β` has
  a left Kan extension along `k` when its images in `C` under `U` and `U ⋙ L₁` do (Theorem 5.7).
* `UlmerBialgebras.Paper.ConcreteBialg.ins_hasLeftKanExtension`: the same for `Ins f g` (Lemma 5.6).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 5.7 (via Theorem 5.5 and Lemma 5.6)
* [J. Adámek, *Free algebras and automata realizations in the language of
  categories*][Adamek1974]
-/

@[expose] public section

universe v u u₁ v₁ u₂ v₂

namespace UlmerBialgebras.Paper.ConcreteBialg

open CategoryTheory Limits Functor

variable {C X Y : Type u} [Category.{v} C] [Category.{v} X] [Category.{v} Y]
  {κ : Cardinal.{v}} (hκ : Cardinal.aleph0 ≤ κ)
  {f g : C ⥤ X} {f' g' : C ⥤ Y} {L₁ L₂ : C ⥤ C}
  (r₁ : RelLeftAdjoint f g L₁) (r₂ : RelLeftAdjoint f' g' L₂)
  (hC : HasColimitsOfSizeLE κ C) (hF : PreservesColimitsOfShape κ.ord.ToType f)

section InsFacts

include hκ r₁ hC hF

/-- Under the hypotheses of Theorem 5.7 of [forsman2026syntactic], the forgetful functor
`U' : Ins(f, g) → C` has a left adjoint (Theorem 5.5 (1)). -/
theorem ins_isRightAdjoint : (Ins.forget f g).IsRightAdjoint := by
  have := hasFiniteColimits_of_sizeLE hκ hC
  exact Ins.forget_isRightAdjoint_of_rel hκ r₁ (hasChainColimitsLE_of_sizeLE hC) hF

/-- For a span `K ← I → Ins(f, g)` with `d` and `k`, if U'd and L₁U'd have left Kan extensions
along `k`, then so does `d` (Lemma 5.6 of [forsman2026syntactic], for `Ins(f, g)`). -/
theorem ins_hasLeftKanExtension {I : Type u₁} [Category.{v₁} I] {K : Type u₂} [Category.{v₂} K]
    (d : I ⥤ Ins f g) (k : I ⥤ K) [k.HasLeftKanExtension (d ⋙ Ins.forget f g)]
    [k.HasLeftKanExtension ((d ⋙ Ins.forget f g) ⋙ L₁)] : k.HasLeftKanExtension d := by
  have := hasFiniteColimits_of_sizeLE hκ hC
  exact Ins.hasLeftKanExtension_of_rel hκ r₁ (hasChainColimitsLE_of_sizeLE hC) hF d k

/-- `Ins(f, g)` has colimits of size at most `κ`, as left Kan extensions along `J → 1`
(by `ins_hasLeftKanExtension`). -/
theorem ins_hasColimitsOfSizeLE : HasColimitsOfSizeLE κ (Ins f g) := by
  intro J _ hJ
  have := hC J hJ
  refine ⟨fun d => ?_⟩
  have := hasLeftKanExtension_star_of_hasColimit.{v} (d ⋙ Ins.forget f g)
  have := hasLeftKanExtension_star_of_hasColimit.{v} ((d ⋙ Ins.forget f g) ⋙ L₁)
  have := ins_hasLeftKanExtension hκ r₁ hC hF d (Functor.star.{v} J)
  exact hasColimit_of_hasLeftKanExtension_star.{v} d

end InsFacts

variable (hF' : PreservesJointEpiOfShape κ.ord.ToType f')
  (α β : Ins.forget f g ⋙ f' ⟶ Ins.forget f g ⋙ g')

include hκ r₁ r₂ hC hF hF' in
/-- The forgetful functor of the equifier over the inserter is monadic. -/
@[instance_reducible]
noncomputable def equifMonadic : MonadicRightAdjoint (Equif.forget α β) := by
  haveI := ins_isRightAdjoint hκ r₁ hC hF
  have hIns := ins_hasColimitsOfSizeLE hκ r₁ hC hF
  haveI := hasFiniteColimits_of_sizeLE hκ hIns
  haveI := hF
  haveI : HasColimitsOfShape κ.ord.ToType C := hasChainColimitsUpTo_of_sizeLE hC κ hκ le_rfl
  have hJE : PreservesJointEpiOfShape κ.ord.ToType (Ins.forget f g ⋙ f') :=
    fun K c hc y p q h => hF' (K ⋙ Ins.forget f g) _ (isColimitOfPreserves (Ins.forget f g) hc)
      p q h
  exact Equif.monadicRightAdjointForgetOfJointEpi hκ
    (r₂.precompAdj (Adjunction.ofIsRightAdjoint (Ins.forget f g))) α β
    (hasChainColimitsLE_of_sizeLE hIns) hJE

/-- A fully faithful right adjoint is reflective. -/
@[instance_reducible]
noncomputable def reflectiveOf {A B : Type*} [Category A] [Category B] (R : A ⥤ B) [R.Full]
    [R.Faithful] [R.IsRightAdjoint] : Reflective R where
  L := R.leftAdjoint
  adj := Adjunction.ofIsRightAdjoint R

include hκ r₁ r₂ hC hF hF' in
/-- `Eq(α, β)` has colimits of size at most `κ` (Theorem 5.7 of [forsman2026syntactic]): it is a
reflective subcategory of `Ins(f, g)`, since its forgetful functor is fully faithful and monadic. -/
theorem equif_hasColimitsOfSizeLE : HasColimitsOfSizeLE κ (Equif α β) := by
  let := equifMonadic hκ r₁ r₂ hC hF hF' α β
  let := reflectiveOf (Equif.forget α β)
  intro J _ hJ
  have := ins_hasColimitsOfSizeLE hκ r₁ hC hF J hJ
  exact hasColimitsOfShape_of_reflective (Equif.forget α β)

include hκ r₁ r₂ hC hF hF' in
/-- The Kan extension clause of Theorem 5.7 of [forsman2026syntactic]: for `d : I → Eq(α, β)` and
`k : I → K`, if Ud and L₁Ud have left Kan extensions along `k`, then so does `d`. -/
theorem equif_hasLeftKanExtension {I : Type u₁} [Category.{v₁} I] {K : Type u₂} [Category.{v₂} K]
    (d : I ⥤ Equif α β) (k : I ⥤ K)
    (h1 : k.HasLeftKanExtension (d ⋙ (Equif.forget α β ⋙ Ins.forget f g)))
    (h2 : k.HasLeftKanExtension ((d ⋙ (Equif.forget α β ⋙ Ins.forget f g)) ⋙ L₁)) :
    k.HasLeftKanExtension d := by
  let := equifMonadic hκ r₁ r₂ hC hF hF' α β
  have : k.HasLeftKanExtension ((d ⋙ Equif.forget α β) ⋙ Ins.forget f g) := h1
  have : k.HasLeftKanExtension (((d ⋙ Equif.forget α β) ⋙ Ins.forget f g) ⋙ L₁) := h2
  have := ins_hasLeftKanExtension hκ r₁ hC hF (d ⋙ Equif.forget α β) k
  exact hasLeftKanExtension_of_reflective (Equif.forget α β) (monadicAdjunction _) d k

include hκ r₁ r₂ hC hF hF' in
/-- The composite forgetful functor `Equif α β ⥤ C` is monadic (the monadicity clause of
Theorem 5.7 of [forsman2026syntactic]). -/
@[instance_reducible]
noncomputable def concreteMonadic : MonadicRightAdjoint (Equif.forget α β ⋙ Ins.forget f g) := by
  letI := equifMonadic hκ r₁ r₂ hC hF hF' α β
  haveI := ins_isRightAdjoint hκ r₁ hC hF
  haveI : Monad.CreatesColimitOfIsSplitPair (Equif.forget α β ⋙ Ins.forget f g) := by
    refine ⟨fun {P Q} a b hab => ?_⟩
    let a' := (Equif.forget α β).map a
    let b' := (Equif.forget α β).map b
    haveI : HasSplitCoequalizer ((Ins.forget f g).map a') ((Ins.forget f g).map b') := hab
    haveI hcrIns : CreatesColimit (parallelPair a' b') (Ins.forget f g) :=
      Ins.createsColimitParallelPair a' b'
    let e₀ : parallelPair a' b' ⋙ Ins.forget f g ≅
        parallelPair ((Ins.forget f g).map a') ((Ins.forget f g).map b') :=
      diagramIsoParallelPair (parallelPair a' b' ⋙ Ins.forget f g)
    haveI : HasColimit (parallelPair ((Ins.forget f g).map a') ((Ins.forget f g).map b')) :=
      inferInstance
    haveI : HasColimit (parallelPair a' b' ⋙ Ins.forget f g) := hasColimit_of_iso e₀
    haveI : HasColimit (parallelPair a' b') := hasColimit_of_created _ (Ins.forget f g)
    haveI : PreservesColimit (parallelPair a' b') (Ins.forget f g) := inferInstance
    haveI : PreservesColimit (parallelPair a' b' ⋙ Ins.forget f g) f' := by
      have := preservesColimit_parallelPair_of_hasSplitCoequalizer
        ((Ins.forget f g).map a') ((Ins.forget f g).map b') f'
      exact preservesColimit_of_iso_diagram f' e₀.symm
    haveI : PreservesColimit (parallelPair a' b') (Ins.forget f g ⋙ f') := inferInstance
    let e : parallelPair a b ⋙ Equif.forget α β ≅ parallelPair a' b' :=
      diagramIsoParallelPair (parallelPair a b ⋙ Equif.forget α β)
    haveI : HasColimit (parallelPair a b ⋙ Equif.forget α β) := hasColimit_of_iso e
    haveI : PreservesColimit (parallelPair a b ⋙ Equif.forget α β) (Ins.forget f g ⋙ f') :=
      preservesColimit_of_iso_diagram _ e.symm
    haveI : CreatesColimit (parallelPair a b) (Equif.forget α β) :=
      Equif.createsColimit (parallelPair a b)
    haveI : CreatesColimit (parallelPair a b ⋙ Equif.forget α β) (Ins.forget f g) :=
      createsColimitOfIsoDiagram (Ins.forget f g) e.symm
    infer_instance
  exact Monad.monadicOfCreatesGSplitCoequalizers (Adjunction.ofIsRightAdjoint _)

end UlmerBialgebras.Paper.ConcreteBialg
