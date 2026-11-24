module

public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism

/-!
# Morphisms of theories induce functors between categories of models (addition beyond the paper)

Not a result of the paper (the author's generality principle). A morphism of many-sorted
equational theories `φ : T₁ → T₂` (`MSLanguage.TheoryMorphism`: sorts to sorts, function symbols
to terms, translated axioms derivable) induces a functor `φ^* : Mod_C(T₂) ⥤ Mod_C(T₁)` for every
category `C` with finite products (`TheoryMorphism.modelFunctor`).

* `modelFunctor_forget`: `φ^*` commutes strictly with the forgetful functors to `C^S`, reindexed
  along the sort map.
* `isTheoryMorphism_comp`: morphisms of theories compose.
* `modelFunctor_id`, `modelFunctor_comp`: `id^* = 𝟭` and `(ψ ∘ φ)^* = ψ^* ⋙ φ^*`.
* `ofLE_forget`, `ofRestrict_forget`: the inclusion of theories and the
  reduct along a sublanguage are instances, whose induced functors do not change the underlying
  objects.

## Main results

* `UlmerBialgebras.Paper.modelFunctor_forget`
* `UlmerBialgebras.Paper.isTheoryMorphism_comp`
* `UlmerBialgebras.Paper.modelFunctor_id`
* `UlmerBialgebras.Paper.modelFunctor_comp`
* `UlmerBialgebras.Paper.ofLE_forget`
* `UlmerBialgebras.Paper.ofRestrict_forget`

## References

* [J. Adámek, J. Rosický, E. M. Vitale, *Algebraic Theories*][Adamek-Rosicky-Vitale],
  Chapters 1 and 14
-/

@[expose] public section

universe v u u₁ u₂ u₃ u₄ u₅ u₆

namespace UlmerBialgebras.Paper

open CategoryTheory Limits MSLanguage

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C]
  {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}} {L₃ : MSLanguage.{u₅, u₆}}
  {T₁ : L₁.Theory} {T₂ : L₂.Theory} {T₃ : L₃.Theory}

/-- **The induced functor commutes with the forgetful functors** (addition beyond
[forsman2026syntactic]): `φ^* ⋙ U₁ = U₂ ⋙ (− ∘ sortMap)`, strictly. -/
theorem modelFunctor_forget (φ : TheoryMorphism T₁ T₂) :
    φ.modelFunctor C ⋙ Theory.ModelCat.forget C T₁ =
      Theory.ModelCat.forget C T₂ ⋙ Pi.comap (fun _ => C) φ.sortMap :=
  sorry

/-- **Morphisms of theories compose** (addition beyond [forsman2026syntactic]): if the axioms of
`T₁` translate to consequences of `T₂`, and those of `T₂` to consequences of `T₃`, then the axioms
of `T₁` translate along the composite to consequences of `T₃`. -/
theorem isTheoryMorphism_comp {F : LangMorphism L₁ L₂} {G : LangMorphism L₂ L₃}
    (hF : F.IsTheoryMorphism T₁ T₂) (hG : G.IsTheoryMorphism T₂ T₃) :
    (G.comp F).IsTheoryMorphism T₁ T₃ :=
  sorry

/-- **The identity induces the identity** (addition beyond [forsman2026syntactic]):
`id^* = 𝟭`. -/
theorem modelFunctor_id (T : L₁.Theory) : (TheoryMorphism.id T).modelFunctor C = 𝟭 _ :=
  sorry

/-- **Induced functors compose** (addition beyond [forsman2026syntactic]):
`(ψ ∘ φ)^* = ψ^* ⋙ φ^*`. The composite is a morphism of theories by `isTheoryMorphism_comp`. -/
theorem modelFunctor_comp (φ : TheoryMorphism T₁ T₂) (ψ : TheoryMorphism T₂ T₃)
    (h : (ψ.toLangMorphism.comp φ.toLangMorphism).IsTheoryMorphism T₁ T₃) :
    TheoryMorphism.modelFunctor C
        ⟨ψ.toLangMorphism.comp φ.toLangMorphism, h⟩ =
      ψ.modelFunctor C ⋙ φ.modelFunctor C :=
  sorry

/-- **Inclusions of theories** (addition beyond [forsman2026syntactic]): for `T ⊆ T'`, the
functor induced by the inclusion keeps the underlying objects. -/
theorem ofLE_forget {T T' : L₁.Theory} (h : T ⊆ T') :
    (TheoryMorphism.ofLE h).modelFunctor C ⋙ Theory.ModelCat.forget C T =
      Theory.ModelCat.forget C T' :=
  sorry

/-- **Reducts along a sublanguage** (addition beyond [forsman2026syntactic]): the functor induced
by the inclusion of a sublanguage forgets the other function symbols and keeps the underlying
objects. -/
theorem ofRestrict_forget {P : L₁.Functions → Prop} {T : (L₁.restrict P).Theory}
    {T' : L₁.Theory}
    (h : ∀ φ ∈ T, (LangMorphism.ofRestrict P).translateEquation φ ∈ T') :
    (TheoryMorphism.ofRestrict h).modelFunctor C ⋙ Theory.ModelCat.forget C T =
      Theory.ModelCat.forget C T' :=
  sorry

end UlmerBialgebras.Paper
