module

public import UlmerBialgebras.Paper.Sec6DefsTheoryMorphism
public import UlmerBialgebras.Proofs.Sec5.AlgTheoryTransport

/-!
# Solution: morphisms of theories induce functors between categories of models

Not a result of the paper. A morphism of many-sorted
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

namespace MSLanguage

section Helpers

variable {L : MSLanguage.{u₁, u₂}}

/-- Substitution is associative. -/
lemma Term.subst_subst {n m k : ℕ} {Γ : Fin n → L.Sorts} {Δ : Fin m → L.Sorts}
    {Θ : Fin k → L.Sorts} (σ : ∀ i, L.Term Γ (Δ i)) (τ : ∀ i, L.Term Δ (Θ i)) :
    ∀ {s : L.Sorts} (t : L.Term Θ s), (t.subst τ).subst σ = t.subst (fun i => (τ i).subst σ)
  | _, .var _ => rfl
  | _, .func f ts => congr(Term.func f $(funext fun j => Term.subst_subst σ τ (ts j)))

/-- Derivability is closed under substitution. -/
lemma Theory.Derives.subst {T : L.Theory} {n m : ℕ} {Γ : Fin n → L.Sorts}
    {Δ : Fin m → L.Sorts} (σ : ∀ i, L.Term Γ (Δ i)) {s : L.Sorts} {a b : L.Term Δ s}
    (h : T.Derives a b) : T.Derives (a.subst σ) (b.subst σ) := by
  induction h generalizing n with
  | ax φ hφ τ =>
    rw [Term.subst_subst, Term.subst_subst]
    exact .ax φ hφ _
  | refl a => exact .refl _
  | symm _ ih => exact (ih σ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ σ).trans (ih₂ σ)
  | congr f _ ih => exact .congr f fun i => ih i σ

/-- Substituting derivably equal terms gives derivably equal terms. -/
lemma Theory.Derives.subst_congr {T : L.Theory} {n m : ℕ} {Γ : Fin n → L.Sorts}
    {Δ : Fin m → L.Sorts} {σ σ' : ∀ i, L.Term Γ (Δ i)} (h : ∀ i, T.Derives (σ i) (σ' i)) :
    ∀ {s : L.Sorts} (t : L.Term Δ s), T.Derives (t.subst σ) (t.subst σ')
  | _, .var i => h i
  | _, .func f ts => .congr f fun j => Theory.Derives.subst_congr h (ts j)

end Helpers

namespace LangMorphism

variable {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}} {L₃ : MSLanguage.{u₅, u₆}}

/-- Translation commutes with substitution. -/
lemma translate_subst (F : LangMorphism L₁ L₂) {n m : ℕ} {Γ : Fin n → L₁.Sorts}
    {Δ : Fin m → L₁.Sorts} (σ : ∀ i, L₁.Term Γ (Δ i)) :
    ∀ {s : L₁.Sorts} (t : L₁.Term Δ s),
      F.translate (t.subst σ) = (F.translate t).subst (fun i => F.translate (σ i))
  | _, .var _ => rfl
  | _, .func f ts => by
    simp only [Term.subst, translate, Term.subst_subst]
    exact congr(Term.subst $(funext fun j => translate_subst F σ (ts j)) (F.funMap f))

/-- Translating along a composite is translating twice. -/
lemma translate_comp (G : LangMorphism L₂ L₃) (F : LangMorphism L₁ L₂) {n : ℕ}
    {Γ : Fin n → L₁.Sorts} :
    ∀ {s : L₁.Sorts} (t : L₁.Term Γ s), (G.comp F).translate t = G.translate (F.translate t)
  | _, .var _ => rfl
  | _, .func f ts => by
    simp only [translate, comp, translate_subst]
    exact congr(Term.subst $(funext fun j => translate_comp G F (ts j)) (G.translate (F.funMap f)))

/-- A morphism of theories translates derivations. -/
lemma Theory.Derives.translate {T₂ : L₂.Theory} {T₃ : L₃.Theory} {G : LangMorphism L₂ L₃}
    (hG : G.IsTheoryMorphism T₂ T₃) {n : ℕ} {Γ : Fin n → L₂.Sorts} {s : L₂.Sorts}
    {a b : L₂.Term Γ s} (h : T₂.Derives a b) : T₃.Derives (G.translate a) (G.translate b) := by
  induction h with
  | ax φ hφ σ =>
    rw [translate_subst, translate_subst]
    exact (hG φ hφ).subst _
  | refl a => exact .refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr f _ ih => exact Theory.Derives.subst_congr ih (G.funMap f)

end LangMorphism

section ModelEq

variable {L : MSLanguage.{u₁, u₂}} {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {T : L.Theory}

/-- Two models on the same family with the same interpretations are equal. -/
lemma modelCat_mk_eq {M : L.Sorts → C} (s₁ s₂ : L.Structure M)
    (h : ∀ f, @funMap _ _ _ _ M s₁ f = @funMap _ _ _ _ M s₂ f) (m₁ m₂) :
    @Theory.ModelCat.mk L C _ _ T M s₁ m₁ = @Theory.ModelCat.mk L C _ _ T M s₂ m₂ := by
  obtain ⟨f₁⟩ := s₁
  obtain ⟨f₂⟩ := s₂
  obtain rfl : f₁ = f₂ := funext h
  rfl

/-- The components of an `eqToHom` between models. -/
lemma modelCat_eqToHom_toFun {A B : T.ModelCat C} (h : A = B) (s : L.Sorts) :
    Hom.toFun (eqToHom h) s = eqToHom (congrFun (congrArg Theory.ModelCat.Carrier h) s) := by
  subst h
  rfl

end ModelEq

end MSLanguage

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C]
  {L₁ : MSLanguage.{u₁, u₂}} {L₂ : MSLanguage.{u₃, u₄}} {L₃ : MSLanguage.{u₅, u₆}}
  {T₁ : L₁.Theory} {T₂ : L₂.Theory} {T₃ : L₃.Theory}

/-- **The induced functor commutes with the forgetful functors** (addition beyond
[forsman2026syntactic]): `φ^* ⋙ U₁ = U₂ ⋙ (− ∘ sortMap)`, strictly. -/
theorem modelFunctor_forget (φ : TheoryMorphism T₁ T₂) :
    φ.modelFunctor C ⋙ Theory.ModelCat.forget C T₁ =
      Theory.ModelCat.forget C T₂ ⋙ Pi.comap (fun _ => C) φ.sortMap :=
  rfl

/-- **Morphisms of theories compose** (addition beyond [forsman2026syntactic]): if the axioms of
`T₁` translate to consequences of `T₂`, and those of `T₂` to consequences of `T₃`, then the axioms
of `T₁` translate along the composite to consequences of `T₃`. -/
theorem isTheoryMorphism_comp {F : LangMorphism L₁ L₂} {G : LangMorphism L₂ L₃}
    (hF : F.IsTheoryMorphism T₁ T₂) (hG : G.IsTheoryMorphism T₂ T₃) :
    (G.comp F).IsTheoryMorphism T₁ T₃ :=
  fun φ hφ => by
    rw [LangMorphism.translate_comp, LangMorphism.translate_comp]
    exact LangMorphism.Theory.Derives.translate hG (hF φ hφ)

/-- **The identity induces the identity** (addition beyond [forsman2026syntactic]):
`id^* = 𝟭`. -/
theorem modelFunctor_id (T : L₁.Theory) : (TheoryMorphism.id T).modelFunctor C = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun A => by
    obtain ⟨M, _, _⟩ := A
    exact modelCat_mk_eq _ _ (fun f =>
      (Pi.lift_π =≫ funMap f).trans (Category.id_comp _)) _ _)
  (fun A B g => Hom.ext (funext fun s => by
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ s).symm
    refine Eq.trans ?_ (((modelCat_eqToHom_toFun _ s) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (MSLanguage.comp_toFun _ _ s)).symm)
    refine Eq.trans ?_ ((_ ≫= _ ≫= modelCat_eqToHom_toFun _ s).symm)
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

/-- **Induced functors compose** (addition beyond [forsman2026syntactic]):
`(ψ ∘ φ)^* = ψ^* ⋙ φ^*`. The composite is a morphism of theories by `isTheoryMorphism_comp`. -/
theorem modelFunctor_comp (φ : TheoryMorphism T₁ T₂) (ψ : TheoryMorphism T₂ T₃)
    (h : (ψ.toLangMorphism.comp φ.toLangMorphism).IsTheoryMorphism T₁ T₃) :
    TheoryMorphism.modelFunctor C
        ⟨ψ.toLangMorphism.comp φ.toLangMorphism, h⟩ =
      ψ.modelFunctor C ⋙ φ.modelFunctor C :=
  CategoryTheory.Functor.ext (fun A => modelCat_mk_eq _ _
    (fun f => LangMorphism.realize_translate ψ.toLangMorphism A.Carrier (φ.funMap f)) _ _)
  (fun A B g => Hom.ext (funext fun s => by
    refine Eq.trans ?_ (MSLanguage.comp_toFun _ _ s).symm
    refine Eq.trans ?_ (((modelCat_eqToHom_toFun _ s) =≫ _).symm)
    refine Eq.trans ?_ ((_ ≫= (MSLanguage.comp_toFun _ _ s)).symm)
    refine Eq.trans ?_ ((_ ≫= _ ≫= modelCat_eqToHom_toFun _ s).symm)
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm))

/-- **Inclusions of theories** (addition beyond [forsman2026syntactic]): for `T ⊆ T'`, the
functor induced by the inclusion keeps the underlying objects. -/
theorem ofLE_forget {T T' : L₁.Theory} (h : T ⊆ T') :
    (TheoryMorphism.ofLE h).modelFunctor C ⋙ Theory.ModelCat.forget C T =
      Theory.ModelCat.forget C T' :=
  rfl

/-- **Reducts along a sublanguage** (addition beyond [forsman2026syntactic]): the functor induced
by the inclusion of a sublanguage forgets the other function symbols and keeps the underlying
objects. -/
theorem ofRestrict_forget {P : L₁.Functions → Prop} {T : (L₁.restrict P).Theory}
    {T' : L₁.Theory}
    (h : ∀ φ ∈ T, (LangMorphism.ofRestrict P).translateEquation φ ∈ T') :
    (TheoryMorphism.ofRestrict h).modelFunctor C ⋙ Theory.ModelCat.forget C T =
      Theory.ModelCat.forget C T' :=
  rfl

end UlmerBialgebras.Paper
