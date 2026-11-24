module

public import UlmerBialgebras.Paper.Sec3Defs2
public import UlmerBialgebras.Paper.Sec4Defs2
public import UlmerBialgebras.Paper.Sec5Defs2
public import UlmerBialgebras.Paper.Sec6Defs2
public import UlmerBialgebras.Kan.SiftedPi
public import UlmerBialgebras.Factorization.RepModel
public import UlmerBialgebras.Factorization.RepTerm
public import UlmerBialgebras.Factorization.RepCat

/-!
# Factorization systems on the theory object of a model (Corollary 6.7)

## Main results

* `UlmerBialgebras.Paper.map_mem_of_componentwise`: a functor on a finite product that sends
  morphisms of the classes `Q i` to a class `P` (containing identities, closed under composition) in
  each variable separately sends componentwise morphisms to `P`.
* `UlmerBialgebras.Paper.fn_repPreservesLeft`: so a function symbol preserving the left classes
  componentwise preserves them representably on the product (in `CAT`);
  `UlmerBialgebras.Paper.fn_repPreservesRight` is the same for the right classes.
* `UlmerBialgebras.Paper.tm_repPreservesLeft_of_isVar`: terms that are sorts (projections) preserve
  the left class; `UlmerBialgebras.Paper.tm_repPreservesRight_of_isVar` the right class.
* `UlmerBialgebras.Paper.hasUniqueLiftedOFS_of_rep`: the development's lifted factorization system
  (`Model.thyRepOFS`) gives `HasUniqueLiftedOFS`.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Corollary 6.7
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u u₁ u₂ u₃ s₁ s₂ s₃

namespace UlmerBialgebras.Paper

open CategoryTheory Limits

section Componentwise

variable {ι : Type w} [DecidableEq ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
  {E : Type*} [Category E]

/-- A class of morphisms meets `G.map f` iff it meets `G'.map f`, for equal functors. -/
lemma map_mem_congr {A : Type*} [Category A] (P : MorphismProperty E) {G G' : A ⥤ E}
    (h : G = G') {a b : A} (f : a ⟶ b) : P (G.map f) ↔ P (G'.map f) := by
  subst h; rfl

/-- If `P` contains the identities and is closed under composition, and every
`updateFunctor x i ⋙ F` sends the morphisms of `Q i` into `P`, then for every finite set `s` of
variables, `restrictP x (· ∈ s) ⋙ F` sends every `f` with all components in `Q i` into `P`. -/
theorem restrictP_map_mem (F : (∀ i, C i) ⥤ E) (Q : ∀ i, MorphismProperty (C i))
    (P : MorphismProperty E) (hid : ∀ X : E, P (𝟙 X))
    (hcomp : ∀ ⦃X Y Z : E⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g))
    (hF : ∀ (i : ι) (x : ∀ j, C j) ⦃a b : C i⦄ (e : a ⟶ b), Q i e →
      P ((updateFunctor x i ⋙ F).map e)) :
    ∀ (s : Finset ι) (x : ∀ j, C j) ⦃a b : ∀ i, C i⦄ (f : a ⟶ b), (∀ i, Q i (f i)) →
      P ((restrictP x (fun j => j ∈ s) ⋙ F).map f) := by
  -- a single variable: restricting to `i` is evaluation at `i` followed by `updateFunctor x i`
  have hsing : ∀ (i : ι) (x : ∀ j, C j) ⦃a b : ∀ i, C i⦄ (f : a ⟶ b), Q i (f i) →
      P ((restrictP x (· = i) ⋙ F).map f) := by
    intro i x a b f hf
    have e : restrictP x (· = i) = Pi.eval C i ⋙ updateFunctor x i := by
      rw [restrictP, updateFunctor, comp_pi']
      refine pi'_congr (fun j => ?_)
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl, dite_eq_left rfl]
        rfl
      · rw [ite_eq_right hj, dite_eq_right hj]
        rfl
    rw [e]
    exact hF i x (f i) hf
  -- induction on `s`, splitting off one variable at a time with `mix`
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro x a b f _
      rw [restrictP_congr x (q := fun _ => False) (fun j => by simp), restrictP_false]
      simpa using hid _
  | insert i₀ s hi₀ ih =>
      intro x a b f hf
      rw [restrictP_congr x (q := fun j => j = i₀ ∨ j ∈ s) (fun j => by simp),
        ← diag_comp_mix x i₀ (fun j => j ∈ s)]
      have hsplit : ((Functor.diag (∀ j, C j) ⋙ mix x i₀ (fun j => j ∈ s)) ⋙ F).map f =
          ((CategoryTheory.Prod.sectL (∀ j, C j) a ⋙ mix x i₀ (fun j => j ∈ s)) ⋙ F).map f ≫
          ((CategoryTheory.Prod.sectR b (∀ j, C j) ⋙ mix x i₀ (fun j => j ∈ s)) ⋙ F).map f := by
        simp only [Functor.comp_map]
        refine (congrArg (F.map ∘ (mix x i₀ fun j => j ∈ s).map) ?_).trans
          ((mix x i₀ (fun j => j ∈ s) ⋙ F).map_comp _ _)
        exact Prod.hom_ext (Category.comp_id f).symm (Category.id_comp f).symm
      -- the first factor moves only `i₀`, the second only the variables of `s`
      rw [hsplit]
      refine hcomp _ _ ?_ ?_
      · exact (map_mem_congr P congr($(sectL_comp_mix x a i₀ (fun j => j ∈ s)) ⋙ F)
          f).2 (hsing i₀ _ f (hf i₀))
      · exact (map_mem_congr P
          congr($(sectR_comp_mix x b i₀ (fun j => j ∈ s) hi₀) ⋙ F) f).2 (ih _ f hf)

/-- **Componentwise preservation gives preservation**: if `F` sends `Q i`-morphisms to
`P`-morphisms in each variable separately, it sends morphisms that are componentwise in the
`Q i` to `P`. -/
theorem map_mem_of_componentwise [Finite ι] (F : (∀ i, C i) ⥤ E)
    (Q : ∀ i, MorphismProperty (C i)) (P : MorphismProperty E) (hid : ∀ X : E, P (𝟙 X))
    (hcomp : ∀ ⦃X Y Z : E⦄ (f : X ⟶ Y) (g : Y ⟶ Z), P f → P g → P (f ≫ g))
    (hF : ∀ (i : ι) (x : ∀ j, C j) ⦃a b : C i⦄ (e : a ⟶ b), Q i e →
      P ((updateFunctor x i ⋙ F).map e))
    ⦃a b : ∀ i, C i⦄ (f : a ⟶ b) (hf : ∀ i, Q i (f i)) : P (F.map f) := by
  have := Fintype.ofFinite ι
  have key := restrictP_map_mem F Q P hid hcomp hF Finset.univ a f hf
  rw [restrictP_congr a (q := fun _ => True) (fun j => by simp), restrictP_true,
    Functor.id_comp] at key
  exact key

end Componentwise

section ModelBridge

variable {Sg : TwoSig.{u₁, u₂, u₃}} (M : Model Sg Cat.{v, max u v})
  (S : ∀ c : Sg.Cat, OFS (M.obj c : Type (max u v)))

/-- If the structural functor `M(B)` of a `Σ`-model in `CAT` preserves the left classes `E` of the
factorization systems `S` componentwise, it preserves them representably on the product
`∏ M_{art B i}` (used for Corollary 6.7 of [forsman2026syntactic]). -/
theorem fn_repPreservesLeft (B : Sg.Fun) (h : PreservesLeftClassComponentwise M S B) :
    RepPreservesLeft ((M.P B).repOFS fun i => (S (Sg.art B i)).toRepOFS)
      (S (Sg.fcod B)).toRepOFS (M.fn B) := by
  intro x g h' α hα y
  exact map_mem_of_componentwise (M.fn B).toFunctor
    (fun i => (S (Sg.art B i)).E) (S (Sg.fcod B)).E (fun X => (S _).e_of_isIso _)
    (fun _ _ _ f g hf hg => (S _).e_comp hf hg) h (α.toNatTrans.app y) (fun i => hα i y)


/-- If the structural functor `M(B)` of a `Σ`-model in `CAT` preserves the right classes `M` of the
factorization systems `S` componentwise, it preserves them representably on the product
`∏ M_{art B i}` (used for Corollary 6.7 of [forsman2026syntactic]). -/
theorem fn_repPreservesRight (B : Sg.Fun) (h : PreservesRightClassComponentwise M S B) :
    RepPreservesRight ((M.P B).repOFS fun i => (S (Sg.art B i)).toRepOFS)
      (S (Sg.fcod B)).toRepOFS (M.fn B) := by
  intro x g h' α hα y
  exact map_mem_of_componentwise (M.fn B).toFunctor
    (fun i => (S (Sg.art B i)).M) (S (Sg.fcod B)).M (fun X => (S _).m_of_isIso _)
    (fun _ _ _ f g hf hg => (S _).m_comp hf hg) h (α.toNatTrans.app y) (fun i => hα i y)

/-- A term which is a sort is a product projection, so it preserves the left class. -/
theorem tm_repPreservesLeft_of_isVar (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    (Sr : ∀ c : Sg.Cat, RepOFS (M.obj c))
    {c : Sg.Cat} (t : sg.CTrm c) (ht : t.IsVar) :
    RepPreservesLeft (M.repOFS0 sg Sr) (Sr c) (M.tm sg t) := by
  cases t with
  | var s => exact (M.P0 sg).repPreservesLeft_π (fun s => Sr (sg.sty s)) s
  | app B args => exact ht.elim

/-- A term which is a sort is a product projection, so it preserves the right class. -/
theorem tm_repPreservesRight_of_isVar (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg)
    [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
    (Sr : ∀ c : Sg.Cat, RepOFS (M.obj c))
    {c : Sg.Cat} (t : sg.CTrm c) (ht : t.IsVar) :
    RepPreservesRight (M.repOFS0 sg Sr) (Sr c) (M.tm sg t) := by
  cases t with
  | var s => exact (M.P0 sg).repPreservesRight_π (fun s => Sr (sg.sty s)) s
  | app B args => exact ht.elim

section Lifted

variable (sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg) [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
  [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}] (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
  [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}]
  (hfnE : ∀ f : sg.Fn, RepPreservesLeft (M.repOFS0 sg fun c => (S c).toRepOFS)
    ((S (sg.fnty f)).toRepOFS) (M.funArity sg f))
  (hfnM : ∀ f : sg.Fn, RepPreservesRight (M.repOFS0 sg fun c => (S c).toRepOFS)
    ((S (sg.fnty f)).toRepOFS) (M.funCoarity sg f))
  (heqE : ∀ r : T.Eqn, RepPreservesLeft (M.repOFS0 sg fun c => (S c).toRepOFS)
    ((S (T.eqty r)).toRepOFS) (M.eqnArity sg T r))
  (heqM : ∀ r : T.Eqn, RepPreservesRight (M.repOFS0 sg fun c => (S c).toRepOFS)
    ((S (T.eqty r)).toRepOFS) (M.eqnCoarity sg T r))

omit [HasChosenProductsOfSize.{s₁} Cat.{v, max u v}]
  [HasChosenProductsOfSize.{s₂} Cat.{v, max u v}]
  [HasChosenProductsOfSize.{s₃} Cat.{v, max u v}] in
/-- Helper for `hasUniqueLiftedOFS_of_rep`: translates a conjugation-invariant predicate on the
target OFS along `oneEquiv`. -/
private lemma conj_oneEval_iff {C : CategoryTheory.Cat.{v, max u v}}
    (P : ∀ ⦃a b : C⦄, (a ⟶ b) → Prop)
    (hconj : ∀ {a b a' b' : C} (i₁ : a' ≅ a) (f : a ⟶ b) (i₂ : b ≅ b'),
      P (i₁.hom ≫ f ≫ i₂.hom) ↔ P f)
    {x y : C} (f : x ⟶ y) :
    (∀ _z : One.{v, max u v},
      P ((oneEval C).map ((oneEquiv C).inverse.map f))) ↔ P f := by
  refine ⟨fun h => ?_, fun h z => ?_⟩
  · have h1 := h One.star
    have h2 : (oneEval C).map ((oneEquiv C).inverse.map f) =
        (oneEquiv C).counit.app x ≫ f ≫ (oneEquiv C).counitInv.app y :=
      Equivalence.fun_inv_map (oneEquiv C) x y f
    rw [h2] at h1
    exact (hconj ((oneEquiv C).counitIso.app x) f ((oneEquiv C).counitIso.app y).symm).1 h1
  · cases z
    have h2 : (oneEval C).map ((oneEquiv C).inverse.map f) =
        (oneEquiv C).counit.app x ≫ f ≫ (oneEquiv C).counitInv.app y :=
      Equivalence.fun_inv_map (oneEquiv C) x y f
    rw [h2]
    exact (hconj ((oneEquiv C).counitIso.app x) f ((oneEquiv C).counitIso.app y).symm).2 h

include hfnE hfnM heqE heqM in
/-- The lifted factorization system of Corollary 6.7 satisfies `HasUniqueLiftedOFS`. -/
theorem hasUniqueLiftedOFS_of_rep : HasUniqueLiftedOFS M S sg T := by
  let R := M.thyRepOFS sg T (fun c => (S c).toRepOFS) hfnE hfnM heqE heqM
  -- at the generic point `One`, both classes of `R` are tested sortwise
  have keyE : ∀ {g h : One.{v, max u v} ⟶ M.thyObj sg T} (α : g ⟶ h),
      (R.ofs One.{v, max u v}).E α ↔ ∀ s : sg.Srt,
        (((S (sg.sty s)).toRepOFS).ofs One.{v, max u v}).E
          (α ▷ (M.thyForget sg T ≫ (M.P0 sg).π s)) := fun α => by
    refine ⟨fun hα s => ?_, fun hα s => ?_⟩
    · rw [show M.thyForget sg T ≫ (M.P0 sg).π s
          = (M.e sg T ≫ M.u sg) ≫ (M.P0 sg).π s from rfl, e_whiskerRight_comp₂_iff]
      exact hα s
    · have h1 := hα s
      rw [show M.thyForget sg T ≫ (M.P0 sg).π s
          = (M.e sg T ≫ M.u sg) ≫ (M.P0 sg).π s from rfl, e_whiskerRight_comp₂_iff] at h1
      exact h1
  have keyM : ∀ {g h : One.{v, max u v} ⟶ M.thyObj sg T} (α : g ⟶ h),
      (R.ofs One.{v, max u v}).M α ↔ ∀ s : sg.Srt,
        (((S (sg.sty s)).toRepOFS).ofs One.{v, max u v}).M
          (α ▷ (M.thyForget sg T ≫ (M.P0 sg).π s)) := fun α => by
    refine ⟨fun hα s => ?_, fun hα s => ?_⟩
    · rw [show M.thyForget sg T ≫ (M.P0 sg).π s
          = (M.e sg T ≫ M.u sg) ≫ (M.P0 sg).π s from rfl, m_whiskerRight_comp₂_iff]
      exact hα s
    · have h1 := hα s
      rw [show M.thyForget sg T ≫ (M.P0 sg).π s
          = (M.e sg T ≫ M.u sg) ≫ (M.P0 sg).π s from rfl, m_whiskerRight_comp₂_iff] at h1
      exact h1
  -- at an arbitrary morphism, by conjugating with the evaluations at `One`
  have hE : ∀ ⦃x y : (M.thyObj sg T : Type (max u v))⦄ (f : x ⟶ y),
      R.toOFS.E f ↔ ∀ s : sg.Srt, (S (sg.sty s)).E ((M.thyForget sg T ≫ (M.P0 sg).π
          s).toFunctor.map f) := fun x y f =>
    (keyE _).trans (forall_congr' fun s =>
      conj_oneEval_iff (fun _ _ g => (S (sg.sty s)).E ((M.thyForget sg T ≫ (M.P0 sg).π
        s).toFunctor.map g)) (fun i₁ g i₂ => by
        rw [Functor.map_comp, Functor.map_comp]; exact (S _).e_conj_iff _ _ _) f)
  have hM : ∀ ⦃x y : (M.thyObj sg T : Type (max u v))⦄ (f : x ⟶ y),
      R.toOFS.M f ↔ ∀ s : sg.Srt, (S (sg.sty s)).M ((M.thyForget sg T ≫ (M.P0 sg).π
          s).toFunctor.map f) := fun x y f =>
    (keyM _).trans (forall_congr' fun s =>
      conj_oneEval_iff (fun _ _ g => (S (sg.sty s)).M ((M.thyForget sg T ≫ (M.P0 sg).π
        s).toFunctor.map g)) (fun i₁ g i₂ => by
        rw [Functor.map_comp, Functor.map_comp]; exact (S _).m_conj_iff _ _ _) f)
  -- any other lifted system has the same classes, so it equals `R.toOFS`
  exact ⟨R.toOFS, hE, hM, fun P' hE' hM' =>
    OFS.ext_of_le (fun _ _ f h => (hE f).2 (hE' f h)) (fun _ _ f h => (hM f).2 (hM' f h))⟩

end Lifted

end ModelBridge

end UlmerBialgebras.Paper
