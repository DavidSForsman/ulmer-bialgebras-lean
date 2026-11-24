module

public import UlmerBialgebras.Kan.Sifted
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# Lemma 4.16: the `n`-ary case

`Sifted.lean` proves Lemma 4.16 of *A Syntactic Approach to Ulmer's Bialgebras* for a
functor of two variables.  Here we deduce the general case: a functor

`F : C₁ × ⋯ × Cₙ ⥤ E`

on a *finite* product of categories preserves colimits of a sifted shape if and only if it
preserves them in each variable separately.

The induction is organised through the functors

`UlmerBialgebras.restrictP x p : (∀ j, C j) ⥤ (∀ j, C j)`, `y ↦ (j ↦ if p j then y j else x j)`,

which freeze all the variables outside `p` at the values given by `x`: the statement proved
by induction on a finite set `s` of variables is that `restrictP x (· ∈ s) ⋙ F` preserves
sifted colimits, the inductive step being an application of the binary case to the functor
`UlmerBialgebras.mix`.

## Main results

* `UlmerBialgebras.restrictP`: the functor freezing the variables outside `p` at the values of `x`.
* `UlmerBialgebras.restrictP_finset_preservesColimitsOfShape`: if `F` preserves sifted `J`-colimits
  in each single variable, then `restrictP x (· ∈ s) ⋙ F` preserves them for every finite set `s`.
* `UlmerBialgebras.preservesColimitsOfShape_pi_of_componentwise`: a functor on a finite product of
  categories that preserves sifted `J`-colimits in each variable preserves `J`-colimits
  (Lemma 4.16).

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 4.16
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

variable {J : Type*} [Category J]
variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {E : Type*} [Category E]

/-! ## Restricting a functor to a set of variables -/

/-- `Functor.pi'` respects pointwise equality of the families of functors. -/
lemma pi'_congr {A : Type*} [Category A] {f g : ∀ j, A ⥤ C j} (h : ∀ j, f j = g j) :
    Functor.pi' f = Functor.pi' g := by rw [funext h]

/-- Precomposition commutes with `Functor.pi'`: `G ⋙ pi' f = pi' (G ⋙ f ·)`. -/
lemma comp_pi' {A B : Type*} [Category A] [Category B] (G : B ⥤ A) (f : ∀ j, A ⥤ C j) :
    G ⋙ Functor.pi' f = Functor.pi' (fun j => G ⋙ f j) := rfl

/-- The functor freezing all the variables outside `p` at the values given by `x`. -/
def restrictP (x : ∀ j, C j) (p : ι → Prop) [DecidablePred p] : (∀ j, C j) ⥤ (∀ j, C j) :=
  Functor.pi' fun j => if p j then Pi.eval C j else (Functor.const (∀ k, C k)).obj (x j)

/-- `restrictP x p` depends only on the extension of the predicate `p`. -/
lemma restrictP_congr (x : ∀ j, C j) {p q : ι → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ j, p j ↔ q j) : restrictP x p = restrictP x q := by
  refine pi'_congr (fun j => ?_)
  by_cases hj : p j
  · rw [ite_eq_left hj, ite_eq_left ((h j).1 hj)]
  · rw [ite_eq_right hj, ite_eq_right (fun hq => hj ((h j).2 hq))]

/-- At a variable `j` with `p j`, `(restrictP x p).obj y` takes the value `y j`. -/
lemma restrictP_obj_pos (x y : ∀ j, C j) {p : ι → Prop} [DecidablePred p] {j : ι} (h : p j) :
    (restrictP x p).obj y j = y j := by
  simp [restrictP, h]

/-- At a variable `j` with `¬ p j`, `(restrictP x p).obj y` takes the frozen value `x j`. -/
lemma restrictP_obj_neg (x y : ∀ j, C j) {p : ι → Prop} [DecidablePred p] {j : ι} (h : ¬ p j) :
    (restrictP x p).obj y j = x j := by
  simp [restrictP, h]

/-- Freezing every variable gives the constant functor at `x`. -/
lemma restrictP_false (x : ∀ j, C j) :
    restrictP x (fun _ => False) = (Functor.const (∀ j, C j)).obj x := by
  rw [restrictP, pi'_congr (g := fun j => (Functor.const (∀ k, C k)).obj (x j))
    (fun j => ite_eq_right not_false)]
  rfl

/-- Freezing no variable gives the identity functor. -/
lemma restrictP_true (x : ∀ j, C j) : restrictP x (fun _ => True) = 𝟭 (∀ j, C j) := by
  rw [restrictP, pi'_congr (g := fun j => Pi.eval C j) (fun j => ite_eq_left trivial)]
  rfl

/-! ## The mixing functor of the inductive step -/

variable [DecidableEq ι]

/-- The functor of two variables `(w, y) ↦ (j ↦ if j = i₀ then w j else if p j then y j
else x j)`. -/
def mix (x : ∀ j, C j) (i₀ : ι) (p : ι → Prop) [DecidablePred p] :
    ((∀ j, C j) × (∀ j, C j)) ⥤ (∀ j, C j) :=
  Functor.pi' fun j =>
    if j = i₀ then CategoryTheory.Prod.fst (∀ k, C k) (∀ k, C k) ⋙ Pi.eval C j
    else if p j then CategoryTheory.Prod.snd (∀ k, C k) (∀ k, C k) ⋙ Pi.eval C j
    else (Functor.const _).obj (x j)

/-- Along the diagonal, `mix x i₀ p` is `restrictP x` for the predicate `j = i₀ ∨ p j`. -/
lemma diag_comp_mix (x : ∀ j, C j) (i₀ : ι) (p : ι → Prop) [DecidablePred p] :
    Functor.diag (∀ j, C j) ⋙ mix x i₀ p = restrictP x (fun j => j = i₀ ∨ p j) := by
  rw [mix, restrictP, comp_pi']
  refine pi'_congr (fun j => ?_)
  by_cases h1 : j = i₀
  · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
    rfl
  · by_cases h2 : p j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (Or.inr h2)]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by tauto)]
      rfl

/-- Fixing the second argument at `y`, `mix x i₀ p` frees only the variable `i₀`, around
the point `(restrictP x p).obj y`. -/
lemma sectL_comp_mix (x y : ∀ j, C j) (i₀ : ι) (p : ι → Prop) [DecidablePred p] :
    CategoryTheory.Prod.sectL (∀ j, C j) y ⋙ mix x i₀ p
      = restrictP ((restrictP x p).obj y) (· = i₀) := by
  rw [mix, restrictP, comp_pi']
  refine pi'_congr (fun j => ?_)
  by_cases h1 : j = i₀
  · rw [ite_eq_left h1, ite_eq_left h1]
    rfl
  · by_cases h2 : p j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, restrictP_obj_pos x y h2]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, restrictP_obj_neg x y h2]
      rfl

/-- Fixing the first argument at `w` (when `¬ p i₀`), `mix x i₀ p` is `restrictP p` around
the point `(restrictP x (· = i₀)).obj w`. -/
lemma sectR_comp_mix (x w : ∀ j, C j) (i₀ : ι) (p : ι → Prop) [DecidablePred p]
    (hi₀ : ¬ p i₀) :
    CategoryTheory.Prod.sectR w (∀ j, C j) ⋙ mix x i₀ p
      = restrictP ((restrictP x (· = i₀)).obj w) p := by
  rw [mix, restrictP, comp_pi']
  refine pi'_congr (fun j => ?_)
  by_cases h1 : j = i₀
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right hi₀, restrictP_obj_pos x w (p := (· = j)) rfl]
    rfl
  · by_cases h2 : p j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, restrictP_obj_neg x w (p := (· = i₀))
        h1]
      rfl

/-! ## Lemma 4.16 for a finite product -/

variable (F : (∀ j, C j) ⥤ E)

/-- The inductive step: the variables of a finite set can be handled jointly. -/
theorem restrictP_finset_preservesColimitsOfShape [IsSifted J]
    (hsing : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimitsOfShape J (restrictP x (· = i) ⋙ F)) :
    ∀ (s : Finset ι) (x : ∀ j, C j),
      PreservesColimitsOfShape J (restrictP x (fun j => j ∈ s) ⋙ F) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro x
      rw [restrictP_congr x (q := fun _ => False) (fun j => by simp), restrictP_false]
      exact preservesColimitsOfShape_of_natIso (Functor.constComp _ x F).symm
  | insert i₀ s hi₀ ih =>
      intro x
      have hmix : PreservesColimitsOfShape J (mix x i₀ (fun j => j ∈ s) ⋙ F) := by
        refine (preservesColimitsOfShape_iff_componentwise
          (mix x i₀ (fun j => j ∈ s) ⋙ F)).2 ⟨fun y => ⟨?_⟩, fun w => ⟨?_⟩⟩ |>.some
        · rw [← Functor.assoc, sectL_comp_mix x y i₀ (fun j => j ∈ s)]
          exact hsing i₀ ((restrictP x (fun j => j ∈ s)).obj y)
        · rw [← Functor.assoc, sectR_comp_mix x w i₀ (fun j => j ∈ s) hi₀]
          exact ih ((restrictP x (· = i₀)).obj w)
      rw [restrictP_congr x (q := fun j => j = i₀ ∨ j ∈ s) (fun j => by simp),
        ← diag_comp_mix x i₀ (fun j => j ∈ s), Functor.assoc]
      have := hmix
      infer_instance

/-- **Lemma 4.16** ([forsman2026syntactic]): a functor on a finite product of categories preserves
colimits of a sifted shape as soon as it preserves them in each variable separately. -/
theorem preservesColimitsOfShape_pi_of_componentwise [IsSifted J] [Finite ι]
    (h : ∀ (i : ι) (x : ∀ j, C j), PreservesColimitsOfShape J (updateFunctor x i ⋙ F)) :
    PreservesColimitsOfShape J F := by
  have := Fintype.ofFinite ι
  have hsing : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimitsOfShape J (restrictP x (· = i) ⋙ F) := by
    intro i x
    have e : restrictP x (· = i) = Pi.eval C i ⋙ updateFunctor x i := by
      rw [restrictP, updateFunctor, comp_pi']
      refine pi'_congr (fun j => ?_)
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl, dite_eq_left rfl]
        rfl
      · rw [ite_eq_right hj, dite_eq_right hj]
        rfl
    rw [e, Functor.assoc]
    have := h i x
    infer_instance
  by_cases hne : Nonempty (∀ j, C j)
  · obtain ⟨x₀⟩ := hne
    have key := restrictP_finset_preservesColimitsOfShape F hsing Finset.univ x₀
    rw [restrictP_congr x₀ (q := fun _ => True) (fun j => by simp), restrictP_true,
      Functor.id_comp] at key
    exact key
  · -- the product category is empty, so there are no diagrams of the (nonempty) shape `J`
    constructor
    intro K
    exact absurd ⟨K.obj (Classical.arbitrary J)⟩ hne

end UlmerBialgebras
