module

public import UlmerBialgebras.Kan.SiftedPi

/-!
# Preservation of one sifted colimit

Diagram-specific versions of the binary argument in `Sifted.lean` and the
finite-set induction in `SiftedPi.lean`. No preservation of other diagrams
of the same shape is assumed.

## Main results

* `UlmerBialgebras.preservesColimit_prod_of_componentwise`: for a sifted diagram `D : J ⥤ A × B`, a
  functor `F : A × B ⥤ E` preserves the colimit of `D` if each partial functor of `F` preserves the
  colimit of the corresponding component diagram.
* `UlmerBialgebras.preservesColimit_diag_of_componentwise`: the case of two copies of a diagram
  `D : J ⥤ A`, for `diag A ⋙ F`.
* `UlmerBialgebras.preservesColimit_pi_of_componentwise`: the analogue for a finite product of
  categories.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Lemma 4.16
* [J. Adámek, J. Rosický, E. M. Vitale, *What are sifted
  colimits?*][AdamekRosickyVitale2010SiftedColimits]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits Functor

section Binary

variable {J : Type*} [Category J]
variable {A B E : Type*} [Category A] [Category B] [Category E]

/-- The binary sifted-colimit argument needs only the two component diagrams. -/
theorem preservesColimit_prod_of_componentwise [IsSifted J]
    (F : A × B ⥤ E) (D : J ⥤ A × B)
    (h₁ : ∀ x : B, PreservesColimit (D ⋙ CategoryTheory.Prod.fst A B)
      (CategoryTheory.Prod.sectL A x ⋙ F))
    (h₂ : ∀ x : A, PreservesColimit (D ⋙ CategoryTheory.Prod.snd A B)
      (CategoryTheory.Prod.sectR x B ⋙ F)) :
    PreservesColimit D F := by
  have : ∀ x : B, PreservesColimit (D ⋙ CategoryTheory.Prod.fst A B)
      ((curry.obj F).flip.obj x) := h₁
  have : ∀ x : A, PreservesColimit (D ⋙ CategoryTheory.Prod.snd A B)
      ((curry.obj F).obj x) := h₂
  refine ⟨fun {c} hc => ?_⟩
  have key := (Functor.Final.isColimitWhiskerEquiv (diag J) _).symm
    (isColimitOfPreserves₂ (curry.obj F) (isColimitFst hc) (isColimitSnd hc))
  exact ⟨(IsColimit.equivOfNatIsoOfIso (diagCompIso F D) _ (F.mapCocone c)
    (diagCompIsoCoconeIso F c)) key⟩

/-- Specialize the binary result to two copies of a fixed diagram. -/
theorem preservesColimit_diag_of_componentwise [IsSifted J]
    (F : A × A ⥤ E) (D : J ⥤ A)
    (h₁ : ∀ x : A, PreservesColimit D (CategoryTheory.Prod.sectL A x ⋙ F))
    (h₂ : ∀ x : A, PreservesColimit D (CategoryTheory.Prod.sectR x A ⋙ F)) :
    PreservesColimit D (diag A ⋙ F) := by
  have : PreservesColimit (D ⋙ diag A) F :=
    preservesColimit_prod_of_componentwise F (D ⋙ diag A) h₁ h₂
  infer_instance

end Binary

section Finite

variable {J : Type*} [Category J] [IsSifted J]
variable {ι : Type w} [DecidableEq ι] {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {E : Type*} [Category E]
variable (F : (∀ j, C j) ⥤ E) (D : J ⥤ ∀ j, C j)

/-- Unfreeze a finite set of coordinates, keeping the diagram fixed. -/
theorem restrictP_finset_preservesColimit
    (hsing : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimit D (restrictP x (· = i) ⋙ F)) :
    ∀ (s : Finset ι) (x : ∀ j, C j),
      PreservesColimit D (restrictP x (fun j => j ∈ s) ⋙ F) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro x
      rw [restrictP_congr x (q := fun _ => False) (fun j => by simp), restrictP_false]
      exact preservesColimit_of_natIso D (Functor.constComp _ x F).symm
  | insert i₀ s hi₀ ih =>
      intro x
      rw [restrictP_congr x (q := fun j => j = i₀ ∨ j ∈ s) (fun j => by simp),
        ← diag_comp_mix x i₀ (fun j => j ∈ s), Functor.assoc]
      apply preservesColimit_diag_of_componentwise
      · intro y
        rw [← Functor.assoc, sectL_comp_mix x y i₀ (fun j => j ∈ s)]
        exact hsing i₀ ((restrictP x (fun j => j ∈ s)).obj y)
      · intro z
        rw [← Functor.assoc, sectR_comp_mix x z i₀ (fun j => j ∈ s) hi₀]
        exact ih ((restrictP x (· = i₀)).obj z)

/-- Finite-product preservation under hypotheses on the component diagrams only. -/
theorem preservesColimit_pi_of_componentwise [Finite ι]
    (h : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimit (D ⋙ Pi.eval C i) (updateFunctor x i ⋙ F)) :
    PreservesColimit D F := by
  have := Fintype.ofFinite ι
  have hsing : ∀ (i : ι) (x : ∀ j, C j),
      PreservesColimit D (restrictP x (· = i) ⋙ F) := by
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
  classical
  let x₀ : ∀ j, C j := D.obj (Classical.arbitrary J)
  have key := restrictP_finset_preservesColimit F D hsing Finset.univ x₀
  rw [restrictP_congr x₀ (q := fun _ => True) (fun j => by simp), restrictP_true,
    Functor.id_comp] at key
  exact key

end Finite

end UlmerBialgebras
