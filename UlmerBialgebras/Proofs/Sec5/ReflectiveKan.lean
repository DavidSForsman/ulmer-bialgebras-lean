module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import UlmerBialgebras.Monadicity.RelAdjoint

/-!
# Left Kan extensions into a reflective subcategory, and relative adjoints along an adjunction

## Main results

* `UlmerBialgebras.hasLeftKanExtension_of_reflective`: if `ι : A ⥤ B` is fully faithful with a left
  adjoint and `d ⋙ ι` has a left Kan extension along `k`, then so does `d`.
* `UlmerBialgebras.RelLeftAdjoint.precompAdj`: an `F`-relative left adjoint of `G` gives a
  `V ⋙ F`-relative left adjoint of `V ⋙ G` whenever `V` is a right adjoint.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.7
-/

@[expose] public section

universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃

namespace UlmerBialgebras

open CategoryTheory Limits Functor

section Reflective

variable {A : Type u₀} [Category.{v₀} A] {B : Type u₁} [Category.{v₁} B]
  {I : Type u₂} [Category.{v₂} I] {K : Type u₃} [Category.{v₃} K]
  (ι : A ⥤ B) [ι.Full] [ι.Faithful]

omit [ι.Full] [ι.Faithful] in
/-- For a family `φ : E ⟶ G ⋙ ι`, the transposed components `R (φ x) ≫ ε (G x)` are natural in
`x`. -/
private lemma reflective_transpose_naturality {R : B ⥤ A} (adj : R ⊣ ι) {E : K ⥤ B} {G : K ⥤ A}
    (φ : E ⟶ G ⋙ ι) {x y : K} (f : x ⟶ y) :
    R.map (E.map f) ≫ R.map (φ.app y) ≫ adj.counit.app (G.obj y) =
      (R.map (φ.app x) ≫ adj.counit.app (G.obj x)) ≫ G.map f := by
  have := φ.naturality f
  dsimp at this
  rw [Category.assoc, ← adj.counit_naturality (G.map f), ← R.map_comp_assoc, this,
    R.map_comp_assoc]

omit [ι.Full] [ι.Faithful] in
/-- For a family `ψ : E ⋙ R ⟶ G`, the transposed components `η (E x) ≫ ι (ψ x)` are natural in
`x`. -/
private lemma reflective_untranspose_naturality {R : B ⥤ A} (adj : R ⊣ ι) {E : K ⥤ B}
    {G : K ⥤ A} (ψ : E ⋙ R ⟶ G) {x y : K} (f : x ⟶ y) :
    E.map f ≫ adj.unit.app (E.obj y) ≫ ι.map (ψ.app y) =
      (adj.unit.app (E.obj x) ≫ ι.map (ψ.app x)) ≫ ι.map (G.map f) := by
  have := ψ.naturality f
  dsimp at this
  rw [Category.assoc, ← ι.map_comp, ← this, ι.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (adj.unit_naturality (E.map f)).symm

/-- For `α : d ⋙ ι ⟶ k ⋙ E`, the components `ε⁻¹ (d i) ≫ R (α i)` are natural in `i`. -/
private lemma reflective_unit_naturality {R : B ⥤ A} (adj : R ⊣ ι) (d : I ⥤ A) (k : I ⥤ K)
    {E : K ⥤ B} (α : d ⋙ ι ⟶ k ⋙ E) {i j : I} (f : i ⟶ j) :
    d.map f ≫ inv (adj.counit.app (d.obj j)) ≫ R.map (α.app j) =
      (inv (adj.counit.app (d.obj i)) ≫ R.map (α.app i)) ≫ R.map (E.map (k.map f)) := by
  have h1 := α.naturality f
  dsimp at h1
  rw [Category.assoc, ← R.map_comp, ← h1, R.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← adj.counit_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- If `ι : A ⥤ B` is fully faithful with left adjoint `R` and `d ⋙ ι` has a left Kan extension `E`
along `k`, then `d` has one along `k`, namely `E ⋙ R` (used for Theorem 5.7 of
[forsman2026syntactic]). -/
theorem hasLeftKanExtension_of_reflective {R : B ⥤ A} (adj : R ⊣ ι) (d : I ⥤ A) (k : I ⥤ K)
    [k.HasLeftKanExtension (d ⋙ ι)] : k.HasLeftKanExtension d := by
  let E := k.leftKanExtension (d ⋙ ι)
  let α := k.leftKanExtensionUnit (d ⋙ ι)
  let ε := adj.counit
  let α' : d ⟶ k ⋙ (E ⋙ R) :=
    { app := fun i => inv (ε.app (d.obj i)) ≫ R.map (α.app i)
      naturality := fun _ _ f => reflective_unit_naturality ι adj d k α f }
  have : (E ⋙ R).IsLeftKanExtension α' := by
    refine ⟨⟨IsInitial.ofUniqueHom (fun T => StructuredArrow.homMk
      { app := fun x => R.map ((E.descOfIsLeftKanExtension α (T.right ⋙ ι)
            (Functor.whiskerRight T.hom ι)).app x) ≫ ε.app (T.right.obj x)
        naturality := fun _ _ f => reflective_transpose_naturality ι adj
          (E.descOfIsLeftKanExtension α (T.right ⋙ ι) (Functor.whiskerRight T.hom ι)) f }
        ?_) ?_⟩⟩
    · ext i
      have h := E.descOfIsLeftKanExtension_fac_app α (T.right ⋙ ι)
        (Functor.whiskerRight T.hom ι) i
      dsimp [α'] at h ⊢
      rw [Category.assoc, ← Category.assoc (R.map _), ← R.map_comp, h]
      rw [adj.counit_naturality, IsIso.inv_hom_id_assoc]
    · intro T m
      apply StructuredArrow.ext
      let γ'' : E ⟶ T.right ⋙ ι :=
        { app := fun x => adj.unit.app (E.obj x) ≫ ι.map (m.right.app x)
          naturality := fun _ _ f => reflective_untranspose_naturality ι adj m.right f }
      have hγ : γ'' = E.descOfIsLeftKanExtension α (T.right ⋙ ι)
          (Functor.whiskerRight T.hom ι) := by
        apply E.hom_ext_of_isLeftKanExtension α
        rw [E.descOfIsLeftKanExtension_fac]
        ext i
        have hm := congr_app (StructuredArrow.w m) i
        dsimp [α'] at hm ⊢
        rw [← hm, ι.map_comp, ι.map_comp, ← Category.assoc]
        congr 1
        rw [show α.app i ≫ adj.unit.app (E.obj (k.obj i)) = _ from
          (adj.unit_naturality (α.app i)).symm]
        congr 1
        rw [← cancel_mono (ι.map (ε.app (d.obj i))), ← ι.map_comp, IsIso.inv_hom_id, ι.map_id]
        exact adj.right_triangle_components (d.obj i)
      ext x
      dsimp
      rw [← hγ]
      dsimp [γ'']
      rw [R.map_comp, Category.assoc, adj.counit_naturality, ← Category.assoc,
        adj.left_triangle_components, Category.id_comp]
  exact HasLeftKanExtension.mk (E ⋙ R) α'

end Reflective

namespace RelLeftAdjoint

variable {A : Type u₀} [Category.{v₀} A] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} {L : C ⥤ C}

/-- A relative left adjoint transported along a right adjoint `V : A ⥤ C`. -/
@[simps]
def precompAdj (r : RelLeftAdjoint F G L) {V : A ⥤ C} {Fr : C ⥤ A} (adj : Fr ⊣ V) :
    RelLeftAdjoint (V ⋙ F) (V ⋙ G) (V ⋙ L ⋙ Fr) where
  homEquiv x y := (adj.homEquiv _ _).trans (r.homEquiv (V.obj x) (V.obj y))
  homEquiv_naturality_left f g := by
    simp only [Equiv.trans_apply, Functor.comp_map, Functor.comp_obj]
    rw [adj.homEquiv_naturality_left, r.homEquiv_naturality_left]
  homEquiv_naturality_right g h := by
    simp only [Equiv.trans_apply, Functor.comp_map, Functor.comp_obj]
    rw [adj.homEquiv_naturality_right, r.homEquiv_naturality_right]

end RelLeftAdjoint

end UlmerBialgebras
