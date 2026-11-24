module

public import UlmerBialgebras.Basic.AccDirClosed
public import UlmerBialgebras.Basic.AccPIE

/-!
# The Makkai–Paré generation theorem for equifiers

Let `F, G : C ⥤ D` be `λ`-accessible functors between accessible categories, with `C`
`λ`-accessible, and assume that `F` takes `λ`-presentable objects to `λ`-presentable
objects.  Let `λ ⊲ κ` (Mathlib's `Cardinal.SharplyLT`).  Then every object of
the equifier `Equif η θ` of two natural transformations `η, θ : F ⟶ G` is a `κ`-filtered
colimit of `κ`-presentable objects of the equifier
(`UlmerBialgebras.Equif.exists_colimitsOfShape_general`), so that the equifier is a `κ`-accessible
category (`UlmerBialgebras.Equif.isCardinalAccessibleCategory_general`).

The proof: write the underlying object as a `λ`-directed colimit `X = colim_α D` of
`λ`-presentable objects.  Since `F (D j)` is `λ`-presentable and `G` preserves the colimit,
the two composites `η_{D j}, θ_{D j} : F (D j) ⟶ G X` become equal at some later stage
`w j ≥ j`; this is the *witness*.  For a `κ`-small `λ`-directed subset `S ⊆ α` closed under
the witnesses (`AccDirClosed.lean`), `η` and `θ` already agree on `colim_S D`, which is a
`κ`-presentable object of the equifier; and `X` is the colimit of these partial colimits
over the `κ`-directed family of such subsets (`AccCover.lean`).

## Main results

* `UlmerBialgebras.Equif.exists_colimitsOfShape_general`: under the hypotheses above, every object
  of the equifier is a `κ`-filtered colimit of `κ`-presentable objects of the equifier.
* `UlmerBialgebras.Equif.isCardinalAccessibleCategory_general`: under the same hypotheses, the
  equifier is a `κ`-accessible category.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3 (2)
* [M. Makkai, R. Paré, *Accessible Categories: The Foundations of Categorical Model
  Theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], 2.72 Theorem,
  2.76 Lemma
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

namespace Equif

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc] {F G : C ⥤ Dc}
  {η θ : F ⟶ G} {lam kappa : Cardinal.{w}} [Fact lam.IsRegular]

section

/-- **The witness.**  If `η` and `θ` agree on the colimit of a `λ`-directed diagram of
`λ`-presentable objects, then for every index `j` they agree on `D j` after moving to a
later stage. -/
lemma exists_witness [G.IsCardinalAccessible lam] {α : Type w} [Preorder α]
    [IsCardinalFiltered α lam] {D : α ⥤ C}
    (hpres : ∀ j, IsCardinalPresentable (D.obj j) lam)
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    {c : Cocone D} (hc : IsColimit c) (hx : η.app c.pt = θ.app c.pt) (j : α) :
    ∃ (k : α) (h : j ≤ k), η.app (D.obj j) ≫ G.map (D.map (homOfLE h)) =
      θ.app (D.obj j) ≫ G.map (D.map (homOfLE h)) := by
  have : PreservesColimitsOfShape α G := G.preservesColimitsOfShape_of_isCardinalAccessible lam α
  have hcG : IsColimit (G.mapCocone c) := isColimitOfPreserves G hc
  have : IsCardinalPresentable (F.obj (D.obj j)) lam := hF _ (hpres j)
  obtain ⟨k, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' (κ := lam) hcG
    (η.app (D.obj j)) (θ.app (D.obj j)) (by
      have h1 := η.naturality (c.ι.app j)
      have h2 := θ.naturality (c.ι.app j)
      dsimp at h1 h2 ⊢
      rw [← h1, ← h2, hx])
  refine ⟨k, leOfHom u, ?_⟩
  rwa [Subsingleton.elim (homOfLE (leOfHom u)) u]

/-- Helper for `exists_colimitsOfShape_general`: the colimit of a witness-closed subset `S`
lies in the equifier `Equif η θ`. -/
private lemma equif_subDiagram_colimit_eq [F.IsCardinalAccessible lam]
    {α : Type w} [PartialOrder α] {D : α ⥤ C} {wj : α → α}
    (hwj : ∀ j, j ≤ wj j)
    (hwspec : ∀ j, η.app (D.obj j) ≫ G.map (D.map (homOfLE (hwj j))) =
      θ.app (D.obj j) ≫ G.map (D.map (homOfLE (hwj j))))
    {wit : α → α → Set α} (hwit : ∀ j, wj j ∈ wit j j)
    (S : dirSubsetsW lam kappa α wit)
    [HasColimit (subDiagram D S.1)] :
    η.app (colimit (subDiagram D S.1)) = θ.app (colimit (subDiagram D S.1)) := by
  have hFS : PreservesColimitsOfShape {y : α // y ∈ S.1} F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible lam _
  apply (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).hom_ext
  intro j
  have hj' : wj j.1 ∈ S.1 := dirSubsetsW.closed S j.2 j.2 (hwit j.1)
  have hiota : colimit.ι (subDiagram D S.1) j
      = (subDiagram D S.1).map
          (homOfLE (show j ≤ (⟨wj j.1, hj'⟩ : {y : α // y ∈ S.1}) from hwj j.1)) ≫
        colimit.ι (subDiagram D S.1) ⟨wj j.1, hj'⟩ :=
    (colimit.w (subDiagram D S.1)
      (homOfLE (show j ≤ (⟨wj j.1, hj'⟩ : {y : α // y ∈ S.1}) from hwj j.1))).symm
  have h1 := η.naturality (colimit.ι (subDiagram D S.1) j)
  have h2 := θ.naturality (colimit.ι (subDiagram D S.1) j)
  dsimp [subDiagram] at h1 h2 ⊢
  rw [h1, h2, hiota]
  simp only [Functor.map_comp, ← Category.assoc]
  -- (`subDiagram D S.1` is `D` on the subset, so this is the witness `hwspec`, whiskered)
  exact hwspec j.1 =≫ _

variable [Fact kappa.IsRegular] [IsCardinalAccessibleCategory.{w} C lam]
  [F.IsCardinalAccessible lam] [G.IsCardinalAccessible lam]

/-- **The generation step for equifiers.**  Every object of the equifier is a `κ`-filtered
colimit of `κ`-presentable objects of the equifier. -/
theorem exists_colimitsOfShape_general
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) (x : Equif η θ) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J kappa),
      (gen η θ kappa).colimitsOfShape J x := by
  classical
  obtain ⟨X, hX⟩ := x
  -- Present `X` as a `λ`-directed colimit of `λ`-presentable objects `D j`.
  obtain ⟨α, hord, hfa, D, c, hc, hcpt, hpres⟩ := exists_directed_presentation lam X
  subst hcpt
  -- For each `j`, a later stage `wj j` where `η` and `θ` agree on `D j` (`exists_witness`).
  choose wj hwj hwspec using exists_witness hpres hF hc hX
  set wit : α → α → Set α := fun j _ => {wj j} with hwit
  have hwitlt : ∀ j k, HasCardinalLT (wit j k) kappa := fun j k =>
    hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)
  have : ∀ S : dirSubsetsW lam kappa α wit, HasColimit (subDiagram D S.1) := fun S =>
    HasCardinalFilteredColimits.hasColimitsOfShape C (κ := lam) {y : α // y ∈ S.1} |>.has_colimit _
  -- On a `κ`-small directed subset closed under the witnesses, the colimit of `D` lies in
  -- the equifier.
  have hkey : ∀ S : dirSubsetsW lam kappa α wit,
      η.app (colimit (subDiagram D S.1)) = θ.app (colimit (subDiagram D S.1)) := fun S =>
    equif_subDiagram_colimit_eq (F := F) (G := G) (η := η) (θ := θ) (D := D) (wit := wit)
      hwj hwspec (fun j => hwit.symm ▸ Set.mem_singleton (wj j)) S
  -- These subsets form a `κ`-filtered cover of `α`, so `X` is the colimit of their colimits ...
  set 𝒮 := dirSubsetsW lam kappa α wit with h𝒮
  have hcover := dirSubsetsW_cover (wit := wit) hsharp hwitlt
  have hdir : ∀ S T : 𝒮, ∃ R : 𝒮, S.1 ⊆ R.1 ∧ T.1 ⊆ R.1 :=
    dirSubsetsW_directed (wit := wit) hsharp hwitlt
  let dia : 𝒮 ⥤ Equif η θ := Equif.liftFunctor (coverFunctor D 𝒮) (by ext S; exact hkey S)
  let coc : Cocone dia :=
    { pt := ⟨c.pt, hX⟩
      ι :=
        { app := fun S => ObjectProperty.homMk ((coverCocone D 𝒮 c).ι.app S)
          naturality := fun S T f => by
            apply (equifProp η θ).ι.map_injective
            exact ((coverCocone D 𝒮 c).w f).trans (Category.comp_id _).symm } }
  have hdia : dia ⋙ Equif.forget η θ = coverFunctor D 𝒮 := rfl
  have hcoc : IsColimit coc := by
    refine isColimitOfReflects (Equif.forget η θ) ?_
    exact IsColimit.ofIsoColimit (isColimitCoverCocone c hc hcover hdir)
      (Cocone.ext (Iso.refl _) (fun S => Category.comp_id _))
  -- ... each of which is `κ`-presentable, as a `κ`-small colimit of `λ`-presentable objects.
  have hgenS : ∀ S : 𝒮, gen η θ kappa (dia.obj S) := by
    intro S
    have p : (CategoryTheory.isCardinalPresentable C lam).ColimitOfShape
        {y : α // y ∈ S.1} (colimit (subDiagram D S.1)) :=
      ObjectProperty.ColimitOfShape.mk (P := CategoryTheory.isCardinalPresentable C lam)
        ⟨subDiagram D S.1, (colimit.cocone (subDiagram D S.1)).ι, colimit.isColimit _⟩
        (fun j => hpres j.1)
    exact p.isCardinalPresentable (le_refl _) kappa hsharp.le (hasCardinalLT_arrow_dirSubsetW S)
  exact ⟨𝒮, inferInstance, isCardinalFiltered_dirSubsetsW hsharp hwitlt,
    ⟨ObjectProperty.ColimitOfShape.mk ⟨dia, coc.ι, hcoc⟩ hgenS⟩⟩

/-- **Equifiers of accessible functors are accessible.** -/
theorem isCardinalAccessibleCategory_general
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) :
    IsCardinalAccessibleCategory.{w} (Equif η θ) kappa := by
  have : IsCardinalAccessibleCategory.{w} C kappa := hsharp.isCardinalAccessibleCategory C
  have : F.IsCardinalAccessible kappa := Functor.isCardinalAccessible_of_le F hsharp.le
  exact Equif.isCardinalAccessibleCategory kappa
    (exists_colimitsOfShape_general hF hsharp)

end

end Equif

end UlmerBialgebras
