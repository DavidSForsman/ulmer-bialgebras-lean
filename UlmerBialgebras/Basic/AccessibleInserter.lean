module

public import UlmerBialgebras.Basic.AccDirClosed
public import UlmerBialgebras.Basic.AccPIE

/-!
# The Makkai–Paré generation theorem for inserters

Let `F, G : C ⥤ D` be `λ`-accessible functors, with `C` a `λ`-accessible category, and
assume that `F` takes `λ`-presentable objects to `λ`-presentable objects.  Let `λ ⊲ κ`
(Mathlib's `Cardinal.SharplyLT`).  Then every object of the inserter
`Ins F G` is a `κ`-filtered colimit of `κ`-presentable objects of the inserter
(`UlmerBialgebras.Ins.exists_colimitsOfShape_general`), so that the inserter is a `κ`-accessible
category (`UlmerBialgebras.Ins.isCardinalAccessibleCategory_general`).

The proof.  Write the underlying object as a `λ`-directed colimit `X = colim_α D` of
`λ`-presentable objects and let `ψ : F X ⟶ G X` be the structure cell.  Since `F (D j)` is
`λ`-presentable and `G` preserves the colimit, the composite `F (D j) ⟶ F X ⟶ G X` factors
as `χ j : F (D j) ⟶ G (D (s j))` at some stage `s j` (the *unary witness*), and for `j ≤ k`
the two resulting cells agree at some later stage `q j k` (the *binary witness*).  On a
`κ`-small `λ`-directed subset `S ⊆ α` closed under both witnesses (`AccDirClosed.lean`) the
cells `χ j` therefore assemble into a cell `F (colim_S D) ⟶ G (colim_S D)`, making
`colim_S D` an object of the inserter which is `κ`-presentable there; and `X` is the colimit
of these partial colimits over the `κ`-directed family of such subsets (`AccCover.lean`).

## Main results

* `UlmerBialgebras.Ins.exists_colimitsOfShape_general`: under the hypotheses above, every object of
  the inserter is a `κ`-filtered colimit of `κ`-presentable objects of the inserter.
* `UlmerBialgebras.Ins.isCardinalAccessibleCategory_general`: under the same hypotheses, the
  inserter is a `κ`-accessible category.

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

namespace Ins

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc] {F G : C ⥤ Dc}
  {lam kappa : Cardinal.{w}} [Fact lam.IsRegular]

section

/-- **The unary witness.**  The composite `F (D j) ⟶ F X ⟶ G X` of the structure cell with
a colimit inclusion factors through some stage of the diagram. -/
lemma exists_cellStage [G.IsCardinalAccessible lam] {α : Type w} [Preorder α]
    [IsCardinalFiltered α lam] {D : α ⥤ C}
    (hpres : ∀ j, IsCardinalPresentable (D.obj j) lam)
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    {c : Cocone D} (hc : IsColimit c) (psi : F.obj c.pt ⟶ G.obj c.pt) (j : α) :
    ∃ (k : α) (chi : F.obj (D.obj j) ⟶ G.obj (D.obj k)),
      chi ≫ G.map (c.ι.app k) = F.map (c.ι.app j) ≫ psi := by
  have : PreservesColimitsOfShape α G := G.preservesColimitsOfShape_of_isCardinalAccessible lam α
  have hcG : IsColimit (G.mapCocone c) := isColimitOfPreserves G hc
  have : IsCardinalPresentable (F.obj (D.obj j)) lam := hF _ (hpres j)
  obtain ⟨k, chi, hchi⟩ := IsCardinalPresentable.exists_hom_of_isColimit (κ := lam) hcG
    (F.map (c.ι.app j) ≫ psi)
  exact ⟨k, chi, hchi⟩

/-- **The binary witness.**  For `j ≤ k`, the cell `χ k` precomposed with `F (D (j ≤ k))`
and the cell `χ j` agree at some later stage. -/
lemma exists_pairStage [G.IsCardinalAccessible lam] {α : Type w} [Preorder α]
    [IsCardinalFiltered α lam] {D : α ⥤ C}
    (hpres : ∀ j, IsCardinalPresentable (D.obj j) lam)
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    {c : Cocone D} (hc : IsColimit c) (psi : F.obj c.pt ⟶ G.obj c.pt)
    (st : α → α) (chi : ∀ j, F.obj (D.obj j) ⟶ G.obj (D.obj (st j)))
    (hchi : ∀ j, chi j ≫ G.map (c.ι.app (st j)) = F.map (c.ι.app j) ≫ psi) (j k : α) :
    ∃ q : α, ∀ h : j ≤ k, ∃ (h1 : st j ≤ q) (h2 : st k ≤ q),
      F.map (D.map (homOfLE h)) ≫ chi k ≫ G.map (D.map (homOfLE h2))
        = chi j ≫ G.map (D.map (homOfLE h1)) := by
  have hfil : IsFiltered α := isFiltered_of_isCardinalFiltered α lam
  by_cases h : j ≤ k
  · have : PreservesColimitsOfShape α G := G.preservesColimitsOfShape_of_isCardinalAccessible lam α
    have hcG : IsColimit (G.mapCocone c) := isColimitOfPreserves G hc
    have : IsCardinalPresentable (F.obj (D.obj j)) lam := hF _ (hpres j)
    obtain ⟨q, u, v, huv⟩ := IsCardinalPresentable.exists_eq_of_isColimit (κ := lam) hcG
      (F.map (D.map (homOfLE h)) ≫ chi k) (chi j) (by
        dsimp
        rw [Category.assoc, hchi k, ← Category.assoc, ← F.map_comp, c.w, hchi j])
    refine ⟨q, fun _ => ⟨leOfHom v, leOfHom u, ?_⟩⟩
    rw [Subsingleton.elim (homOfLE (leOfHom u)) u, Subsingleton.elim (homOfLE (leOfHom v)) v,
      Subsingleton.elim (homOfLE _) (homOfLE h)]
    rw [Category.assoc] at huv
    exact huv
  · exact ⟨(IsFiltered.nonempty (C := α)).some, fun h' => absurd h' h⟩

/-- Naturality of the cocone `cocCell` on a `κ`-small `λ`-directed subset `S`. -/
private lemma cocCell_naturality {α : Type w} [PartialOrder α] {D : α ⥤ C}
    (st : α → α) (chi : ∀ j, F.obj (D.obj j) ⟶ G.obj (D.obj (st j)))
    (q : α → α → α)
    (hq : ∀ j k (h : j ≤ k), ∃ (h1 : st j ≤ q j k) (h2 : st k ≤ q j k),
      F.map (D.map (homOfLE h)) ≫ chi k ≫ G.map (D.map (homOfLE h2))
        = chi j ≫ G.map (D.map (homOfLE h1)))
    {wit : α → α → Set α} (S : dirSubsetsW lam kappa α wit)
    (hstS : ∀ {j : α}, j ∈ S.1 → st j ∈ S.1)
    (hqS : ∀ {j k : α}, j ∈ S.1 → k ∈ S.1 → q j k ∈ S.1)
    [HasColimit (subDiagram D S.1)]
    {j k : {y : α // y ∈ S.1}} (f : j ⟶ k) :
    (subDiagram D S.1 ⋙ F).map f ≫
        (chi k.1 ≫ G.map (colimit.ι (subDiagram D S.1) ⟨st k.1, hstS k.2⟩)) =
      (chi j.1 ≫ G.map (colimit.ι (subDiagram D S.1) ⟨st j.1, hstS j.2⟩)) ≫ 𝟙 _ := by
  obtain ⟨h1, h2, heq⟩ := hq j.1 k.1 (leOfHom f)
  have hqmem : q j.1 k.1 ∈ S.1 := hqS j.2 k.2
  -- The inclusions at the stages `st j`, `st k` factor through the one at `q j k`.
  have hw : ∀ {a : α} (ha : a ∈ S.1) (h : a ≤ q j.1 k.1),
      G.map (colimit.ι (subDiagram D S.1) ⟨a, ha⟩) =
        G.map (D.map (homOfLE h)) ≫ G.map (colimit.ι (subDiagram D S.1) ⟨_, hqmem⟩) := by
    intro a ha h
    rw [← G.map_comp, ← colimit.w (subDiagram D S.1)
      (homOfLE (show (⟨a, ha⟩ : {y : α // y ∈ S.1}) ≤ ⟨_, hqmem⟩ from h))]
    rfl
  rw [Category.comp_id, hw (hstS j.2) h1, hw (hstS k.2) h2]
  exact (reassoc_of% heq) _

/-- The cocone on `subDiagram D S.1 ⋙ F` defining the structure cell on a partial colimit. -/
private noncomputable def cocCell {α : Type w} [PartialOrder α] {D : α ⥤ C}
    (st : α → α) (chi : ∀ j, F.obj (D.obj j) ⟶ G.obj (D.obj (st j)))
    (q : α → α → α)
    (hq : ∀ j k (h : j ≤ k), ∃ (h1 : st j ≤ q j k) (h2 : st k ≤ q j k),
      F.map (D.map (homOfLE h)) ≫ chi k ≫ G.map (D.map (homOfLE h2))
        = chi j ≫ G.map (D.map (homOfLE h1)))
    {wit : α → α → Set α} (S : dirSubsetsW lam kappa α wit)
    (hstS : ∀ {j : α}, j ∈ S.1 → st j ∈ S.1)
    (hqS : ∀ {j k : α}, j ∈ S.1 → k ∈ S.1 → q j k ∈ S.1)
    [HasColimit (subDiagram D S.1)] : Cocone (subDiagram D S.1 ⋙ F) where
  pt := G.obj (colimit (subDiagram D S.1))
  ι :=
    { app := fun j => chi j.1 ≫ G.map (colimit.ι (subDiagram D S.1) ⟨st j.1, hstS j.2⟩)
      naturality := fun _ _ f => cocCell_naturality st chi q hq S hstS hqS f }

/-- Naturality of the partial structure cells across inclusions `S ≤ T` of `κ`-small
`λ`-directed subsets. -/
private lemma partialCell_naturality {α : Type w} [PartialOrder α] [IsCardinalFiltered α lam]
    {D : α ⥤ C} (st : α → α) (chi : ∀ j, F.obj (D.obj j) ⟶ G.obj (D.obj (st j)))
    (q : α → α → α)
    (hq : ∀ j k (h : j ≤ k), ∃ (h1 : st j ≤ q j k) (h2 : st k ≤ q j k),
      F.map (D.map (homOfLE h)) ≫ chi k ≫ G.map (D.map (homOfLE h2))
        = chi j ≫ G.map (D.map (homOfLE h1)))
    {wit : α → α → Set α}
    (hstS : ∀ (S : dirSubsetsW lam kappa α wit) {j : α}, j ∈ S.1 → st j ∈ S.1)
    (hqS : ∀ (S : dirSubsetsW lam kappa α wit) {j k : α}, j ∈ S.1 → k ∈ S.1 → q j k ∈ S.1)
    [∀ S : dirSubsetsW lam kappa α wit, HasColimit (subDiagram D S.1)]
    (hFS : ∀ S : dirSubsetsW lam kappa α wit, PreservesColimitsOfShape {y : α // y ∈ S.1} F)
    {S T : dirSubsetsW lam kappa α wit} (f : S ⟶ T) :
    let cell := fun U =>
      (isColimitOfPreserves F (colimit.isColimit (subDiagram D U.1))).desc
        (cocCell st chi q hq U (hstS U) (hqS U))
    F.map ((coverFunctor D (dirSubsetsW lam kappa α wit)).map f) ≫ cell T =
      cell S ≫ G.map ((coverFunctor D (dirSubsetsW lam kappa α wit)).map f) := by
  intro cell
  have hcell : ∀ (U : dirSubsetsW lam kappa α wit) (j : {y : α // y ∈ U.1}),
      F.map (colimit.ι (subDiagram D U.1) j) ≫ cell U =
        chi j.1 ≫ G.map (colimit.ι (subDiagram D U.1) ⟨st j.1, hstS U j.2⟩) :=
    fun U j =>
      (isColimitOfPreserves F (colimit.isColimit (subDiagram D U.1))).fac
        (cocCell st chi q hq U (hstS U) (hqS U)) j
  have : PreservesColimitsOfShape {y : α // y ∈ S.1} F := hFS S
  refine (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).hom_ext ?_
  intro j
  have hjT : j.1 ∈ T.1 := (leOfHom f) j.2
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
  -- Both sides restrict to `chi j ≫ G.map (colimit.ι _ ⟨st j, _⟩)` at `T`. The objects of
  -- `coverFunctor` are colimits only up to unfolding, so the steps are composed as terms.
  have hF : F.map (colimit.ι (subDiagram D S.1) j) ≫
      F.map ((coverFunctor D (dirSubsetsW lam kappa α wit)).map f) =
      F.map (colimit.ι (subDiagram D T.1) ⟨j.1, hjT⟩) :=
    (F.map_comp _ _).symm.trans congr(F.map $(ι_coverFunctor_map D _ f j))
  have hG : G.map (colimit.ι (subDiagram D S.1) ⟨st j.1, hstS S j.2⟩) ≫
      G.map ((coverFunctor D (dirSubsetsW lam kappa α wit)).map f) =
      G.map (colimit.ι (subDiagram D T.1) ⟨st j.1, (leOfHom f) (hstS S j.2)⟩) :=
    (G.map_comp _ _).symm.trans congr(G.map $(ι_coverFunctor_map D _ f ⟨st j.1, hstS S j.2⟩))
  exact ((Category.assoc _ _ _).symm.trans ((hF =≫ cell T).trans (hcell T ⟨j.1, hjT⟩))).trans
    ((Category.assoc _ _ _).symm.trans ((hcell S j =≫ _).trans
      ((Category.assoc _ _ _).trans (chi j.1 ≫= hG)))).symm

/-- Compatibility of the partial structure cell at `S` with the cover cocone inclusion into `c`. -/
private lemma partialCell_compat {α : Type w} [PartialOrder α] [IsCardinalFiltered α lam]
    {D : α ⥤ C} {c : Cocone D} (psi : F.obj c.pt ⟶ G.obj c.pt)
    (st : α → α) (chi : ∀ j, F.obj (D.obj j) ⟶ G.obj (D.obj (st j)))
    (hchi : ∀ j, chi j ≫ G.map (c.ι.app (st j)) = F.map (c.ι.app j) ≫ psi)
    (q : α → α → α)
    (hq : ∀ j k (h : j ≤ k), ∃ (h1 : st j ≤ q j k) (h2 : st k ≤ q j k),
      F.map (D.map (homOfLE h)) ≫ chi k ≫ G.map (D.map (homOfLE h2))
        = chi j ≫ G.map (D.map (homOfLE h1)))
    {wit : α → α → Set α} (S : dirSubsetsW lam kappa α wit)
    (hstS : ∀ {j : α}, j ∈ S.1 → st j ∈ S.1)
    (hqS : ∀ {j k : α}, j ∈ S.1 → k ∈ S.1 → q j k ∈ S.1)
    [∀ U : dirSubsetsW lam kappa α wit, HasColimit (subDiagram D U.1)]
    (hFS : PreservesColimitsOfShape {y : α // y ∈ S.1} F) :
    (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).desc
        (cocCell st chi q hq S hstS hqS) ≫
      G.map ((coverCocone D (dirSubsetsW lam kappa α wit) c).ι.app S) =
      F.map ((coverCocone D (dirSubsetsW lam kappa α wit) c).ι.app S) ≫ psi := by
  let cellS := (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).desc
    (cocCell st chi q hq S hstS hqS)
  have hcell : ∀ j : {y : α // y ∈ S.1},
      F.map (colimit.ι (subDiagram D S.1) j) ≫ cellS =
        chi j.1 ≫ G.map (colimit.ι (subDiagram D S.1) ⟨st j.1, hstS j.2⟩) :=
    fun j =>
      (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).fac
        (cocCell st chi q hq S hstS hqS) j
  refine (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).hom_ext ?_
  intro j
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι]
  -- Both sides restrict to `F.map (c.ι.app j) ≫ psi`, through the witness `chi j`.
  have hG : G.map (colimit.ι (subDiagram D S.1) ⟨st j.1, hstS j.2⟩) ≫
      G.map ((coverCocone D (dirSubsetsW lam kappa α wit) c).ι.app S) =
      G.map (c.ι.app (st j.1)) :=
    (G.map_comp _ _).symm.trans
      congr(G.map $(ι_coverCocone_app D (dirSubsetsW lam kappa α wit) c S ⟨st j.1, hstS j.2⟩))
  have hF : F.map (colimit.ι (subDiagram D S.1) j) ≫
      F.map ((coverCocone D (dirSubsetsW lam kappa α wit) c).ι.app S) =
      F.map (c.ι.app j.1) :=
    (F.map_comp _ _).symm.trans
      congr(F.map $(ι_coverCocone_app D (dirSubsetsW lam kappa α wit) c S j))
  exact ((Category.assoc _ _ _).symm.trans ((hcell j =≫ _).trans
      ((Category.assoc _ _ _).trans ((chi j.1 ≫= hG).trans (hchi j.1))))).trans
    ((Category.assoc _ _ _).symm.trans (hF =≫ psi)).symm

/-- Lifting an isomorphism of underlying colimit cocones to show `⟨cU.pt, psi⟩` is a colimit
of `Ins.liftFunctor (coverFunctor D 𝒮) cellNat` in `Ins F G`. -/
private noncomputable def isColimitPartialInsCocone {α : Type w} [PartialOrder α] {D : α ⥤ C}
    {wit : α → α → Set α}
    [∀ S : dirSubsetsW lam kappa α wit, HasColimit (subDiagram D S.1)]
    (cellNat : coverFunctor D (dirSubsetsW lam kappa α wit) ⋙ F ⟶
      coverFunctor D (dirSubsetsW lam kappa α wit) ⋙ G)
    (cU : Cocone (coverFunctor D (dirSubsetsW lam kappa α wit)))
    (hcU : IsColimit cU) (psi : F.obj cU.pt ⟶ G.obj cU.pt)
    [PreservesColimitsOfShape (dirSubsetsW lam kappa α wit : Type w) F]
    (hcompat : ∀ S, cellNat.app S ≫ G.map (cU.ι.app S) = F.map (cU.ι.app S) ≫ psi) :
    IsColimit
      ({ pt := ⟨cU.pt, psi⟩
         ι :=
           { app := fun S => ⟨cU.ι.app S, hcompat S⟩
             naturality := fun S T f => by
               ext
               simp } } : Cocone (Ins.liftFunctor (coverFunctor D _) cellNat)) := by
  let K := Ins.liftFunctor (coverFunctor D (dirSubsetsW lam kappa α wit)) cellNat
  let cUK : Cocone (K ⋙ forget F G) := cU
  have hcUK : IsColimit cUK := hcU
  have hcellEq : coconeCell K hcUK = psi := by
    refine (isColimitOfPreserves F hcUK).hom_ext ?_
    intro S
    rw [Functor.mapCocone_ι_app, coconeCell_fac K hcUK S]
    exact hcompat S
  let e : (Ins.cocone K hcUK).pt ≅ (⟨cU.pt, psi⟩ : Ins F G) :=
    { hom := ⟨𝟙 cU.pt, by
        rw [cocone_pt_cell, hcellEq]
        exact Ins.Hom.w (𝟙 (⟨cU.pt, psi⟩ : Ins F G))⟩
      inv := ⟨𝟙 cU.pt, by
        rw [cocone_pt_cell, hcellEq]
        exact Ins.Hom.w (𝟙 (⟨cU.pt, psi⟩ : Ins F G))⟩
      hom_inv_id := by ext; exact Category.comp_id _
      inv_hom_id := by ext; exact Category.comp_id _ }
  exact IsColimit.ofIsoColimit (Ins.isColimitCocone K hcUK)
    (Cocone.ext e (fun S => by ext; exact Category.comp_id _))

variable [Fact kappa.IsRegular] [IsCardinalAccessibleCategory.{w} C lam]
  [F.IsCardinalAccessible lam] [G.IsCardinalAccessible lam]

/-- **The generation step for inserters.**  Every object of the inserter is a `κ`-filtered
colimit of `κ`-presentable objects of the inserter. -/
theorem exists_colimitsOfShape_general [LocallySmall.{w} Dc]
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) (x : Ins F G) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J kappa),
      (gen F G kappa).colimitsOfShape J x := by
  classical
  -- Present the underlying object as a `λ`-directed colimit, and choose the witnesses.
  obtain ⟨X, psi⟩ := x
  obtain ⟨α, hord, hfa, D, c, hc, hcpt, hpres⟩ := exists_directed_presentation lam X
  subst hcpt
  choose st chi hchi using exists_cellStage hpres hF hc psi
  choose q hq using exists_pairStage hpres hF hc psi st chi hchi
  set wit : α → α → Set α := fun j k => {st j, st k, q j k} with hwitdef
  have hwitlt : ∀ j k, HasCardinalLT (wit j k) kappa := fun j k =>
    hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out)
  -- The `κ`-small `λ`-directed subsets closed under the witnesses, and their colimits.
  set 𝒮 := dirSubsetsW lam kappa α wit with h𝒮
  have : ∀ S : 𝒮, HasColimit (subDiagram D S.1) := fun S =>
    HasCardinalFilteredColimits.hasColimitsOfShape C (κ := lam) {y : α // y ∈ S.1} |>.has_colimit _
  have hstS : ∀ (S : 𝒮) {j : α}, j ∈ S.1 → st j ∈ S.1 := fun S {j} hj =>
    dirSubsetsW.closed S hj hj (by simp [hwitdef])
  have hqS : ∀ (S : 𝒮) {j k : α}, j ∈ S.1 → k ∈ S.1 → q j k ∈ S.1 := fun S {j k} hj hk =>
    dirSubsetsW.closed S hj hk (by simp [hwitdef])
  have hFS : ∀ S : 𝒮, PreservesColimitsOfShape {y : α // y ∈ S.1} F := fun S =>
    F.preservesColimitsOfShape_of_isCardinalAccessible lam _
  -- The structure cells on the partial colimits, natural in the subset.
  let cell : ∀ S : 𝒮, F.obj (colimit (subDiagram D S.1)) ⟶ G.obj (colimit (subDiagram D S.1)) :=
    fun S => (isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))).desc
      (cocCell st chi q hq S (hstS S) (hqS S))
  let cellNat : coverFunctor D 𝒮 ⋙ F ⟶ coverFunctor D 𝒮 ⋙ G :=
    { app := fun S => cell S
      naturality := fun _ _ f => partialCell_naturality st chi q hq hstS hqS hFS f }
  let K : 𝒮 ⥤ Ins F G := Ins.liftFunctor (coverFunctor D 𝒮) cellNat
  -- The partial colimits cover `X` along a `κ`-filtered family, compatibly with `psi`.
  let cU := coverCocone D 𝒮 c
  have hcU : IsColimit cU :=
    isColimitCoverCocone c hc (dirSubsetsW_cover hsharp hwitlt) (dirSubsetsW_directed hsharp hwitlt)
  have : IsCardinalFiltered 𝒮 kappa := isCardinalFiltered_dirSubsetsW hsharp hwitlt
  have : IsCardinalFiltered 𝒮 lam := IsCardinalFiltered.of_le 𝒮 (κ := kappa) hsharp.le
  have : PreservesColimitsOfShape (𝒮 : Type w) F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible lam _
  have hcompat : ∀ S : 𝒮, cell S ≫ G.map (cU.ι.app S) = F.map (cU.ι.app S) ≫ psi :=
    fun S => partialCell_compat psi st chi hchi q hq S (hstS S) (hqS S) (hFS S)
  -- Each partial colimit, and its image under `F`, is `κ`-presentable.
  have hgenS : ∀ S : 𝒮, gen F G kappa (K.obj S) := by
    intro S
    constructor
    · have p : (CategoryTheory.isCardinalPresentable C lam).ColimitOfShape
          {y : α // y ∈ S.1} (colimit (subDiagram D S.1)) :=
        ObjectProperty.ColimitOfShape.mk (P := CategoryTheory.isCardinalPresentable C lam)
          ⟨subDiagram D S.1, (colimit.cocone (subDiagram D S.1)).ι, colimit.isColimit _⟩
          (fun j => hpres j.1)
      exact p.isCardinalPresentable (le_refl _) kappa hsharp.le (hasCardinalLT_arrow_dirSubsetW S)
    · have p : (CategoryTheory.isCardinalPresentable Dc lam).ColimitOfShape
          {y : α // y ∈ S.1} (F.obj (colimit (subDiagram D S.1))) :=
        ObjectProperty.ColimitOfShape.mk (P := CategoryTheory.isCardinalPresentable Dc lam)
          ⟨subDiagram D S.1 ⋙ F, (F.mapCocone (colimit.cocone (subDiagram D S.1))).ι,
            isColimitOfPreserves F (colimit.isColimit (subDiagram D S.1))⟩
          (fun j => hF _ (hpres j.1))
      exact p.isCardinalPresentable (le_refl _) kappa hsharp.le (hasCardinalLT_arrow_dirSubsetW S)
  exact ⟨𝒮, inferInstance, inferInstance,
    ⟨ObjectProperty.ColimitOfShape.mk
      ⟨K, _, isColimitPartialInsCocone cellNat cU hcU psi hcompat⟩ hgenS⟩⟩

/-- **Inserters of accessible functors are accessible.** -/
theorem isCardinalAccessibleCategory_general [LocallySmall.{w} Dc]
    (hF : ∀ a : C, IsCardinalPresentable a lam → IsCardinalPresentable (F.obj a) lam)
    (hsharp : lam.SharplyLT kappa) :
    IsCardinalAccessibleCategory.{w} (Ins F G) kappa := by
  have : IsCardinalAccessibleCategory.{w} C kappa := hsharp.isCardinalAccessibleCategory C
  have : F.IsCardinalAccessible kappa := Functor.isCardinalAccessible_of_le F hsharp.le
  have : G.IsCardinalAccessible kappa := Functor.isCardinalAccessible_of_le G hsharp.le
  exact Ins.isCardinalAccessibleCategory kappa
    (exists_colimitsOfShape_general hF hsharp)

end

end Ins

end UlmerBialgebras
