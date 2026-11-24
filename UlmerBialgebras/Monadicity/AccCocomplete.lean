module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas
public import Foundations.CategoryTheory.Presentable.LPComplete

/-!
# A complete accessible category is cocomplete

This file proves one half of the theorem that an accessible category is complete if and only
if it is cocomplete, namely the harder direction:

* `UlmerBialgebras.hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits` — an accessible category
  with small limits has small colimits.

The proof is the classical one.  Given a small diagram `D : J ⥤ C`, the functor
`const J : C ⥤ (J ⥤ C)` preserves limits, so by the general adjoint functor theorem it has a
left adjoint — i.e. `J`-colimits exist — as soon as it satisfies the *solution set
condition*.  That condition is exactly the statement that the cocones under `D` admit a
small weakly initial family, and it follows from accessibility: choosing a regular cardinal
`λ` for which `C` is `λ`-accessible, every `D j` is `λ`-presentable and `Arrow J` has
cardinality `< λ`, any cocone `D ⟹ ΔX` factors through a stage of a presentation of `X` as a
`λ`-filtered colimit of `λ`-presentable objects
(`UlmerBialgebras.exists_cocone_factorization`).

## Main results

* `UlmerBialgebras.exists_cocone_factorization`: a cocone over a diagram of `λ`-presentable objects,
  indexed by `J` with `Arrow J` of cardinality `< λ`, with vertex a `λ`-filtered colimit,
  factors through a stage of that colimit.
* `UlmerBialgebras.hasColimitsOfShape_of_isAccessibleCategory_of_hasLimits`: a complete accessible
  category has colimits of shape `J`.
* `UlmerBialgebras.hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits`: a complete accessible
  category is cocomplete.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Section 5.3
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Corollary 2.47
* [S. Mac Lane, *Categories for the Working Mathematician*][MacLane1998]
-/

@[expose] public section

universe w u

namespace UlmerBialgebras

open CategoryTheory Limits IsCardinalAccessibleCategory

section

variable {C : Type u} [Category.{w} C] {J : Type w} [SmallCategory J]

/-- **Factoring a cocone through a stage of a filtered colimit.**  If `X` is the colimit of a
`λ`-filtered diagram `G`, `D` is a `J`-diagram of `λ`-presentable objects and `Arrow J` has
cardinality `< λ`, then every cocone `D ⟹ ΔX` is the image of a cocone `D ⟹ Δ(G i)` for some
stage `i`. -/
theorem exists_cocone_factorization (lam : Cardinal.{w}) [Fact lam.IsRegular]
    {I : Type w} [SmallCategory I] [IsCardinalFiltered I lam]
    {G : I ⥤ C} {c : Cocone G} (hc : IsColimit c)
    (D : J ⥤ C) [∀ j, IsCardinalPresentable (D.obj j) lam]
    (hJ : HasCardinalLT (Arrow J) lam)
    (psi : D ⟶ (Functor.const J).obj c.pt) :
    ∃ (i : I) (phi : D ⟶ (Functor.const J).obj (G.obj i)),
      ∀ j, phi.app j ≫ c.ι.app i = psi.app j := by
  classical
  have hJobj : HasCardinalLT J lam :=
    hJ.of_injective (fun j => Arrow.mk (𝟙 j)) (fun j j' h => by
      simpa using congr(($(h)).left))
  -- factor each leg through a stage
  have hfac : ∀ j : J, ∃ (i : I) (u : D.obj j ⟶ G.obj i), u ≫ c.ι.app i = psi.app j := by
    intro j
    exact IsCardinalPresentable.exists_hom_of_isColimit lam hc (psi.app j)
  choose i₀ u hu using hfac
  -- move all the stages into a single one
  set i : I := IsCardinalFiltered.max (κ := lam) i₀ hJobj with hi
  set v : ∀ j : J, D.obj j ⟶ G.obj i :=
    fun j => u j ≫ G.map (IsCardinalFiltered.toMax (κ := lam) i₀ hJobj j) with hv
  have hvc : ∀ j : J, v j ≫ c.ι.app i = psi.app j := by
    intro j
    rw [hv]
    simp only [Category.assoc, c.w]
    exact hu j
  -- equalize the naturality squares, one at a time
  have heq : ∀ f : Arrow J, ∃ (k : I) (a : i ⟶ k),
      (D.map f.hom ≫ v f.right) ≫ G.map a = v f.left ≫ G.map a := by
    intro f
    refine IsCardinalPresentable.exists_eq_of_isColimit' lam hc _ _ ?_
    have h1 : D.map f.hom ≫ psi.app f.right = psi.app f.left := by
      simp
    rw [Category.assoc, hvc, hvc, h1]
  choose k a ha using heq
  -- and equalize them all at once
  obtain ⟨m, b, t, hb⟩ := IsCardinalFiltered.wideSpan (κ := lam) a hJ
  refine ⟨m, { app := fun j => v j ≫ G.map t, naturality := ?_ }, ?_⟩
  · intro j j' f
    have h := ha (Arrow.mk f)
    dsimp
    rw [Category.comp_id, ← hb (Arrow.mk f)]
    simp only [G.map_comp, ← Category.assoc]
    exact h =≫ G.map (b (Arrow.mk f))
  · intro j
    dsimp
    rw [Category.assoc, c.w, hvc]

end

section

variable (C : Type u) [Category.{w} C] [IsAccessibleCategory.{w} C]
  (J : Type w) [SmallCategory J]

/-- **The solution set condition for the constant-diagram functor.**  In an accessible
category, the cocones under a fixed small diagram admit a small weakly initial family. -/
theorem solutionSetCondition_const :
    SolutionSetCondition.{w} (Functor.const J : C ⥤ (J ⥤ C)) := by
  classical
  intro D
  -- a regular cardinal that works for `C`, for all the `D j` and for the shape `J`
  obtain ⟨kap, hkapreg, hkapacc⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  have hDpres : ∀ j : J, ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalPresentable (D.obj j) κ := fun j => Functor.IsAccessible.exists_cardinal _
  choose S hSreg hSpres using hDpres
  obtain ⟨kapJ, hkapJ, hJ⟩ := HasCardinalLT.exists_regular_cardinal.{w} (Arrow J)
  have : Fact kapJ.IsRegular := ⟨hkapJ⟩
  obtain ⟨kapS, _, hS⟩ := Cardinal.SharplyLT.exists_of_small S
  obtain ⟨lam, hreg, h₀, h₁, h₂⟩ := Cardinal.SharplyLT.exists_of_triple kap kapS kapJ
  have := hreg
  have : IsCardinalAccessibleCategory.{w} C lam := h₀.isCardinalAccessibleCategory C
  have : ∀ j : J, IsCardinalPresentable (D.obj j) lam := by
    intro j
    have := hSpres j
    exact isCardinalPresentable_of_le _ ((hS j).trans h₁).le
  have hJ : HasCardinalLT (Arrow J) lam := hJ.of_le h₂.le
  -- the solution set: the cocones under `D` whose vertex is `λ`-presentable
  refine ⟨Σ q : PresentableModel C lam,
      (D ⟶ (Functor.const J).obj ((presentableModelι C lam).obj q)),
    fun x => (presentableModelι C lam).obj x.1, fun x => x.2, ?_⟩
  intro X h
  obtain ⟨I, _, _, ⟨p⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C lam).exists_colimitsOfShape X
  have : ∀ i : I, IsCardinalPresentable (p.diag.obj i) lam := fun i => by
    have := p.prop_diag_obj i
    rwa [isCardinalPresentable_iff] at this
  obtain ⟨i, phi, hphi⟩ := exists_cocone_factorization lam p.isColimit D hJ h
  -- transport the vertex into the chosen small model of the `λ`-presentable objects
  set Y : (isCardinalPresentable C lam).FullSubcategory :=
    ⟨p.diag.obj i, by rw [isCardinalPresentable_iff]; infer_instance⟩ with hY
  set q : PresentableModel C lam :=
    (equivSmallModel (isCardinalPresentable C lam).FullSubcategory).functor.obj Y with hq
  have e : (presentableModelι C lam).obj q ≅ p.diag.obj i :=
    (isCardinalPresentable C lam).ι.mapIso
      ((equivSmallModel (isCardinalPresentable C lam).FullSubcategory).unitIso.symm.app Y)
  refine ⟨⟨q, phi ≫ (Functor.const J).map e.inv⟩, e.hom ≫ p.cocone.ι.app i, ?_⟩
  ext j
  have := hphi j
  simp only [NatTrans.comp_app, Functor.const_map_app, Functor.const_obj_obj,
    Category.assoc, Iso.inv_hom_id_assoc]
  simpa using this

variable [HasLimitsOfSize.{w, w} C]

/-- **A complete accessible category has all small colimits.** -/
theorem hasColimitsOfShape_of_isAccessibleCategory_of_hasLimits : HasColimitsOfShape J C := by
  rw [hasColimitsOfShape_iff_isRightAdjoint_const]
  exact isRightAdjoint_of_preservesLimits_of_solutionSetCondition _
    (solutionSetCondition_const C J)

end

/-- **A complete accessible category is cocomplete** ([LPC], Corollary 2.47). -/
theorem hasColimitsOfSize_of_isAccessibleCategory_of_hasLimits (C : Type u) [Category.{w} C]
    [IsAccessibleCategory.{w} C] [HasLimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C where
  has_colimits_of_shape J _ := hasColimitsOfShape_of_isAccessibleCategory_of_hasLimits C J

end UlmerBialgebras
