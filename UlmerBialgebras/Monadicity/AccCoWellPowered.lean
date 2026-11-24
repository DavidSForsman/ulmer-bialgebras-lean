module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Lemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import UlmerBialgebras.Monadicity.AccCollapse
public import Foundations.CategoryTheory.Presentable.LPComplete

/-!
# Accessible categories with pushouts are co-well-powered

An accessible category is always well-powered (this is not used, nor formalized, here).
Dually one asks whether every object has only a set of quotients.  This is *not* automatic, but
it does hold as soon as the category has pushouts; this is Adámek–Rosický [LPC], Theorem 1.58.

The strategy is to attach to a quotient `e : K ↠ L` of a `κ`-presentable object `K` the *set of
collapsing data it admits*: the set of quadruples `(P, R, a : K ⟶ P, t : P ⟶ R)` with `P`, `R`
`κ`-presentable, `t` an `a`-collapsing morphism (`UlmerBialgebras.Collapsing`), such that `a ≫ t`
factors `e`.  Since the `κ`-presentable objects form a small family and `C` is locally `w`-small,
this is a `w`-small piece of data.

The key point (`UlmerBialgebras.exists_hom_of_collapseDominates`) is that this invariant is
complete:  if every collapsing datum for `e` is one for `e'`, then `e` factors through `e'`, i.e.
`e' = e ≫ f` for some `f`.  Applying this in both directions shows that the invariant determines the
quotient, whence `UlmerBialgebras.small_subobject_op_of_isCardinalPresentable` and the main theorems
`UlmerBialgebras.wellPowered_op_of_isAccessibleCategory` (co-well-poweredness of an accessible
category with pushouts) and `UlmerBialgebras.wellPowered_op_of_isLocallyPresentable`.

## Main results

* `UlmerBialgebras.exists_hom_of_collapseDominates`: for an epimorphism `e` out of a `κ`-presentable
  object, if `CollapseDominates κ e e'`, then `e ≫ f = e'` for some `f`.
* `UlmerBialgebras.small_subobject_op_of_isCardinalPresentable`: the quotients of a `κ`-presentable
  object form a `w`-small set.
* `UlmerBialgebras.wellPowered_op_of_isAccessibleCategory`: an accessible category with pushouts is
  co-well-powered.
* `UlmerBialgebras.wellPowered_op_of_isLocallyPresentable`: a locally presentable category is
  co-well-powered.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Theorem 5.10
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], Theorem 1.58
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits IsCardinalAccessibleCategory

section

variable {C : Type u} [Category.{v} C]

/-- `e` **collapse-dominates** `e'` if every collapsing datum through which `e` factors also
supports a factorization of `e'`:  whenever `t : P ⟶ R` is an `a`-collapsing morphism between
`κ`-presentable objects and `a ≫ t ≫ w = e`, there is a `w'` with `a ≫ t ≫ w' = e'`. -/
def CollapseDominates (κ : Cardinal.{w}) [Fact κ.IsRegular] {K L L' : C} (e : K ⟶ L) (e' : K ⟶ L') :
    Prop :=
  ∀ (P R : C), IsCardinalPresentable P κ → IsCardinalPresentable R κ →
    ∀ (a : K ⟶ P) (t : P ⟶ R), Collapsing a t → ∀ w : R ⟶ L, a ≫ t ≫ w = e →
      ∃ w' : R ⟶ L', a ≫ t ≫ w' = e'

end

section Comparison

variable {C : Type u} [Category.{v} C] {κ : Cardinal.{w}} [Fact κ.IsRegular]

/-- A map `W` out of a later stage of a collapsing refinement `f j : j ⟶ m j` which recovers `e'`
from `K` agrees, after the refinement, with any other such map `w'`. -/
private lemma collapse_refinement_eq {K L L' : C} {e : K ⟶ L} {e' : K ⟶ L'}
    (p : UnderPresentation κ e) {j m k : p.J} (f : j ⟶ m)
    (hf : Collapsing (p.a j) (p.D.map f)) (w' : p.D.obj m ⟶ L')
    (hw' : p.a j ≫ p.D.map f ≫ w' = e') (g : m ⟶ k) (W : p.D.obj k ⟶ L')
    (hW : p.a j ≫ p.D.map f ≫ p.D.map g ≫ W = e') :
    p.D.map f ≫ p.D.map g ≫ W = p.D.map f ≫ w' := by
  simpa using hf.eq (p.D.map g ≫ W) w' (by rw [hW]; exact hw'.symm)

/-- In the comparison argument, the maps `D j ⟶ L'` obtained from collapsing refinements
`f j : j ⟶ m j` and factorizations `w' j` of `e'` form a cocone over the presentation of `e`. -/
private lemma collapse_refinement_cocone {K L L' : C} {e : K ⟶ L} {e' : K ⟶ L'}
    (h : CollapseDominates κ e e') (p : UnderPresentation κ e) (m : p.J → p.J)
    (f : ∀ j, j ⟶ m j) (hf : ∀ j, Collapsing (p.a j) (p.D.map (f j)))
    (w' : ∀ j, p.D.obj (m j) ⟶ L') (hw' : ∀ j, p.a j ≫ p.D.map (f j) ≫ w' j = e')
    {i j : p.J} (g₀ : i ⟶ j) :
    p.D.map g₀ ≫ p.D.map (f j) ≫ w' j = p.D.map (f i) ≫ w' i := by
  -- Pass to a stage `k` where `f i` and `g₀ ≫ f j` become equal (`hkey`). The refinement to `k`
  -- is collapsing, so domination gives one map `W` out of `D k` that recovers `e'` from both `i`
  -- and `j`; by `collapse_refinement_eq`, `w' i` and `w' j` both agree with `W`.
  have : IsFiltered p.J := isFiltered_of_isCardinalFiltered p.J κ
  set n : p.J := IsFiltered.max (m i) (m j)
  set u₁ : m i ⟶ n := IsFiltered.leftToMax (m i) (m j)
  set u₂ : m j ⟶ n := IsFiltered.rightToMax (m i) (m j)
  set k : p.J := IsFiltered.coeq (f i ≫ u₁) (g₀ ≫ f j ≫ u₂)
  set psi : n ⟶ k := IsFiltered.coeqHom (f i ≫ u₁) (g₀ ≫ f j ≫ u₂)
  have hcoeq : (f i ≫ u₁) ≫ psi = (g₀ ≫ f j ≫ u₂) ≫ psi :=
    IsFiltered.coeq_condition _ _
  have hkey : p.D.map (f i) ≫ p.D.map (u₁ ≫ psi)
      = p.D.map g₀ ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi) := by
    simp only [← Functor.map_comp]
    congr 1
    simpa using hcoeq
  have hT : Collapsing (p.a i) (p.D.map (f i) ≫ p.D.map (u₁ ≫ psi)) :=
    (hf i).comp_right _
  have hproj : (p.D.map (f i) ≫ p.D.map (u₁ ≫ psi)) ≫ p.proj k = p.proj i := by
    rw [Category.assoc, p.proj_naturality, p.proj_naturality]
  obtain ⟨W, hW⟩ := h _ _ (p.pres i) (p.pres k) (p.a i) _ hT (p.proj k)
    (by rw [hproj]; exact p.fac i)
  have hWi : p.a i ≫ p.D.map (f i) ≫ p.D.map (u₁ ≫ psi) ≫ W = e' := by
    simpa using hW
  have hi := collapse_refinement_eq p (f i) (hf i) (w' i) (hw' i) (u₁ ≫ psi) W hWi
  have hWj : p.a j ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi) ≫ W = e' := by
    rw [← p.a_naturality g₀]
    calc (p.a i ≫ p.D.map g₀) ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi) ≫ W
        = p.a i ≫ (p.D.map g₀ ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi)) ≫ W := by
          simp only [Category.assoc]
      _ = p.a i ≫ (p.D.map (f i) ≫ p.D.map (u₁ ≫ psi)) ≫ W := by rw [hkey]
      _ = e' := by simpa using hWi
  have hj := collapse_refinement_eq p (f j) (hf j) (w' j) (hw' j) (u₂ ≫ psi) W hWj
  calc p.D.map g₀ ≫ p.D.map (f j) ≫ w' j
      = p.D.map g₀ ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi) ≫ W := by rw [hj]
    _ = (p.D.map g₀ ≫ p.D.map (f j) ≫ p.D.map (u₂ ≫ psi)) ≫ W := by simp only [Category.assoc]
    _ = (p.D.map (f i) ≫ p.D.map (u₁ ≫ psi)) ≫ W := by rw [hkey]
    _ = p.D.map (f i) ≫ w' i := by rw [Category.assoc]; exact hi

variable [IsCardinalAccessibleCategory.{w} C κ] [HasPushouts C]

/-- **Comparison lemma.**  If the epimorphism `e : K ⟶ L` out of a `κ`-presentable object
collapse-dominates `e' : K ⟶ L'`, then `e'` factors through `e`. -/
theorem exists_hom_of_collapseDominates {K L L' : C} [IsCardinalPresentable K κ]
    (e : K ⟶ L) [Epi e] (e' : K ⟶ L') (h : CollapseDominates κ e e') :
    ∃ f : L ⟶ L', e ≫ f = e' := by
  classical
  obtain ⟨p⟩ := UnderPresentation.exists_of_isCardinalPresentable κ e
  -- for each stage, a collapsing refinement
  choose m f hf using fun j => p.exists_collapsing_map j
  -- the value of `e` on `L'` at each stage
  have key : ∀ j, ∃ w' : p.D.obj (m j) ⟶ L', p.a j ≫ p.D.map (f j) ≫ w' = e' := by
    intro j
    refine h _ _ (p.pres j) (p.pres (m j)) (p.a j) (p.D.map (f j)) (hf j) (p.proj (m j)) ?_
    rw [p.proj_naturality (f j), p.fac j]
  choose w' hw' using key
  set nu : ∀ j, p.D.obj j ⟶ L' := fun j => p.D.map (f j) ≫ w' j with hnu
  have hanu : ∀ j, p.a j ≫ nu j = e' := fun j => by
    rw [hnu]; simpa using hw' j
  have hcocone : ∀ {i j : p.J} (g : i ⟶ j), p.D.map g ≫ nu j = nu i := fun g =>
    collapse_refinement_cocone h p m f hf w' hw' g
  refine ⟨p.desc nu (fun {i j} g => hcocone g), ?_⟩
  obtain ⟨j⟩ := p.ne
  calc e ≫ p.desc nu (fun {i j} g => hcocone g)
      = (p.a j ≫ p.proj j) ≫ p.desc nu (fun {i j} g => hcocone g) := by rw [p.fac j]
    _ = p.a j ≫ nu j := by rw [Category.assoc, p.desc_fac]
    _ = e' := hanu j

end Comparison

section Smallness

variable (C : Type u) [Category.{w} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalAccessibleCategory.{w} C κ]

/-- The small index type of collapsing data out of an object `K`:  a pair of indices for
`κ`-presentable objects `P`, `R`, together with maps `K ⟶ P` and `P ⟶ R`. -/
abbrev CollapseIdx (K : C) : Type w :=
  Σ (q r : PresentableModel C κ), (K ⟶ (presentableModelι C κ).obj q) ×
    ((presentableModelι C κ).obj q ⟶ (presentableModelι C κ).obj r)

variable {C κ}

/-- The set of collapsing data supporting a factorization of `e : K ⟶ L`. -/
def collapseSet {K L : C} (e : K ⟶ L) : Set (CollapseIdx C κ K) :=
  {v | Collapsing v.2.2.1 v.2.2.2 ∧
    ∃ w : (presentableModelι C κ).obj v.2.1 ⟶ L, v.2.2.1 ≫ v.2.2.2 ≫ w = e}

/-- The collapsing-data invariant is complete: an inclusion of invariants implies
collapse-domination. -/
theorem collapseDominates_of_subset {K L L' : C} (e : K ⟶ L) (e' : K ⟶ L')
    (hsub : collapseSet (κ := κ) e ⊆ collapseSet (κ := κ) e') : CollapseDominates κ e e' := by
  intro P R hP hR a t ht w hw
  have := hP
  have := hR
  obtain ⟨q, ⟨iP⟩⟩ := presentableModelι_essImage C κ P hP
  obtain ⟨r, ⟨iR⟩⟩ := presentableModelι_essImage C κ R hR
  have hmem : (⟨q, r, a ≫ iP.inv, iP.hom ≫ t ≫ iR.inv⟩ : CollapseIdx C κ K)
      ∈ collapseSet (κ := κ) e := by
    refine ⟨?_, iR.hom ≫ w, ?_⟩
    · have h1 : Collapsing (a ≫ iP.inv) (iP.hom ≫ t) := ht.whiskerLeft iP.hom (by simp)
      have h2 := h1.comp_right iR.inv
      simpa using h2
    · simpa using hw
  obtain ⟨-, w₀, hw₀⟩ := hsub hmem
  exact ⟨iR.inv ≫ w₀, by simpa using hw₀⟩

variable [HasPushouts C]

/-- **Quotients of a `κ`-presentable object form a set.** -/
theorem small_subobject_op_of_isCardinalPresentable (K : C) [IsCardinalPresentable K κ] :
    Small.{w} (Subobject (Opposite.op K)) := by
  refine small_of_injective
    (f := fun x : Subobject (Opposite.op K) => collapseSet (κ := κ) x.arrow.unop) ?_
  intro x y hxy
  have : Epi x.arrow.unop := unop_epi_of_mono x.arrow
  have : Epi y.arrow.unop := unop_epi_of_mono y.arrow
  obtain ⟨g, hg⟩ := exists_hom_of_collapseDominates (κ := κ) x.arrow.unop y.arrow.unop
    (collapseDominates_of_subset _ _ (le_of_eq hxy))
  obtain ⟨g', hg'⟩ := exists_hom_of_collapseDominates (κ := κ) y.arrow.unop x.arrow.unop
    (collapseDominates_of_subset _ _ (le_of_eq hxy.symm))
  refine le_antisymm (Subobject.le_of_comm g'.op ?_) (Subobject.le_of_comm g.op ?_)
  · exact Quiver.Hom.unop_inj (by simpa using hg')
  · exact Quiver.Hom.unop_inj (by simpa using hg)

end Smallness

/-- **An accessible category with pushouts is co-well-powered** (Adámek–Rosický [LPC], 1.58). -/
theorem wellPowered_op_of_isAccessibleCategory (C : Type u) [Category.{w} C]
    [IsAccessibleCategory.{w} C] [HasPushouts C] : WellPowered.{w} Cᵒᵖ where
  subobject_small X := by
    obtain ⟨kap, hkapreg, hkapacc⟩ := IsAccessibleCategory.exists_cardinal.{w} C
    obtain ⟨kapX, hkapXreg, hkapXpres⟩ :
        ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), IsCardinalPresentable X.unop κ :=
      Functor.IsAccessible.exists_cardinal _
    obtain ⟨lam, hreg, h₀, h₁⟩ := Cardinal.SharplyLT.exists_of_pair kap kapX
    have := hreg
    have : IsCardinalAccessibleCategory.{w} C lam := h₀.isCardinalAccessibleCategory C
    have : IsCardinalPresentable X.unop lam := isCardinalPresentable_of_le _ h₁.le
    exact small_subobject_op_of_isCardinalPresentable (κ := lam) X.unop

/-- **A locally presentable category is co-well-powered** ([LPC], Theorem 1.58). -/
theorem wellPowered_op_of_isLocallyPresentable (C : Type u) [Category.{w} C]
    [IsLocallyPresentable.{w} C] : WellPowered.{w} Cᵒᵖ := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal C
  have : HasColimitsOfSize.{w, w} C := inferInstance
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C
  exact wellPowered_op_of_isAccessibleCategory C

end UlmerBialgebras
