module

public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Foundations.CategoryTheory.Limits.PiColimits

/-!
# Accessible categories are stable under small products

The first of the three PIE-limit constructions: a product `∀ i, C i` of `κ`-accessible
categories, indexed by a type `ι` with `HasCardinalLT ι κ`, is again `κ`-accessible.

The cardinality assumption on `ι` is what makes the statement true *for the same* regular
cardinal `κ`: `κ`-filtered colimits commute with products of size `< κ` only.  In the
classical statement "`Acc` is closed under small products" one first replaces the given
cardinals by a common, sufficiently large one, using Mathlib's index-raising theorem for the
sharp inequality `κ ⊲ λ` (`Cardinal.SharplyLT.isCardinalAccessibleCategory`); see
`AccClosure.lean`.

## Main results

* `UlmerBialgebras.Pi.isCardinalFiltered` — a product of `κ`-filtered categories is `κ`-filtered;
* `UlmerBialgebras.Pi.isCardinalPresentable_of_forall` — a family of `κ`-presentable objects is
  `κ`-presentable in the product, provided `HasCardinalLT ι κ`;
* `UlmerBialgebras.Pi.isCardinalAccessibleCategory` — the product of `κ`-accessible categories
  (indexed by `ι` with `HasCardinalLT ι κ`) is `κ`-accessible;
* `UlmerBialgebras.Pi.eval_isCardinalAccessible`, `UlmerBialgebras.Pi.pi'_isCardinalAccessible` —
  the projections are `κ`-accessible, and so is the functor induced by a family of
  `κ`-accessible functors.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC]
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits

namespace Pi

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- A product of `κ`-filtered categories is `κ`-filtered. -/
instance isCardinalFiltered {J : ι → Type w} [∀ i, SmallCategory (J i)]
    [∀ i, IsCardinalFiltered (J i) κ] : IsCardinalFiltered (∀ i, J i) κ where
  nonempty_cocone F hA :=
    ⟨piCoconeOfCocones F (fun i => IsCardinalFiltered.cocone (κ := κ) (F ⋙ Pi.eval J i) hA)⟩

/-- A product of categories with `κ`-filtered colimits has `κ`-filtered colimits. -/
instance hasCardinalFilteredColimits [∀ i, HasCardinalFilteredColimits.{w} (C i) κ] :
    HasCardinalFilteredColimits.{w} (∀ i, C i) κ where
  hasColimitsOfShape' J _ _ := by
    have (i : ι) : HasColimitsOfShape J (C i) :=
      HasCardinalFilteredColimits.hasColimitsOfShape (C i) (κ := κ) J
    infer_instance

end

/-- A product of locally `w`-small categories, indexed by a `w`-small type, is
locally `w`-small. -/
instance locallySmall [Small.{w} ι] [∀ i, LocallySmall.{w} (C i)] :
    LocallySmall.{w} (∀ i, C i) where
  hom_small X Y := by
    have : Small.{w} (∀ i, (X i ⟶ Y i)) := inferInstance
    exact small_of_injective (f := fun (f : X ⟶ Y) => (fun i => f i))
      (fun _ _ h => h)

/-- The property of objects of a product category which holds componentwise. -/
def prop (P : ∀ i, ObjectProperty (C i)) : ObjectProperty (∀ i, C i) :=
  fun X => ∀ i, P i (X i)

/-- The componentwise property on a `w`-small product is `w`-small when each factor
property is. -/
instance prop_small [Small.{w} ι] (P : ∀ i, ObjectProperty (C i))
    [∀ i, ObjectProperty.Small.{w} (P i)] : ObjectProperty.Small.{w} (prop P) := by
  have : Small.{w} (∀ i, Subtype (P i)) := inferInstance
  exact small_of_injective (f := fun (X : Subtype (prop P)) => (fun i => ⟨X.1 i, X.2 i⟩))
    (fun X Y h => Subtype.ext (funext fun i => Subtype.ext_iff.mp (funext_iff.mp h i)))

/-- A componentwise colimit presentation in a product of categories. -/
@[simps toColimitPresentation]
def colimitOfShape {X : ∀ i, C i} {J : Type w} [SmallCategory J]
    (P : ∀ i, ObjectProperty (C i)) (q : ∀ i, (P i).ColimitOfShape J (X i)) :
    (prop P).ColimitOfShape J X where
  diag := Functor.pi' (fun i => (q i).diag)
  ι :=
    { app := fun j i => (q i).ι.app j
      naturality := fun _ _ f => by funext i; exact (q i).ι.naturality f }
  isColimit := piIsColimitOfEval (fun i => (q i).isColimit)
  prop_diag_obj j i := (q i).prop_diag_obj j

section

variable (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- The projections of a product of categories are `κ`-accessible. -/
instance eval_isCardinalAccessible (i : ι) : (Pi.eval C i).IsCardinalAccessible κ := by
  classical
  have : PreservesColimitsOfSize.{w, w} (Pi.eval C i) :=
    ⟨fun {J} _ => piEvalPreservesColimitsOfShape i⟩
  infer_instance

/-- The functor into a product of categories induced by a family of `κ`-accessible
functors is `κ`-accessible. -/
instance pi'_isCardinalAccessible {A : Type*} [Category A] (f : ∀ i, A ⥤ C i)
    [∀ i, (f i).IsCardinalAccessible κ] : (Functor.pi' f).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have (i : ι) : PreservesColimitsOfShape J (f i) :=
      (f i).preservesColimitsOfShape_of_isCardinalAccessible κ J
    infer_instance

variable {κ}

/-- A family of `κ`-presentable objects, indexed by a type of cardinality `< κ`,
is `κ`-presentable in the product category. -/
lemma isCardinalPresentable_of_forall (hι : HasCardinalLT ι κ) (X : ∀ i, C i)
    (hX : ∀ i, IsCardinalPresentable (X i) κ) : IsCardinalPresentable X κ := by
  classical
  constructor
  intro J _ _
  constructor
  intro D
  constructor
  intro c hc
  have hfilt := isFiltered_of_isCardinalFiltered J κ
  refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
  · intro f
    have H : ∀ (i : ι), ∃ (j : J) (g : X i ⟶ (D ⋙ Pi.eval C i).obj j),
        g ≫ ((Pi.eval C i).mapCocone c).ι.app j = f i := by
      intro i
      have := hX i
      exact IsCardinalPresentable.exists_hom_of_isColimit κ (piEvalIsColimit hc i) (f i)
    choose j g hg using H
    refine ⟨IsCardinalFiltered.max j hι, fun i =>
      g i ≫ (D ⋙ Pi.eval C i).map (IsCardinalFiltered.toMax j hι i), ?_⟩
    funext i
    have hw := ((Pi.eval C i).mapCocone c).w (IsCardinalFiltered.toMax j hι i)
    have h2 := hg i
    -- `f i` factors through the stage `j i`, hence through the later stage `max j`.
    exact h2.symm.trans ((g i ≫= hw.symm).trans (Category.assoc _ _ _).symm)
  · intro j f g h
    have H : ∀ (i : ι), ∃ (k : J) (u : j ⟶ k), (f i) ≫ (D.map u) i = (g i) ≫ (D.map u) i := by
      intro i
      have := hX i
      exact IsCardinalPresentable.exists_eq_of_isColimit' κ (piEvalIsColimit hc i)
        (f i) (g i) (funext_iff.mp h i)
    choose k u hu using H
    obtain ⟨m, a, b, hab⟩ := IsCardinalFiltered.wideSpan (κ := κ) u hι
    refine ⟨m, b, ?_⟩
    funext i
    dsimp
    rw [← hab i, D.map_comp, Pi.comp_apply]
    exact (reassoc_of% (hu i)) (D.map (a i) i)

/-- **A product of `κ`-accessible categories, indexed by a type of cardinality `< κ`,
is `κ`-accessible.** -/
theorem isCardinalAccessibleCategory (hι : HasCardinalLT ι κ)
    [∀ i, IsCardinalAccessibleCategory.{w} (C i) κ] :
    IsCardinalAccessibleCategory.{w} (∀ i, C i) κ := by
  have : Small.{w} ι := hι.small
  have hgen : ∀ i, ∃ (P : ObjectProperty (C i)) (_ : ObjectProperty.Small.{w} (P)),
      P.IsCardinalFilteredGenerator κ :=
    fun i => HasCardinalFilteredGenerator.exists_small_generator (C i) κ
  choose P hPsmall hP using hgen
  have : ∀ i, ObjectProperty.Small.{w} (P i) := hPsmall
  have hle : prop P ≤ isCardinalPresentable (∀ i, C i) κ := by
    intro X hX
    exact isCardinalPresentable_of_forall hι X (fun i => (hP i).le_isCardinalPresentable _ (hX i))
  have hgen' : (prop P).IsCardinalFilteredGenerator κ := by
    refine ⟨hle, fun X => ?_⟩
    have h : ∀ i, ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J κ),
        (P i).colimitsOfShape J (X i) := fun i => (hP i).exists_colimitsOfShape (X i)
    choose J hJcat hJfilt hJ using h
    refine ⟨∀ i, J i, inferInstance, inferInstance, ?_⟩
    have hfin : ∀ i, (Pi.eval J i).Final := by
      intro i
      have : ∀ k, IsFiltered (J k) := fun k => isFiltered_of_isCardinalFiltered (J k) κ
      infer_instance
    exact ⟨colimitOfShape P (fun i => ((hJ i).some.reindex (Pi.eval J i)))⟩
  exact
    { toHasCardinalFilteredGenerator := hgen'.hasCardinalFilteredGenerator
      toHasCardinalFilteredColimits := inferInstance }

end

end Pi

end UlmerBialgebras
