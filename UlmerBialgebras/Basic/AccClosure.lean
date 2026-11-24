module

public import UlmerBialgebras.Basic.AccPi
public import Mathlib.CategoryTheory.Presentable.Uniformization
public import UlmerBialgebras.Basic.AccessibleInserter
public import UlmerBialgebras.Basic.AccessibleEquifier

/-!
# Accessible categories are closed under the PIE limits of `CAT`

This file collects the closure properties of the 2-category `Acc` of accessible categories,
accessible functors and natural transformations inside `CAT`:

* **products**: `UlmerBialgebras.Pi.isAccessibleCategory`, together with the accessibility of the
  projections and of the induced functors;
* **inserters**: `UlmerBialgebras.Ins.isAccessibleCategory`, with
  `UlmerBialgebras.Ins.forget_isAccessible` and `UlmerBialgebras.Ins.liftFunctor_isAccessible`;
* **equifiers**: `UlmerBialgebras.Equif.isAccessibleCategory`, with the corresponding statements for
  the inclusion and the induced functors.

Mathlib's index raising along sharply smaller cardinals
(`Cardinal.SharplyLT.isCardinalAccessibleCategory`, `Cardinal.SharplyLT.exists_of_small`) and its
uniformization theorem (`CategoryTheory.IsCardinalAccessibleCategory.uniformization_pair`) are
what make it
possible to pass from the individual cardinals of accessibility of the data to a single
cardinal for which all the hypotheses of the generation theorems (`AccessibleInserter.lean`,
`AccessibleEquifier.lean`) hold at once.

## Main results

* `UlmerBialgebras.exists_common_regular`: a small family of accessible categories is `κ`-accessible
  for a single regular cardinal `κ`, which can be chosen above a prescribed small family of small
  types.
* `UlmerBialgebras.Pi.isAccessibleCategory`: a product of accessible categories indexed by a small
  type is accessible.
* `UlmerBialgebras.Ins.isAccessibleCategory`: the inserter of two accessible functors between
  accessible categories is accessible.
* `UlmerBialgebras.Equif.isAccessibleCategory`: the equifier of two natural transformations between
  accessible functors between accessible categories is accessible.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Example 2.3 and Section 5.3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC],
  2.72 Theorem, 2.76 Lemma
-/

@[expose] public section

universe w v v' v'' u u' u''

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

/-! ## Monotonicity and uniformization -/

/-- Having `κ`-filtered colimits only becomes weaker when the cardinal grows. -/
lemma hasCardinalFilteredColimits_of_le (C : Type u) [Category.{v} C]
    {kappa kappa' : Cardinal.{w}} [Fact kappa.IsRegular] [Fact kappa'.IsRegular]
    [HasCardinalFilteredColimits.{w} C kappa] (h : kappa ≤ kappa') :
    HasCardinalFilteredColimits.{w} C kappa' where
  hasColimitsOfShape' J _ _ := by
    have : IsCardinalFiltered J kappa := IsCardinalFiltered.of_le J (κ := kappa') h
    exact HasCardinalFilteredColimits.hasColimitsOfShape C (κ := kappa) J

/-- A small family of cardinals admits a regular upper bound. -/
lemma exists_regular_ge {ι : Type v} [Small.{w} ι] (S : ι → Cardinal.{w}) :
    ∃ (kappa : Cardinal.{w}) (_ : Fact kappa.IsRegular), ∀ i, S i ≤ kappa := by
  obtain ⟨c, hc⟩ := Cardinal.exists_le_of_small S
  exact ⟨Order.succ (max c ℵ₀), ⟨isRegular_succ (le_max_right _ _)⟩,
    fun i => (hc i).trans ((le_max_left _ _).trans (Order.le_succ _))⟩

/-- **A single cardinal of accessibility for a small family of accessible categories.**
Moreover the cardinal can be chosen above a prescribed small family of small types. -/
theorem exists_common_regular {ι : Type v} [Small.{w} ι] (C : ι → Type u)
    [∀ i, Category.{v'} (C i)] [∀ i, IsAccessibleCategory.{w} (C i)]
    {ι' : Type v} [Small.{w} ι'] (X : ι' → Type w) :
    ∃ (kappa : Cardinal.{w}) (_ : Fact kappa.IsRegular),
      (∀ i, IsCardinalAccessibleCategory.{w} (C i) kappa) ∧ ∀ i, HasCardinalLT (X i) kappa := by
  have h : ∀ i, ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
      IsCardinalAccessibleCategory.{w} (C i) κ := fun i => IsAccessibleCategory.exists_cardinal _
  choose S hSreg hSacc using h
  obtain ⟨κX, hκX, hX⟩ := HasCardinalLT.exists_regular_cardinal_forall.{w} X
  have : Fact κX.IsRegular := ⟨hκX⟩
  obtain ⟨κS, _, hS⟩ := SharplyLT.exists_of_small S
  obtain ⟨kappa, hreg, h₁, h₂⟩ := SharplyLT.exists_of_pair κS κX
  refine ⟨kappa, hreg, fun i => ?_, fun i => (hX i).of_le h₂.le⟩
  have := hSacc i
  exact ((hS i).trans h₁).isCardinalAccessibleCategory (C i)

/-! ## Products -/

namespace Pi

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]

/-- **A product of accessible categories, indexed by a small type, is accessible**
([LPC], 2.72 Theorem; Example 2.3 (2) of [forsman2026syntactic]). -/
theorem isAccessibleCategory [∀ i, IsAccessibleCategory.{w} (C i)] :
    IsAccessibleCategory.{w} (∀ i, C i) := by
  obtain ⟨kappa, hreg, hacc, hX⟩ :=
    exists_common_regular (C := C) (ι' := PUnit.{w + 1}) (fun _ => ι)
  have := hreg
  have := hacc
  refine ⟨kappa, hreg, ?_⟩
  have hι : HasCardinalLT ι kappa := hX PUnit.unit
  have : ∀ i, LocallySmall.{w} (C i) := fun i => inferInstance
  exact UlmerBialgebras.Pi.isCardinalAccessibleCategory hι

/-- The projections of a product of categories are accessible. -/
instance eval_isAccessible (i : ι) : Functor.IsAccessible.{w} (Pi.eval C i) := by
  have : Fact (Cardinal.aleph0.{w}).IsRegular := ⟨Cardinal.isRegular_aleph0⟩
  exact Functor.isAccessible_of_isCardinalAccessible _ Cardinal.aleph0.{w}

/-- The functor into a product of categories induced by a family of accessible functors is
accessible. -/
instance pi'_isAccessible {A : Type u'} [Category.{v'} A] (f : ∀ i, A ⥤ C i)
    [∀ i, Functor.IsAccessible.{w} (f i)] : Functor.IsAccessible.{w} (Functor.pi' f) := by
  have h : ∀ i, ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular), (f i).IsCardinalAccessible κ :=
    fun i => Functor.IsAccessible.exists_cardinal (f i)
  choose S hSreg hSacc using h
  obtain ⟨kappa, hreg, hle⟩ := exists_regular_ge S
  have := hreg
  have : ∀ i, (f i).IsCardinalAccessible kappa := by
    intro i
    have := hSreg i
    have := hSacc i
    exact Functor.isCardinalAccessible_of_le (f i) (hle i)
  exact Functor.isAccessible_of_isCardinalAccessible _ kappa

end Pi

/-! ## Inserters -/

namespace Ins

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc] {F G : C ⥤ Dc}

/-- **The inserter of two accessible functors between accessible categories is
accessible** ([LPC], 2.72 Theorem; [MakkaiPare1989AccessibleCategories]). -/
theorem isAccessibleCategory [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} Dc]
    [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] :
    IsAccessibleCategory.{w} (Ins F G) := by
  obtain ⟨lam, _, _, _, -, -, _, _, _, -⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F G
  obtain ⟨kappa, hkreg, hsharp⟩ := SharplyLT.exists_of_small (fun _ : PUnit.{1} => lam)
  exact ⟨kappa, hkreg,
    Ins.isCardinalAccessibleCategory_general (fun _ _ => inferInstance) (hsharp ⟨⟩)⟩

/-- The forgetful functor of the inserter is accessible. -/
theorem forget_isAccessible [IsAccessibleCategory.{w} C] [Functor.IsAccessible.{w} F] :
    Functor.IsAccessible.{w} (forget F G) := by
  obtain ⟨κ₁, hκ₁, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, hκ₂, hF⟩ := Functor.IsAccessible.exists_cardinal (F := F)
  obtain ⟨kappa, hreg, hle⟩ := exists_regular_ge (ι := ULift.{w} Bool)
    (fun b => if b.down then κ₁ else κ₂)
  have := hκ₁; have := hκ₂; have := hreg; have := hC; have := hF
  have h1 : HasCardinalFilteredColimits.{w} C kappa :=
    hasCardinalFilteredColimits_of_le C (kappa := κ₁) (by simpa using hle ⟨true⟩)
  have h2 : F.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le F (by simpa using hle ⟨false⟩)
  exact Functor.isAccessible_of_isCardinalAccessible _ kappa

/-- The functor into the inserter induced by an accessible functor is accessible. -/
theorem liftFunctor_isAccessible [IsAccessibleCategory.{w} C] [Functor.IsAccessible.{w} F]
    {X : Type u''} [Category.{v''} X] (h : X ⥤ C) (α : h ⋙ F ⟶ h ⋙ G)
    [Functor.IsAccessible.{w} h] : Functor.IsAccessible.{w} (liftFunctor h α) := by
  obtain ⟨κ₁, hκ₁, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, hκ₂, hF⟩ := Functor.IsAccessible.exists_cardinal (F := F)
  obtain ⟨κ₃, hκ₃, hh⟩ := Functor.IsAccessible.exists_cardinal (F := h)
  obtain ⟨kappa, hreg, hle⟩ := exists_regular_ge (ι := ULift.{w} (Fin 3))
    (fun b => ![κ₁, κ₂, κ₃] b.down)
  have := hκ₁; have := hκ₂; have := hκ₃; have := hreg; have := hC; have := hF; have := hh
  have h1 : HasCardinalFilteredColimits.{w} C kappa :=
    hasCardinalFilteredColimits_of_le C (kappa := κ₁) (by simpa using hle ⟨0⟩)
  have h2 : F.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le F (by simpa using hle ⟨1⟩)
  have h3 : h.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le h (by simpa using hle ⟨2⟩)
  exact Functor.isAccessible_of_isCardinalAccessible _ kappa

end Ins

/-! ## Equifiers -/

namespace Equif

variable {C : Type u} [Category.{v} C] {Dc : Type u'} [Category.{v'} Dc] {F G : C ⥤ Dc}
  {η θ : F ⟶ G}

/-- **The equifier of two natural transformations between accessible functors is
accessible** ([LPC], 2.76 Lemma; [MakkaiPare1989AccessibleCategories]). -/
theorem isAccessibleCategory [IsAccessibleCategory.{w} C] [IsAccessibleCategory.{w} Dc]
    [Functor.IsAccessible.{w} F] [Functor.IsAccessible.{w} G] :
    IsAccessibleCategory.{w} (Equif η θ) := by
  obtain ⟨lam, _, _, _, -, -, _, _, _, -⟩ :=
    IsCardinalAccessibleCategory.uniformization_pair F G
  obtain ⟨kappa, hkreg, hsharp⟩ := SharplyLT.exists_of_small (fun _ : PUnit.{1} => lam)
  exact ⟨kappa, hkreg,
    Equif.isCardinalAccessibleCategory_general (fun _ _ => inferInstance) (hsharp ⟨⟩)⟩

/-- The inclusion of the equifier is accessible. -/
theorem forget_isAccessible [IsAccessibleCategory.{w} C] [Functor.IsAccessible.{w} F] :
    Functor.IsAccessible.{w} (forget η θ) := by
  obtain ⟨κ₁, hκ₁, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, hκ₂, hF⟩ := Functor.IsAccessible.exists_cardinal (F := F)
  obtain ⟨kappa, hreg, hle⟩ := exists_regular_ge (ι := ULift.{w} Bool)
    (fun b => if b.down then κ₁ else κ₂)
  have := hκ₁; have := hκ₂; have := hreg; have := hC; have := hF
  have h1 : HasCardinalFilteredColimits.{w} C kappa :=
    hasCardinalFilteredColimits_of_le C (kappa := κ₁) (by simpa using hle ⟨true⟩)
  have h2 : F.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le F (by simpa using hle ⟨false⟩)
  exact Functor.isAccessible_of_isCardinalAccessible _ kappa

/-- The functor into the equifier induced by an accessible functor is accessible. -/
theorem liftFunctor_isAccessible [IsAccessibleCategory.{w} C] [Functor.IsAccessible.{w} F]
    {X : Type u''} [Category.{v''} X] (h : X ⥤ C)
    (H : Functor.whiskerLeft h η = Functor.whiskerLeft h θ) [Functor.IsAccessible.{w} h] :
    Functor.IsAccessible.{w} (liftFunctor h H) := by
  obtain ⟨κ₁, hκ₁, hC⟩ := IsAccessibleCategory.exists_cardinal.{w} C
  obtain ⟨κ₂, hκ₂, hF⟩ := Functor.IsAccessible.exists_cardinal (F := F)
  obtain ⟨κ₃, hκ₃, hh⟩ := Functor.IsAccessible.exists_cardinal (F := h)
  obtain ⟨kappa, hreg, hle⟩ := exists_regular_ge (ι := ULift.{w} (Fin 3))
    (fun b => ![κ₁, κ₂, κ₃] b.down)
  have := hκ₁; have := hκ₂; have := hκ₃; have := hreg; have := hC; have := hF; have := hh
  have h1 : HasCardinalFilteredColimits.{w} C kappa :=
    hasCardinalFilteredColimits_of_le C (kappa := κ₁) (by simpa using hle ⟨0⟩)
  have h2 : F.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le F (by simpa using hle ⟨1⟩)
  have h3 : h.IsCardinalAccessible kappa :=
    Functor.isCardinalAccessible_of_le h (by simpa using hle ⟨2⟩)
  exact Functor.isAccessible_of_isCardinalAccessible _ kappa

end Equif

end UlmerBialgebras
