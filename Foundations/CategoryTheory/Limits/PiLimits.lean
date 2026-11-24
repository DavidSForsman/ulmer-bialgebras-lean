module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Limits in a product of categories

Limits in a product `∀ i, C i` of categories are computed componentwise.  Mathlib contains
these constructions (`CategoryTheory.pi`), but only for index types, shapes and hom-types
living in one and the same universe; here we record the universe-polymorphic versions that
the lifting theorems of Section 6 need, together with the two consequences we use.

## Main results

* `UlmerBialgebras.pi_hasLimitsOfShape` — a product of categories with `J`-limits has `J`-limits;
* `UlmerBialgebras.piEvalPreservesLimitsOfShape` — the projections preserve them.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Theorem 4.7 (1), Section 6
-/

@[expose] public section

universe w v v' u u'

namespace UlmerBialgebras

open CategoryTheory Limits

variable {ι : Type w} {C : ι → Type u} [∀ i, Category.{v} (C i)]
variable {J : Type*} [Category J] (F : J ⥤ ∀ i, C i)

/-- The `i`-th component of a cone in a product of categories. This is Mathlib's
`CategoryTheory.pi.coneCompEval` with the universes of `J` and of the `C i` independent. -/
@[simps]
def piConeEval (c : Cone F) (i : ι) : Cone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr($(c.π.naturality f) i) }

/-- A family of componentwise cones assembles into a cone in the product category. This is
Mathlib's `CategoryTheory.pi.coneOfConeCompEval` with the universes independent. -/
@[simps]
def piConeOfCones (c : ∀ i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun _ _ f => by funext i; exact (c i).π.naturality f }

/-- A family of componentwise limit cones assembles into a limit cone. This is Mathlib's
`CategoryTheory.pi.coneOfConeEvalIsLimit` with the universes independent. -/
def piIsLimitOfIsLimit {c : ∀ i, Cone (F ⋙ Pi.eval C i)} (P : ∀ i, IsLimit (c i)) :
    IsLimit (piConeOfCones F c) where
  lift s i := (P i).lift (piConeEval F s i)
  fac s j := by funext i; exact (P i).fac (piConeEval F s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (piConeEval F s i) (m i) fun j => congr($(w j) i)

/-- A product of categories has limits of shape `J` if every factor does. -/
instance pi_hasLimitsOfShape [∀ i, HasLimitsOfShape J (C i)] :
    HasLimitsOfShape J (∀ i, C i) where
  has_limit F :=
    ⟨⟨⟨piConeOfCones F fun _ => limit.cone _, piIsLimitOfIsLimit F fun _ => limit.isLimit _⟩⟩⟩

/-- A product of categories has finite limits if every factor does. -/
instance pi_hasFiniteLimits [∀ i, HasFiniteLimits (C i)] : HasFiniteLimits (∀ i, C i) where
  out _ _ _ := pi_hasLimitsOfShape

/-- The projections of a product of categories preserve all limits that exist
componentwise. -/
noncomputable def piEvalIsLimit [∀ i, HasLimitsOfShape J (C i)] {c : Cone F} (hc : IsLimit c)
    (i : ι) : IsLimit ((Pi.eval C i).mapCone c) := by
  let L : IsLimit (piConeOfCones F fun i => limit.cone (F ⋙ Pi.eval C i)) :=
    piIsLimitOfIsLimit F fun _ => limit.isLimit _
  let e := hc.uniqueUpToIso L
  refine IsLimit.ofIsoLimit (limit.isLimit (F ⋙ Pi.eval C i))
    (Cone.ext ((Pi.eval C i).mapIso ((Cone.forget F).mapIso e)).symm ?_)
  intro j
  exact (congr($(e.inv.w j) i)).symm

/-- The projections of a product of categories preserve limits of shape `J`. -/
noncomputable instance piEvalPreservesLimitsOfShape [∀ i, HasLimitsOfShape J (C i)] (i : ι) :
    PreservesLimitsOfShape J (Pi.eval C i) where
  preservesLimit := ⟨fun hc => ⟨piEvalIsLimit _ hc i⟩⟩

/-- The projections of a product of categories preserve finite limits. -/
noncomputable instance piEvalPreservesFiniteLimits [∀ i, HasFiniteLimits (C i)] (i : ι) :
    PreservesFiniteLimits (Pi.eval C i) where
  preservesFiniteLimits _ _ _ := piEvalPreservesLimitsOfShape i

/-- A cone in a product of categories all of whose components are limit cones is a limit
cone. -/
def piIsLimitOfEval {c : Cone F} (h : ∀ i, IsLimit (piConeEval F c i)) : IsLimit c where
  lift s i := (h i).lift (piConeEval F s i)
  fac s j := by funext i; exact (h i).fac (piConeEval F s i) j
  uniq s m w := by
    funext i
    exact (h i).uniq (piConeEval F s i) (m i) fun j => congr($(w j) i)

end UlmerBialgebras
