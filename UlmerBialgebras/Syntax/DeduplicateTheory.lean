module

public import UlmerBialgebras.Syntax.PathCardinality
public import Mathlib.Logic.Small.Set

/-!
# Deduplicating indexed bialgebraic theories

A theory may index the same parallel pair of paths many times. Its image in the set of
parallel path pairs has exactly the same equations. Shrinking this image back to the original
index universe preserves the existing size convention even for independent symbol universes.

## Main results

* `UlmerBialgebras.Theory.deduplicate`: the image theory, without repeated path pairs.
* `UlmerBialgebras.Theory.forall_equationData_deduplicate_iff`: equations of the image theory
  satisfy exactly the same predicates as the original equations.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic],
  Definition 3.7 and Corollary 5.8
-/

@[expose] public section

namespace UlmerBialgebras.Theory

universe u₁ u₂ u₃ s₁ s₂ s₃ t
variable {Sg : TwoSig.{u₁, u₂, u₃}} {sg : OneSig.{u₁, u₂, u₃, s₁, s₂} Sg}

/-- A parallel pair of paths, retaining its type and endpoints. -/
abbrev ParallelPair (sg : OneSig Sg) :=
  Σ c : Sg.Cat, Σ x y : sg.CTrm c, sg.Path x y × sg.Path x y

/-- The actual parallel pair represented by an equation index. -/
def equationData (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) (r : T.Eqn) : ParallelPair sg :=
  ⟨T.eqty r, T.dom r, T.cod r, T.lhs r, T.rhs r⟩

/-- The theory indexed by distinct parallel pairs occurring in `T`, in its original index universe.
The image is small because it is the surjective image of `T.Eqn`; shrinking it introduces no
restriction on the independent universes of the signature. -/
noncomputable def deduplicate (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) : Theory sg where
  Eqn := Shrink.{s₃} (Set.range T.equationData)
  eqty r := ((equivShrink _).symm r).val.1
  dom r := ((equivShrink _).symm r).val.2.1
  cod r := ((equivShrink _).symm r).val.2.2.1
  lhs r := ((equivShrink _).symm r).val.2.2.2.1
  rhs r := ((equivShrink _).symm r).val.2.2.2.2

/-- The data of a deduplicated equation is its underlying parallel pair. -/
lemma equationData_deduplicate (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) (r : T.deduplicate.Eqn) :
    T.deduplicate.equationData r = ((equivShrink _).symm r).val := rfl

/-- The deduplicated theory has no repeated parallel pairs. -/
theorem equationData_deduplicate_injective (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) :
    Function.Injective T.deduplicate.equationData := by
  intro r r' h
  apply (equivShrink (Set.range T.equationData)).symm.injective
  exact Subtype.ext h

/-- Deduplication preserves every predicate on actual equations. -/
theorem forall_equationData_deduplicate_iff (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    (P : ParallelPair sg → Prop) :
    (∀ r, P (T.deduplicate.equationData r)) ↔ ∀ r, P (T.equationData r) := by
  constructor
  · intro h r
    simpa [equationData, deduplicate] using
      h ((equivShrink _) ⟨T.equationData r, ⟨r, rfl⟩⟩)
  · intro h r
    obtain ⟨r', hr'⟩ := ((equivShrink _).symm r).property
    rw [equationData_deduplicate, ← hr']
    exact h r'

/-- Deduplication preserves algebraicity of the theory. -/
theorem deduplicate_isAlgebraic_iff (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) :
    T.deduplicate.IsAlgebraic ↔ T.IsAlgebraic := by
  exact and_congr Iff.rfl
    (forall_equationData_deduplicate_iff T fun q => q.2.2.1.IsVar)

/-- Deduplication preserves coalgebraicity of the theory. -/
theorem deduplicate_isCoalgebraic_iff (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) :
    T.deduplicate.IsCoalgebraic ↔ T.IsCoalgebraic := by
  exact and_congr Iff.rfl
    (forall_equationData_deduplicate_iff T fun q => q.2.1.IsVar)

/-- The cardinal of the deduplicated equation set is bounded by all parallel path pairs. -/
theorem cardinalMk_deduplicate_le_parallelPair (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃} (Cardinal.mk T.deduplicate.Eqn) ≤
      Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃} (Cardinal.mk (ParallelPair sg)) := by
  have h := Cardinal.lift_mk_le_lift_mk_of_injective (equationData_deduplicate_injective T)
  have h' := Cardinal.lift_le.{max u₁ u₂ u₃ s₁ s₂ s₃}.mpr h
  rwa [Cardinal.lift_lift, Cardinal.lift_lift] at h'

/-- A parallel pair is determined by its two typed paths. -/
def parallelPairPaths (q : ParallelPair sg) : OneSig.Path.Total sg × OneSig.Path.Total sg :=
  (⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩, ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.2⟩)

/-- Encoding parallel pairs by their two typed paths is injective. -/
theorem parallelPairPaths_injective : Function.Injective (parallelPairPaths (sg := sg)) := by
  rintro ⟨c, x, y, p, q⟩ ⟨d, x', y', p', q'⟩ h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  obtain ⟨rfl, h₁⟩ := Sigma.mk.inj_iff.mp h₁
  obtain ⟨rfl, h₁⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h₁)
  obtain ⟨rfl, hp⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h₁)
  cases eq_of_heq hp
  have hq := eq_of_heq (Sigma.mk.inj_iff.mp h₂).2
  have hq := eq_of_heq (Sigma.mk.inj_iff.mp hq).2
  have hq := eq_of_heq (Sigma.mk.inj_iff.mp hq).2
  cases hq
  rfl

/-- Parallel pairs are bounded by the square of the cardinal of typed paths. -/
theorem cardinalMk_parallelPair_le_square :
    Cardinal.mk (ParallelPair sg) ≤ Cardinal.mk (OneSig.Path.Total sg) ^ 2 := by
  have h := Cardinal.mk_le_of_injective (parallelPairPaths_injective (sg := sg))
  simpa only [Cardinal.mk_prod, Cardinal.lift_id, pow_two] using h

/-- Infinite bounds on the symbols bound the number of distinct equations in any theory.
There is no assumption on the cardinal of the original equation-index type. -/
theorem cardinalMk_deduplicate_le_of_bounds (T : Theory.{u₁, u₂, u₃, s₁, s₂, s₃} sg)
    (κ : Cardinal.{max u₁ u₂ u₃ s₁ s₂ s₃ t}) (hκ : Cardinal.aleph0 ≤ κ)
    (hFn : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk sg.Fn) ≤ κ)
    (hTr : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk Sg.Tr) ≤ κ)
    (hF : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk Sg.Fun) ≤ κ)
    (hV : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk sg.Srt) ≤ κ) :
    Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk T.deduplicate.Eqn) ≤ κ := by
  have hT : Cardinal.lift.{max u₁ u₂ u₃ s₁ s₂ s₃ t} (Cardinal.mk (Σ c, sg.CTrm c)) ≤ κ :=
    Trm.cardinalMk_sigma_le_of_bounds.{u₁, u₂, s₁, max u₁ u₂ u₃ s₁ s₂ s₃ t} κ hκ hV hF
  have hA := OneSig.Arr.cardinalMk_total_le_of_bounds.{u₁, u₂, u₃, s₁, s₂, max s₃ t}
    κ hκ hFn hTr hF hT
  have hP := OneSig.Path.cardinalMk_total_le_of_bounds.{u₁, u₂, u₃, s₁, s₂, max s₃ t}
    κ hκ hT hA
  have h1 := Cardinal.lift_le.{t}.mpr (cardinalMk_deduplicate_le_parallelPair T)
  rw [Cardinal.lift_lift, Cardinal.lift_lift] at h1
  refine h1.trans ?_
  have h2 := Cardinal.lift_le.{max u₁ u₂ u₃ s₁ s₂ s₃ t}.mpr
    (cardinalMk_parallelPair_le_square (sg := sg))
  refine h2.trans ?_
  rw [pow_two, Cardinal.lift_mul]
  exact (mul_le_mul' hP hP).trans (Cardinal.mul_eq_self hκ).le

end UlmerBialgebras.Theory
