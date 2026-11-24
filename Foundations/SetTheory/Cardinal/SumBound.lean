module

public import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Bounds for cardinal sums in independent universes

An at most `κ`-indexed family of at most `κ`-sized cardinals has sum at most an infinite `κ`.
The lifts allow the index, summands, and bound to start in independent universes.

## Main results

* `Cardinal.lift_sum_le_of_bounds`: an infinite uniform bound on a cardinal sum.

## References

* `Mathlib.SetTheory.Cardinal.Arithmetic`
-/

@[expose] public section
namespace Cardinal
universe u v w

/-- An infinite bound on the index cardinal and every summand bounds the cardinal sum. -/
theorem lift_sum_le_of_bounds {ι : Type u} (f : ι → Cardinal.{v})
    (κ : Cardinal.{max u v w}) (hκ : aleph0 ≤ κ)
    (hι : lift.{max v w} (mk ι) ≤ κ)
    (hf : ∀ i, lift.{max u w} (f i) ≤ κ) : lift.{w} (sum f) ≤ κ := by
  rw [← lift_id'.{u, max v w} (lift.{w} (sum f)), lift_sum, lift_sum]
  simp_rw [lift_lift.{v, w, u}]
  calc
    _ ≤ sum (fun _ : ι => κ) := sum_le_sum _ _ hf
    _ ≤ κ := by
      rw [sum_const, lift_id'.{u, max v w}, lift_umax.{u, max v w}]
      exact (mul_le_mul' hι le_rfl).trans (mul_eq_self hκ).le

end Cardinal
