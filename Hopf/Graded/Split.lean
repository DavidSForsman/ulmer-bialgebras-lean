module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.CompletePartialOrder

/-!
# Split filtrations

Over a field every increasing filtration `F : ℕ → Submodule k H` of a module can be *split*: one can
choose a family of projections `pr n : H →ₗ[k] H` onto complements `C n` of `F (n-1)` in `F n`. This
file introduces the corresponding bundled structure `HopfAlgebra.Graded.Split` and its basic
calculus.

The point of carrying the projections around is that the associated graded module of `F` can
then be realised concretely, as `⨁ n, C n`, with *no* quotient constructions and hence with no
well-definedness obligations: see `Hopf/Graded/AssocGraded.lean`.

## Main definitions

* `HopfAlgebra.Graded.Split k H` — a filtration `F` together with a compatible family of
  projections;
* `HopfAlgebra.Graded.Split.C` — the homogeneous complements `C n = range (pr n)`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

namespace HopfAlgebra.Graded

variable {k H : Type u} [Field k] [AddCommGroup H] [Module k H]

/-- A **split filtration** of a `k`-module `H`: an increasing filtration `F` together with
projections `pr n` onto complements of `F (n-1)` in `F n`. -/
structure Split (k H : Type u) [Field k] [AddCommGroup H] [Module k H] where
  /-- the filtration -/
  F : ℕ → Submodule k H
  /-- the projection onto the `n`-th graded piece -/
  pr : ℕ → (H →ₗ[k] H)
  /-- the filtration is increasing -/
  mono : Monotone F
  /-- `pr n` takes values in `F n` -/
  pr_mem : ∀ n x, pr n x ∈ F n
  /-- `pr n` kills everything of filtration degree `< n` -/
  pr_of_mem_lt : ∀ {m n : ℕ}, m < n → ∀ x ∈ F m, pr n x = 0
  /-- the projections are orthogonal idempotents -/
  pr_pr : ∀ (m n : ℕ) (x : H), pr m (pr n x) = if m = n then pr n x else 0
  /-- they sum to the identity on each filtration step -/
  sum_pr : ∀ (n : ℕ) (x : H), x ∈ F n → ∑ i ∈ Finset.range (n + 1), pr i x = x

namespace Split

variable (S : Split k H)

/-- The `n`-th homogeneous complement. -/
def C (n : ℕ) : Submodule k H := LinearMap.range (S.pr n)

/-- `pr n x` lies in the homogeneous complement `C n`. -/
theorem pr_mem_C (n : ℕ) (x : H) : S.pr n x ∈ S.C n := ⟨x, rfl⟩

/-- The homogeneous complement is contained in the filtration step: `C n ≤ F n`. -/
theorem c_le_f (n : ℕ) : S.C n ≤ S.F n := by
  rintro _ ⟨y, rfl⟩; exact S.pr_mem n y

/-- Each projection is idempotent: `pr n (pr n x) = pr n x`. -/
@[simp] theorem pr_self (n : ℕ) (x : H) : S.pr n (S.pr n x) = S.pr n x := by
  simpa using S.pr_pr n n x

/-- `pr n` is the identity on `C n`. -/
theorem pr_eq_self_of_mem_C {n : ℕ} {x : H} (hx : x ∈ S.C n) : S.pr n x = x := by
  obtain ⟨y, rfl⟩ := hx; exact S.pr_self n y

/-- For `m ≠ n`, `pr m` vanishes on `C n`. -/
theorem pr_of_mem_C {m n : ℕ} (hmn : m ≠ n) {x : H} (hx : x ∈ S.C n) : S.pr m x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  simpa [hmn] using S.pr_pr m n y

/-- `pr 0` is the identity on `F 0`. -/
theorem pr_zero_of_mem_F_zero {x : H} (hx : x ∈ S.F 0) : S.pr 0 x = x := by
  simpa using S.sum_pr 0 x hx

/-- Subtracting the top graded part drops the filtration degree. -/
theorem sub_pr_mem {n : ℕ} {x : H} (hx : x ∈ S.F (n + 1)) :
    x - S.pr (n + 1) x ∈ S.F n := by
  have h := S.sum_pr (n + 1) x hx
  rw [Finset.sum_range_succ] at h
  rw [← eq_sub_of_add_eq h]
  refine Submodule.sum_mem _ fun i hi => ?_
  exact S.mono (by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (S.pr_mem i x)

/-- An element of `F n` killed by `pr n` has filtration degree `< n`. -/
theorem mem_F_pred_of_pr_eq_zero {n : ℕ} {x : H} (hx : x ∈ S.F (n + 1))
    (h : S.pr (n + 1) x = 0) : x ∈ S.F n := by
  have := S.sub_pr_mem hx
  simpa [h] using this

end Split

end HopfAlgebra.Graded
