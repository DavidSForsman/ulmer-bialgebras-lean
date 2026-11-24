module

public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Order.CompletePartialOrder

/-!
# Lifting freeness along a filtration

This file contains the purely filtration-theoretic step of Sweedler's freeness theorem: the
passage from a *graded* basis to an honest module basis.

Let `H` be a `k`-algebra carrying an increasing filtration `F : ℕ → Submodule k H` which exhausts
a submodule `M`, let `A ⊆ H` be a subalgebra and let `b : ι → H` be a family of elements with
prescribed degrees `d : ι → ℕ`.  Write

```
coefSub A F d n j = A ⊓ F (n - d j)      (and `⊥` when `d j > n`)
```

for the space of coefficients of degree at most `n - d j`.  The two hypotheses

* **graded spanning** `F n ≤ ⨆ j, coefSub A F d n j · b j`, and
* **graded independence** `∑ aⱼ bⱼ ∈ F n` forces every coefficient of degree `≤ n + 1 - d j`
  to have degree `≤ n - d j`,

say exactly that the images of the `b j` form a basis of the associated graded module `gr M` over
`gr A`.  The main results of this file deduce from them that the `b j` are an honest basis of `M`
as a left `A`-module.

Nothing here is specific to Hopf algebras: the input is an algebra with a filtration.

## Main results

* `Module.FilteredFree.eq_zero_of_graded_independent` — independence;
* `Module.FilteredFree.iSup_translate_eq` — spanning;
* `Module.FilteredFree.leftBasis_of_graded` — the two statements together, in the shape of a
  left-basis statement.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [D. E. Radford, *Pointed Hopf algebras are free over Hopf
  subalgebras*][radfordPointedHopfAlgebras1977]
-/

@[expose] public section

section
namespace Module.FilteredFree

variable {k H ι : Type*} [Field k] [Ring H] [Algebra k H]

/-- The space of admissible coefficients of `b j` in filtration degree `n`: the elements of the
subalgebra `A` of filtration degree at most `n - d j`, and `0` if `d j > n`. -/
noncomputable def coefSub (A : Subalgebra k H) (F : ℕ → Submodule k H) (d : ι → ℕ) (n : ℕ)
    (j : ι) : Submodule k H :=
  if d j ≤ n then Subalgebra.toSubmodule A ⊓ F (n - d j) else ⊥

/-- The admissible coefficients `coefSub A F d n j` lie in `A`. -/
theorem coefSub_le_A {A : Subalgebra k H} {F : ℕ → Submodule k H} {d : ι → ℕ} (n : ℕ) (j : ι) :
    coefSub A F d n j ≤ Subalgebra.toSubmodule A := by
  unfold coefSub
  split
  · exact inf_le_left
  · exact bot_le

/-- An element of `A` of filtration degree at most `n - d j`, with `d j ≤ n`, lies in
`coefSub A F d n j`. -/
theorem mem_coefSub {A : Subalgebra k H} {F : ℕ → Submodule k H} {d : ι → ℕ} {n : ℕ} {j : ι}
    {x : H} (hA : x ∈ A) (hd : d j ≤ n) (hF : x ∈ F (n - d j)) : x ∈ coefSub A F d n j := by
  unfold coefSub
  rw [ite_eq_left hd]
  exact ⟨hA, hF⟩

/-- If coefficients `a j ∈ coefSub A F d 0 j` with `∑ a j * b j = 0` vanish (`h0`), and
coefficients in `coefSub A F d (n + 1) j` whose combination lies in `F n` lie in
`coefSub A F d n j` (`hstep`), then for every `n`, coefficients `a j ∈ coefSub A F d n j` with
`∑ a j * b j = 0` vanish. -/
theorem eq_zero_of_coefSub {A : Subalgebra k H} {F : ℕ → Submodule k H} {d : ι → ℕ} {b : ι → H}
    (h0 : ∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d 0 j) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0)
    (hstep : ∀ (n : ℕ) (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d (n + 1) j) →
      ∑ j ∈ s, a j * b j ∈ F n → ∀ j ∈ s, a j ∈ coefSub A F d n j) :
    ∀ (n : ℕ) (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d n j) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0 := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
      intro s a ha hsum
      refine ih s a (hstep n s a ha ?_) hsum
      rw [hsum]
      exact (F n).zero_mem

/-- **Independence.**  Under graded independence, a vanishing `A`-linear combination of the `b j`
has all coefficients zero. -/
theorem eq_zero_of_graded_independent {A : Subalgebra k H} {F : ℕ → Submodule k H}
    {M : Submodule k H}
    {d : ι → ℕ} {b : ι → H}
    (hmono : Monotone F) (hM : ⨆ n, F n = M) (hAM : Subalgebra.toSubmodule A ≤ M)
    (h0 : ∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d 0 j) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0)
    (hstep : ∀ (n : ℕ) (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d (n + 1) j) →
      ∑ j ∈ s, a j * b j ∈ F n → ∀ j ∈ s, a j ∈ coefSub A F d n j)
    (s : Finset ι) (a : ι → H) (ha : ∀ j ∈ s, a j ∈ A) (hsum : ∑ j ∈ s, a j * b j = 0) :
    ∀ j ∈ s, a j = 0 := by
  classical
  -- every coefficient lies in some stage of the filtration
  have hdir : Directed (· ≤ ·) F := hmono.directed_le
  have hmem : ∀ j ∈ s, ∃ m, a j ∈ F m := by
    intro j hj
    have : a j ∈ M := hAM (ha j hj)
    rw [← hM, Submodule.mem_iSup_of_directed _ hdir] at this
    exact this
  choose m hm using hmem
  set N : ℕ := s.attach.sup (fun j => m j.1 j.2) with hN
  set D : ℕ := s.sup d with hD
  have hmemN : ∀ j (hj : j ∈ s), a j ∈ F N := by
    intro j hj
    exact hmono
        (Finset.le_sup (f := fun j : {x // x ∈ s} => m j.1 j.2) (Finset.mem_attach _ ⟨j, hj⟩))
      (hm j hj)
  refine eq_zero_of_coefSub h0 hstep (N + D) s a (fun j hj => ?_) hsum
  refine mem_coefSub (ha j hj) (le_trans (Finset.le_sup hj) (Nat.le_add_left _ _)) ?_
  refine hmono ?_ (hmemN j hj)
  have : d j ≤ D := Finset.le_sup hj
  omega

/-- **Spanning.**  Under graded spanning, the translates `A · b j` fill up `M`. -/
theorem iSup_translate_eq {A : Subalgebra k H} {F : ℕ → Submodule k H} {M : Submodule k H}
    {d : ι → ℕ} {b : ι → H}
    (hM : ⨆ n, F n = M) (hbM : ∀ j, b j ∈ M)
    (hMmul : ∀ x ∈ Subalgebra.toSubmodule A, ∀ y ∈ M, x * y ∈ M)
    (hspan : ∀ n, F n ≤ ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j)) (coefSub A F d n j)) :
    M = ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A) := by
  refine le_antisymm ?_ ?_
  · rw [← hM]
    refine iSup_le fun n => le_trans (hspan n) (iSup_mono fun j => ?_)
    exact Submodule.map_mono (coefSub_le_A n j)
  · refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hMmul x hx _ (hbM j)

/-- **From a graded basis to a basis.** Let `F` be a monotone filtration with union `M`, with
`A ≤ M`, `A • M ≤ M`, `b j ∈ F (d j)`, each `F n` spanned by the `coefSub A F d n j • b j`
(`hspan`), and the independence conditions `h0` and `hstep`. Then every `b j` lies in `M`, `M` is
the sum of the `A • b j`, and the `b j` are independent over `A`: coefficients `a j ∈ A` with
`∑ a j * b j = 0` vanish. -/
theorem leftBasis_of_graded {A : Subalgebra k H} {F : ℕ → Submodule k H} {M : Submodule k H}
    {d : ι → ℕ} {b : ι → H}
    (hmono : Monotone F) (hM : ⨆ n, F n = M) (hAM : Subalgebra.toSubmodule A ≤ M)
    (hbF : ∀ j, b j ∈ F (d j))
    (hMmul : ∀ x ∈ Subalgebra.toSubmodule A, ∀ y ∈ M, x * y ∈ M)
    (hspan : ∀ n, F n ≤ ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j)) (coefSub A F d n j))
    (h0 : ∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d 0 j) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0)
    (hstep : ∀ (n : ℕ) (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A F d (n + 1) j) →
      ∑ j ∈ s, a j * b j ∈ F n → ∀ j ∈ s, a j ∈ coefSub A F d n j) :
    (∀ j, b j ∈ M) ∧
      (M = ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A)) ∧
      (∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ A) →
        ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0) := by
  have hbM : ∀ j, b j ∈ M := fun j => by
    have : F (d j) ≤ M := hM ▸ le_iSup F (d j)
    exact this (hbF j)
  exact ⟨hbM, iSup_translate_eq hM hbM hMmul hspan,
    fun s a ha hsum => eq_zero_of_graded_independent hmono hM hAM h0 hstep s a ha hsum⟩

end Module.FilteredFree
end
