module

public import Hopf.Graded.GrGrading

/-!
# The homogeneous projections of the associated graded algebra

`S.hproj N = cmp N ∘ emb` is the projection of `S.Gr` onto its degree-`N` part.  The point of
this file is the identity

```
hproj N (g * y) = hproj (N - q) g * y      (y homogeneous of degree q ≤ N),
hproj N (g * y) = 0                        (y homogeneous of degree q > N),
```

which is what makes it possible to choose *homogeneous coefficients* when expanding a homogeneous
element in a homogeneous basis.

## Main results

* `HopfAlgebra.Graded.HopfSplit.hproj`: the projection `cmp N ∘ emb` of `S.Gr` onto its degree-`N`
  part.
* `HopfAlgebra.Graded.HopfSplit.hproj_mul`: for `y` homogeneous of degree `q ≤ N`,
  `hproj N (g * y) = hproj (N - q) g * y`.
* `HopfAlgebra.Graded.HopfSplit.hproj_mul_of_lt`: for `y` homogeneous of degree `q > N`,
  `hproj N (g * y) = 0`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)

/-- The projection of `S.Gr` onto its degree-`N` part. -/
noncomputable def hproj (N : ℕ) : S.Gr →ₗ[k] S.Gr := S.cmp N ∘ₗ S.emb

/-- Unfolding `hproj`: `hproj N g = cmp N (emb g)`. -/
theorem hproj_apply (N : ℕ) (g : S.Gr) : S.hproj N g = S.cmp N (S.emb g) := rfl

/-- If `pr n x = 0` then `cmp n x = 0`. -/
theorem cmp_eq_zero_of_pr_eq_zero {n : ℕ} {x : H} (h : S.pr n x = 0) : S.cmp n x = 0 := by
  rw [← S.cmp_pr, h, map_zero]

variable {S}

/-- `hproj N` is the identity on the homogeneous piece `grPiece N`. -/
theorem hproj_eq_self {N : ℕ} {g : S.Gr} (hg : g ∈ S.grPiece N) : S.hproj N g = g :=
  (eq_cmp_emb hg).symm

/-- `hproj N` vanishes on the homogeneous piece `grPiece m` for `m ≠ N`. -/
theorem hproj_eq_zero_of_mem_ne {N m : ℕ} {g : S.Gr} (hg : g ∈ S.grPiece m) (h : m ≠ N) :
    S.hproj N g = 0 := by
  rw [hproj_apply]
  exact S.cmp_eq_zero_of_pr_eq_zero (S.toSplit.pr_of_mem_C (Ne.symm h) hg)

/-- For `y` homogeneous of degree `q ≤ N`: `hproj N (g * y) = hproj (N - q) g * y`. -/
theorem hproj_mul {N q : ℕ} (hqN : q ≤ N) (g : S.Gr) {y : S.Gr} (hy : y ∈ S.grPiece q) :
    S.hproj N (g * y) = S.hproj (N - q) g * y := by
  refine S.induction_on (motive := fun g => S.hproj N (g * y) = S.hproj (N - q) g * y) g ?_ ?_ ?_
  · rw [S.zero_mul', LinearMap.map_zero, LinearMap.map_zero, S.zero_mul']
  · intro m a
    have hg : S.ofC m a ∈ S.grPiece m := S.ofC_mem_grPiece m a
    by_cases h : m = N - q
    · subst h
      have hmem : S.ofC (N - q) a * y ∈ S.grPiece N := by
        have hmul := grPiece_mul hg hy
        rwa [show N - q + q = N by omega] at hmul
      rw [hproj_eq_self hg, hproj_eq_self hmem]
    · have hne : m + q ≠ N := by omega
      rw [hproj_eq_zero_of_mem_ne (grPiece_mul hg hy) hne,
        hproj_eq_zero_of_mem_ne hg h, S.zero_mul']
  · intro x z hx hz
    rw [S.add_mul', map_add, map_add, hx, hz, S.add_mul']

/-- For `y` homogeneous of degree `q > N`: `hproj N (g * y) = 0`. -/
theorem hproj_mul_of_lt {N q : ℕ} (hqN : N < q) (g : S.Gr) {y : S.Gr} (hy : y ∈ S.grPiece q) :
    S.hproj N (g * y) = 0 := by
  refine S.induction_on (motive := fun g => S.hproj N (g * y) = 0) g ?_ ?_ ?_
  · rw [S.zero_mul', LinearMap.map_zero]
  · intro m a
    have hg : S.ofC m a ∈ S.grPiece m := S.ofC_mem_grPiece m a
    exact hproj_eq_zero_of_mem_ne (grPiece_mul hg hy) (by omega)
  · intro x z hx hz
    rw [S.add_mul', map_add, hx, hz, add_zero]

end HopfSplit

end HopfAlgebra.Graded
