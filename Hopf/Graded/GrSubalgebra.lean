module

public import Hopf.Graded.GrGrading

/-!
# The associated graded subalgebra

Let `S : HopfAlgebra.Graded.HopfSplit k H` and let `A` be a subalgebra of `H` which is preserved by
the projections of the splitting. Its **associated graded**

```
gr A = { g ∈ S.Gr | emb g ∈ A }
```

is a graded subalgebra of `S.Gr`.  This file constructs it, together with its grading and the
resulting `GradedAlgebra` instance, and proves that it is *connected* when the filtration is.

## Main results

* `HopfAlgebra.Graded.HopfSplit.grSubmodule`: the submodule `{ g ∈ S.Gr | emb g ∈ A }`.
* `HopfAlgebra.Graded.HopfSplit.grSubmodule_eq_iSup`: if the projections preserve `A`, then `gr A`
  is the supremum of its homogeneous parts.
* `HopfAlgebra.Graded.HopfSplit.grSub`: `gr A`, as a subalgebra of `S.Gr`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)
  (A : Subalgebra k H)

/-- The associated graded of a subalgebra `A ⊆ H`, as a submodule of `S.Gr`. -/
def grSubmodule : Submodule k S.Gr := Submodule.comap S.emb (Subalgebra.toSubmodule A)

/-- The degree-`n` part of `gr A`. -/
def grAPiece (n : ℕ) : Submodule k S.Gr := S.grPiece n ⊓ S.grSubmodule A

variable {S A}

/-- Membership in `grSubmodule A` is membership of `emb x` in `A`. -/
@[simp] theorem mem_grSubmodule {x : S.Gr} : x ∈ S.grSubmodule A ↔ S.emb x ∈ A := Iff.rfl

/-- `⨆ n, grAPiece A n ≤ grSubmodule A`. -/
theorem iSup_grAPiece_le : (⨆ n, S.grAPiece A n) ≤ S.grSubmodule A :=
  iSup_le fun _ => inf_le_right

/-! ### Homogeneous decompositions -/

/-- If `∑ i ∈ s, t i = g` with each `t i ∈ grPiece i` and `j ∈ s`, then
`emb (t j) = pr j (emb g)`. -/
theorem emb_eq_pr_of_homogeneous_sum {s : Finset ℕ} {t : ℕ → S.Gr}
    (ht : ∀ i, t i ∈ S.grPiece i) {g : S.Gr} (hg : ∑ i ∈ s, t i = g) {j : ℕ} (hj : j ∈ s) :
    S.emb (t j) = S.pr j (S.emb g) := by
  subst hg
  rw [map_sum, map_sum, Finset.sum_eq_single j]
  · rw [S.toSplit.pr_eq_self_of_mem_C (ht j)]
  · intro i _ hij
    exact S.toSplit.pr_of_mem_C (Ne.symm hij) (ht i)
  · intro h
    exact absurd hj h

/-- If the projections `pr n` preserve `A`, then `gr A` is the sum of its homogeneous parts:
`grSubmodule A = ⨆ n, grAPiece A n`. -/
theorem grSubmodule_eq_iSup (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) :
    S.grSubmodule A = ⨆ n, S.grAPiece A n := by
  classical
  refine le_antisymm (fun g hg => ?_) iSup_grAPiece_le
  have hsum := DirectSum.sum_support_decompose S.grPiece g
  have htmem : ∀ i, ((DirectSum.decompose S.grPiece g i : ↥(S.grPiece i)) : S.Gr) ∈ S.grPiece i :=
    fun i => (DirectSum.decompose S.grPiece g i).2
  rw [← hsum]
  refine Submodule.sum_mem _ fun j hj => Submodule.mem_iSup_of_mem j ⟨htmem j, ?_⟩
  rw [SetLike.mem_coe, mem_grSubmodule, emb_eq_pr_of_homogeneous_sum htmem hsum hj]
  exact hprA j _ hg

/-! ### Multiplicativity -/

/-- For `x ∈ grPiece m` and `y ∈ grPiece n`, `emb (x * y) = pr (m + n) (emb x * emb y)`. -/
theorem emb_mul_homogeneous {m n : ℕ} {x y : S.Gr} (hx : x ∈ S.grPiece m) (hy : y ∈ S.grPiece n) :
    S.emb (x * y) = S.pr (m + n) (S.emb x * S.emb y) := by
  have hx' := eq_cmp_emb hx
  have hy' := eq_cmp_emb hy
  calc S.emb (x * y) = S.emb (S.cmp m (S.emb x) * S.cmp n (S.emb y)) := by rw [← hx', ← hy']
    _ = S.emb (S.cmp (m + n) (S.emb x * S.emb y)) := by
        rw [S.cmp_mul_cmp (S.c_le_f m hx) (S.c_le_f n hy)]
    _ = S.pr (m + n) (S.emb x * S.emb y) := S.emb_cmp _ _

/-- If every `pr n` maps `A` into `A`, then `x ∈ grAPiece A m` and `y ∈ grAPiece A n` give
`x * y ∈ grAPiece A (m + n)`. -/
theorem grAPiece_mul (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) {m n : ℕ} {x y : S.Gr}
    (hx : x ∈ S.grAPiece A m) (hy : y ∈ S.grAPiece A n) : x * y ∈ S.grAPiece A (m + n) :=
  ⟨grPiece_mul hx.1 hy.1, by
    rw [SetLike.mem_coe, mem_grSubmodule, emb_mul_homogeneous hx.1 hy.1]
    exact hprA _ _ (A.mul_mem (show S.emb x ∈ A from hx.2) (show S.emb y ∈ A from hy.2))⟩

/-- If every `pr n` maps `A` into `A`, then `grSubmodule A` is closed under multiplication. -/
theorem mul_mem_grSubmodule (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) (x y : S.Gr)
    (hx : x ∈ S.grSubmodule A) (hy : y ∈ S.grSubmodule A) : x * y ∈ S.grSubmodule A := by
  rw [grSubmodule_eq_iSup hprA] at hx hy ⊢
  refine Submodule.iSup_induction (motive := fun x => ∀ y ∈ ⨆ n, S.grAPiece A n,
    x * y ∈ ⨆ n, S.grAPiece A n) _ hx ?_ ?_ ?_ y hy
  · intro m x hxm y hy
    refine Submodule.iSup_induction (motive := fun y => x * y ∈ ⨆ n, S.grAPiece A n)
      _ hy ?_ ?_ ?_
    · intro n y hyn
      exact Submodule.mem_iSup_of_mem (m + n) (grAPiece_mul hprA hxm hyn)
    · rw [mul_zero]
      exact Submodule.zero_mem _
    · intro y z hy' hz'
      rw [mul_add]
      exact Submodule.add_mem _ hy' hz'
  · intro y _
    rw [zero_mul]
    exact Submodule.zero_mem _
  · intro x z hx' hz' y hy
    rw [add_mul]
    exact Submodule.add_mem _ (hx' y hy) (hz' y hy)

/-- If `1 ∈ A` then `1 ∈ grSubmodule A`. -/
theorem one_mem_grSubmodule (h1A : (1 : H) ∈ A) : (1 : S.Gr) ∈ S.grSubmodule A := by
  rw [mem_grSubmodule, S.one_def, S.emb_cmp, S.toSplit.pr_zero_of_mem_F_zero S.one_mem]
  exact h1A

variable (S A) in
/-- **The associated graded subalgebra** `gr A ⊆ S.Gr`. -/
def grSub (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) (h1A : (1 : H) ∈ A) : Subalgebra k S.Gr :=
  Submodule.toSubalgebra (S.grSubmodule A) (one_mem_grSubmodule h1A) (mul_mem_grSubmodule hprA)

end HopfSplit

end HopfAlgebra.Graded
