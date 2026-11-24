module

public import Hopf.Graded.AssocGradedHopf

/-!
# The tautological grading of the associated graded Hopf algebra

Let `S : HopfAlgebra.Graded.HopfSplit k H`. The associated graded object `S.Gr = ⨁ₙ Cₙ` is a
commutative Hopf `k`-algebra (`Hopf/Graded/AssocGradedHopf.lean`). This file records its
tautological `ℕ`-grading

```
grPiece n = { g | emb g ∈ Cₙ }  =  range (ofC n) ,
```

the `DirectSum.Decomposition` instance for it, and the fact that the grading is multiplicative.
Working with `grPiece n` as a *comap* along the (injective) embedding `emb : S.Gr →ₗ H` makes
membership completely transparent.

## Main results

* `HopfAlgebra.Graded.HopfSplit.grPiece`: the degree-`n` part `{ g | emb g ∈ Cₙ }` of `S.Gr`.
* `HopfAlgebra.Graded.HopfSplit.grPiece_mul`: the product of elements of degrees `i` and `j` has
  degree `i + j`.
* `HopfAlgebra.Graded.HopfSplit.instDecompositionGrPiece`: the `DirectSum.Decomposition` instance
  for `grPiece`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)

/-- The degree-`n` part of the tautological grading of `S.Gr`. -/
def grPiece (n : ℕ) : Submodule k S.Gr := Submodule.comap S.emb (S.C n)

/-- Membership in `grPiece n` is membership of `emb g` in `Cₙ`. -/
@[simp] theorem mem_grPiece {n : ℕ} {g : S.Gr} : g ∈ S.grPiece n ↔ S.emb g ∈ S.C n := Iff.rfl

/-- `cmp n x` is homogeneous of degree `n`. -/
theorem cmp_mem_grPiece (n : ℕ) (x : H) : S.cmp n x ∈ S.grPiece n := by
  rw [mem_grPiece, S.emb_cmp]
  exact S.toSplit.pr_mem_C n x

/-- `ofC n a` is homogeneous of degree `n`. -/
theorem ofC_mem_grPiece (n : ℕ) (a : ↥(S.C n)) : S.ofC n a ∈ S.grPiece n := by
  rw [S.ofC_eq_cmp]
  exact S.cmp_mem_grPiece n _

variable {S}

/-- A homogeneous element `g` of degree `n` equals `cmp n (emb g)`. -/
theorem eq_cmp_emb {n : ℕ} {g : S.Gr} (hg : g ∈ S.grPiece n) : g = S.cmp n (S.emb g) := by
  refine S.emb_injective ?_
  rw [S.emb_cmp, S.toSplit.pr_eq_self_of_mem_C hg]

/-- The product of homogeneous elements of degrees `i`, `j` has degree `i + j`. -/
theorem grPiece_mul {i j : ℕ} {x y : S.Gr} (hx : x ∈ S.grPiece i) (hy : y ∈ S.grPiece j) :
    x * y ∈ S.grPiece (i + j) := by
  rw [eq_cmp_emb hx, eq_cmp_emb hy,
    S.cmp_mul_cmp (S.c_le_f i hx) (S.c_le_f j hy)]
  exact S.cmp_mem_grPiece _ _

variable (S)

/-- `1` is homogeneous of degree `0`. -/
theorem one_mem_grPiece : (1 : S.Gr) ∈ S.grPiece 0 := by
  rw [S.one_def]
  exact S.cmp_mem_grPiece 0 1

/-! ### The decomposition -/

/-- `Cₙ` and the degree-`n` piece of `S.Gr` are the same thing. -/
noncomputable def toGrPiece (n : ℕ) : ↥(S.C n) →ₗ[k] ↥(S.grPiece n) :=
  LinearMap.codRestrict _ (S.ofC n) (S.ofC_mem_grPiece n)

/-- The decomposition map of the tautological grading. -/
noncomputable def decomposeGr : S.Gr →ₗ[k] DirectSum ℕ (fun n => ↥(S.grPiece n)) :=
  DirectSum.toModule k ℕ _
    (fun n => (DirectSum.lof k ℕ (fun i => ↥(S.grPiece i)) n) ∘ₗ S.toGrPiece n)

/-- `decomposeGr (ofC n a)` is `toGrPiece n a` placed in degree `n`. -/
theorem decomposeGr_ofC (n : ℕ) (a : ↥(S.C n)) :
    S.decomposeGr (S.ofC n a)
      = DirectSum.lof k ℕ (fun i => ↥(S.grPiece i)) n (S.toGrPiece n a) :=
  DirectSum.toModule_lof k
    (φ := fun i => (DirectSum.lof k ℕ (fun i => ↥(S.grPiece i)) i) ∘ₗ S.toGrPiece i) n a

/-- `Gr` decomposes as the direct sum of its homogeneous pieces `grPiece n`. -/
noncomputable instance instDecompositionGrPiece : DirectSum.Decomposition S.grPiece where
  decompose' := S.decomposeGr
  left_inv := by
    intro g
    refine S.induction_on (motive := fun g =>
      DirectSum.coeAddMonoidHom S.grPiece (S.decomposeGr g) = g) g ?_ (fun n a => ?_)
      (fun x y hx hy => by
        simp only [map_add] at hx hy ⊢
        rw [hx, hy])
    · simp only [map_zero]
    · rw [S.decomposeGr_ofC, DirectSum.lof_eq_of, DirectSum.coeAddMonoidHom_of]
      rfl
  right_inv := by
    intro v
    induction v using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n g =>
        have hg : (g : S.Gr) ∈ S.grPiece n := g.2
        have hcoe : DirectSum.coeAddMonoidHom S.grPiece
            (DirectSum.of (fun i => ↥(S.grPiece i)) n g) = (g : S.Gr) :=
          DirectSum.coeAddMonoidHom_of S.grPiece n g
        rw [hcoe]
        have hgc : (g : S.Gr) = S.ofC n ⟨S.emb g, hg⟩ := by
          rw [← S.cmp_eq_ofC hg]
          exact eq_cmp_emb hg
        rw [hgc, S.decomposeGr_ofC]
        have heq : S.toGrPiece n ⟨S.emb g, hg⟩ = g := Subtype.ext hgc.symm
        rw [heq]
        rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]

end HopfSplit

end HopfAlgebra.Graded
