module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Hopf.Graded.GrSubalgebra

/-!
# The grading of the associated graded subalgebra

Continuing `Hopf/Graded/GrSubalgebra.lean`, this file equips the associated graded
subalgebra `gr A ⊆ S.Gr` with its `ℕ`-grading, produces the `GradedAlgebra` instance and the
compatibility `SetLike.GradedSMul` with the tautological grading of `S.Gr`, and proves that
`gr A` is *connected*: its degree-zero part consists of scalars.

## Main results

* `HopfAlgebra.Graded.HopfSplit.grAGrading`: the `ℕ`-grading of `gr A`, pulled back from that of
  `S.Gr`.
* `HopfAlgebra.Graded.HopfSplit.gradedAlgebraGrA`: the `GradedAlgebra` structure of this grading.
* `HopfAlgebra.Graded.HopfSplit.gradedSMul_grAGrading`: compatibility with the tautological grading
  of `S.Gr`.
* `HopfAlgebra.Graded.HopfSplit.grAGrading_zero_scalar`: every element of degree zero of `gr A` is a
  scalar.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra

namespace HopfAlgebra.Graded

namespace HopfSplit

/-- The comap of an independent family of submodules along an injective linear map is
independent. -/
theorem iSupIndep_comap {k M N : Type u} [Field k] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] {f : M →ₗ[k] N} (hf : Function.Injective f)
    {p : ℕ → Submodule k N} (h : iSupIndep p) :
    iSupIndep (fun i => Submodule.comap f (p i)) := by
  rw [iSupIndep_def] at h ⊢
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  have h1 : f x ∈ p i := hx.1
  have h2 : f x ∈ ⨆ j, ⨆ _ : j ≠ i, p j := by
    have hle : Submodule.map f (⨆ j, ⨆ _ : j ≠ i, Submodule.comap f (p j))
        ≤ ⨆ j, ⨆ _ : j ≠ i, p j := by
      rw [Submodule.map_iSup]
      refine iSup_le fun j => ?_
      rw [Submodule.map_iSup]
      exact iSup_le fun hj =>
        le_trans (Submodule.map_comap_le f (p j)) (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
    exact hle ⟨x, hx.2, rfl⟩
  have hfx : f x = 0 := by simpa using (h i).le_bot ⟨h1, h2⟩
  have hx0 : x = 0 := hf (by rw [hfx, map_zero])
  simp [hx0]

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] {S : HopfSplit k H}
  {A : Subalgebra k H} (hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A) (h1A : (1 : H) ∈ A)

/-- The `ℕ`-grading of the associated graded subalgebra. -/
def grAGrading (n : ℕ) : Submodule k ↥(S.grSub A hprA h1A) :=
  Submodule.comap (S.grSub A hprA h1A).val.toLinearMap (S.grPiece n)

/-- The range of the inclusion of `grSub A hprA h1A` into `S.Gr` is `grSubmodule A`. -/
theorem range_grSub_val :
    LinearMap.range (S.grSub A hprA h1A).val.toLinearMap = S.grSubmodule A := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The homogeneous pieces `grPiece n` of `S.Gr` are independent. -/
theorem iSupIndep_grPiece : iSupIndep S.grPiece :=
  ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top S.grPiece).1
    (DirectSum.Decomposition.isInternal S.grPiece)).1

/-- The pieces `grAGrading hprA h1A n` are independent. -/
theorem iSupIndep_grAGrading : iSupIndep (grAGrading hprA h1A) :=
  iSupIndep_comap (f := (S.grSub A hprA h1A).val.toLinearMap) Subtype.val_injective
    iSupIndep_grPiece

/-- The pieces `grAGrading hprA h1A n` span: `⨆ n, grAGrading hprA h1A n = ⊤`. -/
theorem iSup_grAGrading : (⨆ n, grAGrading hprA h1A n) = ⊤ := by
  refine Submodule.map_injective_of_injective
    (f := (S.grSub A hprA h1A).val.toLinearMap) Subtype.val_injective ?_
  rw [Submodule.map_iSup, Submodule.map_top, range_grSub_val]
  have hmap : ∀ n : ℕ, Submodule.map (S.grSub A hprA h1A).val.toLinearMap
      (grAGrading hprA h1A n) = S.grAPiece A n := by
    intro n
    rw [grAGrading, Submodule.map_comap_eq, range_grSub_val, grAPiece, inf_comm]
  simp only [hmap]
  exact (grSubmodule_eq_iSup hprA).symm

/-- The decomposition of `gr A` into its homogeneous parts. -/
@[instance_reducible]
noncomputable def decompositionGrA : DirectSum.Decomposition (grAGrading hprA h1A) :=
  DirectSum.IsInternal.chooseDecomposition _
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
      ⟨iSupIndep_grAGrading hprA h1A, iSup_grAGrading hprA h1A⟩)

/-- `grAGrading hprA h1A` is a graded monoid: `1` has degree `0` and degrees add under
multiplication. -/
theorem gradedMonoid_grAGrading : SetLike.GradedMonoid (grAGrading hprA h1A) where
  one_mem := show (1 : S.Gr) ∈ S.grPiece 0 from S.one_mem_grPiece
  mul_mem := fun {i j gi gj} hi hj =>
    show ((gi * gj : ↥(S.grSub A hprA h1A)) : S.Gr) ∈ S.grPiece (i + j) by
      rw [Subalgebra.coe_mul]
      exact grPiece_mul hi hj

/-- **The associated graded subalgebra is a graded algebra.** -/
@[instance_reducible]
noncomputable def gradedAlgebraGrA : GradedAlgebra (grAGrading hprA h1A) :=
  { gradedMonoid_grAGrading hprA h1A, decompositionGrA hprA h1A with }

/-- The grading of `gr A` is compatible with the grading of `S.Gr` under left multiplication: `gr A`
of degree `i` times `grPiece j` lies in `grPiece (i + j)`. -/
theorem gradedSMul_grAGrading : SetLike.GradedSMul (grAGrading hprA h1A) S.grPiece where
  smul_mem := fun {i j} {ai bj} hi hj =>
    show (ai : S.Gr) * bj ∈ S.grPiece (i + j) from grPiece_mul hi hj

/-- **Connectivity**: the degree-zero part of `gr A` consists of the scalars. -/
theorem grAGrading_zero_scalar (a : ↥(S.grSub A hprA h1A)) (ha : a ∈ grAGrading hprA h1A 0) :
    ∃ c : k, a = algebraMap k ↥(S.grSub A hprA h1A) c := by
  have ha' : (a : S.Gr) ∈ S.grPiece 0 := ha
  obtain ⟨c, hc⟩ := S.exists_smul_one_of_mem_F_zero (S.c_le_f 0 ha')
  refine ⟨c, Subtype.ext ?_⟩
  have hval : ((algebraMap k ↥(S.grSub A hprA h1A) c : ↥(S.grSub A hprA h1A)) : S.Gr)
      = algebraMap k S.Gr c := rfl
  rw [hval, S.algebraMap_eq, ← hc]
  exact eq_cmp_emb ha'

end HopfSplit

end HopfAlgebra.Graded
