module

public import Hopf.Graded.AssocGraded

/-!
# The graded component maps on tensor powers

Let `S : HopfAlgebra.Graded.HopfSplit k H` be a split filtration of a Hopf algebra as in
`Hopf/Graded/AssocGraded.lean`, with associated graded algebra `S.Gr = ⨁ₙ Cₙ`.

To equip `S.Gr` with its coalgebra structure one has to transport the comultiplication of `H`
through the graded component maps `S.cmp n : H →ₗ[k] S.Gr`.  This file introduces the maps

```
S.phi n  : H ⊗ H       →ₗ[k] S.Gr ⊗ S.Gr,      ∑_{i+j=n} cmp i ⊗ cmp j
S.phi3 n : H ⊗ (H ⊗ H) →ₗ[k] S.Gr ⊗ (S.Gr ⊗ S.Gr),  ∑_{i+j=n} cmp i ⊗ phi j
S.phi3' n: (H ⊗ H) ⊗ H →ₗ[k] (S.Gr ⊗ S.Gr) ⊗ S.Gr,  ∑_{i+j=n} phi i ⊗ cmp j
```

and the corresponding filtrations `S.fil2 n = Σ_{i+j=n} Fᵢ ⊗ Fⱼ` of `H ⊗ H`.  Everything else in
the construction of the associated graded Hopf algebra is deduced from the two facts below.

## Main results

* `HopfAlgebra.Graded.HopfSplit.phi_tmul_of_mem`: on a tensor `u ⊗ v` with `u ∈ Fₚ`, `v ∈ F_q` and
  `p + q = n`, `phi n (u ⊗ v) = cmp p u ⊗ cmp q v`.
* `HopfAlgebra.Graded.HopfSplit.phi_apply_eq_zero_of_mem_fil2`: `phi n` kills `fil2 m` for `m < n`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)

/-! ### Vanishing of graded components -/

/-- If `x ∈ Fₘ` and `m < n`, then `cmp n x = 0`. -/
theorem cmp_eq_zero_of_mem_lt {m n : ℕ} (h : m < n) {x : H} (hx : x ∈ S.F m) : S.cmp n x = 0 := by
  have hpr : S.pr n x = S.pr n 0 := by
    rw [map_zero]
    exact S.pr_of_mem_lt h x hx
  rw [S.cmp_eq_cmp_of_pr_eq hpr, map_zero]

/-! ### The filtration of `H ⊗ H` -/

/-- The degree-`n` piece of the induced filtration of `H ⊗ H`. -/
noncomputable def fil2 (n : ℕ) : Submodule k (H ⊗[k] H) :=
  ⨆ i ∈ Finset.range (n + 1), tens (S.F i) (S.F (n - i))

/-- `u ⊗ v` lies in the degree-`n` filtration of `H ⊗ H` for `u ∈ Fᵢ`, `v ∈ Fₙ₋ᵢ`. -/
theorem tmul_mem_fil2 {i n : ℕ} (hi : i ≤ n) {u v : H} (hu : u ∈ S.F i) (hv : v ∈ S.F (n - i)) :
    u ⊗ₜ[k] v ∈ S.fil2 n :=
  Submodule.mem_iSup_of_mem i
    (Submodule.mem_iSup_of_mem (Finset.mem_range.2 (by omega)) (tmul_mem_tens hu hv))

/-- To bound `fil2 n` it suffices to consider the tensors of homogeneous elements. -/
theorem fil2_le_of_tmul {n : ℕ} {P : Submodule k (H ⊗[k] H)}
    (h : ∀ i ≤ n, ∀ u ∈ S.F i, ∀ v ∈ S.F (n - i), u ⊗ₜ[k] v ∈ P) : S.fil2 n ≤ P := by
  refine iSup_le fun i => iSup_le fun hi => tens_le_iff.2 ?_
  exact h i (by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hi)

/-- For `x ∈ Fₙ`, `Δ x` lies in the degree-`n` filtration of `H ⊗ H`. -/
theorem comul_mem_fil2 {n : ℕ} {x : H} (hx : x ∈ S.F n) : comul (R := k) x ∈ S.fil2 n :=
  S.comul_mem n x hx

/-! ### The map `phi` -/

/-- The degree-`n` component map on `H ⊗ H`. -/
noncomputable def phi (n : ℕ) : H ⊗[k] H →ₗ[k] S.Gr ⊗[k] S.Gr :=
  ∑ i ∈ Finset.range (n + 1), TensorProduct.map (S.cmp i) (S.cmp (n - i))

/-- `phi n (u ⊗ v) = ∑_{i ≤ n} cmp i u ⊗ cmp (n - i) v`. -/
theorem phi_tmul (n : ℕ) (u v : H) :
    S.phi n (u ⊗ₜ[k] v) = ∑ i ∈ Finset.range (n + 1), S.cmp i u ⊗ₜ[k] S.cmp (n - i) v := by
  simp [phi, LinearMap.sum_apply]

/-- **The key computation**: on a tensor of homogeneous elements of complementary degrees only
one term of `phi n` survives. -/
theorem phi_tmul_of_mem {p q n : ℕ} (hpq : p + q = n) {u v : H} (hu : u ∈ S.F p)
    (hv : v ∈ S.F q) : S.phi n (u ⊗ₜ[k] v) = S.cmp p u ⊗ₜ[k] S.cmp q v := by
  rw [S.phi_tmul]
  rw [Finset.sum_eq_single p]
  · rw [show n - p = q by omega]
  · intro i _ hip
    rcases lt_or_gt_of_ne hip with h | h
    · rw [S.cmp_eq_zero_of_mem_lt (m := q) (by omega) hv, tmul_zero]
    · rw [S.cmp_eq_zero_of_mem_lt h hu, zero_tmul]
  · intro hp
    exact absurd (Finset.mem_range.2 (by omega)) hp

/-- `phi n` kills tensors of homogeneous elements of total degree `< n`. -/
theorem phi_tmul_eq_zero_of_lt {p q n : ℕ} (hpq : p + q < n) {u v : H} (hu : u ∈ S.F p)
    (hv : v ∈ S.F q) : S.phi n (u ⊗ₜ[k] v) = 0 := by
  rw [S.phi_tmul]
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases h : i ≤ p
  · rw [S.cmp_eq_zero_of_mem_lt (m := q) (by omega) hv, tmul_zero]
  · rw [S.cmp_eq_zero_of_mem_lt (m := p) (by omega) hu, zero_tmul]

/-- `phi n` vanishes on the degree-`m` filtration of `H ⊗ H` for `m < n`. -/
theorem phi_apply_eq_zero_of_mem_fil2 {m n : ℕ} (hmn : m < n) {z : H ⊗[k] H} (hz : z ∈ S.fil2 m) :
    S.phi n z = 0 := by
  have hle : S.fil2 m ≤ LinearMap.ker (S.phi n) :=
    S.fil2_le_of_tmul fun i hi u hu v hv => by
      simp only [LinearMap.mem_ker]
      exact S.phi_tmul_eq_zero_of_lt (p := i) (q := m - i) (by omega) hu hv
  exact hle hz

end HopfSplit

end HopfAlgebra.Graded
