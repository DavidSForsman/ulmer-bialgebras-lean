module

public import Hopf.Coradical.WedgeAssoc
public import Hopf.Coradical.FiltrationTensor

/-!
# The wedge powers form a coalgebra filtration

For a subcoalgebra `X` of a coalgebra `C` the wedge powers `A r = X^{∧ r}` satisfy

```
Δ (A r) ⊆ Σ_{p + q = r} A p ⊗ A q ,
```

the classical statement that the coradical filtration of a coalgebra is a coalgebra filtration.
The proof combines the additivity of wedge powers (`Coalgebra.Coradical.wedgePow_add`), which gives
`Δ (A r) ⊆ A m ⊗ C + C ⊗ A n` for `m + n = r - 1`, with the filtration lemma
`Coalgebra.Coradical.mem_sup_iSup_tens`.

## Main results

* `Coalgebra.Coradical.comul_wedgePow_le`: for a subcoalgebra `X`,
  `Δ (X^{∧ r}) ≤ Σ_{p ≤ r} X^{∧ p} ⊗ X^{∧ (r - p)}`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- **The wedge powers of a subcoalgebra form a coalgebra filtration.** -/
theorem comul_wedgePow_le {X : Submodule k C} (hX : IsSubcoalgebra X) (r : ℕ) :
    Submodule.map (comul : C →ₗ[k] C ⊗[k] C) (wedgePow X r)
      ≤ ⨆ p ∈ Finset.range (r + 1), tens (wedgePow X p) (wedgePow X (r - p)) := by
  rintro _ ⟨c, hc, rfl⟩
  -- `B` is `A` shifted by one, with `B 0 = ⊥`; both are monotone.
  set A := wedgePow X with hAdef
  set B : ℕ → Submodule k C := fun n => Nat.casesOn n (⊥ : Submodule k C) (fun i => A i) with hBdef
  have hB0 : B 0 = ⊥ := rfl
  have hBsucc : ∀ i, B (i + 1) = A i := fun _ => rfl
  have hAmono : Monotone A := wedgePow_mono hX
  have hBmono : Monotone B := by
    refine monotone_nat_of_le_succ fun n => ?_
    cases n with
    | zero => simp [hB0]
    | succ i => rw [hBsucc, hBsucc]; exact hAmono (Nat.le_succ i)
  -- For `m + n = r`, `Δ c ∈ A m ⊗ C + C ⊗ B n`: from `A r = A m ∧ A (n - 1)` if `n > 0`.
  have hsub : ∀ n, IsSubcoalgebra (A n) := fun n => isSubcoalgebra_wedgePow hX n
  have hcomulc : (comul (R := k) c) ∈ tens (A r) (A r) := comul_mem_tens (hsub r) hc
  have hhyp : ∀ m n : ℕ, m + n = r →
      (comul (R := k) c) ∈ tens (A m) (⊤ : Submodule k C) ⊔ tens (⊤ : Submodule k C) (B n) := by
    intro m n hmn
    cases n with
    | zero =>
        have hm : m = r := by omega
        subst hm
        exact Submodule.mem_sup_left (tens_mono le_rfl le_top hcomulc)
    | succ j =>
        have hAr : A r = wedge (A m) (A j) := by
          have h := wedgePow_add X m j
          rw [show m + j + 1 = r by omega] at h
          exact h
        rw [hAr] at hc
        rw [hBsucc]
        exact mem_wedge_iff.1 hc
  -- The intersection over all splittings gives `Δ c ∈ A 0 ⊗ C + ∑ₚ A p ⊗ A (r - p)`.
  have hmain := mem_sup_iSup_tens A B hAmono hBmono hB0 r _ hhyp
  have hrw : (⨆ p ∈ Finset.range (r + 1), tens (A p) (B (r + 1 - p)))
      = ⨆ p ∈ Finset.range (r + 1), tens (A p) (A (r - p)) := by
    refine iSup_congr fun p => iSup_congr fun hp => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hp
    rw [show r + 1 - p = (r - p) + 1 by omega, hBsucc]
  rw [hrw] at hmain
  -- Intersecting with `C ⊗ A r` (as `Δ c ∈ A r ⊗ A r`) removes the term `A 0 ⊗ C`.
  set S := ⨆ p ∈ Finset.range (r + 1), tens (A p) (A (r - p)) with hS
  have hSle : S ≤ tens (⊤ : Submodule k C) (A r) := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hp
    exact tens_mono le_top (hAmono (by omega))
  have hzero : tens (A 0) (A r) ≤ S := by
    have h := le_iSup₂ (f := fun p (_ : p ∈ Finset.range (r + 1)) => tens (A p) (A (r - p))) 0
      (by simp : (0 : ℕ) ∈ Finset.range (r + 1))
    rw [Nat.sub_zero] at h
    exact h
  have hmem2 : (comul (R := k) c) ∈
      (tens (A 0) (⊤ : Submodule k C) ⊔ S) ⊓ tens (⊤ : Submodule k C) (A r) :=
    ⟨hmain, tens_mono le_top le_rfl hcomulc⟩
  rw [sup_comm, sup_inf_assoc_of_le _ hSle, tens_top_inf_top_tens] at hmem2
  exact (sup_le le_rfl hzero : S ⊔ tens (A 0) (A r) ≤ S) hmem2

end Coalgebra.Coradical
