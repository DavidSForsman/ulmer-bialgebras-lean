module

public import Mathlib.Order.CompletePartialOrder
public import Hopf.Coradical.TensorSub

/-!
# Filtrations and tensor products

A purely linear-algebraic lemma about two increasing filtrations `A` of `M` and `B` of `N`:
an element of `M ⊗ N` which lies in `A m ⊗ N + M ⊗ B n` for *every* decomposition `m + n = r`
already lies in `A 0 ⊗ N + Σ_{p ≤ r} A p ⊗ B (r + 1 - p)`.

This is the linear algebra behind the fact that the coradical filtration of a coalgebra is a
*coalgebra* filtration: `Δ C_r ⊆ Σ_{i + j = r} C_i ⊗ C_j`.

The proof is by induction on `r`, shifting the filtration `A`; the only inputs are the modular
law and `Coalgebra.Coradical.tens_top_inf_top_tens` (`A ⊗ N ∩ M ⊗ B = A ⊗ B`).

## Main results

* `Coalgebra.Coradical.mem_iSup_tens_of_mem_tens_top`: for monotone `A`, `B` with `B 0 = ⊥`, if
  `t ∈ M ⊗ B r` and `t ∈ A m ⊗ N + M ⊗ B n` whenever `m + n = r`, then
  `t ∈ Σ_{p ≤ r} A p ⊗ B (r + 1 - p)`.
* `Coalgebra.Coradical.mem_sup_iSup_tens`: for monotone `A`, `B` with `B 0 = ⊥`, if
  `t ∈ A m ⊗ N + M ⊗ B n` whenever `m + n = r`, then
  `t ∈ A 0 ⊗ N + Σ_{p ≤ r} A p ⊗ B (r + 1 - p)`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

open TensorProduct

universe u

namespace Coalgebra.Coradical

variable {k M N : Type u} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The main induction: if `t ∈ M ⊗ B r` and `t ∈ A m ⊗ N + M ⊗ B n` for all `m + n = r`, and the
filtration `B` starts at `0`, then `t ∈ Σ_{p ≤ r} A p ⊗ B (r + 1 - p)`. -/
theorem mem_iSup_tens_of_mem_tens_top (B : ℕ → Submodule k N) (hB : Monotone B) (hB0 : B 0 = ⊥) :
    ∀ (r : ℕ) (A : ℕ → Submodule k M), Monotone A → ∀ t : M ⊗[k] N, t ∈ tens ⊤ (B r) →
      (∀ m n : ℕ, m + n = r → t ∈ tens (A m) (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) (B n)) →
      t ∈ ⨆ p ∈ Finset.range (r + 1), tens (A p) (B (r + 1 - p)) := by
  intro r
  induction r with
  | zero =>
      -- `B 0 = 0`, so `t = 0`
      intro A hA t ht _
      rw [hB0, tens_bot_right, Submodule.mem_bot] at ht
      subst ht
      exact Submodule.zero_mem _
  | succ r IH =>
      -- with `m = 1`: `t ∈ (A 1 ⊗ N + M ⊗ B r) ∩ (M ⊗ B (r + 1)) = M ⊗ B r + A 1 ⊗ B (r + 1)`,
      -- so `t = v + u` with `v ∈ M ⊗ B r` and `u ∈ A 1 ⊗ B (r + 1)`
      intro A hA t ht hyp
      have h1 : t ∈ (tens (A 1) (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) (B r))
          ⊓ tens (⊤ : Submodule k M) (B (r + 1)) := ⟨hyp 1 r (by omega), ht⟩
      rw [sup_comm, sup_inf_assoc_of_le _ (tens_mono le_rfl (hB (Nat.le_succ r))),
        tens_top_inf_top_tens] at h1
      obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.1 h1
      refine Submodule.add_mem _ ?_ ?_
      · -- `v`: the induction hypothesis for the shifted filtration `A (· + 1)`
        have hv' : v ∈ ⨆ p ∈ Finset.range (r + 1), tens (A (p + 1)) (B (r + 1 - p)) := by
          refine IH (fun i => A (i + 1)) (fun i j hij => hA (by omega)) v hv ?_
          intro m n hmn
          have h2 : v + u ∈
              tens (A (m + 1)) (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) (B n) :=
            hyp (m + 1) n (by omega)
          have hu' : u ∈ tens (A (m + 1)) (⊤ : Submodule k N) :=
            tens_mono (hA (by omega)) le_top hu
          have hvsub : v = (v + u) - u := by abel
          rw [hvsub]
          exact Submodule.sub_mem _ h2 (Submodule.mem_sup_left hu')
        refine (iSup₂_le fun p hp => ?_ :
          (⨆ p ∈ Finset.range (r + 1), tens (A (p + 1)) (B (r + 1 - p)))
            ≤ ⨆ p ∈ Finset.range (r + 1 + 1), tens (A p) (B (r + 1 + 1 - p))) hv'
        simp only [Finset.mem_range, Nat.lt_succ_iff] at hp
        have hle := le_iSup₂
          (f := fun q (_ : q ∈ Finset.range (r + 1 + 1)) => tens (A q) (B (r + 1 + 1 - q)))
          (p + 1) (by simp; omega)
        rw [show r + 1 + 1 - (p + 1) = r + 1 - p by omega] at hle
        exact hle
      · -- `u`: the term `p = 1`
        have hle := le_iSup₂
          (f := fun q (_ : q ∈ Finset.range (r + 1 + 1)) => tens (A q) (B (r + 1 + 1 - q)))
          1 (by simp)
        rw [show r + 1 + 1 - 1 = r + 1 by omega] at hle
        exact hle hu

/-- The form in which the previous lemma is applied: without the hypothesis `t ∈ M ⊗ B r`, one
picks up an extra summand `A 0 ⊗ N`. -/
theorem mem_sup_iSup_tens (A : ℕ → Submodule k M) (B : ℕ → Submodule k N)
    (hA : Monotone A) (hB : Monotone B) (hB0 : B 0 = ⊥) (r : ℕ) (t : M ⊗[k] N)
    (h : ∀ m n : ℕ, m + n = r →
      t ∈ tens (A m) (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) (B n)) :
    t ∈ tens (A 0) (⊤ : Submodule k N) ⊔
      ⨆ p ∈ Finset.range (r + 1), tens (A p) (B (r + 1 - p)) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (h 0 r (Nat.zero_add r))
  refine Submodule.add_mem_sup hu ?_
  refine mem_iSup_tens_of_mem_tens_top B hB hB0 r A hA v hv ?_
  intro m n hmn
  have hts : u + v ∈ tens (A m) (⊤ : Submodule k N) ⊔ tens (⊤ : Submodule k M) (B n) := h m n hmn
  have humem : u ∈ tens (A m) (⊤ : Submodule k N) :=
    tens_mono (hA (Nat.zero_le m)) le_rfl hu
  have : v = (u + v) - u := by abel
  rw [this]
  exact Submodule.sub_mem _ hts (Submodule.mem_sup_left humem)

end Coalgebra.Coradical
