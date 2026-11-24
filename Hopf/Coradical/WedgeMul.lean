module

public import Hopf.Coradical.WedgeComul

/-!
# Wedge powers and multiplication in a bialgebra

If `X` is a subcoalgebra of a bialgebra `H` which is closed under multiplication, then the wedge
powers of `X` form an *algebra* filtration:

```
X^{∧ m} · X^{∧ n} ⊆ X^{∧ (m + n)} .
```

Consequently the irreducible component `irrComponent X = ⋃ₙ X^{∧ n}` is closed under
multiplication.  For `X = k · 1` this says that the irreducible component of `1` in a pointed
cocommutative Hopf algebra is a subalgebra.

The proof is the classical one (Sweedler, Montgomery Lemma 5.2.8): by induction on `m + n`, using
`Δ (X^{∧ r}) ⊆ Σ_{p+q=r} X^{∧ p} ⊗ X^{∧ q}` (`Coalgebra.Coradical.comul_wedgePow_le`) and the fact
that `Δ` is multiplicative.

## Main results

* `Coalgebra.Coradical.mul_wedgePow_le`: for a subcoalgebra `X` with `X * X ≤ X`,
  `X^{∧ m} * X^{∧ n} ≤ X^{∧ (m + n)}`.
* `Coalgebra.Coradical.mul_irrComponent_le`: for a subcoalgebra `X` with `X * X ≤ X`,
  `irrComponent X * irrComponent X ≤ irrComponent X`.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 9
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Lemma 5.2.8
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k H : Type u} [Field k] [Ring H] [Bialgebra k H]

/-- Products of `tens`-submodules: `(P ⊗ Q) · (P' ⊗ Q') ⊆ (P P') ⊗ (Q Q')`. -/
theorem tens_mul_tens_le (P Q P' Q' : Submodule k H) :
    tens P Q * tens P' Q' ≤ tens (P * P') (Q * Q') := by
  rw [tens, tens, Submodule.map₂_eq_span_image2, Submodule.map₂_eq_span_image2,
    Submodule.span_mul_span]
  refine Submodule.span_le.2 ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  simp only [Set.mem_image2] at ha hb
  obtain ⟨p, hp, q, hq, rfl⟩ := ha
  obtain ⟨p', hp', q', hq', rfl⟩ := hb
  change (p ⊗ₜ[k] q) * (p' ⊗ₜ[k] q') ∈ _
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  exact tmul_mem_tens (Submodule.mul_mem_mul hp hp') (Submodule.mul_mem_mul hq hq')

/-- **The wedge powers of a multiplicatively closed subcoalgebra form an algebra filtration.** -/
theorem mul_wedgePow_le {X : Submodule k H} (hX : IsSubcoalgebra X) (hXmul : X * X ≤ X)
    (m n : ℕ) : wedgePow X m * wedgePow X n ≤ wedgePow X (m + n) := by
  have hmono : Monotone (wedgePow X) := wedgePow_mono hX
  -- Strong induction on `s = m + n`; `X^{∧0} = X` is closed under multiplication.
  have key : ∀ s : ℕ, ∀ m n : ℕ, m + n = s → wedgePow X m * wedgePow X n ≤ wedgePow X s := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      match s with
      | 0 =>
        intro m n hmn
        obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
        simpa using hXmul
      -- For `s = t + 1`, show `Δ(ab) = Δa Δb ∈ X ⊗ H + H ⊗ X^{∧t}`, term by term in the
      -- filtrations of `Δa` and `Δb` (`comul_wedgePow_le`).
      | (t + 1) =>
        intro m n hmn
        have hAs : wedgePow X (t + 1) = wedge (wedgePow X 0) (wedgePow X t) := by
          simpa using wedgePow_add X 0 t
        rw [hAs]
        refine Submodule.mul_le.2 fun a ha b hb => ?_
        rw [mem_wedge_iff, Bialgebra.comul_mul]
        have hca : (comul (R := k) a) ∈
            ⨆ p ∈ Finset.range (m + 1), tens (wedgePow X p) (wedgePow X (m - p)) :=
          comul_wedgePow_le hX m ⟨a, ha, rfl⟩
        have hcb : (comul (R := k) b) ∈
            ⨆ q ∈ Finset.range (n + 1), tens (wedgePow X q) (wedgePow X (n - q)) :=
          comul_wedgePow_le hX n ⟨b, hb, rfl⟩
        refine (show (⨆ p ∈ Finset.range (m + 1), tens (wedgePow X p) (wedgePow X (m - p)))
            * (⨆ q ∈ Finset.range (n + 1), tens (wedgePow X q) (wedgePow X (n - q)))
            ≤ tens (wedgePow X 0) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) (wedgePow X t)
          from ?_) (Submodule.mul_mem_mul hca hcb)
        simp only [Submodule.iSup_mul, Submodule.mul_iSup]
        refine iSup_le fun i => iSup_le fun hi => iSup_le fun j => iSup_le fun hj => ?_
        simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hj
        refine le_trans (tens_mul_tens_le _ _ _ _) ?_
        -- The term `X ⊗ X^{∧m} · X ⊗ X^{∧n}` lies in `X ⊗ H`; any other in `H ⊗ X^{∧t}`.
        by_cases hij : i = 0 ∧ j = 0
        · obtain ⟨rfl, rfl⟩ := hij
          refine le_trans (tens_mono ?_ le_top) le_sup_left
          simpa using hXmul
        · refine le_trans (tens_mono le_top ?_) le_sup_right
          refine le_trans (IH _ ?_ _ _ rfl) (hmono ?_) <;> omega
  exact key (m + n) m n rfl

/-- The irreducible component of a multiplicatively closed subcoalgebra is closed under
multiplication. -/
theorem mul_irrComponent_le {X : Submodule k H} (hX : IsSubcoalgebra X) (hXmul : X * X ≤ X) :
    irrComponent X * irrComponent X ≤ irrComponent X := by
  rw [irrComponent, Submodule.iSup_mul]
  refine iSup_le fun m => ?_
  rw [Submodule.mul_iSup]
  exact iSup_le fun n =>
    le_trans (mul_wedgePow_le hX hXmul m n) (wedgePow_le_irrComponent X (m + n))

end Coalgebra.Coradical
