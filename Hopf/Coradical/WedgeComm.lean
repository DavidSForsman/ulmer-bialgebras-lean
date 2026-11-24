module

public import Hopf.Coradical.WedgeMul

/-!
# Commutators drop the filtration degree

Let `H` be a bialgebra over a field `k` and let `X ⊆ H` be a subcoalgebra which is closed under
multiplication and *central* — the case of interest is `X = k · 1`, whose wedge powers
`Fₙ = X^{∧ n}` form the coradical filtration of the irreducible component of the unit.  The wedge
powers are already known to form an algebra filtration, `F_m · F_n ⊆ F_{m+n}`
(`Coalgebra.Coradical.mul_wedgePow_le`).  This file proves the sharper statement for commutators:

```
[F_m , F_n] ⊆ F_{m+n-1} .
```

Equivalently: the associated graded algebra of the coradical filtration of a pointed irreducible
coalgebra is **commutative**.  This is one of the two structural inputs of Sweedler's freeness
theorem (the other being freeness over a graded sub-Hopf algebra of a commutative graded connected
Hopf algebra).

The proof is a strong induction on `m + n` using the criterion `F_{r+1} = F_r ∧ X`, i.e.
`z ∈ F_{r+1} ↔ Δ z ∈ F_r ⊗ H + H ⊗ X`, together with the fact that the wedge powers form a coalgebra
filtration (`Coalgebra.Coradical.comul_wedgePow_le`). Writing `Δx = Σ a ⊗ b` and `Δ y = Σ c ⊗ d`
with `a ∈ F_i`, `b ∈ F_{m-i}`, `c ∈ F_p`, `d ∈ F_{n-p}`, the commutator of two such pure tensors
splits as

```
(a ⊗ b)(c ⊗ d) - (c ⊗ d)(a ⊗ b) = (ac - ca) ⊗ bd + ca ⊗ (bd - db) ,
```

whose first summand is handled by the induction hypothesis and whose second summand vanishes
whenever `b` or `d` is central, i.e. whenever `i + p` is maximal.

## Main results

* `Coalgebra.Coradical.Cmm` — the auxiliary predicate "all commutators of `U` and `V` lie in `T`";
* `Coalgebra.Coradical.comm_wedgePow_le` — `[F_m, F_n] ⊆ F_{m+n-1}`;
* `Coalgebra.Coradical.comm_wedgePow_span_one_le` — its specialization to `X = k · 1`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.2
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

/-! ### Commutators of submodules -/

section Comm

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

/-- `Cmm U V T` says that all commutators `u v - v u` with `u ∈ U` and `v ∈ V` lie in `T`. -/
def Cmm (U V T : Submodule k R) : Prop := ∀ u ∈ U, ∀ v ∈ V, u * v - v * u ∈ T

/-- `Cmm U V T` is symmetric in `U` and `V`. -/
theorem Cmm.symm {U V T : Submodule k R} (h : Cmm U V T) : Cmm V U T := by
  intro v hv u hu
  have := T.neg_mem (h u hu v hv)
  simpa using this

/-- The submodule of elements commuting with `V` modulo `T`. -/
noncomputable def commAnn (V T : Submodule k R) : Submodule k R :=
  ⨅ v : V, Submodule.comap (LinearMap.mulRight k (v : R) - LinearMap.mulLeft k (v : R)) T

/-- `u ∈ commAnn V T` iff `u * v - v * u ∈ T` for every `v ∈ V`. -/
theorem mem_commAnn {V T : Submodule k R} {u : R} :
    u ∈ commAnn V T ↔ ∀ v ∈ V, u * v - v * u ∈ T := by
  simp [commAnn, Submodule.mem_iInf, Submodule.mem_comap, Subtype.forall]

/-- `Cmm U V T` iff `U ≤ commAnn V T`. -/
theorem cmm_iff_le {U V T : Submodule k R} : Cmm U V T ↔ U ≤ commAnn V T := by
  constructor
  · intro h u hu
    exact mem_commAnn.2 fun v hv => h u hu v hv
  · intro h u hu v hv
    exact mem_commAnn.1 (h hu) v hv

/-- If `Cmm (U i) V T` for every `i`, then `Cmm (⨆ i, U i) V T`. -/
theorem cmm_iSup_left {ι : Sort*} {U : ι → Submodule k R} {V T : Submodule k R}
    (h : ∀ i, Cmm (U i) V T) : Cmm (⨆ i, U i) V T :=
  cmm_iff_le.2 (iSup_le fun i => cmm_iff_le.1 (h i))

/-- If `Cmm U (V i) T` for every `i`, then `Cmm U (⨆ i, V i) T`. -/
theorem cmm_iSup_right {ι : Sort*} {U : Submodule k R} {V : ι → Submodule k R} {T : Submodule k R}
    (h : ∀ i, Cmm U (V i) T) : Cmm U (⨆ i, V i) T :=
  (cmm_iSup_left (fun i => (h i).symm)).symm

end Comm

/-! ### Commutators of `tens`-submodules -/

section Tens

variable {k H : Type u} [Field k] [Ring H] [Bialgebra k H]

/-- To bound the commutators of two `tens`-submodules it suffices to bound the commutators of
pure tensors. -/
theorem cmm_tens {A B C D : Submodule k H} {T : Submodule k (H ⊗[k] H)}
    (h : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, ∀ d ∈ D,
      (a ⊗ₜ[k] b) * (c ⊗ₜ[k] d) - (c ⊗ₜ[k] d) * (a ⊗ₜ[k] b) ∈ T) :
    Cmm (tens A B) (tens C D) T := by
  refine cmm_iff_le.2 (tens_le_iff.2 fun a ha b hb => mem_commAnn.2 ?_)
  have hle : tens C D
      ≤ Submodule.comap (LinearMap.mulLeft k (a ⊗ₜ[k] b) - LinearMap.mulRight k (a ⊗ₜ[k] b)) T :=
    tens_le_iff.2 fun c hc d hd => by
      simpa using h a ha b hb c hc d hd
  intro v hv
  simpa using hle hv

end Tens

/-! ### The main estimate -/

section Main

variable {k H : Type u} [Field k] [Ring H] [Bialgebra k H]

/-- Inductive tensor-product commutator step for `comm_wedgePow_le`. -/
private lemma comm_wedgePow_tens_step {X : Submodule k H} (hX : IsSubcoalgebra X)
    (hXmul : X * X ≤ X) (hXc : ∀ x ∈ X, ∀ y : H, x * y = y * x) {t m n i p : ℕ}
    (hmn : m + n = t + 2) (hi : i ≤ m) (hp : p ≤ n)
    (IH : ∀ s < t + 2, ∀ m n, m + n = s →
      Cmm (wedgePow X m) (wedgePow X n) (wedgePow X (s - 1)))
    {a b c d : H} (ha : a ∈ wedgePow X i) (hb : b ∈ wedgePow X (m - i))
    (hc : c ∈ wedgePow X p) (hd : d ∈ wedgePow X (n - p)) :
    (a ⊗ₜ[k] b) * (c ⊗ₜ[k] d) - (c ⊗ₜ[k] d) * (a ⊗ₜ[k] b) ∈
      tens (wedgePow X t) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) X := by
  have hmono : Monotone (wedgePow X) := wedgePow_mono hX
  -- `[a ⊗ b, c ⊗ d] = [a, c] ⊗ bd + ca ⊗ [b, d]`.
  have hsplit : (a ⊗ₜ[k] b) * (c ⊗ₜ[k] d) - (c ⊗ₜ[k] d) * (a ⊗ₜ[k] b)
      = (a * c - c * a) ⊗ₜ[k] (b * d) + (c * a) ⊗ₜ[k] (b * d - d * b) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      TensorProduct.sub_tmul, TensorProduct.tmul_sub]
    abel
  rw [hsplit]
  -- If `i + p ≤ t`: `[a, c]` (by induction) and `ca` both lie in `X^{∧t}`.
  by_cases hip : i + p ≤ t
  · have h1 : (a * c - c * a) ⊗ₜ[k] (b * d) ∈
        tens (wedgePow X t) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) X :=
      Submodule.mem_sup_left (tmul_mem_tens
        (hmono (by omega) (IH (i + p) (by omega) i p rfl a ha c hc)) Submodule.mem_top)
    have h2 : (c * a) ⊗ₜ[k] (b * d - d * b) ∈
        tens (wedgePow X t) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) X :=
      Submodule.mem_sup_left (tmul_mem_tens
        (hmono (by omega) (mul_wedgePow_le hX hXmul p i (Submodule.mul_mem_mul hc ha)))
        Submodule.mem_top)
    exact Submodule.add_mem _ h1 h2
  -- Otherwise `b` or `d` lies in `X`, which is central, so `[b, d] = 0`.
  · have hbd : b * d - d * b = 0 := by
      rcases (by omega : m - i = 0 ∨ n - p = 0) with h | h
      · have hbX : b ∈ X := by simpa [h] using hb
        simp [hXc b hbX d]
      · have hdX : d ∈ X := by simpa [h] using hd
        simp [(hXc d hdX b).symm]
    rw [hbd, TensorProduct.tmul_zero, add_zero]
    -- If `i + p = t + 2`, then `b, d ∈ X` and `bd ∈ X`; else `[a, c] ∈ X^{∧t}` by induction.
    by_cases hip2 : i + p = t + 2
    · have hbX : b ∈ X := by simpa [show m - i = 0 by omega] using hb
      have hdX : d ∈ X := by simpa [show n - p = 0 by omega] using hd
      exact Submodule.mem_sup_right (tmul_mem_tens Submodule.mem_top
        (hXmul (Submodule.mul_mem_mul hbX hdX)))
    · exact Submodule.mem_sup_left (tmul_mem_tens
        (hmono (by omega) (IH (i + p) (by omega) i p rfl a ha c hc)) Submodule.mem_top)

/-- **Commutators drop the filtration degree.**  If `X` is a central, multiplicatively closed
subcoalgebra of a bialgebra `H`, then `[X^{∧ m}, X^{∧ n}] ⊆ X^{∧ (m+n-1)}`. -/
theorem comm_wedgePow_le {X : Submodule k H} (hX : IsSubcoalgebra X) (hXmul : X * X ≤ X)
    (hXc : ∀ x ∈ X, ∀ y : H, x * y = y * x) (m n : ℕ) :
    Cmm (wedgePow X m) (wedgePow X n) (wedgePow X (m + n - 1)) := by
  -- Strong induction on `s = m + n`.
  have key : ∀ s : ℕ, ∀ m n : ℕ, m + n = s →
      Cmm (wedgePow X m) (wedgePow X n) (wedgePow X (s - 1)) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s IH =>
      match s with
      -- For `s ≤ 1`, one of `x, y` lies in `X^{∧0}` or `X`, hence is central.
      | 0 =>
          intro m n hmn
          obtain ⟨rfl, rfl⟩ : m = 0 ∧ n = 0 := by omega
          intro x hx y hy
          simp only [wedgePow_zero] at hx hy
          simp [hXc x hx y]
      | 1 =>
          intro m n hmn x hx y hy
          have : x * y = y * x := by
            rcases (by omega : m = 0 ∨ n = 0) with h | h
            · subst h; exact hXc x (by simpa using hx) y
            · subst h; exact (hXc y (by simpa using hy) x).symm
          simp [this]
      -- For `s = t + 2`, test `Δ[x, y] ∈ X^{∧t} ⊗ H + H ⊗ X` on the filtration terms of `Δx`
      -- and `Δy` (`comul_wedgePow_le`), with the step lemma above.
      | (t + 2) =>
          intro m n hmn x hx y hy
          have hst : (t + 2) - 1 = t + 1 := by omega
          rw [hst, wedgePow_succ, mem_wedge_iff, map_sub, Bialgebra.comul_mul,
            Bialgebra.comul_mul]
          have hcx := comul_wedgePow_le hX m ⟨x, hx, rfl⟩
          have hcy := comul_wedgePow_le hX n ⟨y, hy, rfl⟩
          refine cmm_iSup_left (fun i => cmm_iSup_left fun hi =>
            cmm_iSup_right fun p => cmm_iSup_right fun hp =>
              cmm_tens fun a ha b hb c hc d hd => ?_) _ hcx _ hcy
          simp only [Finset.mem_range, Nat.lt_succ_iff] at hi hp
          exact comm_wedgePow_tens_step hX hXmul hXc hmn hi hp IH ha hb hc hd
  simpa using key (m + n) m n rfl

/-- The specialization to `X = k · 1`, whose wedge powers form the coradical filtration of the
irreducible component of the unit. -/
theorem comm_wedgePow_span_one_le (hX : IsSubcoalgebra (Submodule.span k {(1 : H)})) (m n : ℕ) :
    Cmm (wedgePow (Submodule.span k {(1 : H)}) m) (wedgePow (Submodule.span k {(1 : H)}) n)
      (wedgePow (Submodule.span k {(1 : H)}) (m + n - 1)) := by
  refine comm_wedgePow_le hX ?_ ?_ m n
  · rw [Submodule.span_mul_span]
    simp
  · intro x hx y
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    simp

end Main

end Coalgebra.Coradical
