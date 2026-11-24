module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Flat graded modules over a connected graded algebra are graded free

Let `k` be a field, let `R = ⨁ₙ 𝒜 n` be an `ℕ`-graded `k`-algebra which is *connected*
(every element of `𝒜 0` is a scalar), and let `M = ⨁ₙ ℳ n` be an `ℕ`-graded `R`-module.
If `M` is flat as an `R`-module then `M` is free, with a basis consisting of homogeneous
elements.

This is the "graded Nakayama" package.  The proof is the classical one:

* let `J ⊆ R` be the ideal of elements of positive degree, so `R / J = k`;
* choose, in each degree `n`, a `k`-complement `C n` of the degree-`n` part of `J · M` inside
  `ℳ n`, and a `k`-basis of `C n`; the union `b` of these bases spans `M` over `R` (graded
  Nakayama; this step does not use flatness);
* the kernel `N` of `R^{(ι)} ↠ M` is contained in `J · R^{(ι)}` — this is where the choice of
  `C n` as a complement is used;
* flatness of `M ≅ R^{(ι)} / N` gives `N ∩ (J · R^{(ι)}) ⊆ J · N`
  (`Submodule.inter_smul_top_le_smul`),
  hence `N = J · N`, hence `N ⊆ Jᵐ · R^{(ι)}` for every `m`;
* every coefficient of an element of `N` therefore lies in `⋂ₘ Jᵐ ⊆ ⋂ₘ R≥ₘ = 0`.

The main results are `HopfAlgebra.Graded.Free.homBasis` (the homogeneous basis),
`HopfAlgebra.Graded.Free.homBasis_mem` (its homogeneity) and
`HopfAlgebra.Graded.Free.exists_homogeneous_basis`.

## Main results

* `Submodule.inter_smul_top_le_smul`: if `F ⧸ N` is a flat `R`-module, then
  `(I • ⊤) ⊓ N ≤ I • N` for
  every ideal `I`.
* `HopfAlgebra.Graded.Free.homBasis`: for `M` flat over `R` and every element of `𝒜 0` a scalar, an
  `R`-basis of `M`.
* `HopfAlgebra.Graded.Free.homBasis_mem`: the vector of `homBasis` indexed by `p` lies in `ℳ p.1`.
* `HopfAlgebra.Graded.Free.exists_homogeneous_basis`: under the same hypotheses, `M` has an
  `R`-basis of homogeneous elements.

## References

* [J. W. Milnor, J. C. Moore, *On the structure of Hopf algebras*][Milnor-Moore]
* [The Stacks Project][stacks-project], [Lemma 10.56.1](https://stacks.math.columbia.edu/tag/0EKB),
  for the graded Nakayama lemma for finite modules. The degree induction described above proves
  the spanning step here for modules graded by the natural numbers.
-/

@[expose] public section

open DirectSum

universe u v w

/-- If `F / N` is a flat `R`-module then `(I • F) ∩ N ≤ I • N` for every ideal `I`.  This is the
usual consequence of the vanishing of `Tor₁(R/I, F/N)`, proved here directly from the equational
criterion for flatness. -/
theorem Submodule.inter_smul_top_le_smul {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]
    (N : Submodule R F) [Module.Flat R (F ⧸ N)] (I : Ideal R) :
    (I • (⊤ : Submodule R F)) ⊓ N ≤ I • N := by
  rintro x ⟨hx, hxN⟩
  simp only [SetLike.mem_coe] at hx hxN
  have htop : (⊤ : Submodule R F) = Submodule.span R (Set.range (id : F → F)) := by simp
  rw [htop, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
  obtain ⟨a, ha, hsum⟩ := hx
  have hsum' : ∑ i ∈ a.support, a i • i = x := hsum
  have hzero : ∑ i : {i : F // i ∈ a.support}, a i.1 • (N.mkQ i.1) = 0 := by
    rw [Finset.sum_coe_sort a.support (fun i => a i • N.mkQ i)]
    simp only [← map_smul, ← map_sum, hsum']
    simpa using hxN
  obtain ⟨m, A, y, hy1, hy2⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hzero
  choose z hz using fun j => Submodule.Quotient.mk_surjective N (y j)
  have hg : ∀ i : {i : F // i ∈ a.support}, (i.1 - ∑ j, A i j • z j) ∈ N := by
    intro i
    have h0 : N.mkQ (i.1 - ∑ j, A i j • z j) = 0 := by
      simp only [map_sub, map_sum, map_smul, Submodule.mkQ_apply, hz]
      rw [← hy1 i]
      simp
    exact (Submodule.Quotient.mk_eq_zero N).mp h0
  have key : x = ∑ i : {i : F // i ∈ a.support}, a i.1 • (i.1 - ∑ j, A i j • z j) := by
    have expand : ∀ i : {i : F // i ∈ a.support},
        a i.1 • (i.1 - ∑ j, A i j • z j) = a i.1 • i.1 - ∑ j, (a i.1 * A i j) • z j := by
      intro i; rw [smul_sub, Finset.smul_sum]; simp [mul_smul]
    rw [Finset.sum_congr rfl (fun i _ => expand i), Finset.sum_sub_distrib, Finset.sum_comm]
    rw [Finset.sum_coe_sort a.support (fun i => a i • i), hsum']
    have hj : ∑ j : Fin m, ∑ i : {i : F // i ∈ a.support}, (a i.1 * A i j) • z j = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [← Finset.sum_smul, hy2 j, zero_smul]
    rw [hj, sub_zero]
  rw [key]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (ha i.1) (hg i)

namespace HopfAlgebra.Graded.Free

/-! ## The ideal of elements of positive degree -/

section Ring

variable {k : Type u} {R : Type v} [Field k] [CommRing R] [Algebra k R]
variable (𝒜 : ℕ → Submodule k R)

/-- The `k`-submodule of `R` spanned by the homogeneous elements of degree `≥ m`. -/
def Rge (m : ℕ) : Submodule k R := ⨆ (n : ℕ) (_ : m ≤ n), 𝒜 n

variable {𝒜} in
/-- A homogeneous element of degree `n ≥ m` lies in `Rge 𝒜 m`. -/
theorem mem_Rge {m n : ℕ} (h : m ≤ n) {x : R} (hx : x ∈ 𝒜 n) : x ∈ Rge 𝒜 m :=
  Submodule.mem_iSup_of_mem n (Submodule.mem_iSup_of_mem h hx)

variable [GradedAlgebra 𝒜]

/-- The graded pieces span `R`: `⨆ n, 𝒜 n = ⊤`. -/
theorem iSup_grade_eq_top : (⨆ n, 𝒜 n) = ⊤ :=
  (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top

/-- `Rge 𝒜 0 = ⊤`. -/
theorem rge_zero : Rge 𝒜 0 = ⊤ := by
  rw [eq_top_iff, ← iSup_grade_eq_top 𝒜]
  exact iSup_mono fun n => le_iSup (fun _ : 0 ≤ n => 𝒜 n) (Nat.zero_le n)

/-- If `a ∈ 𝒜 i` with `m ≤ i` and `s ∈ Rge 𝒜 l`, then `a * s ∈ Rge 𝒜 (m + l)`. -/
theorem mem_Rge_mul {m l i : ℕ} (hi : m ≤ i) {a : R} (ha : a ∈ 𝒜 i) {s : R}
    (hs : s ∈ Rge 𝒜 l) : a * s ∈ Rge 𝒜 (m + l) := by
  have h : Rge 𝒜 l ≤ Submodule.comap (LinearMap.mulLeft k a) (Rge 𝒜 (m + l)) := by
    refine iSup_le fun n => iSup_le fun hn => ?_
    intro y hy
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact mem_Rge (by omega) (SetLike.mul_mem_graded ha hy)
  exact h hs

/-- `Rge 𝒜 m` is closed under left multiplication by elements of `R`. -/
theorem mul_mem_Rge {m : ℕ} (r : R) {x : R} (hx : x ∈ Rge 𝒜 m) : r * x ∈ Rge 𝒜 m := by
  have h : (⨆ n, 𝒜 n) ≤ Submodule.comap (LinearMap.mulRight k x) (Rge 𝒜 m) := by
    refine iSup_le fun i => ?_
    intro a ha
    simp only [Submodule.mem_comap, LinearMap.mulRight_apply]
    simpa using mem_Rge_mul 𝒜 (m := 0) (Nat.zero_le i) ha hx
  have hr : r ∈ (⨆ n, 𝒜 n) := by rw [iSup_grade_eq_top 𝒜]; trivial
  exact h hr

/-- The ideal of `R` generated by the homogeneous elements of degree `≥ m`. -/
def Ige (m : ℕ) : Ideal R where
  carrier := (Rge 𝒜 m : Set R)
  add_mem' := fun ha hb => add_mem ha hb
  zero_mem' := zero_mem _
  smul_mem' := fun r _ hx => by simpa [smul_eq_mul] using mul_mem_Rge 𝒜 r hx

variable {𝒜} in
/-- `x ∈ Ige 𝒜 m ↔ x ∈ Rge 𝒜 m`. -/
@[simp] theorem mem_Ige_iff {m : ℕ} {x : R} : x ∈ Ige 𝒜 m ↔ x ∈ Rge 𝒜 m := Iff.rfl

/-- `Ige 𝒜 m * Ige 𝒜 l ≤ Ige 𝒜 (m + l)`. -/
theorem ige_mul_le (m l : ℕ) : Ige 𝒜 m * Ige 𝒜 l ≤ Ige 𝒜 (m + l) := by
  rw [Ideal.mul_le]
  intro r hr s hs
  simp only [mem_Ige_iff] at hr hs ⊢
  have outer : Rge 𝒜 m ≤ Submodule.comap (LinearMap.mulRight k s) (Rge 𝒜 (m + l)) := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro a ha
    simp only [Submodule.mem_comap, LinearMap.mulRight_apply]
    exact mem_Rge_mul 𝒜 hi ha hs
  exact outer hr

/-- The ideal of elements of positive degree; the "graded maximal ideal". -/
abbrev posIdeal : Ideal R := Ige 𝒜 1

/-- `posIdeal 𝒜 ^ m ≤ Ige 𝒜 m`. -/
theorem posIdeal_pow_le (m : ℕ) : posIdeal 𝒜 ^ m ≤ Ige 𝒜 m := by
  induction m with
  | zero =>
      simp only [pow_zero, Ideal.one_eq_top]
      intro x _
      rw [mem_Ige_iff, rge_zero]; trivial
  | succ m ih =>
      calc posIdeal 𝒜 ^ (m + 1) = posIdeal 𝒜 ^ m * posIdeal 𝒜 := pow_succ _ _
        _ ≤ Ige 𝒜 m * Ige 𝒜 1 := Ideal.mul_mono ih le_rfl
        _ ≤ Ige 𝒜 (m + 1) := ige_mul_le 𝒜 m 1

/-- Homogeneous components of an element of `Rge 𝒜 m` vanish below degree `m`. -/
theorem decompose_eq_zero_of_mem_Rge {m i : ℕ} (hi : i < m) {x : R} (hx : x ∈ Rge 𝒜 m) :
    (DirectSum.decompose 𝒜 x i : R) = 0 := by
  have h : Rge 𝒜 m ≤ LinearMap.ker
      ((𝒜 i).subtype ∘ₗ (DirectSum.component k ℕ (fun n => 𝒜 n) i) ∘ₗ
        (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap) := by
    refine iSup_le fun n => iSup_le fun hn => ?_
    intro y hy
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.subtype_apply, ← DirectSum.apply_eq_component]
    exact DirectSum.decompose_of_mem_ne 𝒜 hy (by omega)
  have h2 := h hx
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
    Submodule.subtype_apply] at h2
  exact h2

/-- An element lying in every `Rge 𝒜 m` is zero. -/
theorem eq_zero_of_mem_Rge_all {x : R} (hx : ∀ m, x ∈ Rge 𝒜 m) : x = 0 := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Finset.sum_eq_zero fun i _ =>
    decompose_eq_zero_of_mem_Rge 𝒜 (Nat.lt_succ_self i) (hx (i + 1))

/-- Subtracting its degree-zero part from an element leaves an element of positive degree. -/
theorem sub_decompose_zero_mem (x : R) : x - (DirectSum.decompose 𝒜 x 0 : R) ∈ posIdeal 𝒜 := by
  classical
  set d := DirectSum.decompose 𝒜 x with hd
  have hsum : ∑ i ∈ d.support, (d i : R) = x := DirectSum.sum_support_decompose 𝒜 x
  rw [posIdeal, mem_Ige_iff, ← hsum]
  by_cases h0 : (0 : ℕ) ∈ d.support
  · rw [← Finset.sum_erase_add _ _ h0, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun i hi =>
      mem_Rge (Nat.one_le_iff_ne_zero.2 (Finset.ne_of_mem_erase hi)) (d i).2
  · have hz : (d 0 : R) = 0 := by
      have hz0 : d 0 = 0 := DFinsupp.notMem_support_iff.1 h0
      rw [hz0, ZeroMemClass.coe_zero]
    rw [hz, sub_zero]
    exact Submodule.sum_mem _ fun i hi =>
      mem_Rge (Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact h0 hi)) (d i).2

end Ring

/-! ## Coefficientwise description of `I • ⊤` in a free module -/

/-- If every coefficient of `c : ι →₀ R` lies in `I`, then `c ∈ I • ⊤`. -/
theorem finsupp_mem_smul_top {R : Type v} [CommRing R] {ι : Type*} (I : Ideal R) (c : ι →₀ R)
    (h : ∀ j, c j ∈ I) : c ∈ I • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  have key : (c.sum fun j r => Finsupp.single j r) ∈ I • (⊤ : Submodule R (ι →₀ R)) := by
    refine Submodule.sum_mem _ fun j _ => ?_
    beta_reduce
    rw [← Finsupp.smul_single_one]
    exact Submodule.smul_mem_smul (h j) Submodule.mem_top
  rwa [Finsupp.sum_single] at key

/-- Every coefficient of an element of `I • ⊤` in `ι →₀ R` lies in `I`. -/
theorem apply_mem_of_mem_smul_top {R : Type v} [CommRing R] {ι : Type*} (I : Ideal R)
    (c : ι →₀ R) (h : c ∈ I • (⊤ : Submodule R (ι →₀ R))) (j : ι) : c j ∈ I := by
  refine Submodule.smul_induction_on h ?_ ?_
  · intro a ha x _
    simpa [Finsupp.smul_apply, smul_eq_mul] using I.mul_mem_right (x j) ha
  · intro x y hx hy
    simpa using add_mem hx hy

/-! ## Graded modules -/

section GradedModule

variable {k : Type u} {R : Type v} {M : Type w} [Field k] [CommRing R] [Algebra k R]
  [AddCommGroup M] [Module k M]
variable (𝒜 : ℕ → Submodule k R) (ℳ : ℕ → Submodule k M)

/-- The graded pieces span `M`: `⨆ n, ℳ n = ⊤`. -/
theorem iSup_grade_module_eq_top [DirectSum.Decomposition ℳ] : (⨆ n, ℳ n) = ⊤ :=
  (DirectSum.Decomposition.isInternal ℳ).submodule_iSup_eq_top

variable [Module R M]

/-- The degree-`n` part of `J · M`, where `J` is the ideal of positive-degree elements. -/
def Gsub (n : ℕ) : Submodule k M :=
  Submodule.span k {x : M | ∃ i j : ℕ, 0 < i ∧ i + j = n ∧ ∃ a ∈ 𝒜 i, ∃ y ∈ ℳ j, x = a • y}

variable {𝒜 ℳ} in
/-- For `0 < i`, `a ∈ 𝒜 i` and `y ∈ ℳ j`, `a • y ∈ Gsub 𝒜 ℳ (i + j)`. -/
theorem smul_mem_Gsub {i j : ℕ} (hi : 0 < i) {a : R} (ha : a ∈ 𝒜 i) {y : M} (hy : y ∈ ℳ j) :
    a • y ∈ Gsub 𝒜 ℳ (i + j) :=
  Submodule.subset_span ⟨i, j, hi, rfl, a, ha, y, hy, rfl⟩

/-- `Gsub 𝒜 ℳ n ≤ ℳ n`. -/
theorem gsub_le [SetLike.GradedSMul 𝒜 ℳ] (n : ℕ) : Gsub 𝒜 ℳ n ≤ ℳ n := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨i, j, _, rfl, a, ha, y, hy, rfl⟩
  exact SetLike.GradedSMul.smul_mem ha hy

/-- A `k`-complement, inside `ℳ n`, of the degree-`n` part of `J · M`. -/
noncomputable def Ccompl (n : ℕ) : Submodule k (ℳ n) :=
  Classical.choose (Submodule.exists_isCompl (Submodule.comap (ℳ n).subtype (Gsub 𝒜 ℳ n)))

/-- `Ccompl 𝒜 ℳ n` is a complement, in `ℳ n`, of the pullback of `Gsub 𝒜 ℳ n` to `ℳ n`. -/
theorem isCompl_Ccompl (n : ℕ) :
    IsCompl (Submodule.comap (ℳ n).subtype (Gsub 𝒜 ℳ n)) (Ccompl 𝒜 ℳ n) :=
  Classical.choose_spec (Submodule.exists_isCompl _)

/-- The chosen `k`-basis of the complement in degree `n`. -/
noncomputable def Bas (n : ℕ) :
    Module.Basis (Module.Basis.ofVectorSpaceIndex k (Ccompl 𝒜 ℳ n)) k (Ccompl 𝒜 ℳ n) :=
  Module.Basis.ofVectorSpace k _

/-- The index set of the homogeneous basis: pairs of a degree `n` and a basis vector of the
complement in degree `n`. -/
def Idx : Type w := Σ n : ℕ, (Module.Basis.ofVectorSpaceIndex k (Ccompl 𝒜 ℳ n))

/-- The inclusion of the degree-`n` complement into `M`. -/
noncomputable def incl (n : ℕ) : (Ccompl 𝒜 ℳ n) →ₗ[k] M :=
  (ℳ n).subtype ∘ₗ (Ccompl 𝒜 ℳ n).subtype

/-- The candidate homogeneous basis. -/
noncomputable def bfun (p : Idx 𝒜 ℳ) : M := incl 𝒜 ℳ p.1 (Bas 𝒜 ℳ p.1 p.2)

variable {𝒜 ℳ} in
/-- `bfun 𝒜 ℳ p ∈ ℳ p.1`. -/
theorem bfun_mem (p : Idx 𝒜 ℳ) : bfun 𝒜 ℳ p ∈ ℳ p.1 := (Bas 𝒜 ℳ p.1 p.2 : (ℳ p.1)).2

variable {𝒜 ℳ} in
/-- `bfun 𝒜 ℳ p`, as an element of `ℳ p.1`, lies in `Ccompl 𝒜 ℳ p.1`. -/
theorem bfun_mem_Ccompl (p : Idx 𝒜 ℳ) :
    (⟨bfun 𝒜 ℳ p, bfun_mem p⟩ : (ℳ p.1)) ∈ Ccompl 𝒜 ℳ p.1 :=
  (Bas 𝒜 ℳ p.1 p.2).2

/-! ### Spanning -/

section Spanning

variable [IsScalarTower k R M]

/-- Each graded piece `ℳ n` lies in the `R`-span of the vectors `bfun 𝒜 ℳ p`. -/
theorem grade_le_span (n : ℕ) :
    ℳ n ≤ Submodule.restrictScalars k (Submodule.span R (Set.range (bfun 𝒜 ℳ))) := by
  -- Strong induction on `n`: `ℳ n = Gsub n ⊕ Ccompl n`. The part in `Gsub n` is a combination of
  -- `a • w` with `w` of lower degree (induction), and `Ccompl n` is spanned by vectors `bfun`.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy
    have hsup : Submodule.comap (ℳ n).subtype (Gsub 𝒜 ℳ n) ⊔ Ccompl 𝒜 ℳ n = ⊤ :=
      (isCompl_Ccompl 𝒜 ℳ n).sup_eq_top
    have hmem : (⟨y, hy⟩ : (ℳ n)) ∈
        Submodule.comap (ℳ n).subtype (Gsub 𝒜 ℳ n) ⊔ Ccompl 𝒜 ℳ n := by
      rw [hsup]; trivial
    obtain ⟨g, hg, c, hc, hgc⟩ := Submodule.mem_sup.1 hmem
    have hy' : y = (g : M) + (c : M) := by
      simpa using (Subtype.ext_iff.1 hgc).symm
    have hGspan : Gsub 𝒜 ℳ n ≤
        Submodule.restrictScalars k (Submodule.span R (Set.range (bfun 𝒜 ℳ))) := by
      refine Submodule.span_le.2 ?_
      rintro x ⟨i, j, hi, rfl, a, ha, w, hw, rfl⟩
      have hws : w ∈ Submodule.span R (Set.range (bfun 𝒜 ℳ)) := ih j (by omega) hw
      exact Submodule.smul_mem _ a hws
    have hcspan : (c : M) ∈ Submodule.span R (Set.range (bfun 𝒜 ℳ)) := by
      have hc' : c ∈ Ccompl 𝒜 ℳ n := hc
      have hcb : (⟨c, hc'⟩ : (Ccompl 𝒜 ℳ n)) ∈
          Submodule.span k (Set.range (Bas 𝒜 ℳ n)) := by
        rw [(Bas 𝒜 ℳ n).span_eq]; trivial
      have hmap := Submodule.mem_map_of_mem (f := incl 𝒜 ℳ n) hcb
      rw [Submodule.map_span] at hmap
      have hsubset : (incl 𝒜 ℳ n) '' (Set.range (Bas 𝒜 ℳ n)) ⊆
          Set.range (bfun 𝒜 ℳ) := by
        rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨⟨n, t⟩, rfl⟩
      exact (Submodule.span_le_restrictScalars k R _) ((Submodule.span_mono hsubset) hmap)
    rw [hy']
    exact add_mem (hGspan hg) hcspan

end Spanning

variable [DirectSum.Decomposition ℳ]

/-- The projection of `M` onto its degree-`n` piece. -/
noncomputable def dproj (n : ℕ) : M →ₗ[k] (ℳ n) :=
  (DirectSum.component k ℕ (fun i => (ℳ i)) n) ∘ₗ (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

variable {ℳ} in
/-- `dproj ℳ n y`, as an element of `M`, is the degree-`n` component `decompose ℳ y n`. -/
theorem dproj_coe (n : ℕ) (y : M) : (dproj ℳ n y : M) = (DirectSum.decompose ℳ y n : M) := rfl

variable {ℳ} in
/-- For `y ∈ ℳ n`, `dproj ℳ n y = ⟨y, hy⟩`. -/
theorem dproj_of_mem {n : ℕ} {y : M} (hy : y ∈ ℳ n) : dproj ℳ n y = ⟨y, hy⟩ := by
  apply Subtype.ext
  rw [dproj_coe]
  exact DirectSum.decompose_of_mem_same ℳ hy

variable {ℳ} in
/-- For `y ∈ ℳ m` with `m ≠ n`, `dproj ℳ n y = 0`. -/
theorem dproj_of_mem_ne {n m : ℕ} {y : M} (hy : y ∈ ℳ m) (h : m ≠ n) : dproj ℳ n y = 0 := by
  apply Subtype.ext
  rw [dproj_coe]
  simpa using DirectSum.decompose_of_mem_ne ℳ hy h

section ScalarTower

variable [IsScalarTower k R M]

/-- The vectors `bfun 𝒜 ℳ p` span `M` over `R`. -/
theorem span_range_bfun_eq_top : Submodule.span R (Set.range (bfun 𝒜 ℳ)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ (⨆ n, ℳ n) := by rw [iSup_grade_module_eq_top ℳ]; trivial
  exact (iSup_le (grade_le_span 𝒜 ℳ)) hy

variable [GradedAlgebra 𝒜]

/-- `J · M` is contained in the span of the graded pieces `Gsub`. -/
theorem posSmulTop_le :
    Submodule.restrictScalars k (posIdeal 𝒜 • (⊤ : Submodule R M)) ≤ ⨆ n, Gsub 𝒜 ℳ n := by
  intro x hx
  simp only [Submodule.restrictScalars_mem] at hx
  refine Submodule.smul_induction_on hx ?_ (fun x y hx hy => add_mem hx hy)
  intro a ha y _
  have step : ∀ i : ℕ, 1 ≤ i → ∀ b ∈ 𝒜 i, ∀ z : M, b • z ∈ ⨆ n, Gsub 𝒜 ℳ n := by
    intro i hi b hb z
    have h : (⨆ j, ℳ j) ≤ Submodule.comap
        ((LinearMap.lsmul R M b).restrictScalars k) (⨆ n, Gsub 𝒜 ℳ n) := by
      refine iSup_le fun j => ?_
      intro w hw
      simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
      exact Submodule.mem_iSup_of_mem (i + j) (smul_mem_Gsub (by omega) hb hw)
    exact h (by rw [iSup_grade_module_eq_top ℳ]; trivial)
  have h : Rge 𝒜 1 ≤ Submodule.comap
      ((LinearMap.toSpanSingleton R M y).restrictScalars k) (⨆ n, Gsub 𝒜 ℳ n) := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    intro b hb
    simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars,
      LinearMap.toSpanSingleton_apply]
    exact step i hi b hb y
  exact h ha

end ScalarTower

/-! ### The dual functionals -/

/-- The coordinate functional attached to a basis index. -/
noncomputable def eps (p : Idx 𝒜 ℳ) : M →ₗ[k] k :=
  ((Bas 𝒜 ℳ p.1).coord p.2) ∘ₗ
    (Submodule.projectionOnto _ _ (isCompl_Ccompl 𝒜 ℳ p.1).symm) ∘ₗ dproj ℳ p.1

variable {𝒜 ℳ} in
/-- On an element `y` of `Ccompl 𝒜 ℳ p.1`, `eps 𝒜 ℳ p y` is the `p.2`-th coordinate of
`y` in the basis `Bas 𝒜 ℳ p.1`. -/
theorem eps_apply_of_mem_Ccompl (p : Idx 𝒜 ℳ) {y : M} (hy : y ∈ ℳ p.1)
    (hc : (⟨y, hy⟩ : (ℳ p.1)) ∈ Ccompl 𝒜 ℳ p.1) :
    eps 𝒜 ℳ p y = (Bas 𝒜 ℳ p.1).coord p.2 ⟨⟨y, hy⟩, hc⟩ := by
  have hproj : (Submodule.projectionOnto _ _ (isCompl_Ccompl 𝒜 ℳ p.1).symm)
      (⟨y, hy⟩ : (ℳ p.1)) = ⟨⟨y, hy⟩, hc⟩ :=
    Submodule.projectionOnto_apply_left (isCompl_Ccompl 𝒜 ℳ p.1).symm ⟨⟨y, hy⟩, hc⟩
  simp only [eps, LinearMap.coe_comp, Function.comp_apply, dproj_of_mem hy, hproj]

variable {𝒜 ℳ} in
/-- `eps 𝒜 ℳ p (bfun 𝒜 ℳ p) = 1`. -/
theorem eps_bfun_self (p : Idx 𝒜 ℳ) : eps 𝒜 ℳ p (bfun 𝒜 ℳ p) = 1 := by
  rw [eps_apply_of_mem_Ccompl p (bfun_mem p) (bfun_mem_Ccompl p)]
  have he : (⟨⟨bfun 𝒜 ℳ p, bfun_mem p⟩, bfun_mem_Ccompl p⟩ : (Ccompl 𝒜 ℳ p.1))
      = Bas 𝒜 ℳ p.1 p.2 := rfl
  rw [he]
  simp

variable {𝒜 ℳ} in
/-- For `p ≠ q`, `eps 𝒜 ℳ p (bfun 𝒜 ℳ q) = 0`. -/
theorem eps_bfun_ne {p q : Idx 𝒜 ℳ} (h : p ≠ q) : eps 𝒜 ℳ p (bfun 𝒜 ℳ q) = 0 := by
  by_cases hn : q.1 = p.1
  · obtain ⟨n, t⟩ := p
    obtain ⟨n', t'⟩ := q
    simp only at hn
    subst hn
    have ht : t' ≠ t := fun hc => h (by rw [hc])
    have hy : bfun 𝒜 ℳ (⟨n', t'⟩ : Idx 𝒜 ℳ) ∈ ℳ n' := bfun_mem (⟨n', t'⟩ : Idx 𝒜 ℳ)
    have hcm : (⟨bfun 𝒜 ℳ (⟨n', t'⟩ : Idx 𝒜 ℳ), hy⟩ : (ℳ n')) ∈ Ccompl 𝒜 ℳ n' :=
      bfun_mem_Ccompl (⟨n', t'⟩ : Idx 𝒜 ℳ)
    rw [eps_apply_of_mem_Ccompl (⟨n', t⟩ : Idx 𝒜 ℳ) hy hcm]
    have he : (⟨⟨bfun 𝒜 ℳ (⟨n', t'⟩ : Idx 𝒜 ℳ), hy⟩, hcm⟩ : (Ccompl 𝒜 ℳ n'))
        = Bas 𝒜 ℳ n' t' := rfl
    rw [he]
    simpa [Module.Basis.coord] using Finsupp.single_eq_of_ne (Ne.symm ht)
  · simp only [eps, LinearMap.coe_comp, Function.comp_apply,
      dproj_of_mem_ne (bfun_mem q) hn, map_zero]

variable [SetLike.GradedSMul 𝒜 ℳ]

variable {𝒜 ℳ} in
/-- `eps 𝒜 ℳ p` vanishes on `Gsub 𝒜 ℳ n`. -/
theorem eps_eq_zero_of_mem_Gsub (p : Idx 𝒜 ℳ) {n : ℕ} {y : M} (hy : y ∈ Gsub 𝒜 ℳ n) :
    eps 𝒜 ℳ p y = 0 := by
  by_cases hn : n = p.1
  · rw [hn] at hy
    have hm : y ∈ ℳ p.1 := gsub_le 𝒜 ℳ p.1 hy
    have hG : (⟨y, hm⟩ : (ℳ p.1)) ∈ Submodule.comap (ℳ p.1).subtype (Gsub 𝒜 ℳ p.1) := hy
    have hproj : (Submodule.projectionOnto _ _ (isCompl_Ccompl 𝒜 ℳ p.1).symm)
        (⟨y, hm⟩ : (ℳ p.1)) = 0 :=
      Submodule.projectionOnto_apply_right (isCompl_Ccompl 𝒜 ℳ p.1).symm ⟨⟨y, hm⟩, hG⟩
    simp only [eps, LinearMap.coe_comp, Function.comp_apply, dproj_of_mem hm, hproj, map_zero]
  · simp only [eps, LinearMap.coe_comp, Function.comp_apply,
      dproj_of_mem_ne (gsub_le 𝒜 ℳ n hy) hn, map_zero]

variable {𝒜 ℳ} in
/-- `eps 𝒜 ℳ p` vanishes on `⨆ n, Gsub 𝒜 ℳ n`. -/
theorem eps_eq_zero_of_mem_iSup_Gsub (p : Idx 𝒜 ℳ) {y : M} (hy : y ∈ ⨆ n, Gsub 𝒜 ℳ n) :
    eps 𝒜 ℳ p y = 0 := by
  have h : (⨆ n, Gsub 𝒜 ℳ n) ≤ LinearMap.ker (eps 𝒜 ℳ p) :=
    iSup_le fun n => fun z hz => eps_eq_zero_of_mem_Gsub p hz
  exact h hy

variable [IsScalarTower k R M] [GradedAlgebra 𝒜]

/-! ### Independence -/

/-- If every element of `𝒜 0` is a scalar, the kernel of
`Finsupp.linearCombination R (bfun 𝒜 ℳ)` is contained in `posIdeal 𝒜 • ⊤`. -/
theorem ker_le_posIdeal_smul_top
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) :
    LinearMap.ker (Finsupp.linearCombination R (bfun 𝒜 ℳ)) ≤
      posIdeal 𝒜 • (⊤ : Submodule R (Idx 𝒜 ℳ →₀ R)) := by
  classical
  -- Write each coefficient `c j = λⱼ + (c j - λⱼ)` with `λⱼ` its degree-`0` part, a scalar `μⱼ`.
  -- From `∑ c j • bⱼ = 0`, `∑ μⱼ bⱼ ∈ ⨆ n, Gsub n`, so the functionals `eps` give `μⱼ = 0`.
  intro c hc
  refine finsupp_mem_smul_top _ c ?_
  set lam : Idx 𝒜 ℳ → R := fun j => (DirectSum.decompose 𝒜 (c j) 0 : R) with hlamdef
  have hlam0 : ∀ j, lam j ∈ 𝒜 0 := fun j => (DirectSum.decompose 𝒜 (c j) 0).2
  choose mu hmu using fun j => h0 (lam j) (hlam0 j)
  have hsub : ∀ j, c j - lam j ∈ posIdeal 𝒜 := fun j => sub_decompose_zero_mem 𝒜 (c j)
  have hrel : ∑ j ∈ c.support, c j • bfun 𝒜 ℳ j = 0 := by
    have hk := LinearMap.mem_ker.1 hc
    rwa [Finsupp.linearCombination_apply, Finsupp.sum] at hk
  have hlowmem : ∑ j ∈ c.support, (c j - lam j) • bfun 𝒜 ℳ j ∈ ⨆ n, Gsub 𝒜 ℳ n := by
    refine posSmulTop_le 𝒜 ℳ ?_
    simp only [Submodule.restrictScalars_mem]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hsub j) Submodule.mem_top
  have hsplit : ∑ j ∈ c.support, mu j • bfun 𝒜 ℳ j
      = -∑ j ∈ c.support, (c j - lam j) • bfun 𝒜 ℳ j := by
    have hmus : ∀ j, mu j • bfun 𝒜 ℳ j = lam j • bfun 𝒜 ℳ j := by
      intro j
      rw [hmu j, algebraMap_smul]
    rw [Finset.sum_congr rfl (fun j _ => hmus j), eq_neg_iff_add_eq_zero,
      ← Finset.sum_add_distrib, ← hrel]
    exact Finset.sum_congr rfl fun j _ => by rw [← add_smul]; ring_nf
  have hmain : ∑ j ∈ c.support, mu j • bfun 𝒜 ℳ j ∈ ⨆ n, Gsub 𝒜 ℳ n := by
    rw [hsplit]; exact neg_mem hlowmem
  have hmu0 : ∀ j ∈ c.support, mu j = 0 := by
    intro p hp
    have happ := eps_eq_zero_of_mem_iSup_Gsub p hmain
    rw [map_sum] at happ
    have hterm : ∀ j ∈ c.support, eps 𝒜 ℳ p (mu j • bfun 𝒜 ℳ j)
        = if j = p then mu p else 0 := by
      intro j _
      rw [map_smul]
      by_cases hj : j = p
      · subst hj; rw [eps_bfun_self]; simp
      · rw [eps_bfun_ne (Ne.symm hj)]; simp [hj]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' c.support p] at happ
    simpa [hp] using happ
  intro j
  by_cases hj : j ∈ c.support
  · have hlz : lam j = 0 := by rw [hmu j, hmu0 j hj, map_zero]
    have h2 := hsub j
    rwa [hlz, sub_zero] at h2
  · rw [Finsupp.notMem_support_iff.1 hj]
    exact zero_mem _

/-! ### The main theorem -/

variable [Module.Flat R M]

/-- If `M` is flat over `R` and every element of `𝒜 0` is a scalar, the vectors
`bfun 𝒜 ℳ p` are linearly independent over `R`. -/
theorem linearIndependent_bfun
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) :
    LinearIndependent R (bfun 𝒜 ℳ) := by
  classical
  set F := Idx 𝒜 ℳ →₀ R
  set phi := Finsupp.linearCombination R (bfun 𝒜 ℳ) with hphi
  have hsurj : Function.Surjective phi := by
    rw [← LinearMap.range_eq_top, hphi, Finsupp.range_linearCombination]
    exact span_range_bfun_eq_top 𝒜 ℳ
  set N := LinearMap.ker phi with hN
  have : Module.Flat R (F ⧸ N) := Module.Flat.of_linearEquiv (phi.quotKerEquivOfSurjective hsurj)
  have hNle : N ≤ posIdeal 𝒜 • (⊤ : Submodule R F) := ker_le_posIdeal_smul_top 𝒜 ℳ h0
  have hNJ : N ≤ posIdeal 𝒜 • N := fun x hx =>
    Submodule.inter_smul_top_le_smul N (posIdeal 𝒜) ⟨hNle hx, hx⟩
  have hpow : ∀ m : ℕ, N ≤ (posIdeal 𝒜 ^ m) • (⊤ : Submodule R F) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc N ≤ posIdeal 𝒜 • N := hNJ
          _ ≤ posIdeal 𝒜 • ((posIdeal 𝒜 ^ m) • (⊤ : Submodule R F)) :=
              Submodule.smul_mono le_rfl ih
          _ = (posIdeal 𝒜 * posIdeal 𝒜 ^ m) • (⊤ : Submodule R F) := by
              rw [← Submodule.smul_assoc, smul_eq_mul]
          _ = (posIdeal 𝒜 ^ (m + 1)) • (⊤ : Submodule R F) := by rw [← pow_succ']
  rw [linearIndependent_iff]
  intro c hcz
  have hc : c ∈ N := LinearMap.mem_ker.2 hcz
  ext j
  refine eq_zero_of_mem_Rge_all 𝒜 (fun m => ?_)
  exact posIdeal_pow_le 𝒜 m (apply_mem_of_mem_smul_top _ c (hpow m hc) j)

/-- **Graded flat implies graded free.**  A homogeneous `R`-basis of a flat graded module over a
connected graded algebra. -/
noncomputable def homBasis
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) :
    Module.Basis (Idx 𝒜 ℳ) R M :=
  Module.Basis.mk (linearIndependent_bfun 𝒜 ℳ h0)
    (le_of_eq (span_range_bfun_eq_top 𝒜 ℳ).symm)

/-- `homBasis 𝒜 ℳ h0 p = bfun 𝒜 ℳ p`. -/
@[simp] theorem homBasis_apply
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) (p : Idx 𝒜 ℳ) :
    homBasis 𝒜 ℳ h0 p = bfun 𝒜 ℳ p := by
  simp [homBasis]

/-- The basis produced by `homBasis` is homogeneous: the vector indexed by `p` lies in the
graded piece of degree `p.1`. -/
theorem homBasis_mem
    (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) (p : Idx 𝒜 ℳ) :
    homBasis 𝒜 ℳ h0 p ∈ ℳ p.1 := by
  rw [homBasis_apply]; exact bfun_mem p

/-- A flat graded module over a connected graded algebra has a homogeneous basis. -/
theorem exists_homogeneous_basis (h0 : ∀ a ∈ 𝒜 0, ∃ c : k, a = algebraMap k R c) :
    ∃ (ι : Type w) (d : ι → ℕ) (B : Module.Basis ι R M), ∀ i, B i ∈ ℳ (d i) :=
  ⟨Idx 𝒜 ℳ, fun p => p.1, homBasis 𝒜 ℳ h0, homBasis_mem 𝒜 ℳ h0⟩

end GradedModule

end HopfAlgebra.Graded.Free
