module

public import Hopf.Graded.GrHomBasis
public import Hopf.Graded.GrProj
public import Hopf.Graded.FreeBasis

/-!
# From a homogeneous basis of `gr H` over `gr A` to a Sweedler basis

Let `S : HopfAlgebra.Graded.HopfSplit k H` be a split filtered Hopf algebra and `A ⊆ H` a subalgebra
preserved by the projections of the splitting.  Given a basis `B` of the associated graded
algebra `S.Gr` over `gr A` consisting of homogeneous elements of degrees `d j`, the elements
`b j = emb (B j) ∈ C (d j) ⊆ F (d j)` form a **Sweedler basis** of the filtration:

* *graded spanning*: `Fₙ ⊆ Σⱼ (A ⊓ F (n - d j)) · b j`;
* *graded independence*: a combination of the `b j` with coefficients of admissible degrees
  which drops the filtration degree has all its coefficients of smaller degree.

Both are immediate consequences of the fact that `cmp N` turns such a combination into the
corresponding combination of the `B j` with coefficients in `gr A`.

## Main results

* `HopfAlgebra.Graded.HopfSplit.sbElt`: the elements `b j = emb (B j)` attached to a homogeneous
  basis `B`.
* `HopfAlgebra.Graded.HopfSplit.span_le`: graded spanning, `Fₙ ≤ ⨆ⱼ (coefSub A F d n j) · b j`.
* `HopfAlgebra.Graded.HopfSplit.gradedIndependent_zero`: if `∑ⱼ aⱼ bⱼ = 0` with coefficients in
  `coefSub A F d 0 j`, then all `aⱼ = 0`.
* `HopfAlgebra.Graded.HopfSplit.gradedIndependent_step`: if the coefficients lie in
  `coefSub A F d (n + 1) j` and `∑ⱼ aⱼ bⱼ ∈ Fₙ`, then each `aⱼ ∈ coefSub A F d n j`.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical
open Module.FilteredFree

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] {S : HopfSplit k H}
  {A : Subalgebra k H} {hprA : ∀ n, ∀ a ∈ A, S.pr n a ∈ A} {h1A : (1 : H) ∈ A}
  {ι : Type u} {d : ι → ℕ}

section

variable (B : Module.Basis ι ↥(S.grSub A hprA h1A) S.Gr)

/-- The candidate Sweedler basis attached to a homogeneous basis of the associated graded. -/
noncomputable def sbElt (j : ι) : H := S.emb (B j)

variable (hB : ∀ i, B i ∈ S.grPiece (d i))

include hB

/-- The candidate basis element `b j = emb (B j)` lies in `F (d j)`. -/
theorem sbElt_mem_F (j : ι) : sbElt B j ∈ S.F (d j) := S.c_le_f _ (hB j)

/-- Multiplying by a basis element and taking the degree-`N` component. -/
theorem cmp_mul_sbElt {j : ι} {m N : ℕ} (hmN : m + d j = N) {a : H} (ha : a ∈ S.F m) :
    S.cmp N (a * sbElt B j) = S.cmp m a * B j := by
  subst hmN
  rw [← S.cmp_mul_cmp ha (sbElt_mem_F B hB j)]
  congr 1
  exact (eq_cmp_emb (hB j)).symm

end

/-! ### Independence -/

/-- With `d j ≤ N`, an admissible coefficient in degree `N` lies in `F (N - d j)`. -/
theorem mem_F_of_mem_coefSub {N : ℕ} {j : ι} {x : H} (hd : d j ≤ N)
    (hx : x ∈ coefSub A S.F d N j) : x ∈ S.F (N - d j) := by
  unfold coefSub at hx
  rw [ite_eq_left hd] at hx
  exact hx.2

/-- With `d j > N`, the only admissible coefficient in degree `N` is `0`. -/
theorem eq_zero_of_mem_coefSub {N : ℕ} {j : ι} {x : H} (hd : ¬d j ≤ N)
    (hx : x ∈ coefSub A S.F d N j) : x = 0 := by
  unfold coefSub at hx
  rw [ite_eq_right hd] at hx
  simpa using hx

section Independence

variable (B : Module.Basis ι ↥(S.grSub A hprA h1A) S.Gr) (hB : ∀ i, B i ∈ S.grPiece (d i))

include hB

/-- If `cmp N (∑ j ∈ s, a j * sbElt B j) = 0` with each `a j ∈ coefSub A F d N j`, then
`pr (N - d j) (a j) = 0` for all `j ∈ s`. -/
theorem pr_eq_zero_of_cmp_sum_eq_zero (N : ℕ) (s : Finset ι) (a : ι → H)
    (ha : ∀ j ∈ s, a j ∈ coefSub A S.F d N j)
    (hsum : S.cmp N (∑ j ∈ s, a j * sbElt B j) = 0) :
    ∀ j ∈ s, S.pr (N - d j) (a j) = 0 := by
  classical
  -- The classes `αⱼ = cmp (N - d j) aⱼ` in `gr A` satisfy `∑ⱼ αⱼ Bⱼ = cmp N (∑ⱼ aⱼ bⱼ) = 0`, so
  -- they vanish by the independence of the basis `B`.
  set a' : ι → H := fun j => if j ∈ s then a j else 0 with ha'def
  have ha'A : ∀ j, a' j ∈ A := by
    intro j
    by_cases hj : j ∈ s
    · simpa [ha'def, hj] using coefSub_le_A N j (ha j hj)
    · simp [ha'def, hj]
  set α : ι → ↥(S.grSub A hprA h1A) :=
    fun j => cmpToGrSub hprA h1A (N - d j) ⟨a' j, ha'A j⟩ with hαdef
  have hαcoe : ∀ j, ((α j : ↥(S.grSub A hprA h1A)) : S.Gr) = S.cmp (N - d j) (a' j) :=
    fun j => rfl
  have hterm : ∀ j ∈ s, α j • B j = S.cmp N (a j * sbElt B j) := by
    intro j hj
    have hsmul : α j • B j = ((α j : ↥(S.grSub A hprA h1A)) : S.Gr) * B j := rfl
    rw [hsmul, hαcoe, ha'def]
    simp only [hj, ite_true]
    by_cases hd : d j ≤ N
    · have haF : a j ∈ S.F (N - d j) := by
        exact mem_F_of_mem_coefSub hd (ha j hj)
      exact (cmp_mul_sbElt B hB (by omega) haF).symm
    · have ha0 : a j = 0 := by
        exact eq_zero_of_mem_coefSub hd (ha j hj)
      rw [ha0]
      simp
  have hzero : ∑ j ∈ s, α j • B j = 0 := by
    rw [Finset.sum_congr rfl hterm, ← map_sum]
    exact hsum
  have hα0 := linearIndependent_iff'.1 B.linearIndependent s α hzero
  intro j hj
  have : ((α j : ↥(S.grSub A hprA h1A)) : S.Gr) = 0 := by rw [hα0 j hj, ZeroMemClass.coe_zero]
  rw [hαcoe, ha'def] at this
  simp only [hj, ite_true] at this
  have hemb := congr(S.emb $this)
  rwa [S.emb_cmp, map_zero] at hemb

/-- Graded independence in degree `0`: if `∑ⱼ aⱼ bⱼ = 0` with each `aⱼ` in `coefSub A F d 0 j`, then
all `aⱼ = 0`. -/
theorem gradedIndependent_zero (s : Finset ι) (a : ι → H)
    (ha : ∀ j ∈ s, a j ∈ coefSub A S.F d 0 j)
    (hsum : ∑ j ∈ s, a j * sbElt B j = 0) : ∀ j ∈ s, a j = 0 := by
  classical
  have hcmp : S.cmp 0 (∑ j ∈ s, a j * sbElt B j) = 0 := by rw [hsum, map_zero]
  have hpr := pr_eq_zero_of_cmp_sum_eq_zero B hB 0 s a ha hcmp
  intro j hj
  by_cases hd : d j ≤ 0
  · have hdz : d j = 0 := Nat.le_zero.1 hd
    have haF : a j ∈ S.F (0 - d j) := by
      exact mem_F_of_mem_coefSub hd (ha j hj)
    have h0 : a j ∈ S.F 0 := by simpa [hdz] using haF
    have hp := hpr j hj
    simp only [hdz, Nat.sub_self] at hp
    rwa [S.toSplit.pr_zero_of_mem_F_zero h0] at hp
  · exact eq_zero_of_mem_coefSub hd (ha j hj)

/-- Graded independence, one step: if the coefficients lie in `coefSub A F d (n + 1) j` and `∑ⱼ aⱼ
bⱼ ∈ F n`, then each `aⱼ` lies in `coefSub A F d n j`. -/
theorem gradedIndependent_step (n : ℕ) (s : Finset ι) (a : ι → H)
    (ha : ∀ j ∈ s, a j ∈ coefSub A S.F d (n + 1) j)
    (hsum : ∑ j ∈ s, a j * sbElt B j ∈ S.F n) :
    ∀ j ∈ s, a j ∈ coefSub A S.F d n j := by
  classical
  have hcmp : S.cmp (n + 1) (∑ j ∈ s, a j * sbElt B j) = 0 :=
    S.cmp_eq_zero_of_mem_lt (by omega) hsum
  have hpr := pr_eq_zero_of_cmp_sum_eq_zero B hB (n + 1) s a ha hcmp
  intro j hj
  by_cases hd : d j ≤ n
  · have haF : a j ∈ S.F (n + 1 - d j) := by
      exact mem_F_of_mem_coefSub (by omega) (ha j hj)
    have haA : a j ∈ A := coefSub_le_A (n + 1) j (ha j hj)
    have hidx : n + 1 - d j = (n - d j) + 1 := by omega
    rw [hidx] at haF
    have hpr' : S.pr ((n - d j) + 1) (a j) = 0 := by
      have := hpr j hj
      rwa [hidx] at this
    exact mem_coefSub haA hd (S.toSplit.mem_F_pred_of_pr_eq_zero haF hpr')
  · have ha0 : a j = 0 := by
      by_cases hd1 : d j ≤ n + 1
      · have haF : a j ∈ S.F (n + 1 - d j) := by
          exact mem_F_of_mem_coefSub hd1 (ha j hj)
        have hidx : n + 1 - d j = 0 := by omega
        rw [hidx] at haF
        have := hpr j hj
        rw [hidx] at this
        rwa [S.toSplit.pr_zero_of_mem_F_zero haF] at this
      · exact eq_zero_of_mem_coefSub hd1 (ha j hj)
    rw [ha0]
    exact Submodule.zero_mem _

end Independence

/-! ### Spanning -/

/-- `coefSub A F d m j ≤ coefSub A F d n j` whenever `m ≤ n`. -/
theorem coefSub_mono {m n : ℕ} (hmn : m ≤ n) (j : ι) :
    coefSub A S.F d m j ≤ coefSub A S.F d n j := by
  classical
  unfold coefSub
  by_cases hd : d j ≤ m
  · rw [ite_eq_left hd, ite_eq_left (by omega)]
    exact inf_le_inf_left _ (S.mono (by omega))
  · rw [ite_eq_right hd]
    exact bot_le

section Spanning

variable (B : Module.Basis ι ↥(S.grSub A hprA h1A) S.Gr) (hB : ∀ i, B i ∈ S.grPiece (d i))

include hB

/-- The top-degree approximation step. -/
theorem span_aux (n : ℕ) (x : H) (hx : x ∈ S.F n) :
    ∃ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ coefSub A S.F d n j) ∧
      x - ∑ j ∈ s, a j * sbElt B j ∈ S.F n ∧
      S.pr n (x - ∑ j ∈ s, a j * sbElt B j) = 0 := by
  classical
  set g : S.Gr := S.cmp n x with hgdef
  set r := B.repr g with hrdef
  set s : Finset ι := r.support.filter (fun j => d j ≤ n) with hsdef
  set α : ι → ↥(S.grSub A hprA h1A) :=
    fun j => cmpToGrSub hprA h1A (n - d j) ⟨S.emb (r j), (r j).2⟩ with hαdef
  set a : ι → H := fun j => S.pr (n - d j) (S.emb (r j)) with hadef
  have hαcoe : ∀ j, ((α j : ↥(S.grSub A hprA h1A)) : S.Gr)
      = S.hproj (n - d j) ((r j : ↥(S.grSub A hprA h1A)) : S.Gr) := fun j => rfl
  have haA : ∀ j, a j ∈ A := fun j => hprA _ _ (r j).2
  have haC : ∀ j, a j ∈ S.C (n - d j) := fun j => S.toSplit.pr_mem_C _ _
  have hamem : ∀ j ∈ s, a j ∈ coefSub A S.F d n j := by
    intro j hj
    have hd : d j ≤ n := (Finset.mem_filter.1 hj).2
    exact mem_coefSub (haA j) hd (S.c_le_f _ (haC j))
  have hcmpa : ∀ j, S.cmp (n - d j) (a j) = ((α j : ↥(S.grSub A hprA h1A)) : S.Gr) := by
    intro j
    rw [hαcoe, hproj_apply, hadef]
    exact S.cmp_pr _ _
  -- the degree-`n` component of the approximation is `g`
  have hgsum : ∑ j ∈ r.support, ((r j : ↥(S.grSub A hprA h1A)) : S.Gr) * B j = g := by
    have := B.linearCombination_repr g
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at this
    exact this
  have hkey : S.cmp n (∑ j ∈ s, a j * sbElt B j) = g := by
    rw [map_sum]
    have hterm : ∀ j ∈ s, S.cmp n (a j * sbElt B j)
        = S.hproj n (((r j : ↥(S.grSub A hprA h1A)) : S.Gr) * B j) := by
      intro j hj
      have hd : d j ≤ n := (Finset.mem_filter.1 hj).2
      rw [cmp_mul_sbElt B hB (by omega : (n - d j) + d j = n) (S.c_le_f _ (haC j)),
        hproj_mul hd _ (hB j), hcmpa j, hαcoe j]
    rw [Finset.sum_congr rfl hterm]
    have hrest : ∀ j ∈ r.support, j ∉ s →
        S.hproj n (((r j : ↥(S.grSub A hprA h1A)) : S.Gr) * B j) = 0 := by
      intro j hj hjs
      have hd : ¬ d j ≤ n := by
        intro hd
        exact hjs (Finset.mem_filter.2 ⟨hj, hd⟩)
      exact hproj_mul_of_lt (by omega) _ (hB j)
    rw [Finset.sum_subset (Finset.filter_subset _ _) hrest, ← map_sum, hgsum]
    exact hproj_eq_self (S.cmp_mem_grPiece n x)
  refine ⟨s, a, hamem, ?_, ?_⟩
  · refine Submodule.sub_mem _ hx (Submodule.sum_mem _ fun j hj => ?_)
    have hd : d j ≤ n := (Finset.mem_filter.1 hj).2
    have := S.mul_mem (n - d j) (d j)
      (Submodule.mul_mem_mul (S.c_le_f _ (haC j)) (sbElt_mem_F B hB j))
    rwa [show n - d j + d j = n by omega] at this
  · have h1 : S.pr n (∑ j ∈ s, a j * sbElt B j) = S.pr n x := by
      have := congr(S.emb $hkey)
      rwa [S.emb_cmp, S.emb_cmp] at this
    rw [map_sub, h1, sub_self]

/-- Graded spanning: `Fₙ ⊆ ⨆ⱼ (coefSub A F d n j) · bⱼ`, i.e. every element of `Fₙ` is a combination
of the `bⱼ` with coefficients of admissible degree in `A`. -/
theorem span_le (n : ℕ) :
    S.F n ≤ ⨆ j : ι, Submodule.map (LinearMap.mulRight k (sbElt B j))
      (coefSub A S.F d n j) := by
  classical
  -- By `span_aux`, `x = ∑ⱼ aⱼ bⱼ + y` with admissible `aⱼ` and `pr n y = 0`; in degree `0` this
  -- gives `y = 0`, and in degree `n + 1` it gives `y ∈ Fₙ`, covered by induction.
  induction n with
  | zero =>
      intro x hx
      obtain ⟨s, a, hamem, hymem, hy0⟩ := span_aux B hB 0 x hx
      have hy : x - ∑ j ∈ s, a j * sbElt B j = 0 := by
        rw [← S.toSplit.pr_zero_of_mem_F_zero hymem, hy0]
      rw [sub_eq_zero.1 hy]
      refine Submodule.sum_mem _ fun j hj => ?_
      exact Submodule.mem_iSup_of_mem j ⟨a j, hamem j hj, rfl⟩
  | succ n ih =>
      intro x hx
      obtain ⟨s, a, hamem, hymem, hy0⟩ := span_aux B hB (n + 1) x hx
      have hyF : x - ∑ j ∈ s, a j * sbElt B j ∈ S.F n :=
        S.toSplit.mem_F_pred_of_pr_eq_zero hymem hy0
      have hy := ih hyF
      have hmono : (⨆ j : ι, Submodule.map (LinearMap.mulRight k (sbElt B j))
          (coefSub A S.F d n j))
          ≤ ⨆ j : ι, Submodule.map (LinearMap.mulRight k (sbElt B j))
          (coefSub A S.F d (n + 1) j) :=
        iSup_mono fun j => Submodule.map_mono (coefSub_mono (by omega) j)
      have hy' := hmono hy
      have hsum : ∑ j ∈ s, a j * sbElt B j ∈ ⨆ j : ι,
          Submodule.map (LinearMap.mulRight k (sbElt B j)) (coefSub A S.F d (n + 1) j) := by
        refine Submodule.sum_mem _ fun j hj => ?_
        exact Submodule.mem_iSup_of_mem j ⟨a j, hamem j hj, rfl⟩
      have : x = (x - ∑ j ∈ s, a j * sbElt B j) + ∑ j ∈ s, a j * sbElt B j := by abel
      rw [this]
      exact Submodule.add_mem _ hy' hsum

end Spanning

end HopfSplit

end HopfAlgebra.Graded
