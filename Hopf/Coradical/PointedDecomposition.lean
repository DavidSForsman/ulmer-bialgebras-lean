module

public import Hopf.Coradical.ArtinianDecomp
public import Hopf.Coradical.Irreducible
public import Hopf.Coradical.Exhaustive

/-!
# Kostant's decomposition theorem for finite-dimensional cocommutative coalgebras

Let `k` be a field and `C` a finite-dimensional cocommutative `k`-coalgebra.  Its dual `A = C*`
is a finite-dimensional commutative algebra, hence a commutative Artinian ring, and the annihilator
correspondence exchanges

* subcoalgebras of `C` and ideals of `A`;
* simple subcoalgebras and maximal ideals;
* the wedge product and the product of ideals.

By `Hopf/Coradical/ArtinianDecomp.lean` there is an `N ≥ 1` with `⋂_M M^N = 0`, the
powers `M^n` are constant for `n ≥ N`, and `M^N` is comaximal with the intersection of the other
`T^N`.  Dualising these three facts gives **Kostant's theorem**: `C` is the direct sum of the
irreducible components of its simple subcoalgebras.

## Main results

* `Coalgebra.Coradical.ann_irrComponent` — the annihilator of the irreducible component of a simple
  subcoalgebra `S` is `(ann S)^N`;
* `Coalgebra.Coradical.iSup_irrComponent_eq_top` — the irreducible components span `C`;
* `Coalgebra.Coradical.irrComponent_inf_iSup_eq_bot` — the sum is direct.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*][atiyah_introduction_1969],
  Chapter 8
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C]

/-! ### Lattice properties of the annihilator -/

/-- The annihilator of a supremum is the infimum of the annihilators. -/
theorem ann_iSup {ι : Sort*} (W : ι → Submodule k C) :
    ann (⨆ i, W i) = ⨅ i, ann (W i) := by
  refine le_antisymm (le_iInf fun i => ann_antitone (le_iSup W i)) ?_
  intro f hf
  rw [Submodule.mem_iInf] at hf
  rw [mem_ann]
  intro c hc
  have hle : (⨆ i, W i) ≤ LinearMap.ker (f.ofConv) :=
    iSup_le fun i x hx => LinearMap.mem_ker.2 (mem_ann.1 (hf i) x hx)
  exact hle hc

variable [Coalgebra k C]

/-- The annihilator in `C` of `I ⊔ J` is the intersection of those of `I` and `J`. -/
theorem coann_sup (I J : Submodule k (Coalgebra.Coradical.DualAlg k C)) :
    coann (I ⊔ J) = coann I ⊓ coann J := by
  refine le_antisymm (le_inf (coann_antitone le_sup_left) (coann_antitone le_sup_right)) ?_
  rintro c ⟨hcI, hcJ⟩
  rw [mem_coann]
  intro f hf
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
  have : (a + b).ofConv = a.ofConv + b.ofConv := rfl
  rw [this]
  simp [mem_coann.1 hcI a ha, mem_coann.1 hcJ b hb]

/-- For finite-dimensional `C`: `ann (X ⊓ Y) = ann X ⊔ ann Y`. -/
theorem ann_inf [FiniteDimensional k C] (X Y : Submodule k C) :
    ann (X ⊓ Y) = ann X ⊔ ann Y := by
  conv_lhs => rw [← coann_ann X, ← coann_ann Y, ← coann_sup, ann_coann]

/-! ### The annihilator of a wedge power -/

/-- For finite-dimensional `C`: `ann (X^{∧(n+1)}) = (ann X) ^ (n + 1)`. -/
theorem ann_wedgePow [FiniteDimensional k C] (X : Submodule k C) :
    ∀ n, ann (wedgePow X n) = ann X ^ (n + 1)
  | 0 => by simp [Submodule.pow_one]
  | (n + 1) => by
      rw [wedgePow_succ, ann_wedge, ann_wedgePow X n, ← Submodule.pow_succ]

/-- For finite-dimensional `C`: `ann (irrComponent X) = ⨅ n, (ann X) ^ (n + 1)`. -/
theorem ann_irrComponent_eq_iInf [FiniteDimensional k C] (X : Submodule k C) :
    ann (irrComponent X) = ⨅ n : ℕ, ann X ^ (n + 1) := by
  rw [irrComponent, ann_iSup]
  exact iInf_congr fun n => ann_wedgePow X n

/-- For `n ≠ 0`, the `n`-th power of the ideal `annIdeal W hW`, as a `k`-subspace, is
`(ann W) ^ n`. -/
theorem restrictScalars_annIdeal_pow {W : Submodule k C} (hW : IsSubcoalgebra W) {n : ℕ}
    (hn : n ≠ 0) :
    Submodule.restrictScalars k ((annIdeal W hW) ^ n) = ann W ^ n := by
  rw [Submodule.restrictScalars_pow hn, restrictScalars_annIdeal]

/-- The annihilator of a simple subcoalgebra determines it. -/
theorem eq_of_annIdeal_eq {S T : Submodule k C} (hS : IsSimpleSubcoalgebra S)
    (hT : IsSimpleSubcoalgebra T) (h : annIdeal S hS.1 = annIdeal T hT.1) : S = T := by
  refine ann_injective ?_
  rw [← restrictScalars_annIdeal S hS.1, ← restrictScalars_annIdeal T hT.1, h]

/-! ### The finite-dimensional cocommutative case -/

section Cocomm

variable [IsCocomm k C] [FiniteDimensional k C]

/-- **The annihilator of a simple subcoalgebra is a maximal ideal** of the dual algebra. -/
theorem isMaximal_annIdeal {S : Submodule k C} (hS : IsSimpleSubcoalgebra S) :
    (annIdeal S hS.1).IsMaximal := by
  constructor
  constructor
  · intro htop
    have hann : ann S = ⊤ := by
      rw [← restrictScalars_annIdeal S hS.1, htop, Submodule.restrictScalars_top]
    exact hS.2.1 (by rw [← coann_ann S, hann, coann_top])
  · intro J hJ
    set V : Submodule k C := coann (Submodule.restrictScalars k J) with hV
    have hannV : ann V = Submodule.restrictScalars k J := ann_coann _
    have hVsub : IsSubcoalgebra V :=
      isSubcoalgebra_of_isTwoSided_ann (hannV ▸ isTwoSided_restrictScalars J)
    have hVS : V ≤ S := by
      have := coann_antitone (Submodule.restrictScalars_mono (le_of_lt hJ)
        (S := k) (R := Coalgebra.Coradical.DualAlg k C))
      rw [restrictScalars_annIdeal S hS.1, coann_ann] at this
      exact this
    rcases hS.2.2 V hVS hVsub with h | h
    · have : Submodule.restrictScalars k J =
          (⊤ : Submodule k (Coalgebra.Coradical.DualAlg k C)) := by
        rw [← hannV, h, ann_bot]
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 this
    · exfalso
      have : ann V = ann S := by rw [h]
      rw [hannV, ← restrictScalars_annIdeal S hS.1] at this
      exact absurd (Submodule.restrictScalars_injective k _ _ this).symm (ne_of_lt hJ)

section Fixed

variable {N : ℕ} (hN0 : 0 < N)
  (hN : (ArtinianAux.maximalFinset (Coalgebra.Coradical.DualAlg k C)).inf (fun M => M ^ N) = ⊥)
include hN0 hN

/-- **The annihilator of the irreducible component of a simple subcoalgebra `S`** is the `N`-th
power of the maximal ideal `ann S`, for `N` an exponent with `⋂_M M^N = 0`. -/
theorem ann_irrComponent {S : Submodule k C} (hS : IsSimpleSubcoalgebra S) :
    ann (irrComponent S) = Submodule.restrictScalars k ((annIdeal S hS.1) ^ N) := by
  have hM := isMaximal_annIdeal hS
  rw [ann_irrComponent_eq_iInf]
  have hrw : ∀ n : ℕ, ann S ^ (n + 1)
      = Submodule.restrictScalars k ((annIdeal S hS.1) ^ (n + 1)) :=
    fun n => (restrictScalars_annIdeal_pow hS.1 (Nat.succ_ne_zero n)).symm
  simp only [hrw]
  rw [← Submodule.restrictScalars_iInf]
  congr 1
  refine le_antisymm ?_ (le_iInf fun n => ArtinianAux.pow_le_pow_maximal hN hN0 hM (n + 1))
  refine le_trans (iInf_le _ (N - 1)) (le_of_eq ?_)
  congr 1
  omega

end Fixed

/-- **Kostant's theorem, first half**: the irreducible components of the simple subcoalgebras of a
finite-dimensional cocommutative coalgebra span it. -/
theorem iSup_irrComponent_eq_top :
    (⨆ S ∈ {S : Submodule k C | IsSimpleSubcoalgebra S}, irrComponent S) = ⊤ := by
  obtain ⟨N, hN0, hN⟩ :=
    ArtinianAux.exists_inf_pow_maximal_eq_bot (A := Coalgebra.Coradical.DualAlg k C)
  refine ann_injective ?_
  rw [ann_top]
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  refine ArtinianAux.eq_zero_of_mem_pow_maximal hN fun M hM => ?_
  set S : Submodule k C := coann (Submodule.restrictScalars k M) with hSdef
  have hSs : IsSimpleSubcoalgebra S := isSimpleSubcoalgebra_coann_maximal M hM
  have hannS : ann S = Submodule.restrictScalars k M := ann_coann _
  have h1 : f ∈ ann (wedgePow S (N - 1)) :=
    ann_antitone ((wedgePow_le_irrComponent S (N - 1)).trans
      (le_iSup₂ (f := fun S (_ : S ∈ {S : Submodule k C | IsSimpleSubcoalgebra S}) =>
        irrComponent S) S hSs)) hf
  rw [ann_wedgePow, hannS, ← Submodule.restrictScalars_pow (by omega),
    show N - 1 + 1 = N by omega] at h1
  exact h1

/-- **Kostant's theorem, second half**: the sum of the irreducible components is direct. -/
theorem irrComponent_inf_iSup_eq_bot {S : Submodule k C} (hS : IsSimpleSubcoalgebra S) :
    irrComponent S ⊓
        (⨆ T ∈ {T : Submodule k C | IsSimpleSubcoalgebra T ∧ T ≠ S}, irrComponent T) = ⊥ := by
  obtain ⟨N, hN0, hN⟩ :=
    ArtinianAux.exists_inf_pow_maximal_eq_bot (A := Coalgebra.Coradical.DualAlg k C)
  set M : Ideal (Coalgebra.Coradical.DualAlg k C) := annIdeal S hS.1 with hMdef
  have hM : M.IsMaximal := isMaximal_annIdeal hS
  refine ann_injective ?_
  rw [ann_bot, ann_inf, eq_top_iff]
  -- the annihilator of the other components contains the intersection of the other `U ^ N`
  have hother : Submodule.restrictScalars k
      (⨅ U ∈ {U : Ideal (Coalgebra.Coradical.DualAlg k C) | U.IsMaximal ∧ U ≠ M}, U ^ N)
      ≤ ann (⨆ T ∈ {T : Submodule k C | IsSimpleSubcoalgebra T ∧ T ≠ S}, irrComponent T) := by
    rw [ann_iSup]
    refine le_iInf fun T => ?_
    rw [ann_iSup]
    refine le_iInf fun hT => ?_
    rw [ann_irrComponent hN0 hN hT.1]
    have hmem : annIdeal T hT.1.1 ∈
        {U : Ideal (Coalgebra.Coradical.DualAlg k C) | U.IsMaximal ∧ U ≠ M} :=
      ⟨isMaximal_annIdeal hT.1, fun h => hT.2 (eq_of_annIdeal_eq hT.1 hS h)⟩
    exact Submodule.restrictScalars_mono k (iInf₂_le (annIdeal T hT.1.1) hmem)
  refine le_trans (le_of_eq ?_)
    (sup_le_sup (le_of_eq (ann_irrComponent hN0 hN hS).symm) hother)
  rw [← Submodule.restrictScalars_sup, ArtinianAux.sup_biInf_ne_eq_top hM N,
    Submodule.restrictScalars_top]

end Cocomm

end Coalgebra.Coradical
