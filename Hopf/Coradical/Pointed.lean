module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Henselian
public import Hopf.Coradical.Transfer
public import Hopf.Coradical.Exhaustive

/-!
# Group-like elements and one-dimensional subcoalgebras

This file relates group-like elements of a coalgebra over a field to its one-dimensional and
simple subcoalgebras.

## Main results

* `Coalgebra.Coradical.isSimpleSubcoalgebra_span_groupLike`: the line spanned by a group-like
  element is a simple subcoalgebra.
* `Coalgebra.Coradical.exists_groupLike_of_finrank_eq_one`: conversely, a one-dimensional
  subcoalgebra is spanned by a group-like element.
* `Coalgebra.Coradical.finiteDimensional_of_isSimpleSubcoalgebra`: a simple subcoalgebra is
  finite-dimensional.
* `Coalgebra.Coradical.exists_groupLike_of_isSimpleSubcoalgebra`: over an algebraically closed
  field, every simple subcoalgebra of a cocommutative coalgebra is spanned by a group-like element.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Chapter 5
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

variable {k C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

omit [Coalgebra k C] in
/-- `tens (k x) (k y) = k (x ⊗ y)`. -/
theorem tens_span_singleton (x y : C) :
    tens (Submodule.span k {x}) (Submodule.span k {y})
      = Submodule.span k {x ⊗ₜ[k] y} := by
  rw [tens, Submodule.map₂_span_span]
  congr 1
  ext t
  simp [Set.image2, eq_comm]

/-- The line spanned by a group-like element is a subcoalgebra. -/
theorem isSubcoalgebra_span_groupLike {g : C} (hg : IsGroupLikeElem k g) :
    IsSubcoalgebra (Submodule.span k {g}) := by
  rw [isSubcoalgebra_iff]
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, hg.comul_eq_tmul_self, tens_span_singleton]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A group-like element is nonzero. -/
theorem groupLike_ne_zero {g : C} (hg : IsGroupLikeElem k g) : g ≠ 0 := by
  intro h
  have := hg.counit_eq_one
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The line spanned by a group-like element is a simple subcoalgebra. -/
theorem isSimpleSubcoalgebra_span_groupLike {g : C} (hg : IsGroupLikeElem k g) :
    IsSimpleSubcoalgebra (Submodule.span k {g}) := by
  refine ⟨isSubcoalgebra_span_groupLike hg, ?_, ?_⟩
  · simp [groupLike_ne_zero hg]
  · intro V hV _
    by_cases hV0 : V = ⊥
    · exact Or.inl hV0
    refine Or.inr (le_antisymm hV ?_)
    obtain ⟨v, hvV, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hV hvV)
    have hc : c ≠ 0 := by rintro rfl; simp at hv0
    rw [Submodule.span_le, Set.singleton_subset_iff]
    have : c⁻¹ • (c • g) ∈ V := V.smul_mem _ hvV
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- A one-dimensional subcoalgebra is spanned by a group-like element. -/
theorem exists_groupLike_of_finrank_eq_one {W : Submodule k C} (hW : IsSubcoalgebra W)
    (h : Module.finrank k W = 1) :
    ∃ g : C, IsGroupLikeElem k g ∧ W = Submodule.span k {g} := by
  -- `W` is spanned by any nonzero `x ∈ W`, and `Δ x ∈ W ⊗ W` is `c • x ⊗ x`
  have : FiniteDimensional k W := .of_finrank_eq_succ h
  have hW0 : W ≠ ⊥ := by
    intro hbot
    rw [hbot] at h
    simp at h
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hspan : Submodule.span k {x} = W :=
    Submodule.eq_of_le_of_finrank_eq (by simpa [Submodule.span_le] using hxW)
      (by rw [finrank_span_singleton hx0, h])
  have hmem : comul (R := k) x ∈ tens (Submodule.span k {x}) (Submodule.span k {x}) := by
    rw [hspan]
    exact comul_mem_tens hW hxW
  rw [tens_span_singleton, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  -- the counit axiom gives `c ε(x) = 1`, so `g = c • x` is group-like and spans `W`
  have key : (c * counit (R := k) x) • x = x := by
    have h1 := rTensor_counit_comul (R := k) x
    rw [← hc, map_smul] at h1
    have h2 := congr(TensorProduct.lid k C $h1)
    simpa [smul_smul] using h2
  have hc1 : c * counit (R := k) x = 1 :=
    smul_left_injective k hx0 (by simpa using key)
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc1
  refine ⟨c • x, ⟨?_, ?_⟩, ?_⟩
  · rw [map_smul, smul_eq_mul, hc1]
  · rw [map_smul, ← hc]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
  · rw [← hspan]
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      have : c⁻¹ • (c • x) ∈ Submodule.span k {c • x} :=
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- A simple subcoalgebra is finite-dimensional. -/
theorem finiteDimensional_of_isSimpleSubcoalgebra {W : Submodule k C}
    (hW : IsSimpleSubcoalgebra W) : FiniteDimensional k W := by
  obtain ⟨hWsub, hW0, hWmin⟩ := hW
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨E, hxE, hEfg, hE⟩ := Coalgebra.LocallyFinite.exists_fg_subcoalgebra (k := k) x
  have : FiniteDimensional k E := (Submodule.fg_iff_finiteDimensional E).1 hEfg
  have hinf : IsSubcoalgebra (E ⊓ W) := isSubcoalgebra_inf hE hWsub
  have hinf0 : (E ⊓ W : Submodule k C) ≠ ⊥ := by
    intro h
    exact hx0 ((Submodule.mem_bot k).1 (h ▸ Submodule.mem_inf.2 ⟨hxE, hxW⟩))
  rcases hWmin _ inf_le_right hinf with h | h
  · exact absurd h hinf0
  · exact Submodule.finiteDimensional_of_le (h ▸ inf_le_left)

section AlgClosed

variable {E : Type u} [AddCommGroup E] [Module k E] [Coalgebra k E]

/-- The whole coalgebra is a subcoalgebra. -/
theorem isSubcoalgebra_top : IsSubcoalgebra (⊤ : Submodule k E) := by
  rw [isSubcoalgebra_iff]
  intro x _
  rw [tens_top_top]
  exact Submodule.mem_top

/-- The counit of a nonzero coalgebra is nonzero, so its dual algebra is nontrivial. -/
theorem nontrivial_dualAlg [Nontrivial E] : Nontrivial (Coalgebra.Coradical.DualAlg k E) := by
  refine ⟨1, 0, fun h => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hcounit : (counit : E →ₗ[k] k) = 0 := by
    ext y
    have := congr(($h).ofConv y)
    simpa using this
  have h1 := rTensor_counit_comul (R := k) x
  rw [hcounit] at h1
  have h2 := congr(TensorProduct.lid k E $h1)
  simp at h2
  exact hx h2.symm

variable [IsCocomm k E] [FiniteDimensional k E]

/-- If a finite-dimensional cocommutative coalgebra has no subcoalgebras besides `⊥` and `⊤`,
then its dual algebra has no ideals besides `⊥` and `⊤`. -/
theorem ideal_eq_bot_or_eq_top (hE : IsSimpleSubcoalgebra (⊤ : Submodule k E))
    (I : Ideal (Coalgebra.Coradical.DualAlg k E)) : I = ⊥ ∨ I = ⊤ := by
  have hann : ann (coann (Submodule.restrictScalars k I)) = Submodule.restrictScalars k I :=
    ann_coann _
  have hsub : IsSubcoalgebra (coann (Submodule.restrictScalars k I)) := by
    refine isSubcoalgebra_of_isTwoSided_ann ?_
    rw [hann]
    exact isTwoSided_restrictScalars I
  rcases hE.2.2 _ le_top hsub with h | h
  · right
    refine Submodule.restrictScalars_injective k _ _ ?_
    rw [← hann, h, ann_bot, Submodule.restrictScalars_top]
  · left
    refine Submodule.restrictScalars_injective k _ _ ?_
    rw [← hann, h, ann_top, Submodule.restrictScalars_bot]

/-- The dual algebra of a finite-dimensional cocommutative simple coalgebra is a field. -/
theorem isField_dualAlg (hE : IsSimpleSubcoalgebra (⊤ : Submodule k E)) :
    IsField (Coalgebra.Coradical.DualAlg k E) := by
  have : Nontrivial E := by
    rcases subsingleton_or_nontrivial E with h | h
    · exact absurd (Subsingleton.elim _ _) hE.2.1
    · exact h
  have := nontrivial_dualAlg (k := k) (E := E)
  refine ⟨exists_pair_ne _, mul_comm, fun {a} ha => ?_⟩
  rcases ideal_eq_bot_or_eq_top hE (Ideal.span {a}) with h | h
  · exact absurd (Ideal.span_singleton_eq_bot.1 h) ha
  · have : (1 : Coalgebra.Coradical.DualAlg k E) ∈ Ideal.span {a} := by rw [h]; trivial
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨b, by rw [mul_comm]; exact hb⟩

/-- Over an algebraically closed field, a finite-dimensional cocommutative simple coalgebra is
one-dimensional. -/
theorem finrank_eq_one_of_isSimple [IsAlgClosed k]
    (hE : IsSimpleSubcoalgebra (⊤ : Submodule k E)) : Module.finrank k E = 1 := by
  let : Field (Coalgebra.Coradical.DualAlg k E) := (isField_dualAlg hE).toField
  have : Algebra.IsIntegral k (Coalgebra.Coradical.DualAlg k E) := Algebra.IsIntegral.of_finite _ _
  have hsurj : Function.Surjective (algebraMap k (Coalgebra.Coradical.DualAlg k E)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2
  have hspan : Submodule.span k {(1 : Coalgebra.Coradical.DualAlg k E)} = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨r, rfl⟩ := hsurj a
    exact Submodule.mem_span_singleton.2 ⟨r, by rw [Algebra.algebraMap_eq_smul_one]⟩
  have hone : Module.finrank k (Coalgebra.Coradical.DualAlg k E) = 1 := by
    rw [← finrank_top k (Coalgebra.Coradical.DualAlg k E), ← hspan,
      finrank_span_singleton one_ne_zero]
  have hdual : Module.finrank k (Coalgebra.Coradical.DualAlg k E) = Module.finrank k E := by
    rw [(WithConv.linearEquiv k (E →ₗ[k] k)).finrank_eq]
    exact Subspace.dual_finrank_eq
  rw [← hdual, hone]

end AlgClosed

/-- Over an algebraically closed field, every simple subcoalgebra of a cocommutative coalgebra is
the line spanned by a group-like element. -/
theorem exists_groupLike_of_isSimpleSubcoalgebra [IsAlgClosed k] [IsCocomm k C]
    {W : Submodule k C} (hW : IsSimpleSubcoalgebra W) :
    ∃ g : C, IsGroupLikeElem k g ∧ W = Submodule.span k {g} := by
  have := finiteDimensional_of_isSimpleSubcoalgebra hW
  let : Coalgebra k W := subCoalgebra hW.1
  have : IsCocomm k W := ⟨subComul_comm hW.1⟩
  have hcomul : map W.subtype W.subtype ∘ₗ (comul : W →ₗ[k] W ⊗[k] W)
      = comul ∘ₗ W.subtype := map_subtype_comp_subComul hW.1
  have : Nontrivial W := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW.2.1
    exact ⟨⟨0, ⟨x, hxW⟩, fun h => hx0 (Subtype.ext_iff.1 h).symm⟩⟩
  have htop : IsSimpleSubcoalgebra (⊤ : Submodule k W) := by
    refine ⟨isSubcoalgebra_top, ?_, ?_⟩
    · obtain ⟨y, hy⟩ := exists_ne (0 : W)
      intro h
      exact hy ((Submodule.mem_bot k).1 (h ▸ Submodule.mem_top))
    · intro V _ hV
      have h1 : IsSubcoalgebra (V.map W.subtype) := isSubcoalgebra_map hcomul hV
      have h2 : V.map W.subtype ≤ W := Submodule.map_subtype_le W V
      have hinj : Function.Injective (W.subtype) := Submodule.subtype_injective W
      rcases hW.2.2 _ h2 h1 with h | h
      · left
        have := congr(Submodule.comap W.subtype $h)
        rwa [Submodule.comap_map_eq_of_injective hinj, Submodule.comap_bot,
          LinearMap.ker_eq_bot.2 hinj] at this
      · right
        have hV1 : Submodule.map W.subtype V = Submodule.map W.subtype ⊤ := by
          rw [h, Submodule.map_top, Submodule.range_subtype]
        have := congr(Submodule.comap W.subtype $hV1)
        rwa [Submodule.comap_map_eq_of_injective hinj,
          Submodule.comap_map_eq_of_injective hinj] at this
  have hrank : Module.finrank k W = 1 := finrank_eq_one_of_isSimple htop
  exact exists_groupLike_of_finrank_eq_one hW.1 hrank

end Coalgebra.Coradical
