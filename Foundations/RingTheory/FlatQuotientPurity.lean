module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Submodules with flat quotient, and a criterion for faithful flatness

This file contains two pieces of elementary commutative algebra which are used in Takeuchi's
Proposition 2.4 (*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta
math. **7** (1972), 251–270), where they are quoted from Bourbaki.

The first is the "purity" statement that a submodule `N ≤ M` whose quotient `M ⧸ N` is flat
satisfies `N ∩ I·M = I·N` for every ideal `I`; it is proved here directly from Mathlib's
equational criterion for flatness, avoiding any use of `Tor`.

The second is the resulting criterion for faithful flatness: an injective ring map `R → S`
whose cokernel `S ⧸ R` is a flat `R`-module and with `S` flat over `R` is faithfully flat.

## Main results

* `Module.FaithfullyFlat.mem_ideal_smul_of_mem_of_flat_quotient`: `N ∩ I·M ⊆ I·N` when `M ⧸ N` is
  flat;
* `Module.FaithfullyFlat.faithfullyFlat_of_flat_quotient`: the criterion for faithful flatness.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Proposition 2.4
* [N. Bourbaki, *Algèbre commutative, Chapitres 1 à 4*][bourbakiAlgebreCommutative1985], Chapter I
  (flatness), as quoted by Takeuchi
-/

@[expose] public section

namespace Module.FaithfullyFlat

open TensorProduct

section Purity

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Purity for a flat quotient**: if `M ⧸ N` is a flat `R`-module, then every element of `N`
which lies in `I·M` already lies in `I·N`, for any ideal `I` of `R`. -/
theorem mem_ideal_smul_of_mem_of_flat_quotient (N : Submodule R M) (I : Ideal R)
    [Module.Flat R (M ⧸ N)] {x : M} (hxN : x ∈ N) (hxI : x ∈ I • (⊤ : Submodule R M)) :
    x ∈ I • N := by
  classical
  have htop : (⊤ : Submodule R M) = Submodule.span R (Set.range (id : M → M)) := by
    simp
  rw [htop] at hxI
  obtain ⟨a, ha, hsum⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum I id x).1 hxI
  set s : Finset M := a.support with hs
  -- the relation `∑ a m • m = x` becomes a relation `∑ a m • [m] = 0` in `M ⧸ N`
  set f : ↥s → R := fun i => a (i : M) with hf
  set y : ↥s → M := fun i => (i : M) with hy
  have hx : ∑ i : ↥s, f i • y i = x := by
    rw [← hsum, Finsupp.sum]
    exact (Finset.sum_coe_sort s fun m => a m • m)
  have hrel : ∑ i : ↥s, f i • (N.mkQ (y i)) = 0 := by
    have hmap : N.mkQ (∑ i : ↥s, f i • y i) = ∑ i : ↥s, f i • N.mkQ (y i) := by
      rw [map_sum]; simp
    rw [← hmap, hx, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hxN
  obtain ⟨k, c, z, hz1, hz2⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R) (M := M ⧸ N) hrel
  -- lift the `z j` to `M`
  choose w hw using fun j : Fin k => N.mkQ_surjective (z j)
  -- the differences lie in `N`
  have hdiff : ∀ i : ↥s, y i - ∑ j, c i j • w j ∈ N := by
    intro i
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hw]
    rw [← hz1 i, sub_self]
  have hsplit : x = ∑ i : ↥s, f i • (y i - ∑ j, c i j • w j) := by
    have h1 : ∀ i : ↥s, f i • (y i - ∑ j, c i j • w j)
        = f i • y i - ∑ j, (f i * c i j) • w j := by
      intro i
      rw [smul_sub, Finset.smul_sum]
      simp [smul_smul]
    have h2 : ∑ i : ↥s, f i • (y i - ∑ j, c i j • w j)
        = (∑ i : ↥s, f i • y i) - ∑ i : ↥s, ∑ j : Fin k, (f i * c i j) • w j := by
      simp only [h1]
      rw [Finset.sum_sub_distrib]
    have h3 : ∑ i : ↥s, ∑ j : Fin k, (f i * c i j) • w j = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.sum_smul, hz2 j, zero_smul]
    rw [h2, h3, hx, sub_zero]
  rw [hsplit]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (ha _) (hdiff i)

end Purity

section FaithfullyFlat

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

/-- **A criterion for faithful flatness**: if `R → S` is injective, `S` is a flat `R`-module and
the cokernel `S ⧸ R` is also flat, then `S` is faithfully flat over `R`. -/
theorem faithfullyFlat_of_flat_quotient [Module.Flat R S]
    (hinj : Function.Injective (algebraMap R S))
    [Module.Flat R (S ⧸ LinearMap.range (Algebra.linearMap R S))] :
    Module.FaithfullyFlat R S := by
  set N : Submodule R S := LinearMap.range (Algebra.linearMap R S)
  refine ⟨fun {m} hm hmtop => ?_⟩
  have hone : (1 : S) ∈ m • (⊤ : Submodule R S) := by rw [hmtop]; exact Submodule.mem_top
  have honeN : (1 : S) ∈ N := ⟨1, by simp⟩
  have honemN : (1 : S) ∈ m • N := mem_ideal_smul_of_mem_of_flat_quotient N m honeN hone
  have hle : m • N ≤ Submodule.map (Algebra.linearMap R S) m := by
    refine Submodule.smul_le.2 fun a ha n hn => ?_
    obtain ⟨r, rfl⟩ := hn
    exact ⟨a * r, m.mul_mem_right r ha, by simp [Algebra.smul_def]⟩
  obtain ⟨r, hrm, hr⟩ := hle honemN
  have : r = 1 := hinj (by simpa using hr)
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m (this ▸ hrm) isUnit_one)

end FaithfullyFlat

end Module.FaithfullyFlat
