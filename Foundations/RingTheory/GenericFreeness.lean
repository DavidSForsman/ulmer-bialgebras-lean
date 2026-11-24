module

public import Mathlib.RingTheory.PicardGroup

/-!
# Generic freeness over an integral domain

A finitely generated module `M` over a commutative integral domain `B` becomes *free* after
inverting a single nonzero element of `B`:

> there is `g ≠ 0` in `B` such that the localization `M_g` is a free `B_g`-module.

This is Lemma 3.4 of M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*
(manuscripta math. **7** (1972), 251–270), where it is quoted from Bourbaki and used in the proof
of the faithful flatness theorem for reduced Hopf subalgebras.  It is also the "generic freeness"
input of Waterhouse's proof of the same theorem.  Mathlib does not contain it in this form.  This
file proves the freeness criterion behind it; the statement itself is proved, over a reduced
noetherian ring, as `Module.Free.exists_free_localizedModule_of_isReduced` in
`Foundations/RingTheory/GenericFreenessReduced.lean`.

The proof is the classical one.  Over the fraction field `F` of `B` the localization `V` of `M`
is a finite dimensional vector space; choose elements `mᵢ ∈ M` whose images form a basis of `V`.
The resulting map `Bⁿ → M` is injective (linear independence over `F`) and its cokernel is
torsion, hence killed by a single `g ≠ 0` (there are finitely many generators).  After inverting
`g` the map becomes bijective, so `M_g` is free.

## Main results

* `Module.Free.free_localizedModule_of_torsion_basis`: the criterion — a finite family `(mᵢ)` of
  elements of `M` which is independent up to `g`-torsion and generates `M` up to multiplication by
  `g` makes `M_g` free.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Lemma
  3.4
* [A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*][EGAIV2], Section 6.9
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Chapter 14
-/

@[expose] public section

namespace Module.Free


section MkSum

variable {B : Type*} [CommRing B] {S : Submonoid B} {M : Type*} [AddCommGroup M] [Module B M]

/-- A finite sum of fractions with a common denominator. -/
lemma localizedModule_mk_sum {ι : Type*} (t : Finset ι) (f : ι → M) (s : S) :
    ∑ i ∈ t, LocalizedModule.mk (f i) s = LocalizedModule.mk (∑ i ∈ t, f i) s := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, LocalizedModule.mk_add_mk,
      LocalizedModule.mk_eq]
    exact ⟨1, by simp [smul_add, smul_smul, mul_comm]⟩

end MkSum

section Criterion

variable {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M] [Module B M]

variable {ι : Type*} [Fintype ι] (m : ι → M) (g : B)

/-- The map `(cᵢ) ↦ ∑ cᵢ • (mᵢ / 1)` from `B_g^ι` to `M_g`. -/
noncomputable abbrev mkCombination :
    (ι → Localization.Away g) →ₗ[Localization.Away g] LocalizedModule (Submonoid.powers g) M :=
  Fintype.linearCombination (Localization.Away g)
    (fun i => LocalizedModule.mk (m i) (1 : Submonoid.powers g))

/-- `mkCombination` on a family of coefficients. -/
lemma mkCombination_apply (c : ι → Localization.Away g) :
    mkCombination m g c = ∑ i, c i • LocalizedModule.mk (m i) (1 : Submonoid.powers g) :=
  Fintype.linearCombination_apply _ _ c

variable {m g}

/-- If the `mᵢ` generate `M` after multiplication by `g`, then `mkCombination` is surjective. -/
lemma mkCombination_surjective (hspan : ∀ x : M, ∃ a : ι → B, g • x = ∑ i, a i • m i) :
    Function.Surjective (mkCombination m g) := by
  classical
  have hgS : g ∈ Submonoid.powers g := Submonoid.mem_powers g
  set Λ := mkCombination m g
  have hΛapply := mkCombination_apply m g
  intro y
  induction y using LocalizedModule.induction_on with
  | _ x s =>
    obtain ⟨a, ha⟩ := hspan x
    refine ⟨fun i => Localization.mk (a i) (⟨g, hgS⟩ * s), ?_⟩
    rw [hΛapply]
    have hstep : ∀ i, (Localization.mk (a i) (⟨g, hgS⟩ * s) : Localization.Away g) •
        LocalizedModule.mk (m i) (1 : Submonoid.powers g)
        = LocalizedModule.mk (a i • m i) (⟨g, hgS⟩ * s) := by
      intro i
      rw [LocalizedModule.mk_smul_mk, mul_one]
    simp only [hstep]
    rw [localizedModule_mk_sum, ← ha, LocalizedModule.mk_eq]
    exact ⟨1, by simp [mul_smul, mul_comm, smul_smul]⟩

/-- If every relation between the `mᵢ` is killed by `g`, then `mkCombination` is injective. -/
lemma mkCombination_injective (hindep : ∀ a : ι → B, ∑ i, a i • m i = 0 → ∀ i, g * a i = 0) :
    Function.Injective (mkCombination m g) := by
  classical
  have hgS : g ∈ Submonoid.powers g := Submonoid.mem_powers g
  set Λ := mkCombination m g
  have hΛapply := mkCombination_apply m g
  -- It suffices that the kernel is zero: clear denominators of `c`, and the relation becomes
  -- one between the `mᵢ`, which `g` kills.
  have hzero : ∀ c : ι → Localization.Away g, Λ c = 0 → c = 0 := by
    intro c hc
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers g)
      (Finset.univ : Finset ι) c
    choose a ha using fun i => ht i (Finset.mem_univ i)
    have hsmul : ∀ i, (algebraMap B (Localization.Away g)) (a i) = (t : B) • c i := fun i => ha i
    have hct : ∑ i, ((algebraMap B (Localization.Away g)) (a i)) •
        LocalizedModule.mk (m i) (1 : Submonoid.powers g) = 0 := by
      have h0 : (t : B) • (Λ c) = 0 := by rw [hc, smul_zero]
      rw [hΛapply] at h0
      rw [← h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hsmul i, smul_assoc]
    have hmk : LocalizedModule.mk (∑ i, a i • m i) (1 : Submonoid.powers g) = 0 := by
      have hstep : ∀ i, ((algebraMap B (Localization.Away g)) (a i)) •
          LocalizedModule.mk (m i) (1 : Submonoid.powers g)
          = LocalizedModule.mk (a i • m i) 1 := by
        intro i
        rw [algebraMap_smul, LocalizedModule.smul'_mk]
      simp only [hstep] at hct
      rw [← hct, localizedModule_mk_sum]
    rw [show (0 : LocalizedModule (Submonoid.powers g) M) = LocalizedModule.mk 0 1 from
      (LocalizedModule.zero_mk 1).symm, LocalizedModule.mk_eq] at hmk
    obtain ⟨u, hu⟩ := hmk
    simp only [one_smul, smul_zero] at hu
    have hfin : ∑ i, ((u : B) * a i) • m i = 0 := by
      have hu' : ((u : B)) • ∑ i, a i • m i = 0 := hu
      rw [Finset.smul_sum] at hu'
      rw [← hu']
      exact Finset.sum_congr rfl fun i _ => mul_smul _ _ _
    -- `g`, `u` and `t` are units in the localization, so each `c i` vanishes.
    have hzeroa : ∀ i, g * ((u : B) * a i) = 0 := hindep _ hfin
    funext i
    have hai : (algebraMap B (Localization.Away g)) (a i) = 0 := by
      have h1 : (algebraMap B (Localization.Away g)) g *
          ((algebraMap B (Localization.Away g)) (u : B) *
            (algebraMap B (Localization.Away g)) (a i)) = 0 := by
        rw [← map_mul, ← map_mul, hzeroa i, map_zero]
      have hu1 : IsUnit ((algebraMap B (Localization.Away g)) g) :=
        IsLocalization.map_units _ (⟨g, hgS⟩ : Submonoid.powers g)
      have hu2 : IsUnit ((algebraMap B (Localization.Away g)) (u : B)) :=
        IsLocalization.map_units _ u
      exact (hu2.mul_right_eq_zero).1 ((hu1.mul_right_eq_zero).1 h1)
    have h1 : (algebraMap B (Localization.Away g)) (t : B) * c i = 0 := by
      have h2 : (t : B) • c i = 0 := by rw [← hsmul i, hai]
      rwa [Algebra.smul_def] at h2
    have htunit : IsUnit ((algebraMap B (Localization.Away g)) (t : B)) :=
      IsLocalization.map_units _ t
    simpa using (htunit.mul_right_eq_zero).1 h1
  intro c d h
  have h0 : Λ (c - d) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.1 (hzero _ h0)

/-- If a finite family `(mᵢ)` of elements of `M` is linearly independent *after inverting `g`*
(any relation between the `mᵢ` is killed by `g`) and generates `M` after multiplication by `g`,
then the localization of `M` away from `g` is a free module over the localization of `B` away
from `g`. -/
theorem free_localizedModule_of_torsion_basis (m : ι → M) (g : B)
    (hindep : ∀ a : ι → B, ∑ i, a i • m i = 0 → ∀ i, g * a i = 0)
    (hspan : ∀ x : M, ∃ a : ι → B, g • x = ∑ i, a i • m i) :
    Module.Free (Localization.Away g) (LocalizedModule (Submonoid.powers g) M) :=
  Module.Free.of_equiv (LinearEquiv.ofBijective (mkCombination m g)
    ⟨mkCombination_injective hindep, mkCombination_surjective hspan⟩)

end Criterion

section GenericFreeness

variable (B : Type*) [CommRing B] [IsDomain B] (M : Type*) [AddCommGroup M] [Module B M]
  [Module.Finite B M]

end GenericFreeness

end Module.Free
