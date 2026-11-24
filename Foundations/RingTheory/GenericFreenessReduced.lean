module

public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Foundations.RingTheory.GenericFreeness

/-!
# Generic freeness over a reduced noetherian ring

This file proves **Lemma 3.4** of M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf
algebras* (manuscripta math. **7** (1972), 251–270):

> Let `M` be a finitely generated module over a commutative reduced noetherian ring `B`.  Then
> there exists a nonzero `g ∈ B` such that the localization `M_g` is a free `B_g`-module.

The proof given here is not Takeuchi's (which reduces to the case of a domain by inverting an
element and then uses a composition series); instead it works directly at a minimal prime `q` of
`B`.  Because `B` is reduced and `q` is minimal, the localization `B_q` is a *field*, so the
localization `M_q` is a vector space; choosing elements `mᵢ ∈ M` whose images form a basis, both
the relations between the `mᵢ` and the failure of the `mᵢ` to span are killed by elements outside
`q` — uniformly so, thanks to noetherianness — and the product `g` of those elements is not in
`q`, in particular nonzero.  Freeness of `M_g` then follows from the criterion
`Module.Free.free_localizedModule_of_torsion_basis`.

## Main results

* `Module.Free.exists_uniform_annihilator_of_relations`: over a noetherian ring, if every relation
  between finitely many elements is killed coefficientwise by *some* element of a submonoid `S`,
  then a single element of `S` kills all of them;
* `Module.Free.exists_free_localizedModule_of_isReduced`: **generic freeness** over a reduced
  noetherian ring (Takeuchi's Lemma 3.4).

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972], Lemma
  3.4
* [A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*][EGAIV2], Section 6.9
-/

@[expose] public section

namespace Module.Free

open Submodule

section UniformAnnihilator

variable {B : Type*} [CommRing B] [IsNoetherianRing B] {M : Type*} [AddCommGroup M] [Module B M]

/-- Over a noetherian ring, relations between a finite family `(mᵢ)` of elements of a module are
uniformly annihilated: if every relation is coefficientwise killed by some element of a submonoid
`S`, then one element of `S` kills the coefficients of all relations at once. -/
theorem exists_uniform_annihilator_of_relations {ι : Type*} [Fintype ι] (m : ι → M)
    (S : Submonoid B)
    (h : ∀ a : ι → B, ∑ i, a i • m i = 0 → ∀ i, ∃ t ∈ S, t * a i = 0) :
    ∃ t ∈ S, ∀ a : ι → B, ∑ i, a i • m i = 0 → ∀ i, t * a i = 0 := by
  classical
  set φ : (ι → B) →ₗ[B] M := Fintype.linearCombination B m with hφ
  have hφapply : ∀ a : ι → B, φ a = ∑ i, a i • m i := fun a =>
    Fintype.linearCombination_apply _ _ a
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian (LinearMap.ker φ)
  have hGker : ∀ a ∈ G, ∑ i, a i • m i = 0 := by
    intro a ha
    have : a ∈ LinearMap.ker φ := by
      rw [← hG]
      exact Submodule.subset_span ha
    rw [← hφapply]
    exact this
  have hpick : ∀ a ∈ G, ∃ t ∈ S, ∀ i, t * a i = 0 := by
    intro a ha
    choose t htS hta using h a (hGker a ha)
    refine ⟨∏ i, t i, S.prod_mem fun i _ => htS i, fun i => ?_⟩
    have hsplit : (∏ j, t j) = (∏ j ∈ Finset.univ.erase i, t j) * t i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [hsplit, mul_assoc, hta i, mul_zero]
  choose! tt httS httz using hpick
  set t : B := ∏ a ∈ G, tt a with hT
  refine ⟨t, S.prod_mem fun a ha => httS a ha, ?_⟩
  -- `t` kills every element of the kernel
  have hker : LinearMap.ker φ ≤ LinearMap.ker (LinearMap.lsmul B (ι → B) t) := by
    rw [← hG, Submodule.span_le]
    intro a ha
    have ht0 : t • a = 0 := by
      funext i
      have hsplit : t = (∏ b ∈ G.erase a, tt b) * tt a := by
        rw [hT, Finset.prod_erase_mul _ _ ha]
      change t * a i = 0
      rw [hsplit, mul_assoc, httz a ha i, mul_zero]
    simpa [LinearMap.mem_ker] using ht0
  intro a ha i
  have hmem : a ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, hφapply, ha]
  have := hker hmem
  rw [LinearMap.mem_ker] at this
  have h0 : t • a = 0 := this
  exact congrFun h0 i

end UniformAnnihilator

section LocalizedSpan

variable {B : Type*} [CommRing B] (S : Submonoid B) {M : Type*} [AddCommGroup M] [Module B M]

/-- The fractions `x / 1` of a spanning set of `M` span the localization `S⁻¹M` over `S⁻¹B`. -/
lemma span_mk_one_image_eq_top {s : Set M} (hs : span B s = ⊤) :
    span (Localization S) ((fun x : M => LocalizedModule.mk x (1 : S)) '' s) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  induction y using LocalizedModule.induction_on with
  | _ x t =>
    have hx : x ∈ span B s := hs ▸ trivial
    have hmem : LocalizedModule.mk x (1 : S) ∈
        span (Localization S) ((fun x : M => LocalizedModule.mk x (1 : S)) '' s) := by
      refine Submodule.span_induction (p := fun z _ => LocalizedModule.mk z (1 : S) ∈
        span (Localization S) ((fun x : M => LocalizedModule.mk x (1 : S)) '' s)) ?_ ?_ ?_ ?_ hx
      · intro z hz
        exact Submodule.subset_span ⟨z, hz, rfl⟩
      · simp
      · intro z w _ _ hz hw
        have hadd : LocalizedModule.mk (z + w) (1 : S)
            = LocalizedModule.mk z 1 + LocalizedModule.mk w 1 := by
          rw [LocalizedModule.mk_add_mk]
          simp
        rw [hadd]
        exact Submodule.add_mem _ hz hw
      · intro c z _ hz
        have hsm : LocalizedModule.mk (c • z) (1 : S) = c • LocalizedModule.mk z 1 :=
          (LocalizedModule.smul'_mk c z 1).symm
        rw [hsm, ← algebraMap_smul (Localization S) c]
        exact Submodule.smul_mem _ _ hz
    have hunit : LocalizedModule.mk x t
        = (Localization.mk 1 t : Localization S) • LocalizedModule.mk x (1 : S) := by
      rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
    rw [hunit]
    exact Submodule.smul_mem _ _ hmem

variable {S}

/-- A combination of lifts `mᵢ` of elements `vᵢ` of `S⁻¹M`, with coefficients in `B`, is the
fraction of the combination of the `mᵢ`. -/
lemma sum_algebraMap_smul_eq_mk {ι : Type*} [Fintype ι] (v : ι → LocalizedModule S M)
    (m : ι → M) (hm : ∀ i, LocalizedModule.mk (m i) (1 : S) = v i) (a : ι → B) :
    ∑ i, (algebraMap B (Localization S) (a i)) • v i =
      LocalizedModule.mk (∑ i, a i • m i) (1 : S) := by
  have hstep : ∀ i, (algebraMap B (Localization S) (a i)) • v i =
      LocalizedModule.mk (a i • m i) (1 : S) := by
    intro i
    rw [← hm i, algebraMap_smul, LocalizedModule.smul'_mk]
  simp only [hstep]
  rw [localizedModule_mk_sum]

/-- If lifts `mᵢ` of a linearly independent family of `S⁻¹M` satisfy a relation over `B`, each
coefficient is killed by an element of `S`. -/
lemma exists_mul_eq_zero_of_sum_smul_eq_zero {ι : Type*} [Fintype ι]
    (v : ι → LocalizedModule S M) (hv : LinearIndependent (Localization S) v) (m : ι → M)
    (hm : ∀ i, LocalizedModule.mk (m i) (1 : S) = v i) (a : ι → B) (ha : ∑ i, a i • m i = 0)
    (i : ι) : ∃ t ∈ S, t * a i = 0 := by
  have h0 : ∑ i, (algebraMap B (Localization S) (a i)) • v i = 0 := by
    rw [sum_algebraMap_smul_eq_mk v m hm, ha, LocalizedModule.zero_mk]
  have hcoeff := (Fintype.linearIndependent_iff.1 hv)
    (fun i => (algebraMap B (Localization S)) (a i)) h0 i
  obtain ⟨t, ht⟩ := (IsLocalization.map_eq_zero_iff S (Localization S) (a i)).1 hcoeff
  exact ⟨(t : B), t.2, ht⟩

/-- If the lifts `mᵢ` of a basis `vᵢ` of `S⁻¹M` are given, every `x : M` becomes a combination of
the `mᵢ` after multiplication by an element of `S`. -/
lemma exists_smul_eq_sum_of_span {ι : Type*} [Fintype ι] (v : ι → LocalizedModule S M)
    (hv : LinearIndependent (Localization S) v) (hvspan : span (Localization S) (Set.range v) = ⊤)
    (m : ι → M) (hm : ∀ i, LocalizedModule.mk (m i) (1 : S) = v i) (x : M) :
    ∃ (d : B) (a : ι → B), d ∈ S ∧ d • x = ∑ i, a i • m i := by
  classical
  let bas : Module.Basis ι (Localization S) (LocalizedModule S M) :=
    Module.Basis.mk hv (le_of_eq hvspan.symm)
  have hbasapply : ∀ i, bas i = v i := fun i => Module.Basis.mk_apply _ _ _
  set c : ι → Localization S := fun i => bas.repr (LocalizedModule.mk x (1 : S)) i with hc
  have hrepr : ∑ i, c i • v i = LocalizedModule.mk x (1 : S) := by
    have := bas.sum_repr (LocalizedModule.mk x (1 : S))
    simpa [hbasapply] using this
  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples S (Finset.univ : Finset ι) c
  choose a ha using fun i => hu i (Finset.mem_univ i)
  have hsum : ∑ i, (algebraMap B (Localization S) (a i)) • v i =
      (u : B) • LocalizedModule.mk x (1 : S) := by
    rw [← hrepr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, Algebra.smul_def, mul_smul, algebraMap_smul]
  rw [sum_algebraMap_smul_eq_mk v m hm, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hsum
  obtain ⟨w, hw⟩ := hsum
  simp only [one_smul] at hw
  refine ⟨(w : B) * (u : B), fun i => (w : B) * a i, S.mul_mem w.2 u.2, ?_⟩
  have hw' : (w : B) • ∑ i, a i • m i = (w : B) • ((u : B) • x) := hw
  rw [mul_smul, ← hw', Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm

end LocalizedSpan

/-- If `s` spans `M` and each `z ∈ s` has a multiple `d z • z` in `N`, then `(∏ d) • x ∈ N` for
every `x : M`. -/
lemma prod_smul_mem_of_forall_smul_mem {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M]
    [Module B M] {s : Finset M} (hs : span B (s : Set M) = ⊤) (N : Submodule B M) (d : M → B)
    (hd : ∀ z ∈ s, d z • z ∈ N) (x : M) : (∏ y ∈ s, d y) • x ∈ N := by
  classical
  have hx : x ∈ span B (s : Set M) := hs ▸ trivial
  refine Submodule.span_induction (p := fun z _ => (∏ y ∈ s, d y) • z ∈ N) ?_ ?_ ?_ ?_ hx
  · intro z hz
    rw [← Finset.prod_erase_mul s d hz, mul_smul]
    exact Submodule.smul_mem _ _ (hd z hz)
  · simp
  · intro y z _ _ hy hz
    rw [smul_add]
    exact Submodule.add_mem _ hy hz
  · intro c y _ hy
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hy

section Reduced

variable (B : Type*) [CommRing B] [IsNoetherianRing B] [IsReduced B] [Nontrivial B]
  (M : Type*) [AddCommGroup M] [Module B M] [Module.Finite B M]

/-- **Generic freeness over a reduced noetherian ring** (Takeuchi's Lemma 3.4 [Takeuchi1972]): a
finitely generated module over a commutative reduced noetherian ring becomes free after inverting
a single nonzero element of the base ring. -/
theorem exists_free_localizedModule_of_isReduced :
    ∃ g : B, g ≠ 0 ∧
      Module.Free (Localization.Away g) (LocalizedModule (Submonoid.powers g) M) := by
  classical
  -- a minimal prime `q` of `B`; the localization at `q` is a field, since `B` is reduced
  obtain ⟨p, hp⟩ := Ideal.exists_maximal B
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  have : q.IsPrime := hq.1.1
  have : Subsingleton (PrimeSpectrum (Localization.AtPrime q)) :=
    IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes q hq _
  have hfield : IsField (Localization.AtPrime q) := Ring.KrullDimLE.isField_of_isReduced
  let : Field (Localization.AtPrime q) := hfield.toField
  set S : Submonoid B := q.primeCompl with hS
  -- a finite generating family of `M`
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (by infer_instance) : (⊤ : Submodule B M).FG)
  -- its image spans the localization at `q`, a vector space over the field `B_q`
  set T : Set (LocalizedModule S M) := (fun x : M => LocalizedModule.mk x 1) '' (s : Set M) with hT
  have hTspan : span (Localization.AtPrime q) T = ⊤ := span_mk_one_image_eq_top S hs
  -- extract a basis of the localization from the spanning family `T`
  obtain ⟨b, hbT, hbspan, hbindep⟩ := exists_linearIndependent (Localization.AtPrime q) T
  have hTfin : T.Finite := Set.Finite.image _ s.finite_toSet
  have hbfin : b.Finite := hTfin.subset hbT
  have : Fintype ↥b := hbfin.fintype
  have hbtop : span (Localization.AtPrime q) (Set.range ((↑) : ↥b → LocalizedModule S M)) = ⊤ := by
    rw [Subtype.range_coe, hbspan, hTspan]
  -- lift the basis elements to `M`
  have hlift : ∀ y : ↥b, ∃ x : M,
      LocalizedModule.mk x (1 : S) = (y : LocalizedModule S M) := fun y => by
    obtain ⟨x, _, hx⟩ := hbT y.2
    exact ⟨x, hx⟩
  choose m hm using hlift
  -- relations between the `mᵢ` are killed by elements outside `q`, uniformly
  obtain ⟨t, htS, hindep⟩ := exists_uniform_annihilator_of_relations m S
    (fun a ha i => exists_mul_eq_zero_of_sum_smul_eq_zero _ hbindep m hm a ha i)
  -- each generator is in the span of the `mᵢ` after multiplication by an element outside `q`
  choose! d a hdS hda using fun x (_ : x ∈ s) =>
    exists_smul_eq_sum_of_span _ hbindep hbtop m hm x
  -- the element `g`, a product of elements outside `q`, hence itself outside `q` and nonzero
  refine ⟨t * ∏ x ∈ s, d x, ?_, ?_⟩
  · have hmemS : t * ∏ x ∈ s, d x ∈ S := S.mul_mem htS (S.prod_mem fun x hx => hdS x hx)
    intro h0
    exact hmemS (h0 ▸ q.zero_mem)
  refine free_localizedModule_of_torsion_basis m _ ?_ ?_
  · intro c hc i
    rw [mul_comm t, mul_assoc, hindep c hc i, mul_zero]
  · -- the `mᵢ` span `M` after multiplication by `g`
    set N : Submodule B M := Submodule.span B (Set.range m) with hN
    have hmemN : ∀ x : M, (∏ y ∈ s, d y) • x ∈ N :=
      prod_smul_mem_of_forall_smul_mem hs N d fun z hz => by
        rw [hda z hz]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x
    have hxN := hmemN x
    rw [hN, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination] at hxN
    obtain ⟨c, -, hc⟩ := hxN
    refine ⟨fun i => t * c i, ?_⟩
    have hcx : ∑ i, c i • m i = (∏ y ∈ s, d y) • x := by
      rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
    calc (t * ∏ x ∈ s, d x) • x = t • ((∏ y ∈ s, d y) • x) := mul_smul _ _ _
      _ = t • ∑ i, c i • m i := by rw [hcx]
      _ = ∑ i, (t * c i) • m i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm

end Reduced

end Module.Free
