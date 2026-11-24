module

public import Mathlib.RingTheory.Flat.Localization
public import Foundations.RingTheory.GenericFreeness
public import Foundations.RingTheory.GenericFreenessReduced

/-!
# Locally free modules are flat, and transport of generic bases

This file provides the commutative-algebra endgame of Takeuchi's Proposition 3.7 (M. Takeuchi,
*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7** (1972)).

There, a finitely generated module `M` over a reduced noetherian ring `K` is shown to be free after
inverting one element `g` (generic freeness,
`Module.Free.exists_free_localizedModule_of_isReduced`), and then the translates `σ g` of `g` under
a family of automorphisms of `K` — coming from the `k`-points of the Hopf algebra, acting
semilinearly on `M` — are shown to generate the unit ideal. Since `M` is free after inverting each
of the `σ g`, it is flat.

The abstract statement of that endgame is
`Module.Flat.flat_of_free_localization_of_semilinear_cover`.

The bookkeeping is done through the predicate `Module.Flat.HasGenericBasis B M g`: a finite family
of elements of `M` all of whose relations are killed by `g` and which spans `M` after multiplication
by `g`. This predicate

* implies freeness of `M_g` over `B_g` (`Module.Flat.free_localizedModule_of_hasGenericBasis`);
* conversely holds for some power of `g` whenever `M_g` is free, `M` being finitely generated over
  a noetherian ring (`Module.Flat.exists_hasGenericBasis_pow`);
* transports along semilinear isomorphisms (`Module.Flat.HasGenericBasis.map`), which is what makes
  the group of `k`-points usable.

## Main results

* `Module.Flat.flat_of_span_free`: a module whose localizations away from a family of elements
  generating the unit ideal are free is flat;
* `Module.Flat.flat_of_free_localization_of_semilinear_cover`: generic freeness plus a semilinear
  covering family implies flatness.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Proposition 3.7
* [A. Grothendieck, J. Dieudonné, *Éléments de géométrie algébrique IV*][EGAIV2], Section 6.9
-/

@[expose] public section

namespace Module.Flat


section GenericBasis

variable (B : Type*) [CommRing B] (M : Type*) [AddCommGroup M] [Module B M]

/-- `HasGenericBasis B M g` says that `M` admits a finite family of elements which becomes a basis
after inverting `g`, in the equational form: every relation between the family is killed by `g`,
and the family spans `M` after multiplication by `g`. -/
def HasGenericBasis (g : B) : Prop :=
  ∃ (r : ℕ) (m : Fin r → M),
    (∀ a : Fin r → B, ∑ i, a i • m i = 0 → ∀ i, g * a i = 0) ∧
    ∀ x : M, ∃ a : Fin r → B, g • x = ∑ i, a i • m i

variable {B M}

/-- A generic basis indexed by an arbitrary finite type gives one indexed by `Fin r`. -/
theorem hasGenericBasis_of_fintype {ι : Type*} [Fintype ι] (m : ι → M) (g : B)
    (h1 : ∀ a : ι → B, ∑ i, a i • m i = 0 → ∀ i, g * a i = 0)
    (h2 : ∀ x : M, ∃ a : ι → B, g • x = ∑ i, a i • m i) :
    HasGenericBasis B M g := by
  classical
  set e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun j => m (e.symm j), ?_, ?_⟩
  · intro a ha j
    have hsum : ∑ i : ι, a (e i) • m i = 0 := by
      rw [← ha]
      exact Fintype.sum_bijective e e.bijective _ _ (fun i => by simp)
    have := h1 (fun i => a (e i)) hsum (e.symm j)
    simpa using this
  · intro x
    obtain ⟨a, ha⟩ := h2 x
    refine ⟨fun j => a (e.symm j), ?_⟩
    rw [ha]
    exact Fintype.sum_bijective e e.bijective _ _ (fun i => by simp)

/-- A generic basis makes the localization free. -/
theorem free_localizedModule_of_hasGenericBasis {g : B} (h : HasGenericBasis B M g) :
    Module.Free (Localization.Away g) (LocalizedModule (Submonoid.powers g) M) := by
  obtain ⟨r, m, h1, h2⟩ := h
  exact Module.Free.free_localizedModule_of_torsion_basis m g h1 h2

end GenericBasis

section Transport

variable {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M] [Module B M]

/-- Generic bases transport along a semilinear automorphism: if `Φ` is additive and bijective and
`Φ (a • x) = σ a • Φ x` for a ring automorphism `σ`, then a generic basis for `g` yields one for
`σ g`. -/
theorem HasGenericBasis.map {g : B} (h : HasGenericBasis B M g) (σ : B ≃+* B) (Φ : M ≃+ M)
    (hsemi : ∀ (a : B) (x : M), Φ (a • x) = σ a • Φ x) :
    HasGenericBasis B M (σ g) := by
  obtain ⟨r, m, h1, h2⟩ := h
  refine ⟨r, fun i => Φ (m i), ?_, ?_⟩
  · intro a ha i
    set b : Fin r → B := fun i => σ.symm (a i) with hb
    have hsum : Φ (∑ i, b i • m i) = 0 := by
      rw [map_sum]
      simp only [hsemi, hb, RingEquiv.apply_symm_apply]
      exact ha
    have hzero : ∑ i, b i • m i = 0 := by
      simpa using congr(Φ.symm $hsum)
    have := h1 b hzero i
    have hmap : σ (g * b i) = σ g * a i := by
      rw [map_mul, hb]
      simp
    rw [← hmap, this, map_zero]
  · intro x
    obtain ⟨a, ha⟩ := h2 (Φ.symm x)
    refine ⟨fun i => σ (a i), ?_⟩
    have := congr(Φ $ha)
    rw [hsemi, map_sum] at this
    simp only [hsemi] at this
    rwa [Φ.apply_symm_apply] at this

end Transport

section BasisLifts

variable {B : Type*} [CommRing B] {S : Submonoid B} {M : Type*} [AddCommGroup M] [Module B M]
  {ι : Type*} (bas : Module.Basis ι (Localization S) (LocalizedModule S M))
  (m : ι → M) (sden : ι → S) (hmk : ∀ i, LocalizedModule.mk (m i) (sden i) = bas i)
include hmk

/-- If the fractions `mᵢ / sᵢ` form a basis of `S⁻¹M`, a relation between the `mᵢ` over `B` has
each coefficient killed by an element of `S`. -/
lemma exists_mul_eq_zero_of_basis_lift [Fintype ι] (a : ι → B) (ha : ∑ i, a i • m i = 0) (i : ι) :
    ∃ t ∈ S, t * a i = 0 := by
  have hmk1 : ∀ i : ι, LocalizedModule.mk (m i) (1 : S)
      = (algebraMap B (Localization S)) (sden i : B) • bas i := by
    intro i
    rw [← hmk i, algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def]⟩
  have h0 : ∑ i : ι, ((algebraMap B (Localization S)) (a i * (sden i : B))) • bas i = 0 := by
    have hstep : ∀ i : ι, ((algebraMap B (Localization S)) (a i * (sden i : B))) • bas i
        = LocalizedModule.mk (a i • m i) (1 : S) := by
      intro i
      rw [map_mul, mul_smul, ← hmk1 i, algebraMap_smul, LocalizedModule.smul'_mk]
    simp only [hstep]
    rw [Module.Free.localizedModule_mk_sum, ha, LocalizedModule.zero_mk]
  have hcoeff : (algebraMap B (Localization S)) (a i * (sden i : B)) = 0 :=
    Fintype.linearIndependent_iff.1 bas.linearIndependent
      (fun i => (algebraMap B (Localization S)) (a i * (sden i : B))) h0 i
  obtain ⟨t, ht⟩ :=
    (IsLocalization.map_eq_zero_iff S (Localization S) (a i * (sden i : B))).1 hcoeff
  exact ⟨(t : B) * (sden i : B), S.mul_mem t.2 (sden i).2, by linear_combination ht⟩

/-- If the fractions `mᵢ / sᵢ` form a basis of `S⁻¹M`, every `x : M` lies in the span of the `mᵢ`
after multiplication by an element of `S`. -/
lemma exists_smul_mem_span_of_basis_lift [Finite ι] (x : M) :
    ∃ w ∈ S, w • x ∈ Submodule.span B (Set.range m) := by
  classical
  have := Fintype.ofFinite ι
  set c : ι → Localization S := fun i => bas.repr (LocalizedModule.mk x (1 : S)) i with hc
  have hrepr : ∑ i, c i • bas i = LocalizedModule.mk x (1 : S) := bas.sum_repr _
  obtain ⟨u, hu⟩ := IsLocalization.exist_integer_multiples S (Finset.univ : Finset ι) c
  choose a ha using fun i => hu i (Finset.mem_univ i)
  have hsum : ∑ i : ι, ((algebraMap B (Localization S)) (a i)) • bas i
      = (u : B) • LocalizedModule.mk x (1 : S) := by
    rw [← hrepr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, Algebra.smul_def, mul_smul, algebraMap_smul]
  -- put everything over the common denominator `∏ sden i`
  set D : S := ∏ i : ι, sden i with hD
  have hterm : ∀ i : ι, ((algebraMap B (Localization S)) (a i)) • bas i
      = LocalizedModule.mk ((∏ j ∈ Finset.univ.erase i, (sden j : B)) • (a i • m i)) D := by
    intro i
    rw [← hmk i, algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    have hDsplit : (D : B) = (∏ j ∈ Finset.univ.erase i, (sden j : B)) * (sden i : B) := by
      rw [hD]
      push_cast
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [Submonoid.smul_def, smul_smul, hDsplit]
    congr 1
    ring
  have hleft : ∑ i : ι, ((algebraMap B (Localization S)) (a i)) • bas i
      = LocalizedModule.mk (∑ i : ι, (∏ j ∈ Finset.univ.erase i, (sden j : B)) • (a i • m i))
        D := by
    simp only [hterm]
    rw [Module.Free.localizedModule_mk_sum]
  set y : M := ∑ i : ι, (∏ j ∈ Finset.univ.erase i, (sden j : B)) • (a i • m i) with hy
  have hyN : y ∈ Submodule.span B (Set.range m) := by
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  rw [hleft, LocalizedModule.smul'_mk, LocalizedModule.mk_eq] at hsum
  obtain ⟨v, hv⟩ := hsum
  simp only [Submonoid.smul_def, one_smul, smul_smul] at hv
  refine ⟨(v : B) * ((D : B) * (u : B)), S.mul_mem v.2 (S.mul_mem D.2 u.2), ?_⟩
  have hgoal : ((v : B) * ((D : B) * (u : B))) • x = (v : B) • y := by
    rw [← hv]
  rw [hgoal]
  exact Submodule.smul_mem _ _ hyN

end BasisLifts

section Converse

variable {B : Type*} [CommRing B] [IsNoetherianRing B] {M : Type*} [AddCommGroup M] [Module B M]
  [Module.Finite B M]

/-- Conversely, if `M` is finitely generated over a noetherian ring and `M_g` is free over `B_g`,
then `M` has a generic basis for a suitable power of `g`. -/
theorem exists_hasGenericBasis_pow (g : B)
    [Module.Free (Localization.Away g) (LocalizedModule (Submonoid.powers g) M)] :
    ∃ n : ℕ, HasGenericBasis B M (g ^ n) := by
  classical
  set S : Submonoid B := Submonoid.powers g with hS
  set A : Type _ := Localization.Away g with hA
  set V : Type _ := LocalizedModule S M with hV
  -- a finite basis of the localization
  set ι := Module.Free.ChooseBasisIndex A V with hι
  set bas : Module.Basis ι A V := Module.Free.chooseBasis A V with hbas
  -- lift the basis elements to `M`
  have hlift : ∀ i : ι, ∃ (x : M) (s : S), LocalizedModule.mk x s = bas i := by
    intro i
    induction (bas i) using LocalizedModule.induction_on with
    | _ x s => exact ⟨x, s, rfl⟩
  choose m sden hmk using hlift
  -- relations between the `mᵢ` are killed by powers of `g`
  obtain ⟨t, htS, hindep⟩ := Module.Free.exists_uniform_annihilator_of_relations m S
    (exists_mul_eq_zero_of_basis_lift bas m sden hmk)
  obtain ⟨n₁, hn₁'⟩ := htS
  have hn₁ : g ^ n₁ = t := hn₁'
  -- the `mᵢ` span `M` after multiplication by a power of `g`, uniformly over generators of `M`
  set N : Submodule B M := Submodule.span B (Set.range m) with hN
  obtain ⟨s, hs⟩ := (Module.finite_def.1 (by infer_instance) : (⊤ : Submodule B M).FG)
  choose! w hwS hwN using exists_smul_mem_span_of_basis_lift bas m sden hmk
  have hspan2 : ∀ x : M, (∏ z ∈ s, w z) • x ∈ N :=
    Module.Free.prod_smul_mem_of_forall_smul_mem hs N w fun z _ => hwN z
  have hW : (∏ z ∈ s, w z) ∈ S := S.prod_mem fun z _ => hwS z
  obtain ⟨n₂, hn₂'⟩ := hW
  have hn₂ : g ^ n₂ = ∏ z ∈ s, w z := hn₂'
  refine ⟨n₁ + n₂, hasGenericBasis_of_fintype m _ ?_ ?_⟩
  · intro a ha i
    have h1 : t * a i = 0 := hindep a ha i
    rw [pow_add, hn₁, hn₂, mul_comm t, mul_assoc, h1, mul_zero]
  · intro x
    have hxN : (g ^ n₂) • x ∈ N := by rw [hn₂]; exact hspan2 x
    rw [hN, ← Set.image_univ, Finsupp.span_image_eq_map_linearCombination] at hxN
    obtain ⟨c, -, hc⟩ := hxN
    refine ⟨fun i => g ^ n₁ * c i, ?_⟩
    have hcx : ∑ i, c i • m i = (g ^ n₂) • x := by
      rw [← hc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]
    calc (g ^ (n₁ + n₂)) • x = (g ^ n₁) • ((g ^ n₂) • x) := by rw [pow_add, mul_smul]
      _ = (g ^ n₁) • ∑ i, c i • m i := by rw [hcx]
      _ = ∑ i, (g ^ n₁ * c i) • m i := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => (mul_smul _ _ _).symm

end Converse

section Flat

variable {B : Type*} [CommRing B] {M : Type*} [AddCommGroup M] [Module B M]

/-- A module which becomes free after inverting each element of a family generating the unit ideal
is flat. -/
theorem flat_of_span_free (s : Set B) (hspan : Ideal.span s = ⊤)
    (hfree : ∀ g : s, Module.Free (Localization.Away (g : B))
      (LocalizedModule (Submonoid.powers (g : B)) M)) :
    Module.Flat B M := by
  refine Module.flat_of_localized_span B M s hspan fun r => ?_
  have := hfree r
  have : Module.Flat (Localization.Away (r : B)) (LocalizedModule.Away (r : B) M) :=
    Module.Flat.of_free
  have : Module.Flat B (Localization.Away (r : B)) :=
    IsLocalization.flat (Localization.Away (r : B)) (Submonoid.powers (r : B))
  exact Module.Flat.trans B (Localization.Away (r : B)) (LocalizedModule.Away (r : B) M)

variable [IsNoetherianRing B] [Module.Finite B M]

/-- **The endgame of Takeuchi's Proposition 3.7.**  Let `M` be a finitely generated module over a
noetherian ring `B` which becomes free after inverting one element `g`.  If there is a family of
ring automorphisms `σ u` of `B`, acting semilinearly on `M` through additive automorphisms `Φ u`,
such that the translates `σ u g` generate the unit ideal, then `M` is flat over `B`. -/
theorem flat_of_free_localization_of_semilinear_cover {ι : Type*} (σ : ι → B ≃+* B)
    (Φ : ι → M ≃+ M) (hsemi : ∀ (u : ι) (a : B) (x : M), Φ u (a • x) = σ u a • Φ u x) (g : B)
    [Module.Free (Localization.Away g) (LocalizedModule (Submonoid.powers g) M)]
    (hspan : Ideal.span (Set.range fun u => σ u g) = ⊤) :
    Module.Flat B M := by
  classical
  obtain ⟨n, hn⟩ := exists_hasGenericBasis_pow (M := M) g
  -- the `n`-th powers of the translates still generate the unit ideal
  have hspan' : Ideal.span ((fun x => x ^ n) '' (Set.range fun u => σ u g)) = ⊤ :=
    Ideal.span_pow_eq_top _ hspan n
  refine flat_of_span_free _ hspan' ?_
  rintro ⟨-, y, ⟨u, rfl⟩, rfl⟩
  have hbasis : HasGenericBasis B M ((σ u g) ^ n) := by
    have := hn.map (σ u) (Φ u) (hsemi u)
    rwa [map_pow] at this
  exact free_localizedModule_of_hasGenericBasis hbasis

end Flat

end Module.Flat
