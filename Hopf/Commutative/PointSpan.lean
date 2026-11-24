module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.PicardGroup
public import Hopf.Commutative.PointConjugation

/-!
# Takeuchi's Lemma 3.5: translates by points span all translates

Let `H` be a commutative Hopf algebra over a field `k` and let `g ∈ H`.  The coaction (that is,
the comultiplication) of `g` lands in `H ⊗ V` for some finite-dimensional subspace `V` of `H`,
and the translate `w ⇀ g = ∑ g₍₁₎ w (g₍₂₎)` only depends on the restriction of the functional `w`
to `V`.  Consequently, if the points of `H` *separate* `V` — which is Takeuchi's Lemma 3.6, valid
over an algebraically closed field when `V` lies in a reduced sub-Hopf algebra — then the span of
the translates of `g` by arbitrary functionals coincides with the span of its translates by
points.

This is Takeuchi's Lemma 3.5 (*A correspondence between Hopf ideals and sub-Hopf algebras*,
manuscripta math. **7** (1972)), in the form `C* ⇀ g = A ⇀ g` for a dense subspace `A` of `C*`.

## Main results

* `HopfAlgebra.Commutative.dual_span_eq_top_of_separating`: a separating subspace of the dual of a
  finite-dimensional space is the whole dual;
* `HopfAlgebra.Commutative.translSpan_eq_span_translPoint`: the span of all translates of `g` is the
  span of the translates of `g` by the points of `H`;
* `HopfAlgebra.Commutative.exists_fin_translPoint_span`: consequently a *finite* family of
  translates by points spans it.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemmas 3.5 and 3.6
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra.Comodule HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule

universe u

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]

/-- A separating subspace of the dual of a finite-dimensional space is the whole dual. -/
theorem dual_span_eq_top_of_separating {V : Type u} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (A : Submodule k (Module.Dual k V))
    (hA : ∀ x : V, (∀ a ∈ A, a x = 0) → x = 0) : A = ⊤ := by
  have hco : A.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x = 0 := hA x fun a ha => ((Submodule.mem_dualCoannihilator _).1 hx) a ha
    simpa using this
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq A
  rw [hco] at h
  simp only [finrank_bot, add_zero] at h
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [h, Subspace.dual_finrank_eq]

/-- Translation only depends on the restriction of the functional to a subspace carrying the
coaction. -/
theorem transl_congr_of_mem_range {g : H} {V : Submodule k H}
    (hcoact : coact (R := k) (C := H) g ∈ LinearMap.range (LinearMap.lTensor H V.subtype))
    {w w' : H →ₗ[k] k} (hww : ∀ x ∈ V, w x = w' x) :
    Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w g
      = Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w' g := by
  obtain ⟨z, hz⟩ := hcoact
  have hrestr : w ∘ₗ V.subtype = w' ∘ₗ V.subtype := by
    ext x
    exact hww x x.2
  have hcomp : ∀ v : H →ₗ[k] k, LinearMap.lTensor H v ∘ₗ LinearMap.lTensor H V.subtype
      = LinearMap.lTensor H (v ∘ₗ V.subtype) := fun v => by rw [← LinearMap.lTensor_comp]
  simp only [Coalgebra.Comodule.transl, LinearMap.coe_comp, Function.comp_apply, ← hz]
  rw [← LinearMap.comp_apply (LinearMap.lTensor H w), ← LinearMap.comp_apply
    (LinearMap.lTensor H w'), hcomp, hcomp, hrestr]

/-- Translation is additive in the functional. -/
lemma transl_add_functional (w w' : H →ₗ[k] k) (x : H) :
    Coalgebra.Comodule.transl (R := k) (C := H) (M := H) (w + w') x
      = Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w x
        + Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w' x := by
  simp only [Coalgebra.Comodule.transl, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lTensor_add,
    LinearMap.add_apply, map_add]

/-- Translation is homogeneous in the functional. -/
lemma transl_smul_functional (t : k) (w : H →ₗ[k] k) (x : H) :
    Coalgebra.Comodule.transl (R := k) (C := H) (M := H) (t • w) x
      = t • Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w x := by
  simp only [Coalgebra.Comodule.transl, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lTensor_smul,
    LinearMap.smul_apply, map_smul]

/-- Translation is additive over a finite sum of functionals. -/
lemma transl_sum_functional {ι : Type*} (s : Finset ι) (w : ι → (H →ₗ[k] k)) (x : H) :
    Coalgebra.Comodule.transl (R := k) (C := H) (M := H) (∑ i ∈ s, w i) x
      = ∑ i ∈ s, Coalgebra.Comodule.transl (R := k) (C := H) (M := H) (w i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [Coalgebra.Comodule.transl]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, transl_add_functional, ih, Finset.sum_insert ha]

/-- **Takeuchi's Lemma 3.5** [Takeuchi1972].  If the coaction of `g` lands in `H ⊗ V` for a
finite-dimensional subspace `V` on which the points of `H` separate, then the translates of `g` by
the points of `H` span all of its translates. -/
theorem translSpan_eq_span_translPoint (g : H) (V : Submodule k H) [FiniteDimensional k ↥V]
    (hcoact : coact (R := k) (C := H) g ∈ LinearMap.range (LinearMap.lTensor H V.subtype))
    (hsep : ∀ x ∈ V, (∀ u : H →ₐ[k] k, u x = 0) → x = 0) :
    Coalgebra.Comodule.translSpan (k := k) (C := H) g
      = Submodule.span k (Set.range fun u : H →ₐ[k] k => translPoint u g) := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Coalgebra.Comodule.translSpan, Submodule.span_le]
    rintro y ⟨w, rfl⟩
    -- the restrictions of the points span the dual of `V`
    set A : Submodule k (Module.Dual k ↥V) :=
      Submodule.span k (Set.range fun u : H →ₐ[k] k => (u.toLinearMap ∘ₗ V.subtype)) with hA
    have hAtop : A = ⊤ := by
      refine dual_span_eq_top_of_separating A fun x hx => ?_
      have hx0 : (x : H) = 0 := by
        refine hsep x x.2 fun u => ?_
        have := hx _ (Submodule.subset_span ⟨u, rfl⟩)
        simpa using this
      exact Subtype.ext hx0
    have hmem : (w ∘ₗ V.subtype) ∈ A := by rw [hAtop]; trivial
    rw [hA, Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨c, hc⟩ := hmem
    -- so `w` agrees on `V` with a finite combination of points
    set w' : H →ₗ[k] k := c.sum fun u t => t • u.toLinearMap with hw'
    have hww : ∀ x ∈ V, w x = w' x := by
      intro x hx
      have := congrArg (fun f : Module.Dual k ↥V => f ⟨x, hx⟩) hc
      simp only [hw', LinearMap.coe_comp, Function.comp_apply,
        Submodule.subtype_apply] at this ⊢
      rw [← this]
      simp [Finsupp.sum, LinearMap.sum_apply]
    change Coalgebra.Comodule.transl (R := k) (C := H) (M := H) w g ∈
      Submodule.span k (Set.range fun u : H →ₐ[k] k => translPoint u g)
    rw [transl_congr_of_mem_range hcoact hww, hw', Finsupp.sum, transl_sum_functional]
    -- and translation by a finite combination of points is a combination of point translates
    refine Submodule.sum_mem _ fun u _ => ?_
    rw [transl_smul_functional]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)
  · rw [Submodule.span_le]
    rintro y ⟨u, rfl⟩
    exact Coalgebra.Comodule.transl_mem_translSpan _ _

/-- A finite family of translates by points spanning the span of all translates. -/
theorem exists_fin_translPoint_span (g : H) (V : Submodule k H) [FiniteDimensional k ↥V]
    (hcoact : coact (R := k) (C := H) g ∈ LinearMap.range (LinearMap.lTensor H V.subtype))
    (hsep : ∀ x ∈ V, (∀ u : H →ₐ[k] k, u x = 0) → x = 0) :
    ∃ (n : ℕ) (U : Fin n → (H →ₐ[k] k)),
      Submodule.span k (Set.range fun i => translPoint (U i) g)
        = Coalgebra.Comodule.translSpan (k := k) (C := H) g := by
  classical
  have hspan := translSpan_eq_span_translPoint g V hcoact hsep
  obtain ⟨T, hT⟩ := (Coalgebra.Comodule.translSpan_spec (k := k) (C := H) g).1
  -- every generator of the (finitely generated) span of translates is a finite combination of
  -- translates by points
  have hmem : ∀ t : H, t ∈ T → ∃ F : Finset (H →ₐ[k] k),
      t ∈ Submodule.span k ((fun u : H →ₐ[k] k => translPoint u g) '' (F : Set (H →ₐ[k] k))) := by
    intro t ht
    have htmem : t ∈ Submodule.span k (Set.range fun u : H →ₐ[k] k => translPoint u g) := by
      rw [← hspan, ← hT]
      exact Submodule.subset_span ht
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at htmem
    obtain ⟨c, hc⟩ := htmem
    refine ⟨c.support, ?_⟩
    rw [← hc, Finsupp.sum]
    exact Submodule.sum_mem _ fun u hu =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, hu, rfl⟩)
  choose F hF using hmem
  set G : Finset (H →ₐ[k] k) := T.attach.biUnion (fun t => F t.1 t.2) with hG
  have hle : Coalgebra.Comodule.translSpan (k := k) (C := H) g
      ≤ Submodule.span k ((fun u : H →ₐ[k] k => translPoint u g) '' (G : Set (H →ₐ[k] k))) := by
    rw [← hT, Submodule.span_le]
    intro t ht
    refine Submodule.span_mono ?_ (hF t ht)
    refine Set.image_mono ?_
    intro u hu
    simp only [hG, Finset.coe_biUnion, Set.mem_iUnion]
    exact ⟨⟨t, ht⟩, by simp, hu⟩
  refine ⟨G.card, fun i => (G.equivFin.symm i : H →ₐ[k] k), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    exact Coalgebra.Comodule.transl_mem_translSpan _ _
  · refine hle.trans ?_
    refine Submodule.span_le.2 ?_
    rintro y ⟨u, hu, rfl⟩
    refine Submodule.subset_span ⟨G.equivFin ⟨u, hu⟩, ?_⟩
    simp

end HopfAlgebra.Commutative
end
