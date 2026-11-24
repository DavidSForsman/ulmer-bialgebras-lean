module

public import Hopf.Commutative.ExteriorLine

/-!
# Takeuchi's Lemma 4.10(i): the easy half

Let `H` be a commutative Hopf algebra over a field `k`, let `V` be a right `H`-comodule and let
`w : Fin n → V` be a family spanning a subspace `W ≤ V`.  Write `ω = w 0 ∧ ⋯ ∧ w (n-1)` for the
associated element of the exterior algebra `⋀ V`.

`Hopf/Commutative/ExteriorLine.lean` proves the substantial half of Takeuchi's Lemma
4.10(i) (*A correspondence between Hopf ideals and sub-Hopf algebras*, manuscripta math. **7**
(1972)): if the line `k ω` is a subcomodule of `⋀ V` modulo an ideal `J`, then `W` is a subcomodule
of `V` modulo `J`.  This file proves the converse — the easy half — and hence Lemma 4.10(i) itself.

The argument is the expected one: the reduced coaction `Λρ_J` of the exterior algebra is a
homomorphism of algebras, so the coaction of `ω = ι(w 0) ⋯ ι(w (n-1))` is the product of the
coactions of the `ι (w i)`, each of which lies in `P ⊗ H/J` for `P = ι(W)`; and a product of `n`
elements of `P` lies in the line `k ω`, because a wedge product of `n` vectors of `W` is `± ω` or
zero.

## Main results

* `HopfAlgebra.Commutative.isSubcomoduleMod_exterior_line`: the easy half of Lemma 4.10(i);
* `HopfAlgebra.Commutative.nIdeal_exterior_line_le_nIdeal`: consequently `N(⋀ V, k ω) ≤ N(V, W)`;
* `HopfAlgebra.Commutative.nIdeal_exterior_line_eq`: **Takeuchi's Lemma 4.10(i)**,
  `N(V, W) = N(⋀ V, k ω)`, for a linearly independent family `w`.

## References

* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972],
  Lemma 4.10(i)
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

section
open Coalgebra Coalgebra.Comodule HopfAlgebra.Commutative
namespace HopfAlgebra.Commutative

open Coalgebra.Comodule
open scoped Pointwise

universe u

/-! ### Submodules and tensor products -/

section Aux

variable {k : Type u} [Field k]

variable {A B M : Type u} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup M] [Module k M]

/-- Monotonicity of the image of `E ⊗ M` in `A ⊗ M`. -/
theorem mem_range_rTensor_mono {E F : Submodule k A} (hEF : E ≤ F) {x : A ⊗[k] M}
    (hx : x ∈ LinearMap.range (LinearMap.rTensor M E.subtype)) :
    x ∈ LinearMap.range (LinearMap.rTensor M F.subtype) := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨LinearMap.rTensor M (Submodule.inclusion hEF) z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

/-- The image of `E ⊗ M` is carried into the image of `(E.map φ) ⊗ M`. -/
theorem map_mem_range_rTensor (φ : A →ₗ[k] B) {E : Submodule k A} {z : A ⊗[k] M}
    (hz : z ∈ LinearMap.range (LinearMap.rTensor M E.subtype)) :
    TensorProduct.map φ LinearMap.id z
      ∈ LinearMap.range (LinearMap.rTensor M (E.map φ).subtype) := by
  obtain ⟨u, rfl⟩ := hz
  induction u with
  | add p q hp hq =>
      rw [map_add, map_add]
      exact Submodule.add_mem _ hp hq
  | tmul a m =>
      exact ⟨(⟨φ (a : A), Submodule.mem_map_of_mem a.2⟩ : ↥(E.map φ)) ⊗ₜ[k] m, by simp⟩

end Aux

section AuxAlg

variable {k A M : Type u} [Field k] [Ring A] [Algebra k A] [CommRing M] [Algebra k M]

/-- The product of an element of `E ⊗ M` and an element of `F ⊗ M` lies in `(E * F) ⊗ M`. -/
theorem mul_mem_range_rTensor {E F : Submodule k A} {x y : A ⊗[k] M}
    (hx : x ∈ LinearMap.range (LinearMap.rTensor M E.subtype))
    (hy : y ∈ LinearMap.range (LinearMap.rTensor M F.subtype)) :
    x * y ∈ LinearMap.range (LinearMap.rTensor M (E * F).subtype) := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  induction u with
  | add p q hp hq =>
      rw [map_add, add_mul]
      exact Submodule.add_mem _ hp hq
  | tmul a m =>
      induction v with
      | add p q hp hq =>
          rw [map_add, mul_add]
          exact Submodule.add_mem _ hp hq
      | tmul b m' =>
          refine ⟨(⟨(a : A) * (b : A), Submodule.mul_mem_mul a.2 b.2⟩ : ↥(E * F))
            ⊗ₜ[k] (m * m'), ?_⟩
          simp [Algebra.TensorProduct.tmul_mul_tmul]

/-- The product of a list of elements of `P ⊗ M` lies in `P ^ length ⊗ M`. -/
theorem list_prod_mem_range_rTensor (P : Submodule k A) (L : List (A ⊗[k] M))
    (h : ∀ x ∈ L, x ∈ LinearMap.range (LinearMap.rTensor M P.subtype)) :
    L.prod ∈ LinearMap.range (LinearMap.rTensor M (P ^ L.length).subtype) := by
  induction L with
  | nil =>
      refine ⟨(⟨1, by rw [pow_zero]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩ :
        ↥(P ^ (0 : ℕ))) ⊗ₜ[k] (1 : M), ?_⟩
      simp [Algebra.TensorProduct.one_def]
  | cons a L ih =>
      have h1 : a ∈ LinearMap.range (LinearMap.rTensor M P.subtype) := h a (by simp)
      have h2 := ih fun x hx => h x (by simp [hx])
      have hmul := mul_mem_range_rTensor h1 h2
      rw [List.length_cons, pow_succ', List.prod_cons]
      exact hmul

end AuxAlg

/-! ### The easy half of Lemma 4.10(i) -/

section Exterior

variable {k H : Type u} [Field k] [CommRing H] [HopfAlgebra k H]
variable {V : Type u} [AddCommGroup V] [Module k V] [RightComodule k H V]

/-- A product of `n` vectors of the span of a family `w : Fin n → V` lies in the line spanned by
`ω = w 0 ∧ ⋯ ∧ w (n-1)`. -/
theorem prod_ι_mem_span_ιMulti {n : ℕ} (w : Fin n → V) (f : Fin n → Fin n) :
    (List.ofFn fun i => ExteriorAlgebra.ι k (w (f i))).prod
      ∈ (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V)) := by
  classical
  have hrw : (List.ofFn fun i => ExteriorAlgebra.ι k (w (f i))).prod
      = ExteriorAlgebra.ιMulti k n (w ∘ f) := (ExteriorAlgebra.ιMulti_apply (w ∘ f)).symm
  rw [hrw]
  by_cases hinj : Function.Injective f
  · have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
    set σ : Equiv.Perm (Fin n) := Equiv.ofBijective f hbij with hσ
    have hcomp : (w ∘ f) = (w ∘ (σ : Fin n → Fin n)) := rfl
    rw [hcomp, AlternatingMap.map_perm]
    refine Submodule.mem_span_singleton.2 ⟨((Equiv.Perm.sign σ : ℤ) : k), ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    simp [Units.smul_def]
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
      by_contra hcon
      push Not at hcon
      exact hinj fun i j hij => hcon i j hij
    rw [AlternatingMap.map_eq_zero_of_eq _ _ (show (w ∘ f) i = (w ∘ f) j by simp [hij]) hne]
    exact Submodule.zero_mem _

/-- The `n`-th power of the span of `ι (w i)` is contained in the line spanned by `ω`. -/
theorem pow_span_ι_le_span_ιMulti {n : ℕ} (w : Fin n → V) :
    (Submodule.span k (Set.range fun i => ExteriorAlgebra.ι k (w i))) ^ n
      ≤ (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V)) := by
  classical
  set P : Submodule k (ExteriorAlgebra k V) :=
    Submodule.span k (Set.range fun i => ExteriorAlgebra.ι k (w i)) with hP
  set G : ℕ → Set (ExteriorAlgebra k V) := fun m =>
    Set.range fun f : Fin m → Fin n => (List.ofFn fun i => ExteriorAlgebra.ι k (w (f i))).prod
    with hG
  -- `Pᵐ` is spanned by the products `ι (w (f 0)) ⋯ ι (w (f (m - 1)))`, by induction on `m`
  have hstep : ∀ m : ℕ, P ^ m ≤ Submodule.span k (G m) := by
    intro m
    induction m with
    | zero =>
        rw [pow_zero, Submodule.one_eq_span]
        refine Submodule.span_le.2 ?_
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Submodule.subset_span ⟨fun i => i.elim0, by simp⟩
    | succ m ih =>
        -- `Pᵐ⁺¹ = P · Pᵐ`, and `ι (w i)` times a product of length `m` is one of length `m + 1`
        rw [pow_succ']
        calc P * P ^ m ≤ P * Submodule.span k (G m) := mul_le_mul_right ih P
          _ = Submodule.span k ((Set.range fun i => ExteriorAlgebra.ι k (w i)) * G m) := by
              rw [hP, Submodule.span_mul_span]
          _ ≤ Submodule.span k (G (m + 1)) := by
              refine Submodule.span_le.2 ?_
              rintro x ⟨a, ⟨i, rfl⟩, b, ⟨f, rfl⟩, rfl⟩
              set g : Fin (m + 1) → Fin n := Fin.cons i f with hg
              refine Submodule.subset_span ⟨g, ?_⟩
              change (List.ofFn fun j => ExteriorAlgebra.ι k (w (g j))).prod
                  = ExteriorAlgebra.ι k (w i)
                    * (List.ofFn fun j => ExteriorAlgebra.ι k (w (f j))).prod
              rw [List.ofFn_succ]
              simp [hg]
  -- each product of `n` factors is a multiple of `ω = ιMulti w`
  refine (hstep n).trans (Submodule.span_le.2 ?_)
  rintro x ⟨f, rfl⟩
  exact prod_ι_mem_span_ιMulti w f

/-- **The easy half of Takeuchi's Lemma 4.10(i)**: if the span of a family `w : Fin n → V` is a
subcomodule of `V` modulo `J`, then the line spanned by `ω = w 0 ∧ ⋯ ∧ w (n-1)` is a subcomodule
of `⋀ V` modulo `J`. -/
theorem isSubcomoduleMod_exterior_line (J : Ideal H) {n : ℕ} {w : Fin n → V}
    (h : IsSubcomoduleMod J (Submodule.span k (Set.range w))) :
    IsSubcomoduleMod J
      (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V)) := by
  classical
  set W : Submodule k V := Submodule.span k (Set.range w) with hW
  set ω : ExteriorAlgebra k V := ExteriorAlgebra.ιMulti k n w with hω
  set P : Submodule k (ExteriorAlgebra k V) := W.map (ExteriorAlgebra.ι k) with hP
  have hPspan : P = Submodule.span k (Set.range fun i => ExteriorAlgebra.ι k (w i)) := by
    rw [hP, hW, Submodule.map_span, ← Set.range_comp]
    rfl
  -- the coaction of each generator lies in `P ⊗ H/J`
  have hgen : ∀ i : Fin n, extCoactQAlgHom k H V J (ExteriorAlgebra.ι k (w i))
      ∈ LinearMap.range (LinearMap.rTensor (H ⧸ J) P.subtype) := by
    intro i
    rw [extCoactQAlgHom_ι]
    exact map_mem_range_rTensor (ExteriorAlgebra.ι k)
      (h (w i) (Submodule.subset_span ⟨i, rfl⟩))
  -- hence the coaction of `ω` lies in `Pⁿ ⊗ H/J`
  have hprod : extCoactQAlgHom k H V J ω
      ∈ LinearMap.range (LinearMap.rTensor (H ⧸ J) (P ^ n).subtype) := by
    have hlist := list_prod_mem_range_rTensor (M := H ⧸ J) P
      (List.ofFn fun i => extCoactQAlgHom k H V J (ExteriorAlgebra.ι k (w i)))
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact hgen i)
    rw [List.length_ofFn] at hlist
    have hmap : extCoactQAlgHom k H V J ω
        = (List.ofFn fun i => extCoactQAlgHom k H V J (ExteriorAlgebra.ι k (w i))).prod := by
      rw [hω, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
      rfl
    rw [hmap]
    exact hlist
  have hfinal : extCoactQAlgHom k H V J ω
      ∈ LinearMap.range
          (LinearMap.rTensor (H ⧸ J) (k ∙ ω : Submodule k (ExteriorAlgebra k V)).subtype) := by
    refine mem_range_rTensor_mono ?_ hprod
    rw [hPspan]
    exact pow_span_ι_le_span_ιMulti w
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [map_smul, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [← extCoactQAlgHom_apply]
  exact hfinal

/-- **Takeuchi's Lemma 4.10(i), the inclusion `N(⋀ V, k ω) ≤ N(V, W)`**. -/
theorem nIdeal_exterior_line_le_nIdeal {n : ℕ} (w : Fin n → V) :
    NIdeal H (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V))
      ≤ NIdeal H (Submodule.span k (Set.range w)) :=
  (nIdeal_le_iff (fun _ hx => antipode_mem_NIdeal _ hx) _).2
    (isSubcomoduleMod_exterior_line _ (isSubcomoduleMod_NIdeal _))

/-- **Takeuchi's Lemma 4.10(i)** [Takeuchi1972]: for a linearly independent family `w` spanning `W`,
Takeuchi's ideal of `W` is the ideal of the line `⋀ⁿ W = k ω`. -/
theorem nIdeal_exterior_line_eq {n : ℕ} {w : Fin n → V} (hw : LinearIndependent k w) :
    NIdeal H (Submodule.span k (Set.range w))
      = NIdeal H (k ∙ (ExteriorAlgebra.ιMulti k n w) : Submodule k (ExteriorAlgebra k V)) :=
  le_antisymm (nIdeal_le_nIdeal_exterior_line hw) (nIdeal_exterior_line_le_nIdeal w)

end Exterior

end HopfAlgebra.Commutative
end
