module

public import Hopf.Basic.ComoduleTransl
public import Hopf.Basic.RelativeHopfFlat
public import Foundations.RingTheory.TensorContract

/-!
# The fundamental theorem of coalgebras

Every element of a coalgebra over a field lies in a *finite-dimensional subcoalgebra*.

The subcoalgebra is described explicitly: it is the span `E` of the iterated translates
`w ⇁ (u ⇀ x)` of `x` by functionals, where `u ⇀ -` is the right translation
(`Coalgebra.Comodule.transl`) and `w ⇁ -` is the left translation
(`Coalgebra.translLeft`).  Such a span is:

* closed under both translations, because translation turns the convolution product of
  functionals into composition, and the two translations commute
  (`Coalgebra.LocallyFinite.transl_translLeft_comm`);
* finite-dimensional, because the right translates of `x` span a finite-dimensional space
  (`Coalgebra.Comodule.translSpan_fg`) and the left translates of a fixed element span a
  finite-dimensional space;
* a subcoalgebra, because a tensor all of whose contractions lie in a subspace `E` lies in
  `E ⊗ E` (`TensorProduct.mem_range_map_of_forall_contract`).

## Main results

* `Coalgebra.LocallyFinite.transl_translLeft_comm`: the two translations commute;
* `Coalgebra.LocallyFinite.exists_fg_subcoalgebra`: every element of a coalgebra over a field lies
  in a finitely generated subcoalgebra.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], 2.2.1
* [W. C. Waterhouse, *Introduction to Affine Group Schemes*][waterhouseIntroductionAffineGroup1979],
  Section 3.3
-/

@[expose] public section

open TensorProduct Coalgebra Coalgebra.Comodule

section
open _root_.TensorProduct renaming map → tensorMap, rid → tensorRid

namespace Coalgebra.LocallyFinite

variable {k C : Type*} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-! ### The two translations -/

/-- Left translation is `c ↦ ∑ w (c₍₁₎) • c₍₂₎`, i.e. `contractLeft w` applied to `Δ c`. -/
lemma translLeft_eq_contractLeft (w : C →ₗ[k] k) (c : C) :
    translLeft w c = contractLeft w (comul (R := k) c) := rfl

/-- Right translation is `c ↦ ∑ u (c₍₂₎) • c₍₁₎`, i.e. `contractRight u` applied to `Δ c`. -/
lemma transl_eq_contractRight (u : C →ₗ[k] k) (c : C) :
    transl (R := k) (C := C) u c = contractRight u (comul (R := k) c) := rfl

/-- The left and the right translation operators of a coalgebra commute. -/
theorem transl_translLeft_comm (u w : C →ₗ[k] k) (c : C) :
    transl (R := k) (C := C) u (translLeft w c)
      = translLeft w (transl (R := k) (C := C) u c) := by
  classical
  set r := Coalgebra.Repr.arbitrary k c with hr
  set a₁ : (i : C × C) → Coalgebra.Repr k (r.left i) (C × C) :=
    fun i => Coalgebra.Repr.arbitrary k _ with ha₁
  set a₂ : (i : C × C) → Coalgebra.Repr k (r.right i) (C × C) :=
    fun i => Coalgebra.Repr.arbitrary k _ with ha₂
  -- the functional `x ⊗ (y ⊗ z) ↦ (w x * u z) • y`
  set g : C ⊗[k] C →ₗ[k] C := (tensorRid k C).toLinearMap
      ∘ₗ LinearMap.lTensor C u with hg
  set f : C ⊗[k] (C ⊗[k] C) →ₗ[k] C :=
    (TensorProduct.lid k C).toLinearMap ∘ₗ tensorMap w g with hf
  have hfapply : ∀ x y z : C, f (x ⊗ₜ[k] (y ⊗ₜ[k] z)) = (w x * u z) • y := by
    intro x y z
    simp [hf, hg, mul_smul, mul_comm]
  have hkey := Coalgebra.sum_tmul_tmul_eq r a₁ a₂
  apply_fun f at hkey
  rw [map_sum] at hkey
  simp only [map_sum, hfapply] at hkey
  -- the left-hand side of the key identity is `w ⇁ (u ⇀ c)`
  have hleft : translLeft w (transl (R := k) (C := C) u c)
      = ∑ i ∈ r.index, ∑ j ∈ (a₁ i).index,
          (w ((a₁ i).left j) * u (r.right i)) • (a₁ i).right j := by
    rw [transl_apply u r.toComodule, map_sum]
    simp only [Coalgebra.Repr.toComodule]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, translLeft_apply w (a₁ i), Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  -- and the right-hand side is `u ⇀ (w ⇁ c)`
  have hright : transl (R := k) (C := C) u (translLeft w c)
      = ∑ i ∈ r.index, ∑ j ∈ (a₂ i).index,
          (w (r.left i) * u ((a₂ i).right j)) • (a₂ i).left j := by
    rw [translLeft_apply w r, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, transl_apply u (a₂ i).toComodule, Finset.smul_sum]
    simp only [Coalgebra.Repr.toComodule]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
  rw [hleft, hright, ← hkey]

/-! ### Subspaces closed under the translations -/

variable (k C) in
/-- A submodule of a coalgebra closed under both translation operators. -/
def IsTranslClosed (E : Submodule k C) : Prop :=
  (∀ (w : C →ₗ[k] k), ∀ y ∈ E, translLeft w y ∈ E) ∧
    (∀ (u : C →ₗ[k] k), ∀ y ∈ E, transl (R := k) (C := C) u y ∈ E)

/-- A translation-closed subspace is a subcoalgebra. -/
theorem comul_mem_of_isTranslClosed {E : Submodule k C} (hE : IsTranslClosed k C E) {y : C}
    (hy : y ∈ E) :
    comul (R := k) y ∈ LinearMap.range (tensorMap E.subtype E.subtype) :=
  mem_range_map_of_forall_contract E _
    (fun θ => by rw [← translLeft_eq_contractLeft]; exact hE.1 θ y hy)
    (fun θ => by rw [← transl_eq_contractRight]; exact hE.2 θ y hy)

/-- The zero subspace is translation-closed. -/
lemma isTranslClosed_bot : IsTranslClosed k C (⊥ : Submodule k C) := by
  constructor <;>
    · intro w y hy; rw [(Submodule.mem_bot k).1 hy, map_zero]; exact Submodule.zero_mem _

/-- A sum of translation-closed subspaces is translation-closed. -/
lemma IsTranslClosed.sup {E F : Submodule k C} (hE : IsTranslClosed k C E)
    (hF : IsTranslClosed k C F) : IsTranslClosed k C (E ⊔ F) := by
  constructor
  · intro w y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hE.1 w a ha))
      (Submodule.mem_sup_right (hF.1 w b hb))
  · intro u y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hE.2 u a ha))
      (Submodule.mem_sup_right (hF.2 u b hb))

/-- **The fundamental theorem of coalgebras**, in the form used here: every element of a
coalgebra over a field lies in a finitely generated translation-closed subspace. -/
theorem exists_fg_translClosed (x : C) :
    ∃ E : Submodule k C, x ∈ E ∧ E.FG ∧ IsTranslClosed k C E := by
  classical
  set G : Set C := {y | ∃ w u : C →ₗ[k] k, y = translLeft w (transl (C := C) u x)} with hG
  set E : Submodule k C := Submodule.span k G with hE
  have hmemG : ∀ y ∈ G, y ∈ E := fun y hy => Submodule.subset_span hy
  -- `x` itself is a translate
  have hxE : x ∈ E := by
    refine hmemG _ ⟨(counit : C →ₗ[k] k), (counit : C →ₗ[k] k), ?_⟩
    rw [transl_counit_apply, translLeft_counit, LinearMap.id_apply]
  -- closure under the two translations
  have hclosed : IsTranslClosed k C E := by
    constructor
    · intro θ y hy
      refine (Submodule.span_le (p := E.comap (translLeft θ))).2 ?_ hy
      rintro z ⟨w, u, rfl⟩
      exact hmemG _ ⟨convFun w θ, u, by rw [translLeft_translLeft]⟩
    · intro θ y hy
      refine (Submodule.span_le (p := E.comap (transl (R := k) (C := C) θ))).2 ?_ hy
      rintro z ⟨w, u, rfl⟩
      exact hmemG _ ⟨w, convFun θ u, by rw [transl_translLeft_comm, transl_transl]⟩
  -- finite generation
  have hfg : E.FG := by
    obtain ⟨T, hT⟩ := translSpan_fg (k := k) (C := C) (M := C) x
    choose S hS using fun z : C =>
      exists_finset_forall_contractLeft (M := C) (N := C) (comul (R := k) z)
    refine Submodule.FG.of_le ⟨T.biUnion S, rfl⟩ ?_
    have hsub : ∀ z : C, ∀ w : C →ₗ[k] k, z ∈ (T : Set C) →
        translLeft w z ∈ Submodule.span k ((T.biUnion S : Finset C) : Set C) := by
      intro z w hz
      refine Submodule.span_mono ?_ (hS z w)
      intro y hy
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe]
      exact ⟨z, by simpa using hz, hy⟩
    rw [hE, Submodule.span_le]
    rintro y ⟨w, u, rfl⟩
    have hu : transl (R := k) (C := C) u x ∈ Submodule.span k (T : Set C) := by
      rw [hT]
      exact transl_mem_translSpan u x
    exact (Submodule.span_le (p := (Submodule.span k ((T.biUnion S : Finset C) : Set C)).comap
      (translLeft w))).2 (fun z hz => hsub z w hz) hu
  exact ⟨E, hxE, hfg, hclosed⟩

/-- Any finite subset of a coalgebra over a field lies in a finitely generated
translation-closed subspace. -/
theorem exists_fg_translClosed_finset (S : Finset C) :
    ∃ E : Submodule k C, (∀ x ∈ S, x ∈ E) ∧ E.FG ∧ IsTranslClosed k C E := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨⊥, by simp, Submodule.fg_bot, isTranslClosed_bot⟩
  | insert x S _ ih =>
    obtain ⟨E, hE, hEfg, hEcl⟩ := ih
    obtain ⟨F, hxF, hFfg, hFcl⟩ := exists_fg_translClosed (k := k) x
    refine ⟨E ⊔ F, ?_, hEfg.sup hFfg, hEcl.sup hFcl⟩
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hyS
    · exact Submodule.mem_sup_right hxF
    · exact Submodule.mem_sup_left (hE y hyS)

/-- **The fundamental theorem of coalgebras.**  Every element of a coalgebra over a field lies in
a finitely generated subcoalgebra.  ([Sweedler], 2.2.1.) -/
theorem exists_fg_subcoalgebra (x : C) :
    ∃ E : Submodule k C, x ∈ E ∧ E.FG ∧
      ∀ y ∈ E, comul (R := k) y ∈ LinearMap.range (tensorMap E.subtype E.subtype)
          := by
  obtain ⟨E, hxE, hfg, hcl⟩ := exists_fg_translClosed (k := k) x
  exact ⟨E, hxE, hfg, fun y hy => comul_mem_of_isTranslClosed hcl hy⟩

end Coalgebra.LocallyFinite
end
