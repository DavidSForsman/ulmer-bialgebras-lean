module

public import Mathlib.RingTheory.HopfAlgebra.GroupLike
public import Hopf.Coradical.PointedDecompositionGeneral
public import Hopf.Coradical.Pointed

/-!
# The irreducible components of a pointed cocommutative Hopf algebra

A coalgebra is **pointed** (`Coalgebra.Coradical.IsPointed`) when each of its simple subcoalgebras
is the line spanned by a group-like element; over an algebraically closed field every cocommutative
coalgebra is pointed (`Coalgebra.Coradical.isPointed_of_isAlgClosed`).

For a pointed cocommutative Hopf algebra `H` over a field, Kostant's decomposition theorem
(`Hopf/Coradical/PointedDecompositionGeneral.lean`) therefore reads

```
H = ⨁_{g ∈ G(H)} H_g ,       H_g = the irreducible component of the line k g,
```

and left multiplication by a group-like element `d` — a coalgebra automorphism — permutes the
summands: `d • H_g = H_{d g}`.  This `G(H)`-grading of `H` is an input of the Sweedler-basis
constructions in `Hopf/Graded/FreeBasis.lean`.

## Main results

* `Coalgebra.Coradical.IsPointed`, `Coalgebra.Coradical.isPointed_of_isAlgClosed`;
* `Coalgebra.Coradical.glComponent` — the irreducible component of a group-like element;
* `Coalgebra.Coradical.map_mulLeft_glComponent` — `d • H_g = H_{d g}`;
* `Coalgebra.Coradical.iSup_glComponent_eq_top` and `Coalgebra.Coradical.iSupIndep_glComponent` —
  the decomposition;
* `Coalgebra.Coradical.isInternal_glComponent` — its packaging as an internal direct sum.

## References

* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.6
-/

@[expose] public section

open TensorProduct Coalgebra UlmerBialgebras.Subcoalg

universe u

namespace Coalgebra.Coradical

/-! ### Pointed coalgebras -/

section Pointed

variable (k C : Type u) [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A coalgebra is **pointed** if every simple subcoalgebra is the line spanned by a group-like
element. -/
def IsPointed : Prop :=
  ∀ S : Submodule k C, IsSimpleSubcoalgebra S →
    ∃ g : C, IsGroupLikeElem k g ∧ S = Submodule.span k {g}

variable {k C}

/-- Over an algebraically closed field every cocommutative coalgebra is pointed. -/
theorem isPointed_of_isAlgClosed [IsAlgClosed k] [IsCocomm k C] : IsPointed k C :=
  fun _ hS => exists_groupLike_of_isSimpleSubcoalgebra hS

end Pointed

/-! ### Irreducible components and coalgebra maps -/

section MapIrr

variable {k C D : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]
  [AddCommGroup D] [Module k D] [Coalgebra k D]

variable {f : D →ₗ[k] C}
  (hcomul : map f f ∘ₗ (comul : D →ₗ[k] D ⊗[k] D) = comul ∘ₗ f)

include hcomul

/-- The image of a wedge power under a coalgebra map is contained in the wedge power of the
image. -/
theorem map_wedgePow_le (X : Submodule k D) (n : ℕ) :
    Submodule.map f (wedgePow X n) ≤ wedgePow (X.map f) n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact le_trans (map_wedge_le hcomul _ _) (wedge_mono ih le_rfl)

/-- The image of an irreducible component under a coalgebra map is contained in the irreducible
component of the image. -/
theorem map_irrComponent_le (X : Submodule k D) :
    Submodule.map f (irrComponent X) ≤ irrComponent (X.map f) := by
  rw [irrComponent, Submodule.map_iSup]
  exact iSup_le fun n => le_trans (map_wedgePow_le hcomul X n) (wedgePow_le_irrComponent _ n)

end MapIrr

/-! ### The components of a Hopf algebra -/

section Hopf

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-- The **irreducible component** of a group-like element `g` of a Hopf algebra: the union of the
wedge powers of the line `k g`. -/
noncomputable def glComponent (g : GroupLike k H) : Submodule k H :=
  irrComponent (Submodule.span k {(g : H)})

/-- The irreducible component of a group-like element is a subcoalgebra. -/
theorem isSubcoalgebra_glComponent (g : GroupLike k H) : IsSubcoalgebra (glComponent g) :=
  isSubcoalgebra_irrComponent (isSubcoalgebra_span_groupLike g.2)

/-- The line `k g` spanned by a group-like element `g` is a simple subcoalgebra. -/
theorem isSimpleSubcoalgebra_span_gl (g : GroupLike k H) :
    IsSimpleSubcoalgebra (Submodule.span k {(g : H)}) :=
  isSimpleSubcoalgebra_span_groupLike g.2

/-- Left multiplication by a group-like element is a morphism of coalgebras. -/
theorem mulLeft_comul (d : GroupLike k H) :
    map (LinearMap.mulLeft k (d : H)) (LinearMap.mulLeft k (d : H))
        ∘ₗ (comul : H →ₗ[k] H ⊗[k] H)
      = comul ∘ₗ (LinearMap.mulLeft k (d : H)) := by
  have key : ∀ t : H ⊗[k] H,
      map (LinearMap.mulLeft k (d : H)) (LinearMap.mulLeft k (d : H)) t
        = ((d : H) ⊗ₜ[k] (d : H)) * t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add u v hu hv => rw [map_add, hu, hv, mul_add]
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [key, Bialgebra.comul_mul, d.2.comul_eq_tmul_self]

/-- Left multiplication by a group-like element commutes with taking irreducible components. -/
theorem map_mulLeft_irrComponent (d : GroupLike k H) (X : Submodule k H) :
    Submodule.map (LinearMap.mulLeft k (d : H)) (irrComponent X)
      = irrComponent (Submodule.map (LinearMap.mulLeft k (d : H)) X) := by
  have hcancel : ∀ (a b : GroupLike k H) (Y : Submodule k H),
      Submodule.map (LinearMap.mulLeft k (a : H))
        (Submodule.map (LinearMap.mulLeft k (b : H)) Y)
      = Submodule.map (LinearMap.mulLeft k ((a * b : GroupLike k H) : H)) Y := by
    intro a b Y
    rw [← Submodule.map_comp]
    congr 1
    exact LinearMap.ext fun y => by simp
  have hid : ∀ Y : Submodule k H,
      Submodule.map (LinearMap.mulLeft k ((1 : GroupLike k H) : H)) Y = Y := by
    intro Y
    have h1 : LinearMap.mulLeft k ((1 : GroupLike k H) : H) = LinearMap.id :=
      LinearMap.ext fun y => by simp
    rw [h1, Submodule.map_id]
  refine le_antisymm (map_irrComponent_le (mulLeft_comul d) X) ?_
  have h1 := map_irrComponent_le (mulLeft_comul d⁻¹)
    (Submodule.map (LinearMap.mulLeft k (d : H)) X)
  rw [hcancel, inv_mul_cancel, hid] at h1
  have h2 := Submodule.map_mono (f := LinearMap.mulLeft k (d : H)) h1
  rwa [hcancel, mul_inv_cancel, hid] at h2

/-- Left multiplication by a group-like element `d` carries the component of `g` onto the
component of `d * g`. -/
theorem map_mulLeft_glComponent (d g : GroupLike k H) :
    Submodule.map (LinearMap.mulLeft k (d : H)) (glComponent g) = glComponent (d * g) := by
  rw [glComponent, map_mulLeft_irrComponent]
  congr 1
  rw [Submodule.map_span]
  simp

/-- Two group-like elements spanning the same line are equal. -/
theorem groupLike_eq_of_span_eq {g h : GroupLike k H}
    (hgh : Submodule.span k {(g : H)} = Submodule.span k {(h : H)}) : g = h := by
  have hmem : (h : H) ∈ Submodule.span k {(g : H)} := by
    rw [hgh]; exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hcounit : counit (R := k) (h : H) = c * counit (R := k) (g : H) := by
    rw [← hc]; simp
  rw [h.2.counit_eq_one, g.2.counit_eq_one, mul_one] at hcounit
  refine GroupLike.ext ?_
  rw [← hc, ← hcounit, one_smul]

variable [IsCocomm k H]

/-- **Kostant's decomposition for a pointed cocommutative Hopf algebra**: the components of the
group-like elements span. -/
theorem iSup_glComponent_eq_top (hpt : IsPointed k H) :
    (⨆ g : GroupLike k H, glComponent g) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← iSup_irrComponent_eq_top' (k := k) (C := H)]
  refine iSup₂_le fun S hS => ?_
  obtain ⟨g, hg, rfl⟩ := hpt S hS
  exact le_iSup (fun g : GroupLike k H => glComponent g) ⟨g, hg⟩

/-- The components of the group-like elements are independent. -/
theorem iSupIndep_glComponent :
    iSupIndep (fun g : GroupLike k H => glComponent g) := by
  intro g
  rw [disjoint_iff]
  refine le_antisymm ?_ bot_le
  refine le_trans (inf_le_inf_left _ ?_)
    (le_of_eq (irrComponent_inf_iSup_eq_bot' (isSimpleSubcoalgebra_span_gl g)))
  refine iSup₂_le fun h hh => ?_
  exact le_iSup₂ (f := fun T (_ : T ∈ {T : Submodule k H | IsSimpleSubcoalgebra T ∧
      T ≠ Submodule.span k {(g : H)}}) => irrComponent T) (Submodule.span k {(h : H)})
    ⟨isSimpleSubcoalgebra_span_gl h, fun hx => hh (groupLike_eq_of_span_eq hx)⟩

/-- **The `G(H)`-grading of a pointed cocommutative Hopf algebra**, as an internal direct sum. -/
theorem isInternal_glComponent [DecidableEq (GroupLike k H)] (hpt : IsPointed k H) :
    DirectSum.IsInternal (fun g : GroupLike k H => glComponent g) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2
    ⟨iSupIndep_glComponent, iSup_glComponent_eq_top hpt⟩

end Hopf

end Coalgebra.Coradical
