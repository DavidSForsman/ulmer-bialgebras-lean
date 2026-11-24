module

public import Foundations.RingTheory.AbsFlatClass
public import Hopf.Cocommutative.HopfBiIdeal
public import Hopf.Cocommutative.BiIdealQuotient

/-!
# Newman's `μ` lands in sub-bialgebras

Let `H` be a Hopf algebra over a field `k` and let `I ⊆ H` be a left bi-ideal, with quotient
module coalgebra `π : H ↠ H ⧸ I` (`Hopf/Cocommutative/BiIdealQuotient.lean`).  Newman's map
`μ` sends `I` to the space of coinvariants

```
μ I  =  {h ∈ H | (1 ⊗ π) (Δ h) = h ⊗ π 1}
```

`Hopf/Cocommutative/HopfBiIdeal.lean` shows that `μ I` is a subalgebra as soon as `I` is a
left ideal.  This file proves the coalgebra half of the well-definedness of `μ`, which is where
cocommutativity of `H` enters (Newman quotes Sweedler's Lemma 16.1.1 for it).

The argument for `HopfAlgebra.Cocommutative.comul_mem_rightTensor_coinv` is the coassociativity
computation `(1 ⊗ ρ) ∘ Δ = (Δ ⊗ 1) ∘ ρ` for the comodule structure `ρ = (1 ⊗ π) ∘ Δ`: applied to
`h ∈ μ I` its right-hand side is `Δ h ⊗ π 1`, so `Δ h` is a coinvariant in the second variable, i.e.
lies in `H ⊗ μ I` — using that over a field `ker (1 ⊗ f) = H ⊗ ker f`.

## Main results

* `HopfAlgebra.Cocommutative.comul_mem_rightTensor_coinv`: `Δ (μ I) ⊆ H ⊗ μ I`, for an arbitrary
  submodule `I`;
* `HopfAlgebra.Cocommutative.comul_mem_leftTensor_coinv`: `Δ (μ I) ⊆ μ I ⊗ H`, when `H` is
  cocommutative;
* `HopfAlgebra.Cocommutative.rightTensor_inf_leftTensor`: `(H ⊗ G) ∩ (G ⊗ H) = G ⊗ G` for a subspace
  `G` of `H`;
* `HopfAlgebra.Cocommutative.isSubBialg_coinvSubalgebra`: consequently `μ I` is a **sub-bialgebra**
  of a cocommutative `H` for every left ideal `I`.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
* [M. E. Sweedler, *Hopf algebras*][Sweedler]
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra

namespace HopfAlgebra.Cocommutative

variable {k H : Type*} [CommRing k] [Ring H] [HopfAlgebra k H]

/-! ### `(H ⊗ G) ∩ (G ⊗ H) = G ⊗ G` -/

/-- Over a base ring all of whose modules are flat -- a commutative von Neumann regular ring, and
in particular a field -- the two "one-sided" submodules `H ⊗ G` and `G ⊗ H` of `H ⊗ H` meet in
`G ⊗ G`.

Over a field this is the usual argument with a linear complement of `G`; over a von Neumann
regular base ring `G` need not be a direct summand of `H`, and the proof instead uses that `G`
and `H ⧸ G` are flat, so that `G ⊗ (H ⧸ G) ↪ H ⊗ (H ⧸ G)` and `G ⊗ G = ker (G ⊗ H → G ⊗ H⧸G)`. -/
theorem rightTensor_inf_leftTensor [IsAbsFlat k] (G : Submodule k H) :
    rightTensor G ⊓ leftTensor G = LinearMap.range (TensorProduct.mapIncl G G) := by
  have hcomp : (LinearMap.lTensor H G.mkQ).comp (LinearMap.rTensor H G.subtype)
      = (LinearMap.rTensor (H ⧸ G) G.subtype).comp (LinearMap.lTensor G G.mkQ) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have hcomp2 : (LinearMap.rTensor H G.subtype).comp (LinearMap.lTensor G G.subtype)
      = TensorProduct.mapIncl G G := by
    rw [LinearMap.rTensor_comp_lTensor]
  refine le_antisymm ?_ ?_
  · rintro t ⟨htR, htL⟩
    rw [← range_rTensor_subtype] at htL
    obtain ⟨s, rfl⟩ := htL
    have hzero : LinearMap.lTensor H G.mkQ (LinearMap.rTensor H G.subtype s) = 0 := by
      have hle : rightTensor G ≤ LinearMap.ker (LinearMap.lTensor H G.mkQ) :=
        rightTensor_le fun a x hx => by
          simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 hx]
      exact hle htR
    have hinj : Function.Injective (LinearMap.rTensor (H ⧸ G) G.subtype) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
    have hs : LinearMap.lTensor G G.mkQ s = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, ← hcomp, LinearMap.comp_apply, hzero]
    have hex : Function.Exact (LinearMap.lTensor G G.subtype) (LinearMap.lTensor G G.mkQ) :=
      Module.Flat.lTensor_exact G (f := G.subtype) (g := G.mkQ) (by
        rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype])
    obtain ⟨s', rfl⟩ := (hex s).1 hs
    exact ⟨s', by rw [← LinearMap.comp_apply, hcomp2]⟩
  · rw [TensorProduct.range_mapIncl]
    exact le_inf (Submodule.map₂_le.2 fun x hx y hy => tmul_mem_rightTensor x hy)
      (Submodule.map₂_le.2 fun x hx y hy => tmul_mem_leftTensor hx y)

/-! ### Kernels of `1 ⊗ f` -/

/-- Over a base ring all of whose modules are flat, `ker (1 ⊗ f) = H ⊗ ker f`. -/
theorem ker_lTensor_eq_rightTensor [IsAbsFlat k] {Y : Type*} [AddCommGroup Y] [Module k Y]
    (f : H →ₗ[k] Y) :
    LinearMap.ker (LinearMap.lTensor H f) = rightTensor (LinearMap.ker f) := by
  have hex : Function.Exact (LinearMap.lTensor H (LinearMap.ker f).subtype)
      (LinearMap.lTensor H f) :=
    Module.Flat.lTensor_exact H (LinearMap.exact_subtype_ker_map f)
  rw [← range_lTensor_subtype, ← hex.linearMap_ker_eq]

/-! ### The comodule structure and its coinvariants -/

variable (I : Submodule k H)

/-- The right `H/I`-comodule structure `ρ = (1 ⊗ π) ∘ Δ` on `H`. -/
noncomputable def coact : H →ₗ[k] H ⊗[k] (H ⧸ I) :=
  LinearMap.lTensor H I.mkQ ∘ₗ comul (R := k) (A := H)

/-- The map whose kernel is `μ I`. -/
noncomputable def coinvMap : H →ₗ[k] H ⊗[k] (H ⧸ I) :=
  coact I - (TensorProduct.mk k H (H ⧸ I)).flip (I.mkQ 1)

/-- The kernel of `coinvMap I : h ↦ (1 ⊗ π)(Δ h) - h ⊗ π 1` is `coinv I`. -/
lemma ker_coinvMap : LinearMap.ker (coinvMap I) = coinv I := by
  ext h
  rw [LinearMap.mem_ker, coinvMap, LinearMap.sub_apply, sub_eq_zero, mem_coinv_iff_lTensor_mkQ]
  rfl

/-- On `coinv I` the coaction is trivial: `(1 ⊗ π)(Δ h) = h ⊗ π 1`. -/
lemma coact_apply_of_mem_coinv {h : H} (hh : h ∈ coinv I) :
    coact I h = h ⊗ₜ[k] I.mkQ (1 : H) := (mem_coinv_iff_lTensor_mkQ I h).1 hh

/-- Coassociativity in the form `(1 ⊗ ρ) ∘ Δ = assoc ∘ (Δ ⊗ 1) ∘ ρ`. -/
lemma lTensor_coact_comul (x : H) :
    LinearMap.lTensor H (coact I) (comul (R := k) x)
      = TensorProduct.assoc k H H (H ⧸ I)
          (LinearMap.rTensor (H ⧸ I) (comul (R := k) (A := H)) (coact I x)) := by
  have hA : ∀ t : H ⊗[k] H,
      LinearMap.rTensor (H ⧸ I) (comul (R := k) (A := H)) (LinearMap.lTensor H I.mkQ t)
        = TensorProduct.map (comul (R := k) (A := H)) I.mkQ t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add u v hu hv => simp only [map_add, hu, hv]
  have hB' : ∀ (s : H ⊗[k] H) (b : H),
      TensorProduct.assoc k H H (H ⧸ I) (s ⊗ₜ[k] I.mkQ b)
        = LinearMap.lTensor H (LinearMap.lTensor H I.mkQ)
            (TensorProduct.assoc k H H H (s ⊗ₜ[k] b)) := by
    intro s b
    induction s using TensorProduct.inductionOn with
    | tmul a c => simp
    | add s1 s2 h1 h2 => simp only [add_tmul, map_add, h1, h2]
  have hB : ∀ t : H ⊗[k] H,
      TensorProduct.assoc k H H (H ⧸ I) (TensorProduct.map (comul (R := k) (A := H)) I.mkQ t)
        = LinearMap.lTensor H (LinearMap.lTensor H I.mkQ)
            (TensorProduct.assoc k H H H
              (LinearMap.rTensor H (comul (R := k) (A := H)) t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a b => simpa using hB' (comul (R := k) a) b
    | add u v hu hv => simp only [map_add, hu, hv]
  have hco := congr($(Coalgebra.coassoc (R := k) (A := H)) x)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hco
  rw [coact, LinearMap.lTensor_comp]
  simp only [LinearMap.coe_comp, Function.comp_apply, hA, hB, ← hco]

/-- `(id ⊗ (· ⊗ c)) t = assoc (t ⊗ c)` for `t : H ⊗ H` and `c : H ⧸ I`. -/
lemma lTensor_flip_mk (c : H ⧸ I) (t : H ⊗[k] H) :
    LinearMap.lTensor H ((TensorProduct.mk k H (H ⧸ I)).flip c) t
      = TensorProduct.assoc k H H (H ⧸ I) (t ⊗ₜ[k] c) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp
  | add u v hu hv => simp only [map_add, hu, hv, add_tmul]

variable [IsAbsFlat k]

/-- **`Δ (μ I) ⊆ H ⊗ μ I`.**  This holds for an arbitrary submodule `I` of `H`. -/
theorem comul_mem_rightTensor_coinv {h : H} (hh : h ∈ coinv I) :
    comul (R := k) h ∈ rightTensor (coinv I) := by
  rw [← ker_coinvMap I, ← ker_lTensor_eq_rightTensor, LinearMap.mem_ker]
  have h1 : LinearMap.lTensor H (coinvMap I) (comul (R := k) h)
      = LinearMap.lTensor H (coact I) (comul (R := k) h)
        - LinearMap.lTensor H ((TensorProduct.mk k H (H ⧸ I)).flip (I.mkQ 1))
            (comul (R := k) h) := by
    rw [coinvMap, LinearMap.lTensor_sub, LinearMap.sub_apply]
  rw [h1, lTensor_coact_comul, coact_apply_of_mem_coinv I hh, lTensor_flip_mk,
    LinearMap.rTensor_tmul, sub_self]

/-- **`Δ (μ I) ⊆ μ I ⊗ H`** when `H` is cocommutative. -/
theorem comul_mem_leftTensor_coinv [Coalgebra.IsCocomm k H] {h : H} (hh : h ∈ coinv I) :
    comul (R := k) h ∈ leftTensor (coinv I) := by
  have hcomm := congr($(Coalgebra.IsCocomm.comm_comp_comul (R := k) (A := H)) h)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at hcomm
  have hle : rightTensor (coinv I)
      ≤ Submodule.comap (TensorProduct.comm k H H).toLinearMap (leftTensor (coinv I)) :=
    rightTensor_le fun a x hx => by
      simpa using tmul_mem_leftTensor hx a
  have := hle (comul_mem_rightTensor_coinv I hh)
  simpa [hcomm] using this

/-- **Newman's `μ` lands in sub-bialgebras**: for a cocommutative Hopf algebra `H` and a left
ideal `I`, the `λ`-kernel `μ I` is a subalgebra closed under the comultiplication. -/
theorem isSubBialg_coinvSubalgebra [Coalgebra.IsCocomm k H]
    (hI : ∀ (h : H), ∀ x ∈ I, h * x ∈ I) :
    IsSubBialg (coinvSubalgebra hI) where
  comul_mem x hx := by
    have hx' : x ∈ coinv I := hx
    rw [coinvSubalgebra_toSubmodule, ← rightTensor_inf_leftTensor]
    exact ⟨comul_mem_rightTensor_coinv I hx', comul_mem_leftTensor_coinv I hx'⟩

end HopfAlgebra.Cocommutative
