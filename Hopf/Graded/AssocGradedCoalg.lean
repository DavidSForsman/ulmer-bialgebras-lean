module

public import Hopf.Graded.AssocGradedPhi

/-!
# The coalgebra structure on the associated graded object

Let `S : HopfAlgebra.Graded.HopfSplit k H`. The associated graded object `S.Gr = ⨁ₙ Cₙ` is a
commutative `k`-algebra (`Hopf/Graded/AssocGraded.lean`). This file endows it with a coalgebra
structure: the comultiplication of a homogeneous element of degree `n` is obtained by applying `Δ`
in `H` and taking the components of total degree `n`,

```
Δ_gr (a) = ∑_{i+j=n} (cmp i ⊗ cmp j) (Δ a) = S.phi n (Δ a) ,      a ∈ Cₙ ,
```

and the counit is the counit of `H` composed with the (linear) embedding `S.emb : S.Gr →ₗ H`.

The verification of the axioms uses only the two facts isolated in
`Hopf/Graded/AssocGradedPhi.lean`: on a tensor of homogeneous elements of complementary
degrees exactly one term of `phi` survives, and `phi n` kills the tensors of total degree `< n`.

## Main results

* `HopfAlgebra.Graded.HopfSplit.gcomul`: the comultiplication of `S.Gr`, given on `Cₙ` by
  `S.phi n ∘ Δ`.
* `HopfAlgebra.Graded.HopfSplit.gcounit`: the counit of `S.Gr`, the counit of `H` composed with
  `S.emb`.
* `HopfAlgebra.Graded.HopfSplit.gcoassoc`: coassociativity of `gcomul`.
* `HopfAlgebra.Graded.HopfSplit.instCoalgebra`: the resulting `Coalgebra k S.Gr` instance.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [J. W. Milnor, J. C. Moore, *On the structure of Hopf algebras*][Milnor-Moore]
-/

@[expose] public section

universe u

open TensorProduct Coalgebra Coalgebra.Coradical

namespace HopfAlgebra.Graded

namespace HopfSplit

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H] (S : HopfSplit k H)

/-- A criterion for two linear maps out of `H ⊗ H` to agree on `fil2 n`. -/
theorem fil2_ext {n : ℕ} {M : Type u} [AddCommGroup M] [Module k M] {f g : H ⊗[k] H →ₗ[k] M}
    (h : ∀ i ≤ n, ∀ u ∈ S.F i, ∀ v ∈ S.F (n - i), f (u ⊗ₜ[k] v) = g (u ⊗ₜ[k] v))
    {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) : f z = g z := by
  have hle : S.fil2 n ≤ LinearMap.ker (f - g) :=
    S.fil2_le_of_tmul fun i hi u hu v hv => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
      exact h i hi u hu v hv
  have h0 := hle hz
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h0
  exact h0

/-! ### The comultiplication -/

/-- The comultiplication of a homogeneous element of degree `n`, computed in `H`. -/
noncomputable def dAux (n : ℕ) : H →ₗ[k] S.Gr ⊗[k] S.Gr :=
  S.phi n ∘ₗ (comul : H →ₗ[k] H ⊗[k] H)

/-- `dAux n x = phi n (Δ x)`. -/
theorem dAux_apply (n : ℕ) (x : H) : S.dAux n x = S.phi n (comul (R := k) x) := rfl

/-- For `x ∈ Fₘ` with `m < n`, `dAux n x = 0`. -/
theorem dAux_eq_zero_of_mem_lt {m n : ℕ} (hmn : m < n) {x : H} (hx : x ∈ S.F m) :
    S.dAux n x = 0 :=
  S.phi_apply_eq_zero_of_mem_fil2 hmn (S.comul_mem_fil2 hx)

/-- The comultiplication of the associated graded object. -/
noncomputable def gcomul : S.Gr →ₗ[k] S.Gr ⊗[k] S.Gr :=
  DirectSum.toModule k ℕ (S.Gr ⊗[k] S.Gr) (fun n => (S.dAux n) ∘ₗ (S.C n).subtype)

/-- The graded comultiplication of `a ∈ Cₙ` (placed in degree `n`) is `dAux n a`. -/
theorem gcomul_ofC (n : ℕ) (a : ↥(S.C n)) : S.gcomul (S.ofC n a) = S.dAux n (a : H) :=
  DirectSum.toModule_lof k (φ := fun i => S.dAux i ∘ₗ (S.C i).subtype) n a

/-- For `x ∈ Fₙ`, the graded comultiplication of `cmp n x` is `dAux n x`. -/
theorem gcomul_cmp {n : ℕ} {x : H} (hx : x ∈ S.F n) : S.gcomul (S.cmp n x) = S.dAux n x := by
  rw [cmp, LinearMap.comp_apply, S.gcomul_ofC, LinearMap.codRestrict_apply]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [S.toSplit.pr_zero_of_mem_F_zero hx]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsub : x - S.pr (m + 1) x ∈ S.F m := S.toSplit.sub_pr_mem hx
    have : S.dAux (m + 1) (x - S.pr (m + 1) x) = 0 :=
      S.dAux_eq_zero_of_mem_lt (by omega) hsub
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

/-! ### The counit -/

/-- The counit of the associated graded object. -/
noncomputable def gcounit : S.Gr →ₗ[k] k := (counit : H →ₗ[k] k) ∘ₗ S.emb

/-- `gcounit (cmp n x) = ε (pr n x)`. -/
theorem gcounit_cmp (n : ℕ) (x : H) : S.gcounit (S.cmp n x) = counit (R := k) (S.pr n x) := by
  rw [gcounit, LinearMap.comp_apply, S.emb_cmp]

/-- The graded counit vanishes on components of positive degree. -/
theorem gcounit_cmp_of_pos {n : ℕ} (hn : 1 ≤ n) (x : H) : S.gcounit (S.cmp n x) = 0 := by
  rw [S.gcounit_cmp, S.counit_pr n hn x]

/-- For `x ∈ Fₘ`, `ε (pr 0 x) = ε x`. -/
theorem counit_pr_zero {m : ℕ} {x : H} (hx : x ∈ S.F m) :
    counit (R := k) (S.pr 0 x) = counit (R := k) x := by
  have hsum := S.toSplit.sum_pr m x hx
  have : counit (R := k) x = ∑ i ∈ Finset.range (m + 1), counit (R := k) (S.pr i x) := by
    rw [← map_sum, hsum]
  rw [this, Finset.sum_eq_single 0]
  · intro i _ hi
    exact S.counit_pr i (by omega) x
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

/-- For `x ∈ Fₘ`, the graded counit of `cmp 0 x` is `ε(x)`. -/
theorem gcounit_cmp_zero {m : ℕ} {x : H} (hx : x ∈ S.F m) :
    S.gcounit (S.cmp 0 x) = counit (R := k) x := by
  rw [S.gcounit_cmp, S.counit_pr_zero hx]

/-! ### Coassociativity -/

/-- The degree-`n` component map on `H ⊗ (H ⊗ H)`. -/
noncomputable def phi3 (n : ℕ) : H ⊗[k] (H ⊗[k] H) →ₗ[k] S.Gr ⊗[k] (S.Gr ⊗[k] S.Gr) :=
  ∑ i ∈ Finset.range (n + 1), TensorProduct.map (S.cmp i) (S.phi (n - i))

/-- `phi3 n (u ⊗ w) = ∑_{i ≤ n} cmp i u ⊗ phi (n - i) w`. -/
theorem phi3_tmul (n : ℕ) (u : H) (w : H ⊗[k] H) :
    S.phi3 n (u ⊗ₜ[k] w) = ∑ i ∈ Finset.range (n + 1), S.cmp i u ⊗ₜ[k] S.phi (n - i) w := by
  simp [phi3, LinearMap.sum_apply]

/-- For `u ∈ F p`, `w ∈ fil2 q` and `p + q = n`, `phi3 n (u ⊗ w) = cmp p u ⊗ phi q w`. -/
theorem phi3_tmul_of_mem {p q n : ℕ} (hpq : p + q = n) {u : H} (hu : u ∈ S.F p)
    {w : H ⊗[k] H} (hw : w ∈ S.fil2 q) :
    S.phi3 n (u ⊗ₜ[k] w) = S.cmp p u ⊗ₜ[k] S.phi q w := by
  rw [S.phi3_tmul]
  rw [Finset.sum_eq_single p]
  · rw [show n - p = q by omega]
  · intro i _ hip
    rcases lt_or_gt_of_ne hip with h | h
    · rw [S.phi_apply_eq_zero_of_mem_fil2 (m := q) (by omega) hw, tmul_zero]
    · rw [S.cmp_eq_zero_of_mem_lt h hu, zero_tmul]
  · intro hp
    exact absurd (Finset.mem_range.2 (by omega)) hp

/-- Compatibility of `phi3` with the associator. -/
theorem assoc_phi_tmul {p q n : ℕ} (hpq : p + q = n) {w : H ⊗[k] H} (hw : w ∈ S.fil2 p)
    {v : H} (hv : v ∈ S.F q) :
    TensorProduct.assoc k S.Gr S.Gr S.Gr ((S.phi p w) ⊗ₜ[k] (S.cmp q v))
      = S.phi3 n (TensorProduct.assoc k H H H (w ⊗ₜ[k] v)) := by
  refine S.fil2_ext
    (f := (TensorProduct.assoc k S.Gr S.Gr S.Gr).toLinearMap
      ∘ₗ ((TensorProduct.mk k (S.Gr ⊗[k] S.Gr) S.Gr).flip (S.cmp q v)) ∘ₗ S.phi p)
    (g := S.phi3 n ∘ₗ (TensorProduct.assoc k H H H).toLinearMap
      ∘ₗ ((TensorProduct.mk k (H ⊗[k] H) H).flip v))
    (fun i hi x hx y hy => ?_) hw
  have hxy : x ⊗ₜ[k] y ∈ S.fil2 p := S.tmul_mem_fil2 hi hx hy
  have hyv : y ⊗ₜ[k] v ∈ S.fil2 (p - i + q) :=
    S.tmul_mem_fil2 (i := p - i) (by omega) hy (by simpa using hv)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.flip_apply,
    TensorProduct.mk_apply]
  rw [S.phi_tmul_of_mem (p := i) (q := p - i) (by omega) hx hy,
    TensorProduct.assoc_tmul, TensorProduct.assoc_tmul,
    S.phi3_tmul_of_mem (p := i) (q := p - i + q) (by omega) hx hyv,
    S.phi_tmul_of_mem (p := p - i) (q := q) rfl hy hv]

/-- For `z ∈ fil2 n`, reassociating `(gcomul ⊗ id) (phi n z)` gives `phi3 n` of the
reassociated `(Δ ⊗ id) z`. -/
theorem coassoc_aux_rTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    TensorProduct.assoc k S.Gr S.Gr S.Gr (LinearMap.rTensor S.Gr S.gcomul (S.phi n z))
      = S.phi3 n (TensorProduct.assoc k H H H
          (LinearMap.rTensor H (comul : H →ₗ[k] H ⊗[k] H) z)) := by
  refine S.fil2_ext
    (f := (TensorProduct.assoc k S.Gr S.Gr S.Gr).toLinearMap
      ∘ₗ (LinearMap.rTensor S.Gr S.gcomul) ∘ₗ S.phi n)
    (g := S.phi3 n ∘ₗ (TensorProduct.assoc k H H H).toLinearMap
      ∘ₗ (LinearMap.rTensor H (comul : H →ₗ[k] H ⊗[k] H)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, S.gcomul_cmp hu]
  exact S.assoc_phi_tmul (p := i) (q := n - i) (by omega) (S.comul_mem_fil2 hu) hv

/-- For `z ∈ fil2 n`, `(id ⊗ gcomul) (phi n z) = phi3 n ((id ⊗ Δ) z)`. -/
theorem coassoc_aux_lTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    LinearMap.lTensor S.Gr S.gcomul (S.phi n z)
      = S.phi3 n (LinearMap.lTensor H (comul : H →ₗ[k] H ⊗[k] H) z) := by
  refine S.fil2_ext
    (f := (LinearMap.lTensor S.Gr S.gcomul) ∘ₗ S.phi n)
    (g := S.phi3 n ∘ₗ (LinearMap.lTensor H (comul : H →ₗ[k] H ⊗[k] H)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, S.gcomul_cmp hv,
    S.phi3_tmul_of_mem (p := i) (q := n - i) (by omega) hu (S.comul_mem_fil2 hv)]
  rfl

/-- Coassociativity of `gcomul`: `assoc ∘ (gcomul ⊗ id) ∘ gcomul = (id ⊗ gcomul) ∘ gcomul`. -/
theorem gcoassoc :
    (TensorProduct.assoc k S.Gr S.Gr S.Gr).toLinearMap ∘ₗ LinearMap.rTensor S.Gr S.gcomul
        ∘ₗ S.gcomul
      = LinearMap.lTensor S.Gr S.gcomul ∘ₗ S.gcomul := by
  refine LinearMap.ext fun g => ?_
  refine S.induction_on (motive := fun g =>
    ((TensorProduct.assoc k S.Gr S.Gr S.Gr).toLinearMap ∘ₗ LinearMap.rTensor S.Gr S.gcomul
        ∘ₗ S.gcomul) g = (LinearMap.lTensor S.Gr S.gcomul ∘ₗ S.gcomul) g) g ?_ (fun n a => ?_)
    (fun x y hx hy => by simp only [map_add, hx, hy])
  · rw [LinearMap.map_zero, LinearMap.map_zero]
  · have ha : (a : H) ∈ S.F n := S.c_le_f n a.2
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [S.gcomul_ofC, S.dAux_apply]
    rw [S.coassoc_aux_rTensor (S.comul_mem_fil2 ha), S.coassoc_aux_lTensor (S.comul_mem_fil2 ha)]
    congr 1
    exact Coalgebra.coassoc_apply (R := k) (a : H)

/-! ### The counit laws -/

/-- For `z ∈ fil2 n`, `lid ((gcounit ⊗ id) (phi n z)) = cmp n (lid ((ε ⊗ id) z))`. -/
theorem counit_aux_rTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    TensorProduct.lid k S.Gr (LinearMap.rTensor S.Gr S.gcounit (S.phi n z))
      = S.cmp n (TensorProduct.lid k H (LinearMap.rTensor H (counit : H →ₗ[k] k) z)) := by
  refine S.fil2_ext
    (f := (TensorProduct.lid k S.Gr).toLinearMap ∘ₗ (LinearMap.rTensor S.Gr S.gcounit) ∘ₗ S.phi n)
    (g := S.cmp n ∘ₗ (TensorProduct.lid k H).toLinearMap
      ∘ₗ (LinearMap.rTensor H (counit : H →ₗ[k] k)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
    TensorProduct.lid_tmul, map_smul]
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    rw [S.gcounit_cmp_zero hu]
    simp
  · rw [S.gcounit_cmp_of_pos hi0, zero_smul,
      S.cmp_eq_zero_of_mem_lt (m := n - i) (by omega) hv, smul_zero]

/-- For `z ∈ fil2 n`, `rid ((id ⊗ gcounit) (phi n z)) = cmp n (rid ((id ⊗ ε) z))`. -/
theorem counit_aux_lTensor {n : ℕ} {z : H ⊗[k] H} (hz : z ∈ S.fil2 n) :
    TensorProduct.rid k S.Gr (LinearMap.lTensor S.Gr S.gcounit (S.phi n z))
      = S.cmp n (TensorProduct.rid k H (LinearMap.lTensor H (counit : H →ₗ[k] k) z)) := by
  refine S.fil2_ext
    (f := (TensorProduct.rid k S.Gr).toLinearMap ∘ₗ (LinearMap.lTensor S.Gr S.gcounit) ∘ₗ S.phi n)
    (g := S.cmp n ∘ₗ (TensorProduct.rid k H).toLinearMap
      ∘ₗ (LinearMap.lTensor H (counit : H →ₗ[k] k)))
    (fun i hi u hu v hv => ?_) hz
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [S.phi_tmul_of_mem (p := i) (q := n - i) (by omega) hu hv,
    LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
    TensorProduct.rid_tmul, map_smul]
  rcases Nat.eq_zero_or_pos (n - i) with hi0 | hi0
  · rw [hi0] at hv ⊢
    rw [S.gcounit_cmp_zero hv]
    rw [show i = n by omega]
  · rw [S.gcounit_cmp_of_pos hi0, zero_smul,
      S.cmp_eq_zero_of_mem_lt (m := i) (by omega) hu, smul_zero]

/-- Left counit law for `Gr`: `(gcounit ⊗ id) ∘ gcomul = (x ↦ 1 ⊗ x)`. -/
theorem grTensor_counit_comp_comul :
    LinearMap.rTensor S.Gr S.gcounit ∘ₗ S.gcomul = TensorProduct.mk k k S.Gr 1 := by
  refine LinearMap.ext fun g => ?_
  refine S.induction_on (motive := fun g =>
    (LinearMap.rTensor S.Gr S.gcounit ∘ₗ S.gcomul) g = TensorProduct.mk k k S.Gr 1 g) g ?_
    (fun n a => ?_) (fun x y hx hy => by simp only [map_add, hx, hy])
  · simp
  · have ha : (a : H) ∈ S.F n := S.c_le_f n a.2
    apply (TensorProduct.lid k S.Gr).injective
    simp only [LinearMap.comp_apply, TensorProduct.mk_apply, TensorProduct.lid_tmul, one_smul]
    rw [S.gcomul_ofC, S.dAux_apply, S.counit_aux_rTensor (S.comul_mem_fil2 ha)]
    have h : TensorProduct.lid k H
        (LinearMap.rTensor H (counit : H →ₗ[k] k) (comul (R := k) (a : H))) = (a : H) := by
      have := Coalgebra.rTensor_counit_comp_comul (R := k) (A := H)
      have h2 : LinearMap.rTensor H (counit : H →ₗ[k] k) (comul (R := k) (a : H))
          = (1 : k) ⊗ₜ[k] (a : H) := LinearMap.ext_iff.1 this (a : H)
      rw [h2, TensorProduct.lid_tmul, one_smul]
    rw [h]
    exact (S.ofC_eq_cmp n a).symm

/-- Right counit law for `Gr`: `(id ⊗ gcounit) ∘ gcomul = (x ↦ x ⊗ 1)`. -/
theorem glTensor_counit_comp_comul :
    LinearMap.lTensor S.Gr S.gcounit ∘ₗ S.gcomul = (TensorProduct.mk k S.Gr k).flip 1 := by
  refine LinearMap.ext fun g => ?_
  refine S.induction_on (motive := fun g =>
    (LinearMap.lTensor S.Gr S.gcounit ∘ₗ S.gcomul) g = (TensorProduct.mk k S.Gr k).flip 1 g) g ?_
    (fun n a => ?_) (fun x y hx hy => by simp only [map_add, hx, hy])
  · simp
  · have ha : (a : H) ∈ S.F n := S.c_le_f n a.2
    apply (TensorProduct.rid k S.Gr).injective
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      TensorProduct.rid_tmul, one_smul]
    rw [S.gcomul_ofC, S.dAux_apply, S.counit_aux_lTensor (S.comul_mem_fil2 ha)]
    have h : TensorProduct.rid k H
        (LinearMap.lTensor H (counit : H →ₗ[k] k) (comul (R := k) (a : H))) = (a : H) := by
      have h2 : LinearMap.lTensor H (counit : H →ₗ[k] k) (comul (R := k) (a : H))
          = (a : H) ⊗ₜ[k] (1 : k) :=
        LinearMap.ext_iff.1 (Coalgebra.lTensor_counit_comp_comul (R := k) (A := H)) (a : H)
      rw [h2, TensorProduct.rid_tmul, one_smul]
    rw [h]
    exact (S.ofC_eq_cmp n a).symm

/-- **The associated graded object is a coalgebra.** -/
noncomputable instance instCoalgebra : Coalgebra k S.Gr where
  comul := S.gcomul
  counit := S.gcounit
  coassoc := S.gcoassoc
  rTensor_counit_comp_comul := S.grTensor_counit_comp_comul
  lTensor_counit_comp_comul := S.glTensor_counit_comp_comul

end HopfSplit

end HopfAlgebra.Graded
