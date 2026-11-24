module

public import Hopf.Cocommutative.DescentAlgClosure
public import Hopf.Coradical.TensorSub

/-!
# The coinvariants and the bi-ideals under a scalar extension

Newman's second closure identity `τ (μ I) = I` is reduced, in his paper, first to an
algebraically closed base field (his Corollary 3.4) and then to a pointed irreducible Hopf
algebra.  This file carries out the first of these two reductions on the Hopf-algebraic side:
all the data of the identity — left bi-ideals, the coinvariants `μ` and the left ideal `τ` —
behave well under a field extension `k ⊆ L`.

## Main results

* `HopfAlgebra.Cocommutative.bcInv` — the natural `L`-linear isomorphism
  `(L ⊗ H) ⊗_L (L ⊗ H) ≅ L ⊗ (H ⊗ H)`;
* `HopfAlgebra.Cocommutative.restrictScalars_baseChange` — `L ⊗ W` computed as a `k`-submodule is
  `Coalgebra.Coradical.tens ⊤ W`;
* `HopfAlgebra.Cocommutative.isLeftBiIdeal_baseChange` — the base change of a left bi-ideal is a
  left bi-ideal;
* `HopfAlgebra.Cocommutative.coinv_baseChange_le` — `μ (L ⊗ I) ≤ L ⊗ μ I`;
* `HopfAlgebra.Cocommutative.tau_baseChange_le` — `τ (L ⊗ K) ≤ L ⊗ τ K`;
* `HopfAlgebra.Cocommutative.tau_coinv_eq_of_baseChange'` — **the second closure identity descends
  along `k ⊆ L`**; hence it suffices to prove it over an algebraic closure of `k`, where every
  cocommutative Hopf algebra is pointed (this is how
  `HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq` is proved).

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975], Corollary 3.4
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
-/

@[expose] public section

open TensorProduct Coalgebra HopfAlgebra Coalgebra.Coradical

universe u

namespace HopfAlgebra.Cocommutative

section BaseChange

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {H : Type u} [Ring H] [HopfAlgebra k H]

/-! ### The comparison isomorphism -/

/-- The natural `L`-linear isomorphism `(L ⊗ H) ⊗_L (L ⊗ H) ≅ L ⊗ (H ⊗ H)`. -/
noncomputable def bcInv (k L : Type u) [Field k] [Field L] [Algebra k L]
    (H : Type u) [Ring H] [Algebra k H] :
    (L ⊗[k] H) ⊗[L] (L ⊗[k] H) ≃ₗ[L] L ⊗[k] (H ⊗[k] H) :=
  (AlgebraTensorModule.cancelBaseChange k L L (L ⊗[k] H) H).trans
    (AlgebraTensorModule.assoc k k L L H H)

/-- `bcInv ((a ⊗ x) ⊗_L (b ⊗ y)) = (b * a) ⊗ (x ⊗ y)`. -/
@[simp]
theorem bcInv_tmul (a b : L) (x y : H) :
    bcInv k L H ((a ⊗ₜ[k] x) ⊗ₜ[L] (b ⊗ₜ[k] y)) = (b * a) ⊗ₜ[k] (x ⊗ₜ[k] y) := by
  simp [bcInv, AlgebraTensorModule.cancelBaseChange, AlgebraTensorModule.assoc,
    TensorProduct.smul_tmul', smul_eq_mul]

/-- `a • (1 ⊗ t) = a ⊗ t`. -/
theorem smul_one_tmul {M : Type u} [AddCommGroup M] [Module k M] (a : L) (t : M) :
    a • ((1 : L) ⊗ₜ[k] t) = a ⊗ₜ[k] t := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- `bcInv` inverts the comparison map `bcRel`. -/
theorem bcInv_bcRel (t : H ⊗[k] H) :
    bcInv k L H (bcRel (L := L) t) = (1 : L) ⊗ₜ[k] t := by
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp
  | add u v hu hv => rw [map_add, map_add, hu, hv, TensorProduct.tmul_add]

/-! ### Base change of submodules -/

section Submodules

variable {M : Type u} [AddCommGroup M] [Module k M]

/-- The base change `L ⊗ W` of a `k`-submodule, computed as a `k`-submodule of `L ⊗ M`. -/
theorem restrictScalars_baseChange (W : Submodule k M) :
    Submodule.restrictScalars k (W.baseChange L) = tens (⊤ : Submodule k L) W := by
  have hker : Submodule.restrictScalars k
      (LinearMap.ker (LinearMap.baseChange L W.mkQ)) = tens (⊤ : Submodule k L) W := by
    have h : LinearMap.ker (LinearMap.lTensor L W.mkQ) = tens (⊤ : Submodule k L) W := by
      rw [ker_lTensor, Submodule.ker_mkQ]
    rw [← h]
    ext t
    simp [LinearMap.mem_ker, LinearMap.baseChange_eq_lTensor]
  refine le_antisymm ?_ ?_
  · rw [← hker]
    have hle : W.baseChange L ≤ LinearMap.ker (LinearMap.baseChange L W.mkQ) := by
      rw [Submodule.baseChange_eq_span]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).2 ha]
    exact fun t ht => hle ht
  · refine tens_le_iff.2 fun a _ w hw => ?_
    have h1 : (1 : L) ⊗ₜ[k] w ∈ W.baseChange L := Submodule.tmul_mem_baseChange_of_mem _ hw
    have := (W.baseChange L).smul_mem a h1
    rwa [TensorProduct.smul_tmul', smul_eq_mul, mul_one] at this

end Submodules

/-! ### The coinvariants of a base-changed bi-ideal -/

/-- The `k`-linear map `θ : x ↦ Δ x - x ⊗ 1` whose preimage of `H ⊗ I` is `μ I`. -/
noncomputable def coinvMapAux : H →ₗ[k] H ⊗[k] H :=
  comul (R := k) (A := H) - (TensorProduct.mk k H H).flip 1

/-- The comparison isomorphism identifies the base-changed `θ` with the `θ` of `L ⊗ H`. -/
theorem bcInv_comul_sub (z : L ⊗[k] H) :
    bcInv k L H (comul (R := L) z - z ⊗ₜ[L] (1 : L ⊗[k] H))
      = LinearMap.baseChange L (coinvMapAux (k := k) (H := H)) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      have hsm : (a : L) ⊗ₜ[k] x = a • ((1 : L) ⊗ₜ[k] x) := (smul_one_tmul a x).symm
      have hone : (1 : L ⊗[k] H) = (1 : L) ⊗ₜ[k] (1 : H) := rfl
      have hbase : bcInv k L H (comul (R := L) ((1 : L) ⊗ₜ[k] x)
            - ((1 : L) ⊗ₜ[k] x) ⊗ₜ[L] (1 : L ⊗[k] H))
          = (1 : L) ⊗ₜ[k] (coinvMapAux (k := k) (H := H) x) := by
        rw [comul_one_tmul, map_sub, bcInv_bcRel, hone, bcInv_tmul]
        simp [coinvMapAux, TensorProduct.tmul_sub]
      have h1 : comul (R := L) ((a : L) ⊗ₜ[k] x) - ((a : L) ⊗ₜ[k] x) ⊗ₜ[L] (1 : L ⊗[k] H)
          = a • (comul (R := L) ((1 : L) ⊗ₜ[k] x)
              - ((1 : L) ⊗ₜ[k] x) ⊗ₜ[L] (1 : L ⊗[k] H)) := by
        rw [hsm, map_smul, smul_sub]
        congr 1
      rw [h1, map_smul, hbase, smul_one_tmul, LinearMap.baseChange_tmul]
  | add u v hu hv =>
      have hadd : comul (R := L) (u + v) - (u + v) ⊗ₜ[L] (1 : L ⊗[k] H)
          = (comul (R := L) u - u ⊗ₜ[L] (1 : L ⊗[k] H))
            + (comul (R := L) v - v ⊗ₜ[L] (1 : L ⊗[k] H)) := by
        rw [map_add, TensorProduct.add_tmul]
        abel
      rw [hadd, map_add, hu, hv, map_add]

/-- The comparison isomorphism carries `(L ⊗ H) ⊗_L (L ⊗ I)` into `L ⊗ (H ⊗ I)`. -/
theorem bcInv_tmul_mem (I : Submodule k H) (u : L ⊗[k] H) {v : L ⊗[k] H}
    (hv : v ∈ I.baseChange L) :
    bcInv k L H (u ⊗ₜ[L] v) ∈ (rightTensor I).baseChange L := by
  have hv' : v ∈ tens (⊤ : Submodule k L) I := by
    rw [← restrictScalars_baseChange (L := L) I]
    exact hv
  induction u using TensorProduct.inductionOn with
  | tmul a x =>
      have hQ : tens (⊤ : Submodule k L) I ≤ Submodule.comap
          (((bcInv k L H).toLinearMap ∘ₗ
            (TensorProduct.mk L (L ⊗[k] H) (L ⊗[k] H) ((a : L) ⊗ₜ[k] x))).restrictScalars k)
          (Submodule.restrictScalars k ((rightTensor I).baseChange L)) := by
        refine tens_le_iff.2 fun b _ y hy => ?_
        simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply,
          LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
          LinearEquiv.coe_coe, bcInv_tmul, Submodule.restrictScalars_mem]
        rw [← smul_one_tmul]
        exact Submodule.smul_mem _ _
          (Submodule.tmul_mem_baseChange_of_mem _ (tmul_mem_rightTensor x hy))
      exact hQ hv'
  | add u₁ u₂ h₁ h₂ =>
      rw [TensorProduct.add_tmul, map_add]
      exact Submodule.add_mem _ h₁ h₂

/-- **The coinvariants of a base-changed left ideal.**  `μ (L ⊗ I) ≤ L ⊗ μ I`. -/
theorem coinv_baseChange_le (I : Submodule k H) :
    coinv (I.baseChange L) ≤ (coinv I).baseChange L := by
  intro z hz
  have hz' : comul (R := L) z - z ⊗ₜ[L] (1 : L ⊗[k] H) ∈ rightTensor (I.baseChange L) := hz
  -- transport along the comparison isomorphism
  have hmap : rightTensor (I.baseChange L)
      ≤ Submodule.comap (bcInv k L H).toLinearMap ((rightTensor I).baseChange L) :=
    Submodule.map₂_le.2 fun u _ v hv => Submodule.mem_comap.2 (bcInv_tmul_mem I u hv)
  have hstep : LinearMap.baseChange L (coinvMapAux (k := k) (H := H)) z
      ∈ (rightTensor I).baseChange L := by
    rw [← bcInv_comul_sub]
    exact hmap hz'
  -- and read it off as a kernel
  have hker : Submodule.restrictScalars k ((rightTensor I).baseChange L)
      = LinearMap.ker (LinearMap.lTensor L (rightTensor I).mkQ) := by
    rw [ker_lTensor, Submodule.ker_mkQ, restrictScalars_baseChange]
  have hz0 : LinearMap.lTensor L ((rightTensor I).mkQ ∘ₗ
      (coinvMapAux (k := k) (H := H))) z = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    have : LinearMap.lTensor L (coinvMapAux (k := k) (H := H)) z
        = LinearMap.baseChange L (coinvMapAux (k := k) (H := H)) z := by
      rw [LinearMap.baseChange_eq_lTensor]
    rw [this]
    have : LinearMap.baseChange L (coinvMapAux (k := k) (H := H)) z
        ∈ Submodule.restrictScalars k ((rightTensor I).baseChange L) := hstep
    rw [hker] at this
    exact this
  have hfin : z ∈ tens (⊤ : Submodule k L) (coinv I) := by
    have h := ker_lTensor (M := L) ((rightTensor I).mkQ ∘ₗ (coinvMapAux (k := k) (H := H)))
    have hz1 : z ∈ LinearMap.ker (LinearMap.lTensor L
        ((rightTensor I).mkQ ∘ₗ (coinvMapAux (k := k) (H := H)))) := hz0
    rw [h] at hz1
    have hkereq : LinearMap.ker ((rightTensor I).mkQ ∘ₗ (coinvMapAux (k := k) (H := H)))
        = coinv I := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      rfl
    rwa [hkereq] at hz1
  rw [← Submodule.restrictScalars_mem k, restrictScalars_baseChange (L := L) (coinv I)]
  exact hfin

/-! ### `τ` and the bi-ideal conditions under base change -/

/-- The counit of `L ⊗ H` is the base change of the counit of `H`. -/
theorem counit_baseChange_apply (z : L ⊗[k] H) :
    counit (R := L) z
      = TensorProduct.rid k L (LinearMap.lTensor L (counit (R := k) (A := H)) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-- The kernel of the counit of `L ⊗ H`, viewed as a `k`-submodule, is `L ⊗ ker ε`
(`tens ⊤ (ker ε)`). -/
theorem ker_counit_baseChange :
    Submodule.restrictScalars k (LinearMap.ker (counit (R := L) (A := L ⊗[k] H)))
      = tens (⊤ : Submodule k L) (LinearMap.ker (counit (R := k) (A := H))) := by
  rw [← ker_lTensor]
  ext z
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, counit_baseChange_apply]
  constructor
  · intro h
    exact (TensorProduct.rid k L).injective (by simpa using h)
  · intro h
    rw [h, map_zero]

/-- `(L ⊗ W)⁺ ≤ L ⊗ W⁺`, where `⁺` is `augPart`. -/
theorem augPart_baseChange_le (W : Submodule k H) :
    augPart (W.baseChange L) ≤ (augPart W).baseChange L := by
  intro z hz
  have h1 : z ∈ tens (⊤ : Submodule k L) W := by
    rw [← restrictScalars_baseChange (L := L) W]; exact hz.1
  have h2 : z ∈ tens (⊤ : Submodule k L) (LinearMap.ker (counit (R := k) (A := H))) := by
    rw [← ker_counit_baseChange (L := L) (H := H)]; exact hz.2
  have h3 : z ∈ tens (⊤ : Submodule k L) (augPart W) := by
    rw [augPart, ← tens_inf_tens_right]
    exact ⟨h1, h2⟩
  rw [← Submodule.restrictScalars_mem k, restrictScalars_baseChange (L := L) (augPart W)]
  exact h3

/-- **`τ` under a scalar extension**: `τ (L ⊗ W) ≤ L ⊗ τ W`. -/
theorem tau_baseChange_le (W : Submodule k H) :
    tau (W.baseChange L) ≤ (tau W).baseChange L := by
  refine tau_le fun u w hw => ?_
  have hw' : w ∈ tens (⊤ : Submodule k L) (augPart W) := by
    rw [← restrictScalars_baseChange (L := L) (augPart W)]
    exact augPart_baseChange_le W hw
  induction u using TensorProduct.inductionOn with
  | tmul a x =>
      have hQ : tens (⊤ : Submodule k L) (augPart W) ≤ Submodule.comap
          ((LinearMap.mulLeft L ((a : L) ⊗ₜ[k] x)).restrictScalars k)
          (Submodule.restrictScalars k ((tau W).baseChange L)) := by
        refine tens_le_iff.2 fun b _ y hy => ?_
        simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply,
          LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
          Submodule.restrictScalars_mem]
        rw [← smul_one_tmul]
        exact Submodule.smul_mem _ _
          (Submodule.tmul_mem_baseChange_of_mem _ (mul_mem_tau x hy))
      exact hQ hw'
  | add u₁ u₂ h₁ h₂ =>
      rw [add_mul]
      exact Submodule.add_mem _ h₁ h₂

/-- The comparison map carries `I ⊗ H + H ⊗ I` into `(L ⊗ I) ⊗ (L ⊗ H) + (L ⊗ H) ⊗ (L ⊗ I)`. -/
theorem bcRel_mem_sup (I : Submodule k H) {t : H ⊗[k] H}
    (ht : t ∈ leftTensor I ⊔ rightTensor I) :
    bcRel (L := L) t ∈ leftTensor (I.baseChange L) ⊔ rightTensor (I.baseChange L) := by
  have hle : leftTensor I ⊔ rightTensor I ≤ Submodule.comap (bcRel (L := L))
      (Submodule.restrictScalars k
        (leftTensor (I.baseChange L) ⊔ rightTensor (I.baseChange L))) := by
    refine sup_le (leftTensor_le fun y hy h => ?_) (rightTensor_le fun h y hy => ?_)
    · refine Submodule.mem_comap.2 ?_
      rw [bcRel_tmul]
      exact Submodule.mem_sup_left
        (tmul_mem_leftTensor (Submodule.tmul_mem_baseChange_of_mem _ hy) _)
    · refine Submodule.mem_comap.2 ?_
      rw [bcRel_tmul]
      exact Submodule.mem_sup_right
        (tmul_mem_rightTensor _ (Submodule.tmul_mem_baseChange_of_mem _ hy))
  exact hle ht

/-- **The base change of a left bi-ideal is a left bi-ideal.** -/
theorem isLeftBiIdeal_baseChange {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    IsLeftBiIdeal (I.baseChange L) where
  -- Over `k`, `I_L` is spanned by the `b ⊗ y` with `b : L` and `y ∈ I`
  -- (`restrictScalars_baseChange`); each condition is checked on these generators.
  mul_mem := by
    intro u z hz
    have hz' : z ∈ tens (⊤ : Submodule k L) I := by
      rw [← restrictScalars_baseChange (L := L) I]; exact hz
    induction u using TensorProduct.inductionOn with
    | tmul a x =>
        have hQ : tens (⊤ : Submodule k L) I ≤ Submodule.comap
            ((LinearMap.mulLeft L ((a : L) ⊗ₜ[k] x)).restrictScalars k)
            (Submodule.restrictScalars k (I.baseChange L)) := by
          refine tens_le_iff.2 fun b _ y hy => ?_
          simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply,
            LinearMap.mulLeft_apply, Algebra.TensorProduct.tmul_mul_tmul,
            Submodule.restrictScalars_mem]
          rw [← smul_one_tmul]
          exact Submodule.smul_mem _ _
            (Submodule.tmul_mem_baseChange_of_mem _ (hI.mul_mem x y hy))
        exact hQ hz'
    | add u₁ u₂ h₁ h₂ =>
        rw [add_mul]
        exact Submodule.add_mem _ h₁ h₂
  counit_eq_zero := by
    intro z hz
    have hz' : z ∈ tens (⊤ : Submodule k L) I := by
      rw [← restrictScalars_baseChange (L := L) I]; exact hz
    have hle : tens (⊤ : Submodule k L) I
        ≤ tens (⊤ : Submodule k L) (LinearMap.ker (counit (R := k) (A := H))) :=
      tens_mono le_rfl (fun y hy => hI.counit_eq_zero y hy)
    -- the counit of `L ⊗ H` kills `(ker ε)_L`
    refine LinearMap.mem_ker.mp ((Submodule.restrictScalars_mem k _ _).mp ?_)
    rw [ker_counit_baseChange (L := L) (H := H)]
    exact hle hz'
  comul_mem := by
    intro z hz
    have hz' : z ∈ tens (⊤ : Submodule k L) I := by
      rw [← restrictScalars_baseChange (L := L) I]; exact hz
    have hQ : tens (⊤ : Submodule k L) I ≤ Submodule.comap
        ((comul (R := L) (A := L ⊗[k] H)).restrictScalars k)
        (Submodule.restrictScalars k
          (leftTensor (I.baseChange L) ⊔ rightTensor (I.baseChange L))) := by
      refine tens_le_iff.2 fun b _ y hy => ?_
      have hsm : (b : L) ⊗ₜ[k] y = b • ((1 : L) ⊗ₜ[k] y) := (smul_one_tmul b y).symm
      simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply,
        Submodule.restrictScalars_mem]
      rw [hsm, map_smul]
      refine Submodule.smul_mem _ _ ?_
      rw [comul_one_tmul]
      exact bcRel_mem_sup I (hI.comul_mem y hy)
    exact hQ hz'

/-! ### The reduction -/

/-- **Newman's second closure identity descends along a field extension.**  If `τ (μ J) = J` for
every left bi-ideal `J` of `L ⊗ H`, then `τ (μ I) = I` for every left bi-ideal `I` of `H`. -/
theorem tau_coinv_eq_of_baseChange' {I : Submodule k H} (hI : IsLeftBiIdeal I)
    (hL : ∀ J : Submodule L (L ⊗[k] H), IsLeftBiIdeal J → tau (coinv J) = J) :
    tau (coinv I) = I := by
  refine le_antisymm (tau_coinv_le hI.mul_mem) fun x hx => ?_
  have hx' : (1 : L) ⊗ₜ[k] x ∈ I.baseChange L := Submodule.tmul_mem_baseChange_of_mem _ hx
  -- `I_L = τ (μ I_L) ≤ τ ((μ I)_L) ≤ (τ (μ I))_L`
  have hle : I.baseChange L ≤ (tau (coinv I)).baseChange L :=
    ((hL _ (isLeftBiIdeal_baseChange hI)).ge.trans (tau_mono (coinv_baseChange_le I))).trans
      (tau_baseChange_le (L := L) (coinv I))
  exact mem_of_one_tmul_mem_baseChange (L := L) _ (hle hx')

end BaseChange

end HopfAlgebra.Cocommutative
