module

public import Hopf.Cocommutative.HopfBiIdeal
public import Hopf.Coradical.WedgeComul
public import Hopf.Graded.FreeBasis

/-!
# Reducing Newman's second closure identity to a statement about primitives

Newman's correspondence has two closure identities, `μ (τ K) = K` and `τ (μ I) = I`; both are proved
for cocommutative Hopf algebras over a field in `Hopf/Cocommutative/Correspondence/Main.lean`
(`HopfAlgebra.Cocommutative.Correspondence.coinv_tau_eq`,
`HopfAlgebra.Cocommutative.Correspondence.tau_coinv_eq`).

This file carries out the first (and completely general) step of Newman's proof of the second
identity: for an *irreducible* Hopf algebra it is enough to treat the elements of `I` which are
**primitive modulo** `τ (μ I)`.  In coalgebra language: a nonzero coideal of a pointed
irreducible coalgebra contains a nonzero primitive, so a surjection of pointed irreducible
coalgebras which is injective on primitives is injective.

## Main results

* `Coalgebra.Coradical.sup_tens_inf_tens_le` — the linear algebra behind the reduction:
  `(A ⊗ M + M ⊗ A) ∩ (D ⊗ D) = (A ∩ D) ⊗ D + D ⊗ (A ∩ D)` over a field;
* `HopfAlgebra.Cocommutative.comul_sub_mem_tens_oneFiltration` — for `x` in the `(n+1)`-st step of
  the coradical filtration of the irreducible component of the unit,
  `Δ x - x ⊗ 1 - 1 ⊗ x ∈ Fₙ ⊗ Fₙ`;
* `HopfAlgebra.Cocommutative.inf_glComponent_le_of_primitive_mem` — **the reduction**, in relative
  form: if every element of a left bi-ideal `I` which is primitive modulo a submodule `N ≤ I` lies
  in `N`, then every element of `I` in the irreducible component of `1` lies in `N`.

## References

* [R. G. Heyneman, D. E. Radford, *Reflexivity and coalgebras of finite
  type*][heynemanRadfordReflexivity1974]
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.3
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra

universe u

namespace Coalgebra.Coradical

/-! ### Linear algebra: intersecting `A ⊗ M + M ⊗ A` with `D ⊗ D` -/

section LinearAlgebra

variable {k M : Type u} [Field k] [AddCommGroup M] [Module k M]

/-- In a modular lattice with `⊥`: if `S ≤ K` and `K ⊓ T = ⊥`, then `K ⊓ (S ⊔ T) = S`. -/
theorem inf_sup_eq_of_disjoint {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α]
    {K S T : α} (hSK : S ≤ K) (hKT : K ⊓ T = ⊥) : K ⊓ (S ⊔ T) = S := by
  calc K ⊓ (S ⊔ T) = (S ⊔ T) ⊓ K := inf_comm _ _
    _ = S ⊔ (T ⊓ K) := by rw [sup_inf_assoc_of_le _ hSK]
    _ = S := by rw [inf_comm, hKT, sup_bot_eq]

/-- `tens` distributes over `⊔` in its first argument: `(X + Y) ⊗ Z = X ⊗ Z + Y ⊗ Z`. -/
theorem tens_sup_left (X Y Z : Submodule k M) :
    tens (X ⊔ Y) Z = tens X Z ⊔ tens Y Z := by
  simp [tens, Submodule.map₂_sup_left]

/-- `tens` distributes over `⊔` in its second argument: `X ⊗ (Y + Z) = X ⊗ Y + X ⊗ Z`. -/
theorem tens_sup_right (X Y Z : Submodule k M) :
    tens X (Y ⊔ Z) = tens X Y ⊔ tens X Z := by
  simp [tens, Submodule.map₂_sup_right]

/-- A complement of `A ⊓ D` inside `D`. -/
theorem exists_compl_inf (A D : Submodule k M) :
    ∃ E : Submodule k M, E ≤ D ∧ (A ⊓ D) ⊔ E = D ∧ Disjoint A E := by
  classical
  obtain ⟨E₀, hE₀⟩ := (Submodule.comap D.subtype A).exists_isCompl
  refine ⟨E₀.map D.subtype, by simpa using Submodule.map_subtype_le _ _, ?_, ?_⟩
  · have h := congrArg (Submodule.map D.subtype) hE₀.sup_eq_top
    rw [Submodule.map_sup, Submodule.map_top, Submodule.range_subtype,
      Submodule.map_comap_subtype, inf_comm] at h
    exact h
  · rw [Submodule.disjoint_def]
    rintro x hxA ⟨y, hy, rfl⟩
    have hmem : y ∈ Submodule.comap D.subtype A := hxA
    have h0 : y = 0 := (Submodule.disjoint_def.1 hE₀.disjoint) y hmem hy
    simp [h0]

/-- If `A` and `E` are disjoint then `E ⊗ E` meets `A ⊗ M + M ⊗ A` trivially. -/
theorem disjoint_ker_tens {A E : Submodule k M} (hdisj : Disjoint A E) :
    (tens A (⊤ : Submodule k M) ⊔ tens (⊤ : Submodule k M) A) ⊓ tens E E = ⊥ := by
  rw [← ker_map_mkQ A A, eq_bot_iff]
  rintro t ⟨htK, htE⟩
  have htE' : t ∈ tens E E := htE
  rw [mem_tens_iff_mem_range] at htE'
  obtain ⟨s, rfl⟩ := htE'
  have hinj : Function.Injective (A.mkQ ∘ₗ E.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, eq_bot_iff]
    rintro ⟨y, hy⟩ hmem
    have hyA : y ∈ A := hmem
    have hy0 : y = 0 := (Submodule.disjoint_def.1 hdisj) y hyA hy
    simpa [Submodule.mem_bot, Subtype.ext_iff] using hy0
  rw [SetLike.mem_coe, LinearMap.mem_ker, ← LinearMap.comp_apply, ← TensorProduct.map_comp] at htK
  have hs0 : s = 0 := map_injective_of_flat_flat' _ _ hinj hinj (by simpa using htK)
  simp [hs0]

/-- If `E ≤ D` and `P ⊔ E = D`, then `D ⊗ D ≤ (P ⊗ D + D ⊗ P) + E ⊗ E`. -/
theorem tens_le_of_sup (P E D : Submodule k M) (hE : E ≤ D) (h : P ⊔ E = D) :
    tens D D ≤ (tens P D ⊔ tens D P) ⊔ tens E E := by
  have e1 : tens D D = tens P D ⊔ tens E D := by rw [← h, tens_sup_left]
  have e2 : tens E D = tens E P ⊔ tens E E := by rw [← h, tens_sup_right]
  rw [e1, e2]
  refine sup_le (le_sup_of_le_left le_sup_left) (sup_le ?_ le_sup_right)
  exact le_sup_of_le_left (le_sup_of_le_right (tens_mono hE le_rfl))

/-- **Over a field, `(A ⊗ M + M ⊗ A) ∩ (D ⊗ D) ≤ (A ∩ D) ⊗ D + D ⊗ (A ∩ D)`.**  (The reverse
inclusion is obvious.) -/
theorem sup_tens_inf_tens_le (A D : Submodule k M) :
    (tens A (⊤ : Submodule k M) ⊔ tens (⊤ : Submodule k M) A) ⊓ tens D D
      ≤ tens (A ⊓ D) D ⊔ tens D (A ⊓ D) := by
  classical
  obtain ⟨E, hED, hsup, hdisj⟩ := exists_compl_inf A D
  have hSK : tens (A ⊓ D) D ⊔ tens D (A ⊓ D)
      ≤ tens A (⊤ : Submodule k M) ⊔ tens (⊤ : Submodule k M) A :=
    sup_le (le_trans (tens_mono inf_le_left le_top) le_sup_left)
      (le_trans (tens_mono le_top inf_le_left) le_sup_right)
  have hDD := tens_le_of_sup (A ⊓ D) E D hED hsup
  have hkey := inf_sup_eq_of_disjoint hSK (disjoint_ker_tens (A := A) (E := E) hdisj)
  exact le_trans (inf_le_inf_left _ hDD) (le_of_eq hkey)

end LinearAlgebra

end Coalgebra.Coradical

namespace HopfAlgebra.Cocommutative

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### The augmentation projection on the tensor square -/

/-- `(π ⊗ id) (Δ x) = Δ x - 1 ⊗ x`, where `π = id - 1 ∘ ε`. -/
lemma rTensor_augProj_comul (x : H) :
    LinearMap.rTensor H (augProj k H) (comul (R := k) x) = comul (R := k) x - (1 : H) ⊗ₜ[k] x := by
  have h1 : LinearMap.rTensor H (augProj k H)
      = LinearMap.id - LinearMap.rTensor H ((LinearMap.toSpanSingleton k H 1) ∘ₗ
        (counit (R := k) (A := H))) := by
    rw [augProj]; ext a b; simp
  rw [h1]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_right_inj]
  rw [LinearMap.rTensor_comp, LinearMap.comp_apply,
    show LinearMap.rTensor H (counit (R := k) (A := H)) (comul (R := k) x) = (1 : k) ⊗ₜ[k] x from
      congr($(rTensor_counit_comp_comul (R := k) (A := H)) x)]
  simp

/-- `(π ⊗ π) (Δ x) = Δ x - x ⊗ 1 - 1 ⊗ x + ε x · (1 ⊗ 1)`. -/
lemma map_augProj_comul (x : H) :
    _root_.TensorProduct.map (augProj k H) (augProj k H) (comul (R := k) x)
      = comul (R := k) x - x ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] x
        + (counit (R := k) x) • ((1 : H) ⊗ₜ[k] (1 : H)) := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, lTensor_augProj_comul, map_sub,
    rTensor_augProj_comul]
  simp only [LinearMap.rTensor_tmul, augProj_apply]
  rw [sub_tmul]
  simp only [smul_tmul']
  abel

/-! ### The coradical filtration of the irreducible component of the unit -/

/-- The zeroth step of `oneFiltration k H` is the line `k · 1`. -/
lemma oneFiltration_zero : oneFiltration k H 0 = Submodule.span k {(1 : H)} := by
  simp [oneFiltration, GroupLike.val_one]

/-- `1` lies in every step of `oneFiltration k H`. -/
lemma one_mem_oneFiltration (n : ℕ) : (1 : H) ∈ oneFiltration k H n :=
  oneFiltration_monotone (Nat.zero_le n)
    (by rw [oneFiltration_zero]; exact Submodule.subset_span rfl)

/-- A submodule `X` containing `1` is stable under `augProj`. -/
lemma augProj_mem {X : Submodule k H} (h1 : (1 : H) ∈ X) {x : H} (hx : x ∈ X) :
    augProj k H x ∈ X := by
  rw [augProj_apply]
  exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ h1)

/-- `augProj` vanishes on the line `k · 1`. -/
lemma augProj_eq_zero_of_mem_span_one {x : H} (hx : x ∈ Submodule.span k {(1 : H)}) :
    augProj k H x = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
  simp [augProj_apply, Bialgebra.counit_one]

/-- **Elements of the `(n+1)`-st step of the coradical filtration are primitive modulo
`Fₙ ⊗ Fₙ`.** -/
theorem comul_sub_mem_tens_oneFiltration (n : ℕ) {x : H} (hx : x ∈ oneFiltration k H (n + 1)) :
    comul (R := k) x - x ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] x
      ∈ tens (oneFiltration k H n) (oneFiltration k H n) := by
  classical
  set F := oneFiltration k H with hF
  set T := tens (F n) (F n) with hT
  set Φ := map (augProj k H) (augProj k H) with hΦ
  have hone : ∀ m, (1 : H) ∈ F m := one_mem_oneFiltration
  have hkill : tens (F 0) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) (F 0)
      ≤ LinearMap.ker Φ := by
    refine sup_le (tens_le_iff.2 fun a ha b _ => ?_) (tens_le_iff.2 fun a _ b hb => ?_)
    · have h0 : augProj k H a = 0 :=
        augProj_eq_zero_of_mem_span_one (by rwa [← oneFiltration_zero])
      simp [hΦ, LinearMap.mem_ker, h0]
    · have h0 : augProj k H b = 0 :=
        augProj_eq_zero_of_mem_span_one (by rwa [← oneFiltration_zero])
      simp [hΦ, LinearMap.mem_ker, h0]
  have hpres : T ≤ Submodule.comap Φ T := by
    refine tens_le_iff.2 fun a ha b hb => ?_
    simp only [Submodule.mem_comap, hΦ, map_tmul]
    exact tmul_mem_tens (augProj_mem (hone n) ha) (augProj_mem (hone n) hb)
  have hX : UlmerBialgebras.Subcoalg.IsSubcoalgebra (Submodule.span k {(1 : H)}) := by
    have h := isSubcoalgebra_span_groupLike (1 : GroupLike k H).2
    simpa [GroupLike.val_one] using h
  have hΔ : comul (R := k) x ∈ ⨆ p ∈ Finset.range (n + 1 + 1), tens (F p) (F (n + 1 - p)) :=
    comul_wedgePow_le hX (n + 1) ⟨x, hx, rfl⟩
  have hbound : (⨆ p ∈ Finset.range (n + 1 + 1), tens (F p) (F (n + 1 - p)))
      ≤ (tens (F 0) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) (F 0)) ⊔ T := by
    refine iSup₂_le fun p hp => ?_
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hp
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · exact le_sup_of_le_left (le_sup_of_le_left (tens_mono le_rfl le_top))
    · rcases eq_or_lt_of_le hp with heq | hplt
      · have h0 : n + 1 - p = 0 := by omega
        rw [h0]
        exact le_sup_of_le_left (le_sup_of_le_right (tens_mono le_top le_rfl))
      · exact le_sup_of_le_right (tens_mono (oneFiltration_monotone (by omega))
          (oneFiltration_monotone (by omega)))
  set z : H ⊗[k] H := comul (R := k) x - x ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] x with hz
  have hzmem : z ∈ (tens (F 0) (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) (F 0)) ⊔ T := by
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (hbound hΔ) ?_) ?_
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_right (tmul_mem_tens Submodule.mem_top (hone 0)))
    · exact Submodule.mem_sup_left
        (Submodule.mem_sup_left (tmul_mem_tens (hone 0) Submodule.mem_top))
  have hΦz : Φ z = z + (counit (R := k) x) • ((1 : H) ⊗ₜ[k] (1 : H)) := by
    have h1 : Φ (x ⊗ₜ[k] (1 : H)) = 0 := by simp [hΦ, augProj_apply, Bialgebra.counit_one]
    have h2 : Φ ((1 : H) ⊗ₜ[k] x) = 0 := by simp [hΦ, augProj_apply, Bialgebra.counit_one]
    rw [hz, map_sub, map_sub, h1, h2, map_augProj_comul]
    abel
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.1 hzmem
  have hΦw : Φ w = 0 := hkill hw
  have hΦt : Φ t ∈ T := hpres ht
  have hΦzT : Φ z ∈ T := by rw [← hwt, map_add, hΦw, zero_add]; exact hΦt
  rw [hΦz] at hΦzT
  have hone11 : (counit (R := k) x) • ((1 : H) ⊗ₜ[k] (1 : H)) ∈ T :=
    Submodule.smul_mem _ _ (tmul_mem_tens (hone n) (hone n))
  simpa using Submodule.sub_mem _ hΦzT hone11

/-! ### The reduction -/

/-- **Newman's reduction to primitives, in relative form.**  Let `H` be a Hopf algebra over a
field, `I` a left bi-ideal and `N` a submodule.  If every element of `I` which is *primitive
modulo `N`* already lies in `N`, then every element of `I` lying in the irreducible component of
the unit lies in `N`.

The mechanism is the classical one: a nonzero coideal of a pointed irreducible coalgebra contains
a nonzero primitive.  Here it appears in the equivalent filtered form, an induction along the
coradical filtration of the irreducible component of `1`. -/
theorem inf_glComponent_le_of_primitive_mem
    {I N : Submodule k H} (hI : IsLeftBiIdeal I)
    (hprim : ∀ y ∈ I, y ∈ glComponent (1 : GroupLike k H) →
      comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y
      ∈ leftTensor N ⊔ rightTensor N → y ∈ N) :
    I ⊓ glComponent (1 : GroupLike k H) ≤ N := by
  classical
  have key : ∀ n : ℕ, I ⊓ oneFiltration k H n ≤ N := by
    intro n
    induction n with
    | zero =>
        rintro y ⟨hyI, hy0⟩
        rw [oneFiltration_zero] at hy0
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy0
        have hc : counit (R := k) (c • (1 : H)) = 0 := hI.counit_eq_zero _ hyI
        rw [map_smul] at hc
        simp only [Bialgebra.counit_one, smul_eq_mul, mul_one] at hc
        rw [hc, zero_smul]
        exact Submodule.zero_mem _
    | succ n IH =>
        rintro y ⟨hyI, hyF⟩
        refine hprim y hyI (oneFiltration_le_glComponent_one _ hyF) ?_
        have h1 : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y
            ∈ tens (oneFiltration k H n) (oneFiltration k H n) :=
          comul_sub_mem_tens_oneFiltration n hyF
        have h2 : comul (R := k) y - y ⊗ₜ[k] (1 : H) - (1 : H) ⊗ₜ[k] y
            ∈ tens I (⊤ : Submodule k H) ⊔ tens (⊤ : Submodule k H) I := by
          refine Submodule.sub_mem _ (Submodule.sub_mem _ (hI.comul_mem y hyI) ?_) ?_
          · exact Submodule.mem_sup_left (tmul_mem_tens hyI Submodule.mem_top)
          · exact Submodule.mem_sup_right (tmul_mem_tens Submodule.mem_top hyI)
        have h3 := sup_tens_inf_tens_le I (oneFiltration k H n) ⟨h2, h1⟩
        refine le_trans ?_ (le_refl (leftTensor N ⊔ rightTensor N)) h3
        exact sup_le (le_trans (tens_mono IH le_top) le_sup_left)
          (le_trans (tens_mono le_top IH) le_sup_right)
  rintro y ⟨hy, hy1⟩
  have h : y ∈ ⨆ n, oneFiltration k H n := by rw [iSup_oneFiltration]; exact hy1
  rw [Submodule.mem_iSup_of_directed _ (Monotone.directed_le oneFiltration_monotone)] at h
  obtain ⟨n, hn⟩ := h
  exact key n ⟨hy, hn⟩

end HopfAlgebra.Cocommutative
