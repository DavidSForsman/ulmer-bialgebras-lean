module

public import Hopf.Graded.FreeBasisAssembly
public import Hopf.Basic.AntipodeBialgHom
public import Hopf.Cocommutative.DescentSubgroupComponent
public import Hopf.Coradical.Transfer
public import Hopf.Coradical.PointedComponents
public import Hopf.Cocommutative.SubHopfStructure
public import Hopf.Cocommutative.DescentAlgClosure

/-!
# Right-linear retractions from Sweedler bases

Use graded Sweedler bases to construct stable complements and right-linear retractions
for sub-Hopf algebras of the irreducible component. These constructions supply the
retraction input used by the three-layer correspondence in `Newman/Correspondence/`.

## Main results

* `HopfAlgebra.Cocommutative.exists_leftCompl_of_hasGradedFreeBasis`: if `A ⊆ H₁` has a Sweedler
  basis, then `A` has a complement in `H₁` stable under left multiplication by `A`.
* `HopfAlgebra.Cocommutative.exists_rightCompl_of_leftCompl`: for `A` stable under the antipode, a
  left `A`-stable complement of `A` in `H₁` gives a right `A`-stable one.
* `HopfAlgebra.Cocommutative.exists_rightRetraction_of_rightCompl`: for pointed cocommutative `H`, a
  right `A`-stable complement of `A` in `H₁` gives a `k`-linear `pA : H → H` with values in `A`, the
  identity on `A`, with `pA (x * u) = pA x * u` for `u ∈ A`.
* `HopfAlgebra.Cocommutative.hasGradedFreeBasis_irrPart`: for a sub-Hopf algebra `K` of a
  cocommutative `H`, `K ∩ H₁` has a Sweedler basis.

## References

* [M. E. Sweedler, *Hopf algebras with one grouplike element*][sweedlerHopfAlgebrasOne1967]
* [D. E. Radford, *Pointed Hopf algebras are free over Hopf
  subalgebras*][radfordPointedHopfAlgebras1977]
* [M. Takeuchi, *A correspondence between Hopf ideals and sub-Hopf algebras*][Takeuchi1972]
* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975]
-/

@[expose] public section

open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra
open Module.FilteredFree HopfAlgebra.Commutative.Cocomm
open HopfAlgebra.Commutative.Cocomm

universe u

namespace HopfAlgebra.Cocommutative

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### From a basis to a complement -/

section Basis

variable {ι : Type u}

/-- An element of a supremum of translates `A · b j`, `j ≠ j₀`, is a finite `A`-combination of
the `b j` with vanishing `j₀`-coefficient. -/
theorem exists_finsupp_of_mem_biSup (A : Subalgebra k H) (b : ι → H) (j₀ : ι) {x : H}
    (hx : x ∈ ⨆ (j : ι) (_ : j ≠ j₀),
      Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A)) :
    ∃ a : ι →₀ H, (∀ j, a j ∈ A) ∧ a j₀ = 0 ∧ x = a.sum (fun j c => c * b j) := by
  classical
  rw [iSup_subtype'] at hx
  refine Submodule.iSup_induction (motive := fun y => ∃ a : ι →₀ H, (∀ j, a j ∈ A) ∧ a j₀ = 0 ∧
      y = a.sum (fun j c => c * b j)) _ hx ?_
    ⟨0, fun j => by simp, rfl, by simp⟩ ?_
  · rintro ⟨j, hj⟩ y ⟨c, hc, rfl⟩
    refine ⟨Finsupp.single j c, fun i => ?_, ?_, ?_⟩
    · rcases eq_or_ne i j with rfl | hij
      · simpa using hc
      · simp [hij]
    · simp [Ne.symm hj]
    · rw [Finsupp.sum_single_index (by simp)]
      simp
  · rintro y z ⟨a, ha, ha0, hy⟩ ⟨a', ha', ha'0, hz⟩
    refine ⟨a + a', fun j => by simpa using Subalgebra.add_mem _ (ha j) (ha' j),
      by simp [ha0, ha'0], ?_⟩
    rw [Finsupp.sum_add_index' (by simp) (by intro j c d; simp [add_mul]), ← hy, ← hz]

/-- **From a basis to a complement.**  If `M` is free as a left `A`-module on `b : ι → H` and the
translate `A · b j₀` is `A` itself, then the sum of the remaining translates is a left `A`-stable
complement of `A` in `M`. -/
theorem exists_leftCompl_of_basis (A : Subalgebra k H) (M : Submodule k H) (b : ι → H) (j₀ : ι)
    (hbj₀ : Submodule.map (LinearMap.mulRight k (b j₀)) (Subalgebra.toSubmodule A)
      = Subalgebra.toSubmodule A)
    (hspan : M = ⨆ j : ι, Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A))
    (hind : ∀ (s : Finset ι) (a : ι → H), (∀ j ∈ s, a j ∈ A) →
      ∑ j ∈ s, a j * b j = 0 → ∀ j ∈ s, a j = 0) :
    ∃ N : Submodule k H, N ≤ M ∧ Subalgebra.toSubmodule A ⊔ N = M ∧
      Disjoint (Subalgebra.toSubmodule A) N ∧ (∀ u ∈ A, ∀ x ∈ N, u * x ∈ N) := by
  classical
  -- `N` is spanned by the translates `A b_j`, `j ≠ j₀`: `A ⊔ N = M` by `hspan`, the sum is
  -- direct by the independence `hind`, and `N` is stable under left multiplication by `A`.
  set N : Submodule k H := ⨆ (j : ι) (_ : j ≠ j₀),
    Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A) with hN
  have hsplit : M = Subalgebra.toSubmodule A ⊔ N := by
    rw [hspan, hN, iSup_split_single _ j₀, hbj₀]
  refine ⟨N, ?_, hsplit.symm, ?_, ?_⟩
  · rw [hsplit]; exact le_sup_right
  · rw [Submodule.disjoint_def]
    intro x hxA hxN
    obtain ⟨a, ha, ha0, hxa⟩ := exists_finsupp_of_mem_biSup A b j₀ hxN
    obtain ⟨c, hc, hcx⟩ : ∃ c ∈ Subalgebra.toSubmodule A, c * b j₀ = x := by
      rw [← hbj₀] at hxA
      obtain ⟨c, hc, hcx⟩ := hxA
      exact ⟨c, hc, hcx⟩
    have hj₀ : j₀ ∉ a.support := by simp [Finsupp.mem_support_iff, ha0]
    set a' : ι → H := fun j => if j = j₀ then -c else a j with ha'
    have hsum : ∑ j ∈ insert j₀ a.support, a' j * b j = 0 := by
      rw [Finset.sum_insert hj₀]
      have h1 : ∀ j ∈ a.support, a' j * b j = a j * b j := by
        intro j hj
        have : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
        simp [ha', this]
      rw [Finsupp.sum] at hxa
      rw [Finset.sum_congr rfl h1, ← hxa]
      simp only [ha', ite_eq_left rfl, neg_mul, hcx, neg_add_cancel]
    have := hind (insert j₀ a.support) a' ?_ hsum j₀ (Finset.mem_insert_self _ _)
    · have hnc : (-c : H) = 0 := by simpa [ha'] using this
      have hc0 : c = 0 := neg_eq_zero.mp hnc
      rw [← hcx, hc0, zero_mul]
    · intro j hj
      rcases eq_or_ne j j₀ with rfl | hjne
      · simpa [ha'] using Subalgebra.neg_mem _ hc
      · rw [ha']
        simp only [hjne, ite_false]
        exact ha j
  · intro u hu x hx
    have hle : N ≤ Submodule.comap (LinearMap.mulLeft k u) N := by
      conv_lhs => rw [hN]
      refine iSup_le fun j => iSup_le fun hj => ?_
      rintro _ ⟨c, hc, rfl⟩
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
      rw [← mul_assoc, hN]
      exact le_iSup₂ (f := fun (j : ι) (_ : j ≠ j₀) =>
        Submodule.map (LinearMap.mulRight k (b j)) (Subalgebra.toSubmodule A)) j hj
        ⟨u * c, Subalgebra.mul_mem _ hu hc, rfl⟩
    exact hle hx

end Basis

/-! ### The complement coming from a Sweedler basis -/

section GradedFreeBasis

variable [Coalgebra.IsCocomm k H]

omit [Coalgebra.IsCocomm k H] in
/-- **A Sweedler basis gives a left `A`-stable complement of `A` in `H₁`.**  The basis vector of
degree `0` is a nonzero multiple of `1`, so its translate is `A` itself. -/
theorem exists_leftCompl_of_hasGradedFreeBasis [Nontrivial H] {A : Subalgebra k H}
    (hA : Subalgebra.toSubmodule A ≤ glComponent (1 : GroupLike k H))
    (hsw : HasGradedFreeBasis A) :
    ∃ N : Submodule k H,
      Subalgebra.toSubmodule A ⊔ N = glComponent (1 : GroupLike k H) ∧
      Disjoint (Subalgebra.toSubmodule A) N ∧ (∀ u ∈ A, ∀ x ∈ N, u * x ∈ N) := by
  classical
  obtain ⟨ι, b, d, hbF, hspan, h0, hstep⟩ := hsw
  obtain ⟨hbM, hMspan, hind⟩ :=
    leftBasis_of_graded (F := oneFiltration k H) oneFiltration_monotone iSup_oneFiltration hA hbF
      (fun x hx y hy => mul_glComponent_one_le (Submodule.mul_mem_mul (hA hx) hy)) hspan h0 hstep
  -- the zeroth filtration step is the line spanned by `1`
  have hF0 : oneFiltration k H 0 = Submodule.span k {(1 : H)} := by
    simp [oneFiltration, GroupLike.val_one]
  have hone : (1 : H) ∈ oneFiltration k H 0 := by
    rw [hF0]; exact Submodule.subset_span rfl
  -- some basis vector of degree zero survives
  have hex : ∃ j₀ : ι,
      Submodule.map (LinearMap.mulRight k (b j₀)) (coefSub A (oneFiltration k H) d 0 j₀) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have : (1 : H) ∈ (⊥ : Submodule k H) := by
      refine (iSup_le fun j => le_of_eq (hcon j)) (hspan 0 hone)
    simp at this
  obtain ⟨j₀, hj₀⟩ := hex
  have hd0 : d j₀ = 0 := by
    by_contra hne
    apply hj₀
    have hne' : ¬ (d j₀ ≤ 0) := by omega
    rw [coefSub, ite_eq_right hne']
    simp
  have hcoef : coefSub A (oneFiltration k H) d 0 j₀ = oneFiltration k H 0 := by
    rw [coefSub, ite_eq_left (le_of_eq hd0), hd0, Nat.sub_zero]
    refine inf_eq_right.2 ?_
    rw [hF0, Submodule.span_le]
    rintro _ rfl
    exact A.one_mem
  have hbmem : b j₀ ∈ Submodule.span k {(1 : H)} := by
    rw [← hF0, ← hd0]; exact hbF j₀
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.1 hbmem
  have hμne : μ ≠ 0 := by
    rintro rfl
    apply hj₀
    rw [hcoef, hF0, eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    simp only [LinearMap.mulRight_apply]
    rw [← hμ]
    simp
  have hbj₀ : Submodule.map (LinearMap.mulRight k (b j₀)) (Subalgebra.toSubmodule A)
      = Subalgebra.toSubmodule A := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simp only [LinearMap.mulRight_apply, ← hμ]
      rw [mul_smul_comm, mul_one]
      exact Submodule.smul_mem _ _ hx
    · intro x hx
      refine ⟨μ⁻¹ • x, Submodule.smul_mem _ _ hx, ?_⟩
      simp only [LinearMap.mulRight_apply, ← hμ]
      rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul, inv_mul_cancel₀ hμne, one_smul]
  obtain ⟨N, _, hsup, hdisj, hstable⟩ :=
    exists_leftCompl_of_basis A (glComponent (1 : GroupLike k H)) b j₀ hbj₀ hMspan hind
  exact ⟨N, hsup, hdisj, hstable⟩

/-- **The mirror image of a left complement under the antipode is a right complement.** -/
theorem exists_rightCompl_of_leftCompl {A : Subalgebra k H}
    (hAanti : ∀ a ∈ A, antipode k a ∈ A) {N : Submodule k H}
    (hsup : Subalgebra.toSubmodule A ⊔ N = glComponent (1 : GroupLike k H))
    (hdisj : Disjoint (Subalgebra.toSubmodule A) N)
    (hstable : ∀ u ∈ A, ∀ x ∈ N, u * x ∈ N) :
    ∃ N' : Submodule k H,
      Subalgebra.toSubmodule A ⊔ N' = glComponent (1 : GroupLike k H) ∧
      Disjoint (Subalgebra.toSubmodule A) N' ∧ (∀ u ∈ A, ∀ x ∈ N', x * u ∈ N') := by
  classical
  -- The antipode `S` is an involutive anti-automorphism fixing `A` and `H₁`: it turns the left
  -- `A`-stable complement `N` into the right `A`-stable complement `S N`.
  set S : H →ₗ[k] H := antipode k with hS
  have hSS : ∀ x : H, S (S x) = x := fun x => antipode_antipode x
  have hmapA : Submodule.map S (Subalgebra.toSubmodule A) = Subalgebra.toSubmodule A := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩; exact hAanti x hx
    · intro x hx
      exact ⟨S x, hAanti x hx, hSS x⟩
  have hmapH₁ : Submodule.map S (glComponent (1 : GroupLike k H))
      = glComponent (1 : GroupLike k H) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      have := Coalgebra.Coradical.map_antipode_glComponent (k := k) (1 : GroupLike k H) hx
      simpa using this
    · intro x hx
      refine ⟨S x, ?_, hSS x⟩
      have := Coalgebra.Coradical.map_antipode_glComponent (k := k) (1 : GroupLike k H)
        ⟨x, hx, rfl⟩
      simpa using this
  refine ⟨Submodule.map S N, ?_, ?_, ?_⟩
  · rw [← hmapA, ← Submodule.map_sup, hsup, hmapH₁]
  · rw [Submodule.disjoint_def]
    rintro x hxA ⟨y, hy, rfl⟩
    have hSy : S y ∈ Subalgebra.toSubmodule A := hxA
    have hyA : y ∈ Subalgebra.toSubmodule A := by
      have := hAanti _ hSy
      rwa [hSS] at this
    have : y = 0 := (Submodule.disjoint_def.1 hdisj) y hyA hy
    rw [this]
    simp
  · rintro u hu x ⟨y, hy, rfl⟩
    refine ⟨antipode k u * y, hstable _ (hAanti u hu) y hy, ?_⟩
    change antipode k (antipode k u * y) = antipode k y * u
    rw [antipode_mul, hSS]

end GradedFreeBasis

/-! ### The retraction on all of `H` -/

section Retraction

variable [Coalgebra.IsCocomm k H]

/-- Completing a complement `N` of `A` inside `glComponent 1` by the remaining Kostant
components yields a complement of `A` in `H`. -/
private lemma isCompl_subalgebra_sup_glComponent (hpt : IsPointed k H) {A : Subalgebra k H}
    {N : Submodule k H}
    (hsup : Subalgebra.toSubmodule A ⊔ N = glComponent (1 : GroupLike k H))
    (hdisj : Disjoint (Subalgebra.toSubmodule A) N) :
    IsCompl (Subalgebra.toSubmodule A)
      (N ⊔ ⨆ (g : GroupLike k H) (_ : g ≠ 1), glComponent g) := by
  have hAle : Subalgebra.toSubmodule A ≤ glComponent (1 : GroupLike k H) :=
    hsup ▸ le_sup_left
  have hNle : N ≤ glComponent (1 : GroupLike k H) :=
    hsup ▸ le_sup_right
  have hdisjW : Disjoint (glComponent (1 : GroupLike k H))
      (⨆ (g : GroupLike k H) (_ : g ≠ 1), glComponent g) :=
    iSupIndep_glComponent (k := k) (H := H) 1
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxA hxC
    obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.1 hxC
    have hwH₁ : w ∈ glComponent (1 : GroupLike k H) := by
      have h1 : (n + w) - n = w := add_sub_cancel_left n w
      rw [← h1]
      exact Submodule.sub_mem _ (hAle hxA) (hNle hn)
    have hw0 : w = 0 := (Submodule.disjoint_def.1 hdisjW) w hwH₁ hw
    rw [hw0, add_zero] at hxA ⊢
    exact (Submodule.disjoint_def.1 hdisj) n hxA hn
  · rw [codisjoint_iff, ← sup_assoc, hsup, eq_top_iff, ← iSup_glComponent_eq_top hpt]
    refine iSup_le fun g => ?_
    rcases eq_or_ne g 1 with rfl | hg
    · exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (g : GroupLike k H) (_ : g ≠ 1) =>
        glComponent g) g hg)

/-- **The right `A`-linear retraction `H ↠ A`.**  Given a right `A`-stable complement of `A`
inside the irreducible component `H₁` of the unit of a pointed cocommutative Hopf algebra, the
remaining Kostant components complete it to a right `A`-stable complement of `A` in `H`. -/
theorem exists_rightRetraction_of_rightCompl (hpt : IsPointed k H) {A : Subalgebra k H}
    {N : Submodule k H}
    (hsup : Subalgebra.toSubmodule A ⊔ N = glComponent (1 : GroupLike k H))
    (hdisj : Disjoint (Subalgebra.toSubmodule A) N)
    (hstable : ∀ u ∈ A, ∀ x ∈ N, x * u ∈ N) :
    ∃ pA : H →ₗ[k] H, (∀ x : H, pA x ∈ A) ∧ (∀ a ∈ A, pA a = a) ∧
      (∀ (x : H), ∀ u ∈ A, pA (x * u) = pA x * u) := by
  classical
  -- `C = N ⊔ ⨆_{g ≠ 1} H_g` is a right `A`-stable complement of `A` in `H`; the retraction is
  -- the projection onto `A` along `C`.
  set W : Submodule k H := ⨆ (g : GroupLike k H) (_ : g ≠ 1), glComponent g with hW
  set C : Submodule k H := N ⊔ W with hC
  have hAle : Subalgebra.toSubmodule A ≤ glComponent (1 : GroupLike k H) :=
    hsup ▸ le_sup_left
  have hcompl : IsCompl (Subalgebra.toSubmodule A) C :=
    isCompl_subalgebra_sup_glComponent hpt hsup hdisj
  have hCstable : ∀ u ∈ A, ∀ x ∈ C, x * u ∈ C := by
    intro u hu x hx
    obtain ⟨n, hn, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
    rw [add_mul]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hstable u hu n hn)) ?_
    refine Submodule.mem_sup_right ?_
    have hWstable : W ≤ Submodule.comap (LinearMap.mulRight k u) W := by
      conv_lhs => rw [hW]
      refine iSup_le fun g => iSup_le fun hg => fun y hy => ?_
      simp only [Submodule.mem_comap, LinearMap.mulRight_apply]
      have : y * u ∈ glComponent (g * 1) :=
        mul_glComponent_le g 1 (Submodule.mul_mem_mul hy (hAle hu))
      rw [mul_one] at this
      rw [hW]
      exact le_iSup₂ (f := fun (g : GroupLike k H) (_ : g ≠ 1) => glComponent g) g hg this
    exact hWstable hw
  refine ⟨(Subalgebra.toSubmodule A).subtype ∘ₗ
    (Subalgebra.toSubmodule A).projectionOnto C hcompl, fun x => ?_, fun a ha => ?_,
    fun x u hu => ?_⟩
  · exact ((Subalgebra.toSubmodule A).projectionOnto C hcompl x).2
  · exact congrArg Subtype.val
      ((Subalgebra.toSubmodule A).projectionOnto_apply_left hcompl ⟨a, ha⟩)
  · have hpC : ∀ v ∈ C, ((Subalgebra.toSubmodule A).subtype ∘ₗ
        (Subalgebra.toSubmodule A).projectionOnto C hcompl) v = 0 := fun v hv => by
      rw [LinearMap.comp_apply,
        (Subalgebra.toSubmodule A).projectionOnto_apply_right hcompl ⟨v, hv⟩]
      rfl
    have hpid : ∀ a ∈ Subalgebra.toSubmodule A, ((Subalgebra.toSubmodule A).subtype ∘ₗ
        (Subalgebra.toSubmodule A).projectionOnto C hcompl) a = a := fun a ha =>
      congrArg Subtype.val
        ((Subalgebra.toSubmodule A).projectionOnto_apply_left hcompl ⟨a, ha⟩)
    obtain ⟨y, hy, v, hv, rfl⟩ :=
      Submodule.mem_sup.1 (hcompl.sup_eq_top ▸ Submodule.mem_top (x := x))
    rw [add_mul, map_add, map_add, hpid y hy, hpC v hv, add_zero,
      hpid (y * u) (Subalgebra.mul_mem _ hy hu), hpC (v * u) (hCstable u hu v hv), add_zero]

end Retraction

/-! ### Descent, unconditionally -/

section Main

variable [Coalgebra.IsCocomm k H]

/-- The intersection `K ∩ H₁` of a sub-Hopf algebra with the irreducible component of the unit is
stable under the antipode. -/
theorem antipode_mem_irrPart {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) {a : H}
    (ha : a ∈ irrPart k H K) : antipode k a ∈ irrPart k H K := by
  refine ⟨hK.antipode_mem a ha.1, ?_⟩
  simpa using
    Coalgebra.Coradical.map_antipode_glComponent (k := k) (1 : GroupLike k H) ⟨a, ha.2, rfl⟩

/-- **Sweedler's freeness theorem, applied to `K ∩ H₁`** (Sweedler [sweedlerHopfAlgebrasOne1967]).
-/
theorem hasGradedFreeBasis_irrPart {K : Subalgebra k H} (hK : IsSubHopfAlgebra k K) :
    HasGradedFreeBasis (irrPart k H K) := by
  refine HopfAlgebra.Graded.hasGradedFreeBasis_of_subHopfAlgebra _ ?_
    (fun a ha => antipode_mem_irrPart hK ha)
  have h1 : UlmerBialgebras.Subcoalg.IsSubcoalgebra (Subalgebra.toSubmodule K) :=
    fun x hx => hK.comul_mem x hx
  have h2 := Coalgebra.Coradical.isSubcoalgebra_glComponent (k := k) (1 : GroupLike k H)
  exact Coalgebra.Coradical.isSubcoalgebra_inf h1 h2

end Main

end HopfAlgebra.Cocommutative
