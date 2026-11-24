module

public import Hopf.Cocommutative.PrimitiveReduction
public import Hopf.Cocommutative.BiIdealQuotient
public import Hopf.Coradical.PointedComponents
public import Hopf.Coradical.Transfer

/-!
# Kostant's reduction: from pointed to pointed irreducible

This file supplies one of the two links which were still missing in the proof of Newman's second
closure identity `τ (μ I) = I`: the reduction of the identity, for a **pointed** cocommutative
Hopf algebra, to its **irreducible** case (Newman's Corollary 3.3).

The mechanism is Kostant's decomposition `H = ⨁_{g ∈ G(H)} H_g` into the irreducible components
of the group-like elements, together with the elementary observation that a group-like element
`a` lies in `μ I` as soon as `1 - a ∈ I`.  Given `y ∈ I`, write `y = ∑ y_g` with `y_g ∈ H_g`.
Two group-like elements in the same coset of the group of group-like elements of `μ I` contribute
to the same component *modulo* `N = τ (μ I)` — this uses the stability of the irreducible
component of `1` under conjugation — so one may assume that the group-like elements occurring lie
in distinct cosets; then Kostant's decomposition of the quotient coalgebra `H ⧸ I` separates the
summands, so each `y_g` lies in `I`, and translating it back into the component of `1` the
irreducible case applies.

## Main results

* `Coalgebra.Coradical.map_eq_zero_of_sum_map_eq_zero` — the separation lemma at the level of
  coalgebras: a coalgebra map which keeps group-like elements apart also keeps their irreducible
  components apart;
* `HopfAlgebra.Cocommutative.mem_coinv_of_one_sub_mem` — a group-like element `a` with `1 - a ∈ I`
  lies in `μ I`;
* `HopfAlgebra.Cocommutative.IrreducibleCore` — the statement of the irreducible case, in the form
  in which it is used: the elements of `I` lying in the irreducible component of `1` lie in
  `τ (μ I)`;
* `HopfAlgebra.Cocommutative.tau_coinv_eq_of_irreducibleCore` — **the reduction**: for a pointed
  cocommutative Hopf algebra, the second closure identity `τ (μ I) = I` follows from its irreducible
  case.

## References

* [K. Newman, *A correspondence between bi-ideals and sub-Hopf algebras in cocommutative Hopf
  algebras*][Newman1975], Corollary 3.3
* [M. E. Sweedler, *Hopf algebras*][Sweedler], Chapter 8
* [S. Montgomery, *Hopf algebras and their actions on rings*][Montgomery1993], Section 5.6
-/

@[expose] public section

open TensorProduct Coalgebra Coalgebra.Coradical HopfAlgebra

universe u

namespace Coalgebra.Coradical

section Separation

variable {k A B : Type u} [Field k] [AddCommGroup A] [Module k A] [Coalgebra k A]
  [AddCommGroup B] [Module k B] [Coalgebra k B]

/-- Two group-like elements spanning the same line are equal. -/
theorem groupLikeElem_eq_of_span_eq {a b : B} (ha : IsGroupLikeElem k a)
    (hb : IsGroupLikeElem k b) (hab : Submodule.span k {a} = Submodule.span k {b}) : a = b := by
  have hmem : b ∈ Submodule.span k {a} := by
    rw [hab]; exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  have hcounit : counit (R := k) b = c * counit (R := k) a := by rw [← hc]; simp
  rw [ha.counit_eq_one, hb.counit_eq_one, mul_one] at hcounit
  rw [← hc, ← hcounit, one_smul]

variable [IsCocomm k B]

/-- **Separation of irreducible components along a coalgebra map.**  If `f` is a morphism of
coalgebras which separates the group-like elements `f g₀` and `f (g i)`, then an element of the
irreducible component of `g₀` whose image is cancelled by images of elements of the components of
the `g i` is itself killed by `f`. -/
theorem map_eq_zero_of_sum_map_eq_zero {f : A →ₗ[k] B}
    (hcomul : _root_.TensorProduct.map f f ∘ₗ (comul : A →ₗ[k] A ⊗[k] A) = comul ∘ₗ f)
    {ι : Type*} (S : Finset ι) {g₀ u₀ : A} {g u : ι → A}
    (hu₀ : u₀ ∈ irrComponent (Submodule.span k {g₀}))
    (hg₀ : IsGroupLikeElem k (f g₀))
    (hgl : ∀ i ∈ S, IsGroupLikeElem k (f (g i)))
    (hne : ∀ i ∈ S, f (g i) ≠ f g₀)
    (hu : ∀ i ∈ S, u i ∈ irrComponent (Submodule.span k {g i}))
    (hsum : f u₀ + ∑ i ∈ S, f (u i) = 0) : f u₀ = 0 := by
  classical
  have himg : ∀ (x y : A), x ∈ irrComponent (Submodule.span k {y}) →
      f x ∈ irrComponent (Submodule.span k {f y}) := by
    intro x y hx
    have h := map_irrComponent_le hcomul (Submodule.span k {y}) ⟨x, hx, rfl⟩
    rwa [Submodule.map_span, Set.image_singleton] at h
  have h0 : f u₀ ∈ irrComponent (Submodule.span k {f g₀}) := himg _ _ hu₀
  have h1 : f u₀ ∈ ⨆ T ∈ {T : Submodule k B | IsSimpleSubcoalgebra T ∧
      T ≠ Submodule.span k {f g₀}}, irrComponent T := by
    have hneg : f u₀ = -∑ i ∈ S, f (u i) := by
      rw [eq_neg_iff_add_eq_zero]; exact hsum
    rw [hneg]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    have hne' : Submodule.span k {f (g i)} ≠ Submodule.span k {f g₀} := fun hspan =>
      hne i hi (groupLikeElem_eq_of_span_eq (hgl i hi) hg₀ hspan)
    exact le_iSup₂ (f := fun T (_ : T ∈ {T : Submodule k B | IsSimpleSubcoalgebra T ∧
        T ≠ Submodule.span k {f g₀}}) => irrComponent T) (Submodule.span k {f (g i)})
      ⟨isSimpleSubcoalgebra_span_groupLike (hgl i hi), hne'⟩ (himg _ _ (hu i hi))
  have hbot := irrComponent_inf_iSup_eq_bot' (isSimpleSubcoalgebra_span_groupLike hg₀)
  exact (Submodule.eq_bot_iff _).1 hbot _ ⟨h0, h1⟩

end Separation

end Coalgebra.Coradical

namespace HopfAlgebra.Cocommutative

variable {k H : Type u} [Field k] [Ring H] [HopfAlgebra k H]

/-! ### Group-like elements and the coinvariants -/

/-- A group-like element `a` with `1 - a ∈ I` lies in the coinvariants `μ I`. -/
theorem mem_coinv_of_one_sub_mem {I : Submodule k H} {a : GroupLike k H}
    (h : (1 : H) - (a : H) ∈ I) : (a : H) ∈ coinv I := by
  rw [mem_coinv, a.2.comul_eq_tmul_self, ← TensorProduct.tmul_sub]
  refine tmul_mem_rightTensor _ ?_
  rw [show (a : H) - 1 = -((1 : H) - (a : H)) from (neg_sub _ _).symm]
  exact Submodule.neg_mem _ h

/-- If a group-like element `a` lies in `μ I`, then `H (a - 1) ⊆ τ (μ I)`. -/
theorem mul_sub_one_mem_tau {I : Submodule k H} {a : GroupLike k H}
    (ha : (a : H) ∈ coinv I) (h : H) : h * ((a : H) - 1) ∈ tau (coinv I) := by
  refine mul_mem_tau h ⟨Submodule.sub_mem _ ha (one_mem_coinv I), ?_⟩
  simp [a.2.counit_eq_one, Bialgebra.counit_one]

/-- Two group-like elements whose difference lies in a left ideal `I` differ by a group-like
element of `μ I`. -/
theorem inv_mul_mem_coinv_of_sub_mem {I : Submodule k H}
    (hI : ∀ (h : H), ∀ x ∈ I, h * x ∈ I) {g a : GroupLike k H}
    (h : (g : H) - (a : H) ∈ I) : ((g⁻¹ * a : GroupLike k H) : H) ∈ coinv I := by
  refine mem_coinv_of_one_sub_mem ?_
  have hmul : ((g⁻¹ * a : GroupLike k H) : H) = (g⁻¹ : GroupLike k H) * (a : H) := rfl
  have hone : ((g⁻¹ : GroupLike k H) : H) * (g : H) = 1 := by
    rw [show ((g⁻¹ : GroupLike k H) : H) * (g : H) = ((g⁻¹ * g : GroupLike k H) : H) from rfl,
      inv_mul_cancel]
    rfl
  have := hI ((g⁻¹ : GroupLike k H) : H) _ h
  rw [mul_sub, hone] at this
  rwa [hmul]

/-! ### Translation and conjugation of the components -/

/-- Elements of the component of a group-like element `g` are `g` times an element of the
component of `1`. -/
theorem exists_mem_glComponent_one {g : GroupLike k H} {x : H} (hx : x ∈ glComponent g) :
    ∃ v ∈ glComponent (1 : GroupLike k H), x = (g : H) * v := by
  have h := map_mulLeft_glComponent g (1 : GroupLike k H)
  rw [mul_one] at h
  rw [← h] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨v, hv, rfl⟩

/-- Conjugation by a group-like element preserves the irreducible component of `1`. -/
theorem conj_mem_glComponent_one (d : GroupLike k H) {x : H}
    (hx : x ∈ glComponent (1 : GroupLike k H)) :
    (d : H) * x * ((d⁻¹ : GroupLike k H) : H) ∈ glComponent (1 : GroupLike k H) := by
  have h1 : (d : H) * x ∈ glComponent d := mul_mem_glComponent d hx
  have h2 := map_mulRight_glComponent (d⁻¹ : GroupLike k H) d
  rw [mul_inv_cancel] at h2
  rw [← h2]
  exact ⟨(d : H) * x, h1, rfl⟩

/-! ### Separation of the components modulo a left bi-ideal -/

/-- The class of a group-like element in the quotient coalgebra `H ⧸ I` is group-like. -/
theorem isGroupLikeElem_mkQ {I : Submodule k H} (hI : IsLeftBiIdeal I) (g : GroupLike k H) :
    letI := quotCoalgebraStruct hI
    letI := quotCoalgebra hI
    IsGroupLikeElem k (I.mkQ (g : H)) := by
  let := quotCoalgebraStruct hI
  let := quotCoalgebra hI
  constructor
  · exact (quotCounit_mk hI (g : H)).trans g.2.counit_eq_one
  · refine (quotComul_mk hI (g : H)).trans ?_
    rw [g.2.comul_eq_tmul_self]
    rfl

/-- The quotient of a cocommutative Hopf algebra by a left bi-ideal is cocommutative. -/
theorem isCocomm_quot [IsCocomm k H] {I : Submodule k H} (hI : IsLeftBiIdeal I) :
    letI := quotCoalgebraStruct hI
    letI := quotCoalgebra hI
    IsCocomm k (H ⧸ I) := by
  let := quotCoalgebraStruct hI
  let := quotCoalgebra hI
  constructor
  refine LinearMap.ext fun q => ?_
  obtain ⟨x, rfl⟩ := I.mkQ_surjective q
  refine (TensorProduct.map_comm I.mkQ I.mkQ (comul (R := k) x)).symm.trans ?_
  rw [Coalgebra.comm_comul]
  exact (quotComul_mk hI x).symm

/-- **Separation modulo `I`.**  If the group-like elements `g₀` and `g ∈ S` have pairwise
different classes modulo the left bi-ideal `I`, then a relation `u₀ + ∑ u g ∈ I` between elements
of the corresponding components forces `u₀ ∈ I`. -/
theorem mem_of_sum_mem [IsCocomm k H] {I : Submodule k H} (hI : IsLeftBiIdeal I)
    {g₀ : GroupLike k H} {u₀ : H} (hu₀ : u₀ ∈ glComponent g₀)
    (S : Finset (GroupLike k H)) (u : GroupLike k H → H)
    (hu : ∀ g ∈ S, u g ∈ glComponent g)
    (hne : ∀ g ∈ S, (g : H) - (g₀ : H) ∉ I)
    (hsum : u₀ + ∑ g ∈ S, u g ∈ I) : u₀ ∈ I := by
  classical
  let := quotCoalgebraStruct hI
  let := quotCoalgebra hI
  have := isCocomm_quot hI
  have hcomul := (quotComul_comp_mkQ hI).symm
  have hzero : I.mkQ u₀ + ∑ g ∈ S, I.mkQ (u g) = 0 := by
    rw [← map_sum, ← map_add]
    exact (Submodule.Quotient.mk_eq_zero _).2 hsum
  have hkey : I.mkQ u₀ = 0 :=
    Coalgebra.Coradical.map_eq_zero_of_sum_map_eq_zero hcomul S (g₀ := (g₀ : H)) (u₀ := u₀)
      (g := fun g : GroupLike k H => (g : H)) (u := u) hu₀ (isGroupLikeElem_mkQ hI g₀)
      (fun g hg => isGroupLikeElem_mkQ hI g)
      (fun g hg hgeq => hne g hg (by
        have hq : (Submodule.Quotient.mk (g : H) : H ⧸ I) = Submodule.Quotient.mk (g₀ : H) := hgeq
        exact (Submodule.Quotient.eq I).1 hq))
      (fun g hg => hu g hg) hzero
  exact (Submodule.Quotient.mk_eq_zero _).1 hkey

/-! ### The reduction -/

variable (k H) in
/-- The **irreducible case** of Newman's second closure identity, in the form in which the
reduction uses it: every element of the left bi-ideal `I` which lies in the irreducible component
of `1` lies in `τ (μ I)`. -/
def IrreducibleCore (I : Submodule k H) : Prop :=
  ∀ y ∈ I, y ∈ glComponent (1 : GroupLike k H) → y ∈ tau (coinv I)

/-- Moving the term at `g` onto the term at `g₀ ≠ g`, corrected by `w`: the sum over `S.erase g`
of the updated family is the old sum minus `y g - w`. -/
theorem sum_erase_update_add [DecidableEq (GroupLike k H)] {S : Finset (GroupLike k H)}
    {g g₀ : GroupLike k H} (hgS : g ∈ S)
    (hg₀S : g₀ ∈ S) (hgne : g ≠ g₀) (y : GroupLike k H → H) (w : H) :
    ∑ h ∈ S.erase g, Function.update y g₀ (y g₀ + w) h = (∑ h ∈ S, y h) - (y g - w) := by
  have hg₀erase : g₀ ∈ S.erase g := Finset.mem_erase.2 ⟨fun h => hgne h.symm, hg₀S⟩
  have h1 : ∑ h ∈ S.erase g, Function.update y g₀ (y g₀ + w) h = ∑ h ∈ S.erase g, y h + w := by
    rw [← Finset.add_sum_erase _ _ hg₀erase, ← Finset.add_sum_erase _ y hg₀erase]
    have h2 : ∑ h ∈ (S.erase g).erase g₀, Function.update y g₀ (y g₀ + w) h =
        ∑ h ∈ (S.erase g).erase g₀, y h :=
      Finset.sum_congr rfl fun h hh => by
        simp [Function.update_of_ne (Finset.ne_of_mem_erase hh)]
    rw [h2]
    simp only [Function.update_self]
    abel
  rw [h1, ← Finset.add_sum_erase _ y hgS]
  abel

/-- **The merge step.** If `g₀⁻¹ g ∈ μ I`, every element `x` of the component of `g` differs from
an element `w` of the component of `g₀` by an element of `τ (μ I)`. -/
theorem exists_mem_glComponent_sub_mem_tau {I : Submodule k H} {g₀ g : GroupLike k H}
    (ha : ((g₀⁻¹ * g : GroupLike k H) : H) ∈ coinv I) {x : H} (hx : x ∈ glComponent g) :
    ∃ w ∈ glComponent g₀, x - w ∈ tau (coinv I) := by
  set a : GroupLike k H := g₀⁻¹ * g with hadef
  obtain ⟨v, hv, hyg⟩ := exists_mem_glComponent_one hx
  have hv'mem : (a : H) * v * ((a⁻¹ : GroupLike k H) : H) ∈ glComponent (1 : GroupLike k H) :=
    conj_mem_glComponent_one a hv
  have hga : (g : H) = (g₀ : H) * (a : H) := by
    rw [hadef, show ((g₀ : H)) * ((g₀⁻¹ * g : GroupLike k H) : H)
      = ((g₀ * (g₀⁻¹ * g) : GroupLike k H) : H) from rfl]
    rw [mul_inv_cancel_left]
  have haa : ((a⁻¹ : GroupLike k H) : H) * (a : H) = 1 := by
    rw [show ((a⁻¹ : GroupLike k H) : H) * (a : H) = ((a⁻¹ * a : GroupLike k H) : H) from rfl,
      inv_mul_cancel]
    rfl
  set w : H := (g₀ : H) * ((a : H) * v * ((a⁻¹ : GroupLike k H) : H)) with hwdef
  have key : w * (a : H) = x := by
    rw [hwdef, hyg, hga]
    simp only [mul_assoc, haa, mul_one]
  refine ⟨w, mul_mem_glComponent g₀ hv'mem, ?_⟩
  have hdiff : x - w = w * ((a : H) - 1) := by
    rw [mul_sub, mul_one, key]
  rw [hdiff]
  exact mul_sub_one_mem_tau ha _

/-- **The irreducible case, moved to any component.** An element of `I` in the component of a
group-like `g₀` lies in `τ (μ I)`: translate it into the component of `1` by `g₀⁻¹`. -/
theorem mem_tau_of_mem_glComponent {I : Submodule k H} (hI : IsLeftBiIdeal I)
    (hcore : IrreducibleCore k H I) {g₀ : GroupLike k H} {y : H} (hyI : y ∈ I)
    (hy : y ∈ glComponent g₀) : y ∈ tau (coinv I) := by
  obtain ⟨v, hv, hyv⟩ := exists_mem_glComponent_one hy
  have hvI : v ∈ I := by
    have hone : ((g₀⁻¹ : GroupLike k H) : H) * (g₀ : H) = 1 := by
      rw [show ((g₀⁻¹ : GroupLike k H) : H) * (g₀ : H) = ((g₀⁻¹ * g₀ : GroupLike k H) : H)
        from rfl, inv_mul_cancel]
      rfl
    have := hI.mul_mem ((g₀⁻¹ : GroupLike k H) : H) _ hyI
    rwa [hyv, ← mul_assoc, hone, one_mul] at this
  rw [hyv]
  exact tau_isLeftIdeal _ _ _ (hcore v hvI hv)

/-- The induction behind the reduction: an element of `I` which is a sum of elements of the
components of finitely many group-like elements lies in `τ (μ I)`. -/
theorem sum_mem_tau_coinv [IsCocomm k H] {I : Submodule k H} (hI : IsLeftBiIdeal I)
    (hcore : IrreducibleCore k H I) :
    ∀ (n : ℕ) (S : Finset (GroupLike k H)) (y : GroupLike k H → H), S.card = n →
      (∀ g ∈ S, y g ∈ glComponent g) → (∑ g ∈ S, y g) ∈ I → (∑ g ∈ S, y g) ∈ tau (coinv I) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro S y hcard hmem hsum
    rcases S.eq_empty_or_nonempty with rfl | ⟨g₀, hg₀S⟩
    · simp
    by_cases hcase : ∃ g ∈ S.erase g₀, ((g₀⁻¹ * g : GroupLike k H) : H) ∈ coinv I
    · -- **Merge**: two group-like elements in the same coset of `G(μ I)`.
      obtain ⟨g, hgerase, ha⟩ := hcase
      have hgS : g ∈ S := Finset.mem_of_mem_erase hgerase
      have hgne : g ≠ g₀ := Finset.ne_of_mem_erase hgerase
      obtain ⟨w, hwmem, hdiffN⟩ := exists_mem_glComponent_sub_mem_tau ha (hmem g hgS)
      -- the new family
      set y' : GroupLike k H → H := Function.update y g₀ (y g₀ + w) with hy'def
      have hsum' : ∑ h ∈ S.erase g, y' h = (∑ h ∈ S, y h) - (y g - w) :=
        sum_erase_update_add hgS hg₀S hgne y w
      have hmem' : ∀ h ∈ S.erase g, y' h ∈ glComponent h := by
        intro h hh
        by_cases hh0 : h = g₀
        · subst hh0
          simp only [hy'def, Function.update_self]
          exact Submodule.add_mem _ (hmem h hg₀S) hwmem
        · simp only [hy'def, Function.update_of_ne hh0]
          exact hmem h (Finset.mem_of_mem_erase hh)
      have hIsum' : ∑ h ∈ S.erase g, y' h ∈ I := by
        rw [hsum']
        exact Submodule.sub_mem _ hsum (tau_coinv_le hI.mul_mem hdiffN)
      have := IH _ (hcard ▸ Finset.card_erase_lt_of_mem hgS) (S.erase g) y' rfl hmem' hIsum'
      have hfinal : ∑ h ∈ S, y h = (∑ h ∈ S.erase g, y' h) + (y g - w) := by
        rw [hsum']; abel
      rw [hfinal]
      exact Submodule.add_mem _ this hdiffN
    · -- **Separate**: the class of `g₀` differs from all the others.
      push Not at hcase
      have hne : ∀ g ∈ S.erase g₀, (g : H) - (g₀ : H) ∉ I := by
        intro g hg hmemI
        refine hcase g hg (inv_mul_mem_coinv_of_sub_mem hI.mul_mem ?_)
        rw [show (g₀ : H) - (g : H) = -((g : H) - (g₀ : H)) from (neg_sub _ _).symm]
        exact Submodule.neg_mem _ hmemI
      have hsplit : y g₀ + ∑ g ∈ S.erase g₀, y g = ∑ g ∈ S, y g :=
        Finset.add_sum_erase _ y hg₀S
      have hy₀I : y g₀ ∈ I :=
        mem_of_sum_mem hI (hmem g₀ hg₀S) (S.erase g₀) y
          (fun g hg => hmem g (Finset.mem_of_mem_erase hg)) hne (by rw [hsplit]; exact hsum)
      have hy₀N : y g₀ ∈ tau (coinv I) := mem_tau_of_mem_glComponent hI hcore hy₀I (hmem g₀ hg₀S)
      have hcardlt : (S.erase g₀).card < n := hcard ▸ Finset.card_erase_lt_of_mem hg₀S
      have hrestI : ∑ g ∈ S.erase g₀, y g ∈ I := by
        have : ∑ g ∈ S.erase g₀, y g = (∑ g ∈ S, y g) - y g₀ := by rw [← hsplit]; abel
        rw [this]
        exact Submodule.sub_mem _ hsum hy₀I
      have := IH _ hcardlt (S.erase g₀) y rfl
        (fun g hg => hmem g (Finset.mem_of_mem_erase hg)) hrestI
      rw [← hsplit]
      exact Submodule.add_mem _ hy₀N this

/-- **Kostant's reduction.**  For a pointed cocommutative Hopf algebra over a field, Newman's
second closure identity `τ (μ I) = I` follows from its irreducible case (Newman [Newman1975],
Corollary 3.3). -/
theorem tau_coinv_eq_of_irreducibleCore [IsCocomm k H] (hpt : IsPointed k H)
    {I : Submodule k H} (hI : IsLeftBiIdeal I) (hcore : IrreducibleCore k H I) :
    tau (coinv I) = I := by
  classical
  refine le_antisymm (tau_coinv_le hI.mul_mem) fun y hy => ?_
  have hmemsup : y ∈ ⨆ g : GroupLike k H, glComponent g := by
    rw [iSup_glComponent_eq_top hpt]; trivial
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ y).1 hmemsup
  set S : Finset (GroupLike k H) := f.support with hS
  set z : GroupLike k H → H := fun g => (f g : H) with hz
  have hsum : ∑ g ∈ S, z g = y := hf
  have hmem : ∀ g ∈ S, z g ∈ glComponent g := fun g _ => (f g).2
  have := sum_mem_tau_coinv hI hcore S.card S z rfl hmem (by rw [hsum]; exact hy)
  rwa [hsum] at this

end HopfAlgebra.Cocommutative
