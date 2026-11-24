module

public import Mathlib.CategoryTheory.Presentable.SharplyLT.Basic

/-!
# Directed subsets closed under witnesses

Let `λ ⊲ κ` be regular cardinals (Mathlib's `Cardinal.SharplyLT λ κ`) and let `J` be a
`λ`-directed partially ordered type. Mathlib's `Cardinal.SharplyLT.exists_isCardinalFiltered_set`
(characterization (iv) of `λ ⊲ κ`) says that every `κ`-small subset of `J` is contained in a
`κ`-small `λ`-directed subset. This file adds a closure condition, which Mathlib does not have:
given *witness sets* `wit j k` of cardinality `< κ` for all `j, k : J`, the subset can be chosen
so that `wit j k ⊆ S` for all `j, k ∈ S`
(`Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed₂`).
The case of witness sets `wit j` attached to single elements is the corollary
`Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed`.

The subset is the union of a transfinite chain of length `λ`. At each step the current subset is
first enlarged by Mathlib's (iv), and then the witnesses of all pairs of its elements are added.
Regularity of `λ` makes the union `λ`-directed; regularity of `κ`, together with `λ < κ`, makes
it `κ`-small.

## Main results

* `Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed₂`: witnesses attached to pairs.
* `Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed`: witnesses attached to elements.

## References

* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], 2.11
* [M. Makkai, R. Paré, *Accessible Categories: The Foundations of Categorical Model
  Theory*][MakkaiPare1989AccessibleCategories]
-/

@[expose] public section

universe w

open CategoryTheory

namespace Cardinal.SharplyLT

namespace WitnessClosure

/-! Auxiliary definitions for the proof of `exists_isCardinalFiltered_set_closed₂`. -/

variable {J : Type w}

/-- One step of the closure: enlarge `V` to `dir V` and add the witnesses `wit j k` of all
pairs of elements of `dir V`. -/
def step (dir : Set J → Set J) (wit : J → J → Set J) (V : Set J) : Set J :=
  dir V ∪ ⋃ (p : dir V × dir V), wit p.1.1 p.2.1

/-- The set `dir V` is contained in `step dir wit V`. -/
lemma dir_subset_step (dir : Set J → Set J) (wit : J → J → Set J) (V : Set J) :
    dir V ⊆ step dir wit V :=
  Set.subset_union_left

/-- If `j, k ∈ dir V`, then `wit j k ⊆ step dir wit V`. -/
lemma wit_subset_step (dir : Set J → Set J) (wit : J → J → Set J) (V : Set J) {j k : J}
    (hj : j ∈ dir V) (hk : k ∈ dir V) : wit j k ⊆ step dir wit V :=
  (Set.subset_iUnion (fun (p : dir V × dir V) ↦ wit p.1.1 p.2.1) ⟨⟨j, hj⟩, ⟨k, hk⟩⟩).trans
    Set.subset_union_right

/-- The transfinite iteration of `step`, of length `λ`, starting from `U`. -/
noncomputable def seq (lam : Cardinal.{w}) (dir : Set J → Set J) (wit : J → J → Set J)
    (U : Set J) : lam.ord.ToType → Set J
  | a => U ∪ ⋃ (b : {b : lam.ord.ToType // b < a}), step dir wit (seq lam dir wit U b.1)
  termination_by a => a
  decreasing_by exact b.2

variable {lam : Cardinal.{w}} {dir : Set J → Set J} {wit : J → J → Set J} {U : Set J}

/-- The defining equation of `seq`: its value at `a` is the union of `U` and of the sets
`step dir wit (seq lam dir wit U b)` for `b < a`. -/
lemma seq_eq (a : lam.ord.ToType) :
    seq lam dir wit U a =
      U ∪ ⋃ (b : {b : lam.ord.ToType // b < a}), step dir wit (seq lam dir wit U b.1) := by
  rw [seq]

/-- Every stage `seq lam dir wit U a` contains `U`. -/
lemma subset_seq (a : lam.ord.ToType) : U ⊆ seq lam dir wit U a := by
  rw [seq_eq]
  exact Set.subset_union_left

/-- If `b < a`, then `step dir wit (seq lam dir wit U b) ⊆ seq lam dir wit U a`. -/
lemma step_seq_subset {a b : lam.ord.ToType} (hb : b < a) :
    step dir wit (seq lam dir wit U b) ⊆ seq lam dir wit U a := by
  rw [seq_eq (a := a)]
  exact Set.subset_union_of_subset_right
    (Set.subset_iUnion (fun (c : {b' : lam.ord.ToType // b' < a}) ↦
      step dir wit (seq lam dir wit U c.1)) ⟨b, hb⟩) _

/-- If `V ⊆ dir V` for all `V`, then `seq lam dir wit U b ⊆ seq lam dir wit U a` whenever
`b ≤ a`. -/
lemma seq_mono (hdir : ∀ V, V ⊆ dir V) {a b : lam.ord.ToType} (hb : b ≤ a) :
    seq lam dir wit U b ⊆ seq lam dir wit U a := by
  rcases eq_or_lt_of_le hb with rfl | h
  · exact subset_rfl
  · exact (hdir _).trans ((dir_subset_step dir wit _).trans (step_seq_subset h))

end WitnessClosure

open WitnessClosure

variable {lam kappa : Cardinal.{w}} [Fact lam.IsRegular] [Fact kappa.IsRegular]

/-- **Directed subsets closed under witnesses.** Let `λ ⊲ κ` and let `J` be a `λ`-directed
partially ordered type with a set `wit j k` of fewer than `κ` witnesses for all `j, k : J`.
Then every subset `U` of `J` of cardinality `< κ` is contained in a `λ`-directed subset `S` of
cardinality `< κ` with `wit j k ⊆ S` for all `j, k ∈ S`. -/
theorem exists_isCardinalFiltered_set_closed₂ (hsharp : lam.SharplyLT kappa) {J : Type w}
    [PartialOrder J] [IsCardinalFiltered J lam] (wit : J → J → Set J)
    (hwit : ∀ j k, HasCardinalLT (wit j k) kappa) (U : Set J) (hU : HasCardinalLT U kappa) :
    ∃ S : Set J, U ⊆ S ∧ IsCardinalFiltered S lam ∧ HasCardinalLT S kappa ∧
      ∀ j ∈ S, ∀ k ∈ S, wit j k ⊆ S := by
  classical
  have hκ : Cardinal.aleph0 ≤ kappa := Cardinal.IsRegular.aleph0_le Fact.out
  -- A choice of a `λ`-directed superset of each small set.
  have hdir (V : Set J) : ∃ (B : Set J), V ⊆ B ∧
      (HasCardinalLT V kappa → IsCardinalFiltered B lam ∧ HasCardinalLT B kappa) := by
    by_cases hV : HasCardinalLT V kappa
    · obtain ⟨B, h₁, h₂, h₃⟩ := hsharp.exists_isCardinalFiltered_set V hV
      exact ⟨B, h₁, fun _ ↦ ⟨h₂, h₃⟩⟩
    · exact ⟨V, subset_rfl, fun h' ↦ (hV h').elim⟩
  choose dir hdir₁ hdir₂ using hdir
  have hlam : HasCardinalLT lam.ord.ToType kappa := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hsharp.lt
  -- One step (directed hull plus witnesses) and the transfinite sequence stay small.
  have hstep (V : Set J) (hV : HasCardinalLT V kappa) :
      HasCardinalLT (step dir wit V) kappa :=
    hasCardinalLT_union hκ (hdir₂ V hV).2
      (hasCardinalLT_iUnion _ (hasCardinalLT_prod hκ (hdir₂ V hV).2 (hdir₂ V hV).2)
        (fun _ ↦ hwit _ _))
  have hseq (a : lam.ord.ToType) : HasCardinalLT (seq lam dir wit U a) kappa := by
    induction a using WellFoundedLT.induction with
    | _ a ih =>
      rw [seq_eq]
      exact hasCardinalLT_union hκ hU (hasCardinalLT_iUnion _
        (hlam.of_injective _ Subtype.val_injective) (fun b ↦ hstep _ (ih b.1 b.2)))
  have : NoMaxOrder lam.ord.ToType := Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  have hne : Nonempty lam.ord.ToType := IsCardinalFiltered.nonempty lam.ord.ToType lam
  -- `S` is the union of the sequence: it contains `U`, is small, directed and closed.
  refine ⟨⋃ a, seq lam dir wit U a, ?_, ?_, hasCardinalLT_iUnion _ hlam hseq, ?_⟩
  · exact (subset_seq hne.some).trans (Set.subset_iUnion _ hne.some)
  · refine isCardinalFiltered_preorder _ _ (fun K s hK ↦ ?_)
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    choose a ha using fun k ↦ Set.mem_iUnion.1 (s k).2
    let c := IsCardinalFiltered.max a hK
    have hc (k : K) : (s k).1 ∈ dir (seq lam dir wit U c) :=
      hdir₁ _ (seq_mono hdir₁ (leOfHom (IsCardinalFiltered.toMax a hK k)) (ha k))
    have := (hdir₂ _ (hseq c)).1
    let m := IsCardinalFiltered.max (fun k ↦ (⟨(s k).1, hc k⟩ : dir (seq lam dir wit U c))) hK
    obtain ⟨c', hc'⟩ := exists_gt c
    refine ⟨⟨m.1, Set.mem_iUnion.2 ⟨c', step_seq_subset hc' (dir_subset_step _ _ _ m.2)⟩⟩,
      fun k ↦ ?_⟩
    exact leOfHom (IsCardinalFiltered.toMax
      (fun k ↦ (⟨(s k).1, hc k⟩ : dir (seq lam dir wit U c))) hK k)
  · intro j hj k hk
    obtain ⟨a₁, ha₁⟩ := Set.mem_iUnion.1 hj
    obtain ⟨a₂, ha₂⟩ := Set.mem_iUnion.1 hk
    obtain ⟨a', ha'⟩ := exists_gt (max a₁ a₂)
    exact (wit_subset_step dir wit _ (hdir₁ _ (seq_mono hdir₁ (le_max_left _ _) ha₁))
      (hdir₁ _ (seq_mono hdir₁ (le_max_right _ _) ha₂))).trans
        ((step_seq_subset ha').trans (Set.subset_iUnion _ a'))


/-- Let `λ ⊲ κ` and let `J` be a `λ`-directed partially ordered type in which each element `j`
has a set `wit j` of fewer than `κ` witnesses. Then any subset `U` of `J` of cardinality `< κ`
is contained in a `λ`-directed subset `A` of cardinality `< κ` that is closed under witnesses. -/
theorem exists_isCardinalFiltered_set_closed (hsharp : lam.SharplyLT kappa) {J : Type w}
    [PartialOrder J] [IsCardinalFiltered J lam] (wit : J → Set J)
    (hwit : ∀ j, HasCardinalLT (wit j) kappa) (U : Set J) (hU : HasCardinalLT U kappa) :
    ∃ (A : Set J), U ⊆ A ∧ IsCardinalFiltered A lam ∧ HasCardinalLT A kappa ∧
      ∀ j ∈ A, wit j ⊆ A := by
  obtain ⟨A, hUA, hA, hAκ, hclosed⟩ :=
    exists_isCardinalFiltered_set_closed₂ hsharp (fun j _ => wit j) (fun j _ => hwit j) U hU
  exact ⟨A, hUA, hA, hAκ, fun j hj => hclosed j hj j hj⟩

end Cardinal.SharplyLT
