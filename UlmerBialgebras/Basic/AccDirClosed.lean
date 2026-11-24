module

public import Foundations.CategoryTheory.Limits.AccCover
public import Foundations.CategoryTheory.Presentable.WitnessClosure

/-!
# `κ`-small `λ`-directed subsets closed under witnesses

Mathlib's `Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT λ κ α` is the property of the
subsets of a partially ordered type `α` that are `λ`-directed and of cardinality `< κ`; for
`λ ⊲ κ` they form a `κ`-directed family
(`Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.isCardinalFiltered_subtype`), and an
object presented by a `λ`-directed diagram is the colimit of the colimits of its restrictions
to these subsets (`Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT.isColimit`), which is
how Mathlib raises the index of accessibility (`Cardinal.SharplyLT.isCardinalAccessibleCategory`).

The Makkai–Paré generation theorem for inserters and equifiers (`AccessibleEquifier.lean`,
`AccessibleInserter.lean`) needs a refinement which Mathlib does not have: given *witnesses*
`wit : α → α → Set α`, each of cardinality `< κ`, we consider those subsets `S` which also
satisfy `wit j k ⊆ S` for all `j, k ∈ S` (`UlmerBialgebras.dirSubsetsW`). Thanks to `λ ⊲ κ`, through
`Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed₂`, they still cover `α` and form a
`κ`-directed family. The witnesses record the stage at which a defect of the structure is corrected.

## Main results

* `UlmerBialgebras.exists_directed_presentation`: every object of a `λ`-accessible category is the
  colimit of a `λ`-directed diagram of `λ`-presentable objects (Mathlib's
  `isCardinalFilteredGenerator_isCardinalPresentable`, reindexed along
  `IsCardinalFiltered.exists_cardinal_directed`).
* `UlmerBialgebras.dirSubsetsW`: the `κ`-small `λ`-directed subsets closed under the witnesses.
* `UlmerBialgebras.dirSubsetsW_cover`: for `λ ⊲ κ` and `κ`-small witness sets, every element lies
  in some such subset.
* `UlmerBialgebras.isCardinalFiltered_dirSubsetsW`: under the same hypotheses, these subsets form a
  `κ`-directed poset.

## References

* [D. Forsman, *A Syntactic Approach to Ulmer's Bialgebras*][forsman2026syntactic], Example 2.3
* [M. Makkai, R. Paré, *Accessible categories: The foundations of categorical model
  theory*][MakkaiPare1989AccessibleCategories]
* [J. Adámek, J. Rosický, *Locally Presentable and Accessible Categories*][LPC], 1.21, 2.11
-/

@[expose] public section

universe w v u

namespace UlmerBialgebras

open CategoryTheory Limits Cardinal

/-- Every object of a `λ`-accessible category is the colimit of a `λ`-directed diagram of
`λ`-presentable objects. -/
theorem exists_directed_presentation {C : Type u} [Category.{v} C] (lam : Cardinal.{w})
    [Fact lam.IsRegular] [IsCardinalAccessibleCategory.{w} C lam] (X : C) :
    ∃ (α : Type w) (_ : PartialOrder α) (_ : IsCardinalFiltered α lam) (D : α ⥤ C)
      (c : Cocone D) (_ : IsColimit c), c.pt = X ∧ ∀ j, IsCardinalPresentable (D.obj j) lam := by
  obtain ⟨J₀, _, _, ⟨p₀⟩⟩ :=
    (isCardinalFilteredGenerator_isCardinalPresentable C lam).exists_colimitsOfShape X
  obtain ⟨α, _, _, F, _⟩ := IsCardinalFiltered.exists_cardinal_directed J₀ lam
  let p := p₀.reindex F
  exact ⟨α, _, inferInstance, p.diag, p.cocone, p.isColimit, rfl, p.prop_diag_obj⟩

variable {lam kappa : Cardinal.{w}} [Fact lam.IsRegular] [Fact kappa.IsRegular]
  {α : Type w} [PartialOrder α]

variable (lam kappa) in
/-- The `κ`-small `λ`-directed subsets of a partially ordered type (Mathlib's
`Cardinal.SharplyLT.IsCardinalFilteredAndHasCardinalLT`) which are closed under a family of
witnesses. -/
def dirSubsetsW (α : Type w) [PartialOrder α] (wit : α → α → Set α) : Set (Set α) :=
  {S | SharplyLT.IsCardinalFilteredAndHasCardinalLT lam kappa α S ∧
    ∀ j ∈ S, ∀ k ∈ S, wit j k ⊆ S}

variable {wit : α → α → Set α}

omit [Fact kappa.IsRegular] in
/-- A witness-closed subset contains the witnesses `wit j k` of any two of its elements. -/
lemma dirSubsetsW.closed (S : dirSubsetsW lam kappa α wit) {j : α} (hj : j ∈ S.1) {k : α}
    (hk : k ∈ S.1) : wit j k ⊆ S.1 := S.2.2 j hj k hk

/-- A witness-closed `κ`-small `λ`-directed subset is `λ`-filtered as a full subposet. -/
instance isCardinalFiltered_dirSubsetW (S : dirSubsetsW lam kappa α wit) :
    IsCardinalFiltered {x : α // x ∈ S.1} lam :=
  S.2.1.1

/-- A witness-closed `κ`-small `λ`-directed subset has fewer than `κ` arrows. -/
lemma hasCardinalLT_arrow_dirSubsetW (S : dirSubsetsW lam kappa α wit) :
    HasCardinalLT (Arrow {x : α // x ∈ S.1}) kappa :=
  (hasCardinalLT_arrow_iff_of_isThin _ _ (Cardinal.IsRegular.aleph0_le Fact.out)).2 S.2.1.2

section

variable [IsCardinalFiltered α lam]

/-- Every subset `U` of cardinality `< κ` of a `λ`-directed partially ordered type lies in some
witness-closed `κ`-small `λ`-directed subset (for `λ ⊲ κ` and `κ`-small witness sets). -/
lemma exists_dirSubsetW (hsharp : lam.SharplyLT kappa)
    (hwit : ∀ j k, HasCardinalLT (wit j k) kappa) (U : Set α) (hU : HasCardinalLT U kappa) :
    ∃ S : dirSubsetsW lam kappa α wit, U ⊆ S.1 := by
  obtain ⟨S, hUS, hS, hSκ, hclosed⟩ :=
      Cardinal.SharplyLT.exists_isCardinalFiltered_set_closed₂ hsharp wit hwit U hU
  exact ⟨⟨S, ⟨hS, hSκ⟩, hclosed⟩, hUS⟩

/-- Every element of a `λ`-directed partially ordered type lies in some witness-closed
`κ`-small `λ`-directed subset (for `λ ⊲ κ` and `κ`-small witness sets). -/
lemma dirSubsetsW_cover (hsharp : lam.SharplyLT kappa)
    (hwit : ∀ j k, HasCardinalLT (wit j k) kappa) (j : α) :
    ∃ S : dirSubsetsW lam kappa α wit, j ∈ S.1 := by
  obtain ⟨S, hS⟩ := exists_dirSubsetW hsharp hwit {j}
    (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))
  exact ⟨S, hS rfl⟩

/-- The witness-closed `κ`-small `λ`-directed subsets form a `κ`-directed poset (for `λ ⊲ κ`
and `κ`-small witness sets). -/
lemma isCardinalFiltered_dirSubsetsW (hsharp : lam.SharplyLT kappa)
    (hwit : ∀ j k, HasCardinalLT (wit j k) kappa) :
    IsCardinalFiltered (dirSubsetsW lam kappa α wit) kappa := by
  refine isCardinalFiltered_preorder _ _ (fun {K} s hs => ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hs
  obtain ⟨R, hR⟩ := exists_dirSubsetW hsharp hwit (⋃ k : K, (s k).1)
    (hasCardinalLT_iUnion _ hs (fun k => (s k).2.1.2))
  exact ⟨R, fun k x hx => hR (Set.mem_iUnion.2 ⟨k, hx⟩)⟩

/-- Any two witness-closed `κ`-small `λ`-directed subsets are contained in a third
(for `λ ⊲ κ` and `κ`-small witness sets). -/
lemma dirSubsetsW_directed (hsharp : lam.SharplyLT kappa)
    (hwit : ∀ j k, HasCardinalLT (wit j k) kappa) (S T : dirSubsetsW lam kappa α wit) :
    ∃ R : dirSubsetsW lam kappa α wit, S.1 ⊆ R.1 ∧ T.1 ⊆ R.1 := by
  have := isCardinalFiltered_dirSubsetsW hsharp hwit
  have : IsFiltered (dirSubsetsW lam kappa α wit) := isFiltered_of_isCardinalFiltered _ kappa
  exact ⟨IsFiltered.max S T, leOfHom (IsFiltered.leftToMax S T),
    leOfHom (IsFiltered.rightToMax S T)⟩

end

end UlmerBialgebras
